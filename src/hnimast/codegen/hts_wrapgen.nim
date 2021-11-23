import hmisc/core/all

importx:
  std/[
    macros, options, sequtils, strutils,
    tables, sets, sha1, uri
  ]

  compiler/ast

  hmisc/[
    other/[hjson, hshell, oswrap, hlogger, hargparse],
    algo/[clformat, halgorithm, hstring_algo, hseq_distance, namegen],
    wrappers/treesitter
  ]

  ../../hnimast
  ../pprint


template mapItSome*[T](opt: Option[T], expr: untyped): untyped =
  type ResT = typeof((var it {.inject.}: typeof(opt.get()); expr))
  var res: Option[ResT]
  if opt.isSome():
    let it {.inject.} = opt.get()
    res = some(expr)

  res


{.experimental: "caseStmtMacros".}

type
  TreeChildren = object
    multiple: bool
    required: bool
    types: seq[tuple[ttype: string, named: bool]]

  Tree = object
    ttype: string
    named: bool
    children: Option[TreeChildren]

  NodeSpec = object
    nodes: seq[Tree]
    externals: seq[string]



func id(str: string): PNode = newPident(str)
proc lit(arg: string | int): PNode = newPLit(arg)



func toTree(js: JsonNode): Tree =
  result = Tree(
    ttype: js["type"].asStr(),
    named: js["named"].asBool()
  )

  if "children" in js:
    let ch = js["children"]
    result.children = some TreeChildren(
      multiple: ch["multiple"].asBool(),
      required: ch["required"].asBool(),
      types: ch["types"].mapIt((
        ttype: it["type"].asStr(),
        named: it["named"].asBool())))


func toNtermName(str: string): string =
  if str.validIdentifier() and str != "_":
    str.splitCamel().joinCamel()
  else:
    str.toNamedMulticharJoin()

func ntermName(elem: Tree, lang: string): string =
  result = lang & elem.ttype.toNtermName().capitalizeAscii()
  if not elem.named:
    result &= "Tok"

func makeNodeName(lang: string): string =
  "Ts" & lang.capitalizeAscii() & "Node"

func makeNodeKindName(lang: string): string =
  lang.capitalizeAscii() & "NodeKind"

func langErrorName(lang: string): string =
  lang & "SyntaxError"


proc makeKindEnum(
    spec: NodeSpec,
    lang: string,
    names: var StringNameCache
  ): PEnumDecl =

  result = PEnumDecl(name: lang.makeNodeKindName(), exported: true)
  for elem in spec.nodes:
    let name = elem.ntermName(lang)
    if not names.hasExactName(name):
      let newName = names.getName(name)
      # debug "name", name, "used first time -> ", newName
      result.values.add makeEnumField[PNode](
        newName, comment = elem.ttype)

    # else:
    #   debug "Name", name, "already used."

  result.values.add makeEnumField[PNode](
    lang.langErrorName(),
    comment = "Tree-sitter parser syntax error"
  )


proc makeGetKind(
    spec: NodeSpec,
    lang: string,
    names: var StringNameCache
  ): ProcDecl[PNode] =

  result = newPProcDecl(
    "kind",
    {"node" : newPType(lang.makeNodeName())},
    some newPType(lang.makeNodeKindName()),
    pragma = newPPragma("noSideEffect")
  )

  let nameGet = nnkDotExpr.newPTree("node".id, "tsNodeType".id)
  var impl = nnkCaseStmt.newPTree(nameGet)

  var used: HashSet[string]
  for elem in spec.nodes:
    let name = elem.ttype
    if name notin used:
      used.incl name
      impl.add nnkOfBranch.newPTree(
        newPLit(name),
        newPIdent(names.getName(elem.ntermName(lang)))
      )

  impl.add nnkOfBranch.newPTree(
    newPLit("ERROR"),
    newPIdent(lang & "SyntaxError")
  )

  let assrt = pquote do:
    raiseAssert("Invalid element name '" & `nameGet` & "'")

  impl.add nnkElse.newPTree(assrt)

  result.impl = pquote do:
    {.cast(noSideEffect).}:
      `impl`

func camelCase(str: varargs[string, `$`]): string =
  str.joinCamel()

func pascalCase(str: varargs[string, `$`]): string =
  result = str.joinCamel()
  result[0] = result[0].toUpperAscii()

func makeLangParserName(lang: string): string =
  pascalCase(lang, "parser")


proc makeImplTsFor(lang: string, onlyCore: bool): PNode =
  result = nnkStmtList.newPTree()
  let
    langCap       = lang.capitalizeAscii()
    parser        = lang.makeLangParserName().newPType().toNNode()
    kindType      = lang.makeNodeKindName().newPIdent()
    nodeType      = lang.makeNodeName().newPType().toNNode()
    langLen       = newPLit(lang.len)
    langImpl      = newPIdent("tree_sitter_" & lang)
    newParserID   = newPIdent("newTs" & lang.makeLangParserName())
    parseStringID = newPIdent(&["parseTs", langCap, "String"])
    parseTreeId   = newPident(&["parse", langCap, "String"])
    htsType       = newPident(langCap & "Node")
    treeReprId    = newPIdent("treeReprTs" & langCap)



  result.add pquote do:
    func isNil*(node: `nodeType`): bool =
      ts_node_is_null(TSNode(node))

    func len*(node: `nodeType`, unnamed: bool = false): int =
      if unnamed:
        int(ts_node_child_count(TSNode(node)))
      else:
        int(ts_node_named_child_count(TSNode(node)))

    func has*(node: `nodeType`, idx: int, unnamed: bool = false): bool =
      0 <= idx and idx < node.len(unnamed)

    proc `langImpl`(): PtsLanguage {.importc, cdecl.}

    proc tsNodeType*(node: `nodeType`): string =
      $ts_node_type(TSNode(node))

    proc `newParserID`*(): `parser` =
      result = `parser`(ts_parser_new())
      discard ts_parser_set_language(PtsParser(result), `langImpl`())

    proc parseString*(parser: `parser`; str: string): `nodeType` =
      `nodeType`(
        ts_tree_root_node(
          ts_parser_parse_string(
            PtsParser(parser), nil, str.cstring, uint32(len(str)))))

    proc `parseStringID`*(str: string): `nodeType` =
      let parser = `newParserId`()
      return parseString(parser, str)

    func `$`*(node: `nodeType`): string =
      if isNil(node):
        "<nil tree>"

      else:
        $node.kind



  if onlyCore:
    result.add pquote do:
      proc treeRepr*(node: `nodeType`, str: string): string =
        var res = addr result

        proc aux(node: `nodeType`, level: int) =
          for i in 0 ..< level:
            res[].add "  "

          res[].add $node.kind

          if len(node) == 0:
            res[].add " "
            res[].add str[node]

          else:
            for sub in items(node):
              res[].add "\n"
              aux(sub, level + 1)

        aux(node, 0)




  else:
    result.add pquote do:
      func `[]`*(
          node: `nodeType`,
          idx: int,
          kind: `kindType` | set[`kindType`]): `nodeType` =

        assert 0 <= idx and idx < node.len
        result = `nodeType`(ts_node_named_child(TSNode(node), uint32(idx)))
        assertKind(
          result, kind,
          "Child node at index " & $idx & " for node kind " & $node.kind)

      type `htsType`* = HtsNode[`nodeType`, `kindType`]

      proc `treeReprId`*(
          str: string,
          unnamed: bool = false
        ): ColoredText =
        treeRepr[`nodeType`, `kindType`](
          `parseStringId`(str), str,
          `langLen`,
          unnamed = unnamed
        )

      proc toHtsNode*(node: `nodeType`, str: ptr string):
        HtsNode[`nodeType`, `kindType`] =

        toHtsNode[`nodeType`, `kindType`](node, str)

      proc toHtsTree*(node: `nodeType`, str: ptr string): `htsType` =
        toHtsNode[`nodeType`, `kindType`](node, str)

      proc `parseTreeID`*(
          str: ptr string, unnamed: bool = false
        ): `htsType` =

        let parser = `newParserId`()
        return toHtsTree[`nodeType`, `kindType`](
          parseString(parser, str[]), str)

      proc `parseTreeID`*(
          str: string, unnamed: bool = false
        ): `htsType` =

        let parser = `newParserId`()
        return toHtsTree[`nodeType`, `kindType`](
          parseString(parser, str), unsafeAddr str, storePtr = false)

proc makeDistinctType*(baseType, aliasType: NType[PNode]): PNode =
  let
    aliasType = aliasType.toNNode()
    baseType = baseType.toNNode()

  pquote do:
    type `aliasType`* = distinct `baseType`


proc createProcDefinitions(
    spec: NodeSpec,
    inputLang: string,
    names: var StringNameCache,
    l: HLogger,
    onlyCore: bool
  ): PNode =

  result = nnkStmtList.newPTree()

  if onlyCore:
    result.add pquote do:
      import
        hmisc/wrappers/treesitter_core

      export treesitter_core

  else:
    result.add pquote do:
      import
        hmisc/wrappers/treesitter,
        hmisc/core/all,
        hmisc/types/colorstring,
        std/strutils

      export treesitter

  result.add makeKindEnum(spec, inputLang, names).toNNode(standalone = true)

  if spec.externals.len > 0:
    var externEnum = PEnumDecl(
      name: inputLang.capitalizeAscii() & "ExternalTok",
      exported: true)

    var externSet: CountTable[string]
    for extern in spec.externals:
      if extern.normalize() notin externSet:
        externEnum.values.add makeEnumField[PNode](
          inputLang & "Extern" & extern.capitalizeAscii(),
          comment = extern
        )


      else:
        let name = inputLang & "Extern" & extern.capitalizeAscii() &
          "_" & $(externSet[extern.normalize()] + 1)

        l.warn "External enum name clash"
        l.debug extern, "will be wrapped as", name

        externEnum.values.add makeEnumField[PNode](
          name,
          comment = extern
        )

      externSet.inc extern.normalize()

    result.add externEnum.toNNode(standalone = true)

  result.add makeDistinctType(
    newPType("TSNode"),
    newPType(makeNodeName(inputLang)))

  result.add makeDistinctType(
    newPType("PtsParser"),
    newPType(makeLangParserName(inputLang))
  )

  let langId = newPident makeNodeName(inputLang)

  result.add pquote do:
    proc tsNodeType*(node: `langId`): string

  result.add makeGetKind(spec, inputLang, names).toNNode()
  result.add makeImplTsFor(inputLang, onlyCore)


proc getAppCachedHashes*(): seq[string] =
  let cacheDir = getAppCacheDir()
  let cachedFiles = (cacheDir /. "cachedFiles.txt")
  if cachedFiles.fileExists():
    return cachedFiles.readFile().split("\n")

proc setAppCachedHashes*(files: seq[string]) =
  (getAppCacheDir() /. "cachedFiles.txt").writeFile(files.join("\n"))

proc noChangesForFile*(file: AnyFile): bool =
  if $secureHashFile(file.getStr()) in getAppCachedHashes():
    true
  else:
    false

const
  codegenConf = nformatConf(
    flags -= nffVerticalPackedOf
  )

proc compileGrammar(
    grammarJs:   AbsFile,
    langPrefix:  string,
    junkDir:     AbsDir,
    scannerFile: Option[AbsFile]                           = none(AbsFile),
    parserOut:   Option[AbsFile]                           = none(AbsFile),
    wrapperOut:  Option[AbsFile]                           = none(AbsFile),
    forceBuild:  bool                                      = false,
    testLink:    bool                                      = true,
    testCheck:   bool                                      = true,
    extraFiles:  seq[tuple[src: AbsFile, target: RelFile]] = @[],
    l:           HLogger                                   = newTermLogger()
  ): string =

  let junkDir = junkDir / langPrefix

  l.info "Lang prefix", langPrefix
  l.debug junkDir

  l.info "Using cache dir", junkDir

  let startDir = cwd()

  rmDir junkDir
  mkDir junkDir
  withDir junkDir:
    l.info "Started temporary directory"
    l.debug cwd()
    cpFile grammarJs, RelFile("grammar.js")
    if extraFiles.len > 0:
      l.indented:
        l.info "Copying extra files"
        for (src, target) in extraFiles:
          mkDir target.dir
          cpFile src, target
          l.debug src, "->\n", target

    l.execShell(shellCmd(
      npm, --silent, link,
      "regexp-util", "tree-sitter-c", "readdir-enhanced", "nan"
    ))

    l.info "Linked regexp-util BS for node.js, generating files"
    for file in walkDir(cwd(), yieldFilter = {}):
      l.debug file

    l.execShell shellCmd("tree-sitter", "generate")
    l.debug "Done"

    if scannerFile.isSome():
      let file = scannerFile.get()
      cpFile file, RelFile("src/scanner.c")

    var spec = NodeSpec(
      nodes: "src/node-types.json".parseFile(
      ).getElems().mapIt(it.toTree())
    )

    let grammar = "src/grammar.json".parseFile()

    for extra in grammar["extras"]:
      if "name" in extra:
        let name = extra["name"]
        spec.nodes.add Tree(ttype: name.asStr(), named: true)

    for extern in grammar["externals"]:
      if "name" in extern:
        spec.externals.add extern["name"].asStr()


    let lang: string = grammar["name"].asStr()

    let
      parserOut = if parserOut.isSome():
                    parserOut.get()

                  else:
                    startDir /. (lang & "_parser.o")

      wrapperOut = if wrapperOut.isSome():
                     wrapperOut.get()

                   else:
                     startDir /. (lang & "_wrapper.nim")

      wrapperCoreOut = wrapperOut.withBaseSuffix("_core")


    block:
      var names: StringNameCache
      wrapperOut.writeFile(
        createProcDefinitions(spec, lang, names, l, false).toPString(codegenConf))

      l.info "Wrote generated wrappers to", wrapperOut

    block:
      var names: StringNameCache
      wrapperCoreOut.writeFile(
        createProcDefinitions(spec, lang, names, l, true).toPString(codegenConf))

      l.info "Wrote core-only wrappers to", wrapperCoreOut


    if testCheck:
      l.debug "Running test check for generated wrapper"
      l.execShell shellCmd(nim, check, errormax = 2).withIt do:
        it.arg wrapperOut

      l.success "Generated wrapper semcheck ok"

    if testLink:
      l.debug "Linking parser.c"
      l.execShell makeGnuShellCmd("gcc").withIt do:
        it.arg "src/parser.c"
        it - "c"
        it - ("o", "", "parser.o")

    cpFile RelFile("src/parser.c"), parserOut
    l.debug "Copied parser file to", parserOut

    if scannerFile.isSome():
      let file = scannerFile.get()
      if testLink:
        l.debug "Linking", file
        l.execShell makeGnuShellCmd("gcc").withIt do:
          it.arg $file
          it - "c"
          it - ("o", "", "scanner.o")

    if extraFiles.len > 0:
      l.indented:
        l.info "Copying extra files to target directory"
        for (src, target) in extraFiles:
          if target.ext != "js":
            cpFile target, parserOut.dir / target
            l.debug target, "->\n", parserOut.dir / target

    l.info "tree-sitter object files generation ok"
    return lang

# proc argParse(
#   dst: var tuple[src: AbsFile, target: RelFile],
#   dfl: tuple[src: AbsFile, target: RelFile],
#   a: var ArgcvtParams): bool =

#   return false


proc grammarFromFile*(
    grammarJs:   AbsFile,
    scannerFile: Option[AbsFile] = none(AbsFile),
    parserUser:  Option[AbsFile] = none(AbsFile),
    parserOut:   Option[AbsFile] = none(AbsFile),
    wrapperOut:  Option[AbsFile] = none(AbsFile),
    cacheDir:    AbsDir         = getAppCacheDir(),
    nimcacheDir: Option[FsDir]  = none(FsDir),
    forceBuild:  bool           = false,
    langPrefix:  string         = "",
    testLink:    bool           = true,
    testCheck:   bool           = true,
    extraFiles: seq[tuple[src: AbsFile, target: RelFile]] = @[],
    l: HLogger             = newTermLogger()
  ) =

  l.info "Working directory is", cwd()
  if scannerFile.isNone():
    l.warn "No input scanner file"

  else:
    l.info "Scanner file is", scannerFile.get()
    l.info "Absolute scanner file position", scannerFile.get().toAbsFile()

  let lang = compileGrammar(
    grammarJs   = grammarJs,
    langPrefix  = langPrefix,
    junkDir     = cacheDir,
    forceBuild  = forceBuild,
    extraFiles  = extraFiles,
    scannerFile = scannerFile,
    wrapperOut  = wrapperOut,
    parserOut   = parserOut,
    testLink    = testLink,
    testCheck   = testCheck,
    l           = l
  )


  if parserUser.isSome():
    l.info "Test parser user file is some. Compiling ..."
    let user = parserUser.get()
    try:
      let res = runShell makeNimShellCmd("nim").withIt do:
        it.cmd "c"
        it - "r"
        if nimcacheDir.isSome():
          it - ("nimcache", nimcacheDir.get().getStr())

        it - ("warnings", "off")

        it - ("forceBuild", "on")
        # if scannerFile.isSome():
        #   it - ("passL", lang & "_scanner.o")

        # # Link parser
        # it - ("passL", lang & "_parser.o")

        # TODO make linking with C++ stdlib optional
        it - ("passL", "-lstdc++")

        # Link tree-sitter
        it - ("passL", "-ltree-sitter")

        it.arg user

      echo res.stdout
      echo res.stderr

    except ShellError as ex:
      echo ex.outstr
      # echo ex.msg
      for line in ex.errstr.split("\n"):
        if line.contains(["undefined reference"]):
          if line.contains("external"):
            once: l.err "Missing linking with external scanners"
            l.info line.split(" ")[^1][1..^2]

          elif line.contains("ts_"):
            once: l.err "Missing linking with tree-sitter library"
            l.info line

          elif line.contains("std::"):
            once: l.err "Missing linking with C++ stdlib"
            l.info line

          elif line.contains("tree_sitter_"):
            once: l.err "Missing linking with compiled parser"

          else:
            once: l.err "Missing linking with other library"
            l.info line

        elif line.contains(["/bin/ld", "ld returned"]):
          discard
        else:
          echo line

import std/httpclient

func cliCheckFor*(url: typedesc[Url]): CliCheck = checkAcceptAll()
func toCliValue*(url: Url, doc: string = "", desc: CliDesc = nil): CliValue =
  specialStringCliValue(url.string, doc, desc)

func fromCLiValue*(value: CliValue, url: var Url) =
  url = Url(value.strVal)

proc grammarFromUrl*(
    grammarUrl: Url,
    grammarFile: AbsFile,
    scannerUrl: Option[Url]      = none(Url),
    scannerFile: Option[AbsFile] = none(AbsFile),
    parserOut: Option[AbsFile]   = none(AbsFile),
    extraFiles: seq[tuple[src: AbsFile, target: RelFile]] = @[],
    testLink: bool = true,
    l: HLogger = newTermLogger()
  ) =

  let client = newHttpClient()
  client.downloadFile(grammarUrl.string, grammarFile.getStr())
  if scannerUrl.getSome(scanner):
    assertOption scannerFile
    client.downloadFile(scanner.string, scannerFile.get().getStr())

  else:
    assertArg(
      scannerFile,
      scannerFile.isNone(),
      "Scanner URL was 'none', but download path for target " &
      "scanner was specified."
    )

  grammarFromFile(
    grammarJs   = grammarFile,
    scannerFile = scannerFile,
    parserOut   = parserOut,
    extraFiles  = extraFiles,
    testLink    = testLink,
    l           = l
  )

const
  commonOpts = @{
    "parserOut": "File to write generated parser to",
    "testLink": "Test linkage of the generated parsers",
    "testCheck": "Test `nim check` on the generated wrappers",
    "extraFiles": "Additional files to copy",
  }
  confGrammarFromUrl = procConf(
    ignore = @["l"],
    help = commonOpts & @{
      "grammarUrl": "URL to download grammar file from",
      "grammarFile": "Path to save downloaded file",
      "scannerUrl": "ULR to download scanner file from",
      "scannerFile": "Path to save scanner file",
    }
  )

  confGrammarFromFile = procConf(
    ignore = @["l"],
    positional = @["grammarJs"],
    help = commonOpts & @{
      "grammarJs": "Input js grammar file",
      "scannerFile": "C/C++ code for tree-sitter scanner",
      "parseruser": "Nim file to compile immediately after grammar generation",
      "wrapperOut": "File to write generated nim wrappers to",
      "cacheDir": "Grammar generation cache directory",
      "nimcacheDir": "Nim compilation cache directory",
      "forceBuild": "Force rebuild",
      "langPrefix": "Language prefix, will be prefixed for wrappers types",
    }
  )

proc newApp*(): CliApp =
  result = newCliApp(
    "hts_wrapgen", (0, 1, 1), "haxscramper",
    "Generate nim wrappers for tree-sitter grammars",
    noDefault = cliNoLoggerConfig & "force"
  )

  result.add cmd(grammarFromFile, conf = confGrammarFromFile)
  result.add cmd(grammarFromUrl, conf = confGrammarFromUrl)

proc main*(
    args: seq[string],
    logger: HLogger = newTermLogger(),
    doQuit: bool = true
  ) =
  echo args
  var app = newApp()
  app.acceptArgsAndRunBody(logger, args):
    app.runDispatched([
      (grammarFromFile, confGrammarFromFile),
      (grammarFromUrl, confGrammarFromUrl)
    ], logger, doQuit = doQuit)

when isMainModule:
  main(paramStrs())
  # if paramCount() == 0:
  #   grammarFromFile(
  #     forceBuild = true,
  #     parserUser = some RelFile("parser_user.nim"))
  # else:
  #   dispatchMulti(
  #     [grammarFromFile],
  #     [grammarFromUrl]
  #   )
