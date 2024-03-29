import hmisc/core/[all, code_errors]

importx:
  std/[
    macros, options, sequtils, strutils,
    tables, sets, sha1, uri
  ]

  compiler/ast

  hmisc/[
    other/[hjson, hshell, oswrap, hlogger, hargparse, hpprint],
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

  GrammarRule* = ref object
    ttype*: string
    members*: seq[GrammarRule]
    name*: string
    value*: string
    content*: GrammarRule

  GrammarSpec* = object
    name*: string
    rules*: Table[string, GrammarRule]


  HtsGenConf = object
    grammarJs*:   AbsFile
    langPrefix*:  string
    junkDir*:     AbsDir
    scannerFile*: Option[AbsFile]
    parserOut*:   Option[AbsFile]
    wrapperOut*:  Option[AbsFile]
    forceBuild*:  bool
    testLink*:    bool
    testCheck*:   bool
    extraFiles*:  seq[tuple[src: AbsFile, target: RelFile]]
    l*:           HLogger
    describeGrammar*: proc(grammar: GrammarSpec, names: var StringNameCache): PNode
    parserUser*:  Option[AbsFile]
    nimcacheDir*: Option[AbsDir]


let defaultHtsGenConf* = HtsGenConf(
    scannerFile:     none(AbsFile),
    parserOut:       none(AbsFile),
    wrapperOut:      none(AbsFile),
    forceBuild:      false,
    testLink:        true,
    testCheck:       true,
    extraFiles:      @[],
    describeGrammar: nil
)


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

func ntermName*(ttype: string, named: bool, lang: string): string =
  var lead = true
  result &= lang
  if ttype[0] == '_':
    result.add "Hid"
  #   result.add ttype[1..^1]

  # else:
  #   result.add ttype

  result.add ttype.toNtermName().capitalizeAscii()

  if not named:
    result &= "Tok"

  # if "jsx_element" in ttype:
  #   echov ttype, "->", result

func ntermName*(elem: Tree, lang: string): string =
  ntermName(elem.ttype, elem.named, lang)

func makeNodeName(lang: string): string =
  "Ts" & lang.capitalizeAscii() & "Node"

func makeNodeKindName*(lang: string): string =
  lang.capitalizeAscii() & "NodeKind"

func langErrorName(lang: string): string =
  lang & "SyntaxError"

proc tryGetName*(
    names: var StringNameCache, tt: string,
    named: bool, lang: string): Option[string] =

  let name = ntermName(tt, named, lang)
  result = some names.getName(name)

proc makeKindEnum(
    spec: NodeSpec,
    lang: string,
    names: var StringNameCache,
    hidden: HashSet[string]
  ): tuple[penum: PEnumDecl, pproc: PProcDecl] =

  var namecase = newCase(newPIdent("kind"))

  result.penum = PEnumDecl(name: lang.makeNodeKindName(), exported: true)
  var generated: HashSet[string]

  for (ttype, named) in
    spec.nodes.mapIt((it.ttype, it.named)) &
    hidden.mapIt((it, true)):

    let newName = names.getName(ntermName(ttype, named, lang))
    if newName notin generated:
      generated.incl newName
      result.penum.values.add makeEnumField[PNode](
        newName, comment = ttype)

      namecase.addBranch(newPIdent(newName), newPLit(ttype))

    else:
      echov newName

  namecase.addBranch(lang.langErrorName().newPident(), newPLit("ERROR"))

  result.pproc = newPprocDecl(
    "strRepr",
    {"kind": newPType(result.penum.name)},
    returnType = some newPType("string"),
    impl = namecase
  )

  result.penum.values.add makeEnumField[PNode](
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


proc makeImplTsFor(
    lang: string, onlyCore: bool, langFull: string): PNode =
  result = nnkStmtList.newPTree()
  let
    langCap       = lang.capitalizeAscii()
    parser        = lang.makeLangParserName().newPType().toNNode()
    kindType      = lang.makeNodeKindName().newPIdent()
    nodeType      = lang.makeNodeName().newPType().toNNode()
    langLen       = newPLit(lang.len)
    langImpl      = newPIdent("tree_sitter_" & langFull)
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
    onlyCore: bool,
    langFull: string,
    hidden: HashSet[string]
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

  let (penum, pconvert) = makeKindEnum(spec, inputLang, names, hidden)
  result.add penum.toNNode(standalone = true)
  result.add pconvert.toNNode()

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

  var allowedKinds = newPStmtList()
  var tokenKinds = newPTree(nnkCurly)
  var hiddenKinds = newPTree(nnkCurly)

  for name in hidden:
    hiddenKinds.add newPIdent(
      names.getName(name.ntermName(true, inputLang)))

  for node in spec.nodes:
    let name = newPIdent(names.getName(node.ntermName(inputLang)))
    if not node.named:
      tokenKinds.add name

    if node.children.isSome():
      allowedKinds.add newXCall("[]=",
        newPIdent("tmp"),
        name,
        newPTree(
          nnkCurly,
          node.children.get().types.mapIt(
            newPIdent(
              names.getName((
                ntermName(it[0], it[1], inputLang)))))))


  let kindType = inputLang.makeNodeKindName().newPIdent()

  let tmp1 = newPIdent(inputLang & "AllowedSubnodes")
  let tmp2 = newPIdent(inputLang & "TokenKinds")
  let tmp3 = newPIdent(inputLang & "HiddenKinds")

  result.add pquote do:
    const `tmp1`*: array[`kindType`, set[`kindType`]] =
      block:
        var tmp: array[`kindType`, set[`kindType`]]
        `allowedKinds`
        tmp

    const `tmp2`*: set[`kindType`] = `tokenKinds`
    const `tmp3`*: set[`kindType`] = `hiddenKinds`

  result.add pquote do:
    proc tsNodeType*(node: `langId`): string

  result.add makeGetKind(spec, inputLang, names).toNNode()
  result.add makeImplTsFor(inputLang, onlyCore, langFull)


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

proc toRules(j: JsonNode): GrammarSpec =
  proc aux(j: JsonNode): GrammarRule =
    result = GrammarRule(ttype: j["type"].asStr())
    case result.ttype:
      of "REPEAT", "REPEAT1":
        result.content = aux(j["content"])

      of "PATTERN", "STRING":
        result.value = j["value"].asStr()

      of "SYMBOL":
        result.name = j["name"].asStr()

      of "CHOICE", "SEQ":
        result.members = j["members"].mapIt(aux(it))

      of "FIELD", "ALIAS", "TOKEN", "PREC_RIGHT",
         "PREC_DYNAMIC", "PREC", "PREC_LEFT",
         "IMMEDIATE_TOKEN":
        result = j["content"].aux()

      of "BLANK":
        discard

      else:
        raise newUnexpectedKindError(result.ttype)


  result.name = j["name"].asStr()

  for key, rule in j["rules"]:
    result.rules[key] = aux(rule)

proc findHidden(conf: GrammarSpec, explicit: HashSet[string]): HashSet[string] =
  proc aux(rule: GrammarRule, res: var HashSet[string]) =
    if isNil(rule): return
    case rule.ttype:
      of "SYMBOL":
        if rule.name.startsWith("_") or rule.name notin explicit:
          res.incl rule.name

      else:
        aux(rule.content, res)
        for mem in rule.members:
          aux(mem, res)


  for key, rule in conf.rules:
    aux(rule, result)

    if key notin explicit:
      result.incl key

proc findHidden(conf: NodeSpec, explicit: HashSet[string]): HashSet[string] =
  for node in conf.nodes:
    if node.ttype notin explicit:
      result.incl node.ttype

    if node.children.isSome():
      for (ch, named) in node.children.get().types:
        if ch notin explicit:
          result.incl ch

proc compileGrammar(conf: HtsGenConf): string =
  doAssert conf.langPrefix.len > 0
  let l = conf.l

  let junkDir = conf.junkDir / conf.langPrefix

  l.info "Lang prefix", conf.langPrefix
  let lang = conf.langPrefix
  l.debug junkDir

  l.info "Using cache dir", junkDir

  let startDir = cwd()

  rmDir junkDir
  mkDir junkDir
  withDir junkDir:
    l.info "Started temporary directory"
    l.debug cwd()
    cpFile conf.grammarJs, RelFile("grammar.js")
    if conf.extraFiles.len > 0:
      l.indented:
        l.info "Copying extra files"
        for (src, target) in conf.extraFiles:
          mkDir target.dir
          cpFile src, target
          l.debug src, "->\n", target

    l.execShell(shellCmd(
      npm, --silent, link,
      "regexp-util", "tree-sitter-c", "readdir-enhanced", "nan"
    ))

    l.info "Linked regexp-util BS for node.js, generating files"
    l.dump cwd()
    for file in walkDir(cwd(), yieldFilter = {}):
      l.debug file

    l.execShell shellCmd("tree-sitter", "generate")
    l.debug "Done"

    if conf.scannerFile.isSome():
      let file = conf.scannerFile.get()
      cpFile file, RelFile("src/scanner.c")

    var spec = NodeSpec()
    for el in parseFile("src/node-types.json"):
      spec.nodes.add el.toTree()

    let grammar = "src/grammar.json".parseFile()
    let grammarRules = grammar.toRules()

    var explicitlySpecified: HashSet[string]
    for elem in spec.nodes:
      explicitlySpecified.incl elem.ttype

    for extra in grammar["extras"]:
      if "name" in extra:
        let name = extra["name"].asStr()
        if name notin explicitlySpecified:
          spec.nodes.add Tree(ttype: name, named: true)

    for extern in grammar["externals"]:
      if "name" in extern:
        spec.externals.add extern["name"].asStr()


    let
      parserOut = if conf.parserOut.isSome():
                    conf.parserOut.get()

                  else:
                    startDir /. (lang & "_parser.o")

      wrapperOut = if conf.wrapperOut.isSome():
                     conf.wrapperOut.get()

                   else:
                     startDir /. (lang & "_wrapper.nim")

      wrapperCoreOut = wrapperOut.withBaseSuffix("_core")


    var hidden = grammarRules.findHidden(explicitlySpecified)
    let hiddenMissing = spec.findHidden(hidden + explicitlySpecified)
    hidden.incl hiddenMissing

    block:
      var names: StringNameCache
      var tmp = newPStmtList()

      tmp.add createProcDefinitions(
        spec, lang, names, l, false, grammar["name"].asStr(), hidden)

      if notNil(conf.describeGrammar):
        tmp.add conf.describeGrammar(grammarRules, names)

      wrapperOut.writeFile(tmp.toPString(codegenConf))
      l.info "Wrote generated wrappers to", wrapperOut

    block:
      var names: StringNameCache
      var tmp = newPStmtList()
      tmp.add createProcDefinitions(
        spec, lang, names, l, true, grammar["name"].asStr(), hidden)

      if notNil(conf.describeGrammar):
        tmp.add conf.describeGrammar(grammarRules, names)

      wrapperCoreOut.writeFile(tmp.toPString(codegenConf))

      l.info "Wrote core-only wrappers to", wrapperCoreOut

    if conf.testCheck:
      l.debug "Running test check for generated wrapper"
      l.execShell shellCmd(nim, check, errormax = 2).withIt do:
        it.arg wrapperOut

      l.success "Generated wrapper semcheck ok"

    if conf.testLink:
      l.debug "Linking parser.c"
      l.execShell makeGnuShellCmd("gcc").withIt do:
        it.arg "src/parser.c"
        it - "c"
        it - ("o", "", "parser.o")

    cpFile RelFile("src/parser.c"), parserOut
    l.debug "Copied parser file to", parserOut

    if conf.scannerFile.isSome():
      let file = conf.scannerFile.get()
      if conf.testLink:
        l.debug "Linking", file
        l.execShell makeGnuShellCmd("gcc").withIt do:
          it.arg $file
          it - "c"
          it - ("o", "", "scanner.o")

    if conf.extraFiles.len > 0:
      l.indented:
        l.info "Copying extra files to target directory"
        for (src, target) in conf.extraFiles:
          if target.ext != "js":
            cpFile target, parserOut.dir / target
            l.debug target, "->\n", parserOut.dir / target

    l.info "tree-sitter object files generation ok"
    return lang

proc grammarFromFile*(conf: HtsGenConf) =

  let l = conf.l

  l.info "Working directory is", cwd()
  if conf.scannerFile.isNone():
    l.warn "No input scanner file"

  else:
    l.info "Scanner file is", conf.scannerFile.get()
    l.info "Absolute scanner file position", conf.scannerFile.get().toAbsFile()

  let lang = compileGrammar(conf)


  if conf.parserUser.isSome():
    l.info "Test parser user file is some. Compiling ..."
    let user = conf.parserUser.get()
    try:
      let res = runShell makeNimShellCmd("nim").withIt do:
        it.cmd "c"
        it - "r"
        if conf.nimcacheDir.isSome():
          it - ("nimcache", conf.nimcacheDir.get().getStr())

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
    scannerUrl: Option[Url]                               = none(Url),
    conf: HtsGenConf
  ) =

  let client = newHttpClient()
  client.downloadFile(grammarUrl.string, conf.grammarJs.getStr())
  if scannerUrl.getSome(scanner):
    assertOption conf.scannerFile
    client.downloadFile(scanner.string, conf.scannerFile.get().getStr())

  else:
    assertArg(
      conf.scannerFile,
      conf.scannerFile.isNone(),
      "Scanner URL was 'none', but download path for target " &
      "scanner was specified."
    )

  grammarFromFile(
    conf
  )
