
import hmisc/other/[oswrap, hshell, hjson]
import hmisc/core/all
import hmisc/types/[colortext, colorstring]
import std/[parseutils, sequtils, with, hashes]

export colorstring

import ./hast_common

export colorizeToStr

import compiler /
  [ idents, options, modulegraphs, passes, lineinfos, sem, pathutils, ast,
    modules, condsyms, passaux, llstream, parser, nimblecmd, scriptconfig,
    wordrecg, passes, trees
  ]

export idents, options, modulegraphs, passes, lineinfos, pathutils, sem,
    ast, modules, condsyms, passaux, llstream, parser

import compiler/astalgo except debug

export astalgo except debug


proc getInstallationPath*(): AbsDir =
  var version = evalShellStdout shellCmd(nim, --version)
  let start = "Nim Compiler Version ".len
  let finish = start + version.skipWhile({'0'..'9', '.'}, start)
  version = version[start ..< finish]
  result = AbsDir(~".choosenim/toolchains" / ("nim-" & version))

proc getStdPath*(): AbsDir =
  let j = shellCmd(nim, dump, "--dump.format=json", "-").
    evalShellStdout().parseJson()
  return j["libpath"].asStr().AbsDir()

proc getFilePath*(config: ConfigRef, info: TLineInfo): AbsFile =
  ## Get absolute file path for declaration location of `node`
  if info.fileIndex.int32 >= 0:
    result = config.m.fileInfos[info.fileIndex.int32].fullPath.
      string.AbsFile()

proc getFilePath*(graph: ModuleGraph, node: PNode): AbsFile =
  ## Get absolute file path for declaration location of `node`
  graph.config.getFilePath(node.getInfo()).string.AbsFile()

proc getFilePath*(graph: ModuleGraph, sym: PSym): AbsFile =
  ## Get absolute file path for symbol
  graph.config.getFilePath(sym.info).string.AbsFile()

proc isObjectDecl*(node: PNode): bool =
  node.kind == nkTypeDef and
  (
    node[2].kind == nkObjectTy or
    (
      node[2].kind in {nkPtrTy, nkRefTy} and
      node[2][0].kind == nkObjectTy
    )
  )

proc headSym*(node: PNode): PSym =
  case node.kind:
    of nkProcDeclKinds, nkDistinctTy, nkVarTy, nkAccQuoted,
       nkBracketExpr, nkTypeDef, nkPragmaExpr, nkPar, nkEnumFieldDef,
       nkIdentDefs, nkRecCase:
      result = headSym(node[0])

    of nkCommand, nkCall, nkPrefix, nkPostfix,
       nkHiddenStdConv, nkInfix:
      if node.len == 0:
        result = nil

      elif node.kind == nkCall:
        if node.len > 1 and node[1].kind == nkSym:
          result = node[1].sym

        else:
          result = headSym(node[0])

      else:
        result = headSym(node[0])

    of nkDotExpr:
      result = headSym(node[1])

    of nkSym:
      result = node.sym

    of nkRefTy, nkPtrTy:
      if node.len == 0:
        result = nil

      else:
        result = headSym(node[0])

    of nkIdent, nkEnumTy, nkProcTy, nkObjectTy, nkTupleTy,
       nkTupleClassTy, nkIteratorTy, nkOpenSymChoice,
       nkClosedSymChoice, nkCast, nkLambda, nkCurly:
      result = nil

    of nkCheckedFieldExpr:
      # First encountered during processing of `locks` file. Most likely
      # this is a `object.field` check
      result = nil

    of nkStmtListExpr:
      if isNil(node.typ):
        if node.len > 0:
          result = headSym(node[1])

        else:
          result = nil

      else:
        result = node.typ.skipTypes({tyRef}).sym

    of nkType, nkObjConstr:
      result = node.typ.skipTypes({tyRef}).sym

    else:
      raise newImplementKindError(node, $node.treeRepr())

proc getPragma*(n: PNode, name: string): Option[PNode] =
  case n.kind:
    of nkPragmaExpr:
      for pr in n:
        result = getPragma(pr, name)
        if result.isSome():
          return

    of nkPragma:
      if n.safeLen > 0:
        case n[0].kind:
          of nkSym, nkIdent:
            if n[0].getStrVal() == name:
              return some n[0]

          of nkCall, nkCommand, nkExprColonExpr:
            if n[0][0].getStrVal() == name:
              return some n[0]

          else:
            raise newImplementKindError(n[0], $n.treeRepr())

    of nkTypeDef, nkIdentDefs, nkRecCase:
      return getPragma(n[0], name)

    of nkProcDeclKinds:
      return getPragma(n[4], name)

    else:
      discard

proc typeHead*(node: PNode): PNode =
  case node.kind:
    of nkSym: node
    of nkTypeDef: typeHead(node[0])
    of nkPragmaExpr: typeHead(node[0])
    else:
      raise newImplementKindError(node)

proc declHead*(node: PNode): PNode =
  case node.kind:
    of nkRecCase, nkIdentDefs, nkProcDeclKinds, nkPragmaExpr,
       nkVarTy, nkBracketExpr, nkPrefix,
       nkDistinctTy, nkBracket:
      result = declHead(node[0])

    of nkRefTy, nkPtrTy:
      if node.len > 0:
        result = declHead(node[0])

      else:
        result = node

    of nkSym, nkIdent, nkEnumFieldDef, nkDotExpr,
       nkExprColonExpr, nkCall,
       nkRange, # WARNING
       nkEnumTy,
       nkProcTy,
       nkIteratorTy,
       nkTupleClassTy,
       nkLiteralKinds:
      result = node

    of nkPostfix, nkCommand:
      result = node[1]

    of nkInfix, nkPar:
      result = node[0]

    of nkTypeDef:
      let head = typeHead(node)
      doAssert head.kind == nkSym, $head.treeRepr()
      result = head

    of nkObjectTy:
      result = node

    else:
      raise newImplementKindError(node, $node.treeRepr())




proc exprTypeSym*(n: PNode): PSym =
  case n.kind:
    of nkCall:
      result = n.typ.sym

    else:
      result = headSym(n)


proc isExported*(n: PNode): bool =
  case n.kind:
    of nkPostfix: true
    of nkSym: sfExported in n.sym.flags
    of nkPragmaExpr, nkTypeDef, nkIdentDefs, nkRecCase,
       nkProcDeclKinds:
      isExported(n[0])

    else:
      false


proc effectSpec*(n: PNode, effectType: set[TSpecialWord]): PNode =
  assertKind(n, {nkPragma, nkEmpty})
  for it in n:
    case it.kind:
      of nkExprColonExpr, nkCall:
        if whichPragma(it) in effectType:
          result = it[1]
          if result.kind notin {nkCurly, nkBracket}:
            result = newNodeI(nkCurly, result.info)
            result.add(it[1])
          return

      of nkIdent, nkSym, nkEmpty:
        discard

      else:
        raise newUnexpectedKindError(it, $treeRepr(it))


proc effectSpec*(sym: PSym, word: TSpecialWord): PNode =
  if notNil(sym) and notNil(sym.ast) and sym.ast.safeLen >= pragmasPos:
    return sym.ast.asProcDecl().pragmas().effectSpec(word)


proc getEffects*(node: PNode, effectPos: int): PNode =
  if node.safeLen > 0 and
     node[0].len >= effectListLen and
     not isNil(node[0][effectPos]):
    result = nnkBracket.newPTree()
    for node in node[0, {nkArgList}][effectPos]:
      result.add node

  else:
    result = newEmptyPNode()

proc hash*(s: PSym): Hash = hash($s)


proc newModuleGraph*(
    file: AbsFile,
    path: AbsDir = getStdPath(),
    structuredErrorHook: proc(
      config: ConfigRef; info: TLineInfo; msg: string; level: Severity
    ) {.closure, gcsafe.} = nil,
    useNimblePath: bool = false,
    symDefines: seq[string] = @[],
    optionsConfig: proc(config: var ConfigRef) = nil
  ): ModuleGraph =

  assert file.ext() == "nim"

  var
    cache: IdentCache = newIdentCache()
    config: ConfigRef = newConfigRef()


  with config:
    libpath = AbsoluteDir(path)
    cmd = cmdIdeTools

  config.verbosity = 0
  config.options.excl optHints
  config.searchPaths.add @[
    config.libpath,
    path / "pure",
    path / "pure" / "collections",
    path / "pure" / "concurrency",
    path / "impure",
    path / "js",
    path / "packages" / "docutils",
    path / "std",
    path / "core",
    path / "posix",
    path / "windows",
    path / "wrappers",
    path / "wrappers" / "linenoise"
  ]

  config.projectFull = file


  config.structuredErrorHook = structuredErrorHook

  wantMainModule(config)

  initDefines(config.symbols)
  defineSymbol(config.symbols, "nimcore")
  defineSymbol(config.symbols, "c")
  defineSymbol(config.symbols, "ssl")
  for sym in symDefines:
    defineSymbol(config.symbols, sym)

  if useNimblePath:
    nimblePath(config, ~".nimble/pkgs", TLineInfo())

  else:
    config.disableNimblePath()

  if notNil(optionsConfig):
    optionsConfig(config)

  return newModuleGraph(cache, config)

proc compileString*(
    text: string,
    stdpath: AbsDir = getStdPath(),
    symDefines: seq[string] = @[],
    optionsConfig: proc(config: var ConfigRef) = nil
  ): PNode =
  assertExists(stdpath)

  var graph {.global.}: ModuleGraph
  var moduleName {.global.}: string
  moduleName = "compileStringModuleName.nim"
  graph = newModuleGraph(AbsFile(moduleName), stdpath,
    proc(config: ConfigRef; info: TLineInfo; msg: string; level: Severity) =
      if config.errorCounter >= config.errorMax:
        echo msg

    ,
    symDefines = symDefines,
    optionsConfig = optionsConfig
  )

  var res {.global.}: PNode
  res = nkStmtList.newTree()

  registerPass(graph, semPass)
  registerPass(
    graph, makePass(
      (
        proc(graph: ModuleGraph, module: PSym): PPassContext {.nimcall.} =
          return PPassContext()
      ),
      (
        proc(c: PPassContext, n: PNode): PNode {.nimcall.} =
          if n.info.fileIndex.int32 == 1:
            res.add n
          result = n
      ),
      (
        proc(graph: ModuleGraph; p: PPassContext,
             n: PNode): PNode {.nimcall.} =
          discard
      )
    )
  )

  var m = graph.makeModule(moduleName)
  graph.vm = setupVM(m, graph.cache, moduleName, graph)
  graph.compileSystemModule()
  discard graph.processModule(m, llStreamOpen(text))

  return res

when isMainModule:
  import ./pnode_parse
  let str = """

const test {.intdefine.} = 190

"""
  let n = compileString(str, getStdPath())
  echo n.treeRepr1()

  # echo parsePnodeStr(str).treeRepr1()
