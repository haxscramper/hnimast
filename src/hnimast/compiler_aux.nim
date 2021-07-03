import hmisc/other/[oswrap, hshell, hjson]
import hmisc/helpers
import hmisc/types/[colortext]
import std/[parseutils, sequtils, with]

import ./hast_common

export colorizeToStr

import compiler /
  [ idents, options, modulegraphs, passes, lineinfos, sem, pathutils, ast,
    modules, condsyms, passaux, llstream, parser, nimblecmd, scriptconfig,
    passes
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

proc newModuleGraph*(
    file: AbsFile,
    path: AbsDir,
    structuredErrorHook: proc(
      config: ConfigRef; info: TLineInfo; msg: string; level: Severity
    ) {.closure, gcsafe.} = nil,
    useNimblePath: bool = false,
    symDefines: seq[string] = @[],
    optionsConfig: proc(config: var ConfigRef) = nil
  ): ModuleGraph =

  var
    cache: IdentCache = newIdentCache()
    config: ConfigRef = newConfigRef()


  with config:
    libpath = AbsoluteDir(path)
    cmd = cmdIdeTools

  config.verbosity = 0
  config.options -= optHints
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
  moduleName = "compileStringModuleName"
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

type
  IcppPartKind* = enum
    ipkArgSplice
    ipkTextPart
    ipkNextArg
    ipkNextDotArg ## `#.`
    ipkNextCnewArg

    ipkResultType
    ipkArgType

  IcppPart* = object
    case kind*: IcppPartKind
      of ipkTextPart:
        text*: string

      of ipkResultType, ipkArgType:
        argIdx*: int
        baseGet*: int

      else:
        discard

  IcppPattern* = object
    parts*: seq[IcppPart]

proc genPatternCall(pat: string): IcppPattern =
  var i = 0
  var j = 1

  template pushText(str: string): untyped =
    if result.parts.len > 0 and
       result.parts[^1].kind == ipkTextPart:
      result.parts[^1].text.add str

    else:
      result.parts.add IcppPart(kind: ipkTextPart, text: str)

  while i < pat.len:
    case pat[i]:
      of '@':
        result.parts.add IcppPart(kind: ipkArgSplice)
        inc i

      of '#':
        if i + 1 < pat.len and pat[i + 1] in {'+', '@'}:
          assert pat[i + 1] != '+',
           "`+` is handled differently for importcpp, but " &
             "manual does not say what this combination means exactly " &
             "so it is not supported for now."

          result.parts.add IcppPart(kind: ipkNextCnewArg)

          inc i
        elif i + 1 < pat.len and pat[i + 1] == '.':
          result.parts.add IcppPart(kind: ipkNextDotArg)

          inc i

        # elif i + 1 < pat.len and pat[i + 1] == '[':
        #   discard

        else:
          result.parts.add IcppPart(kind: ipkNextArg)

        inc j
        inc i
      of '\'':
        let begin = i
        var
          stars: int
          argIdx: int
          isPattern = false

        inc i

        while pat[i] == '*':
          inc stars
          inc i

        if pat[i] in Digits:
          argIdx = pat[i].ord - '0'.ord
          inc i
          isPattern = true

        else:
          i = begin


        if isPattern:
          if argIdx == 0:
            result.parts.add IcppPart(
              kind: ipkResultType, argIdx: -1, baseGet: stars)

          else:
            result.parts.add IcppPart(
              kind: ipkResultType, argIdx: argIdx - 1, baseGet: stars)

        else:
          pushText("'")
          inc i

      else:
        let start = i
        while i < pat.len:
          if pat[i] notin {'@', '#', '\''}: inc(i)
          else:
            break

        if i - 1 >= start:
          pushText(pat[start .. i - 1])

import ./nimble_aux
export nimble_aux

when isMainModule:
  import ./pnode_parse
  let str = """

type
  Obj = object
    f1: int
    f2: string

  En = enum
    ## Other
    a ## Test field

proc test(o: Obj): int = discard

"""
  let n = compileString(str, getStdPath())
  echo n.treeRepr1()

  echo parsePnodeStr(str).treeRepr1()
