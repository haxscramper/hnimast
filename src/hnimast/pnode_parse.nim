import compiler/[
  parser, llstream, idents, options, pathutils, ast, lineinfos]

import
  hmisc/base_errors

import
  std/strformat


type NimParseError* = object of ParseError

proc parsePNodeStr*(str: string, doRaise: bool = false): PNode =
  let cache: IdentCache = newIdentCache()
  let config: ConfigRef = newConfigRef()
  var pars: Parser

  pars.lex.errorHandler =
    proc(conf: ConfigRef; info: TLineInfo; msg: TMsgKind; arg: string) =
      if msg notin {hintLineTooLong}:
        let file = config.m.fileInfos[info.fileIndex.int32].fullPath.string
        raise newException(
          NimParseError, &"{file}:{info.line}:{info.col} {arg}")

  config.verbosity = 0
  config.options.excl optHints

  try:
    openParser(
      p = pars,
      filename = AbsoluteFile(currentSourcePath()),
      inputStream = llStreamOpen(str),
      cache = cache,
      config = config
    )
  except:
    if doRaise:
      raise

    else:
      return nil

  try:
    result = parseAll(pars)
    closeParser(pars)
  except NimParseError:
    if doRaise:
      raise

    else:
      return nil

when isMainModule:
  let r = parsePNodeStr("""
type
  Type = object
    hello: float
""")
