import compiler/[
  parser, llstream, idents, options, pathutils, ast, lineinfos]


type ParseError = ref object of CatchableError

proc parsePNodeStr*(str: string): PNode =
  let cache: IdentCache = newIdentCache()
  let config: ConfigRef = newConfigRef()
  var pars: Parser

  pars.lex.errorHandler =
    proc(conf: ConfigRef; info: TLineInfo; msg: TMsgKind; arg: string) =
      if msg notin {hintLineTooLong}:
        raise ParseError(msg: arg)

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
    return nil

  try:
    result = parseAll(pars)
    closeParser(pars)
  except ParseError:
    return nil

when isMainModule:
  let r = parsePNodeStr("""
type
  Type = object
    hello: float
""")
