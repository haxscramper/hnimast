import compiler/[parser, llstream, idents, options, pathutils, astalgo]
import compiler/[ast, lineinfos]

proc parsePNodeStr*(str: string): PNode =
  let cache: IdentCache = newIdentCache()
  let config: ConfigRef = newConfigRef()
  var pars: Parser

  config.verbosity = 0
  config.options.excl optHints

  openParser(
    p = pars,
    filename = AbsoluteFile(currentSourcePath()),
    inputStream = llStreamOpen(str),
    cache = cache,
    config = config
  )

  pars.lex.errorHandler =
    proc(conf: ConfigRef; info: TLineInfo; msg: TMsgKind; arg: string) =
      if msg notin {hintLineTooLong}:
        echo arg

  result = parseAll(pars)
  closeParser(pars)
