import hnimast/[cst_parser, cst_lexer, cst_Types]

import
  compiler/[options, idents, lineinfos, pathutils, llstream]

import
  std/[strformat]

import
  hmisc/[base_errors, hdebug_misc]

proc parseString1*(str: string): CstNode =
  let cache: IdentCache = newIdentCache()
  let config: ConfigRef = newConfigRef()
  var pars: Parser

  pars.lex.errorHandler =
    proc(conf: ConfigRef; info: TLineInfo; msg: TMsgKind; arg: string) =
      if msg notin {hintLineTooLong}:
        let file = config.m.fileInfos[info.fileIndex.int32].fullPath.string
        raise newException(
          ParseError, &"{file}:{info.line}:{info.col} {arg}")

  config.verbosity = 0
  config.options.excl optHints

  openParser(
    p = pars,
    filename = AbsoluteFile(""),
    inputStream = llStreamOpen(str),
    cache = cache,
    config = config
  )

  result = parseAll(pars)
  closeParser(pars)

var conf = newCOnfigRef()

conf.mainPackageNotes.incl hintMsgOrigin

let node = parseString1("""
iterator pairs*(main: `mainType`, slice: SliceTypes):
  (int, `fieldType`) =
  let slice = clamp(slice, main.`field`.high)
  for idx in slice:
    yield (idx, main.`field`[idx])

proc opt*(
    name,
    doc, docDetailed, docBrief: string,
    default:       CliDefault                  = nil,
    values:        openarray[(string, string)] = @[],
    docFull:       string                      = "",
    alt:           seq[string]                 = @[],
    defaultAsFlag: CLiDefault                  = nil,
    groupKind:     CliOptKind                  = coOpt,
    varname:       string                      = name,
    maxRepeat:     int                         = 1,
    aliasof:       CliOpt                      = CliOpt(),
    selector:      CliCheck                    = nil,
    check:         CliCheck                    = nil,
    disabled:      string                      = ""
  ): CliDesc =

  discard

""")

startHax()

echo node.treeRepr()
echo node
