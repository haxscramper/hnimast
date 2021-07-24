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

startHax()

let str1 = """
type
  Test = object
    field*: int = 10 ## Documentation
    ## for multiline doc comment

proc optLayout(
    self: var LytBlock,
    rest: var Option[LytSolution],
    opts: LytOptions
  ): Option[LytSolution] =
  ## Retrieve or compute the least-cost (optimum) layout for this block.
  ## - @arg{rest} :: text to the right of this block.
  ## - @ret{} :: Optimal layout for this block and the rest of the line.
  # Deeply-nested choice block may result in the same continuation
  # supplied repeatedly to the same block. Without memoisation, this
  # may result in an exponential blow-up in the layout algorithm.
  if rest notin self.layoutCache:
    self.layoutCache[rest] = self.doOptLayout(rest, opts)

  return self.layoutCache[rest]

"""

let str2 = "var test: int = 12 # Regular comment"

let node = parseString1(str2)


# echo node.treeRepr()
echo node
