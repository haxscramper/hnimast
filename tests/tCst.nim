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

let str3 = """
let
  t1: int = 2 # Regular comment
  t2: float = 2 #[ trailing inline comment ]#
  t3 #[ inline inline comment ]# = 3
"""

let str4 = """
while true:
  case L.buf[pos]
  of ' ':
    inc(pos)
    inc(tok.strongSpaceA)
  of '\t':
    if not L.allowTabs: lexMessagePos(
      L, errGenerated, pos, "tabs are not allowed, use spaces instead")

    inc(pos)
  of CR, LF:
    tokenEndPrevious(tok, pos)
    pos = handleCRLF(L, pos)
    var indent = 0
    while true:
      if L.buf[pos] == ' ':
        inc(pos)
        inc(indent)
      elif L.buf[pos] == '#' and L.buf[pos+1] == '[':
        hasComment = true
        if tok.line < 0:
          tok.line = L.lineNumber
          commentIndent = indent
        tok.literal.add "#["
        skipMultiLineComment(L, tok, pos+2, false)
        pos = L.bufpos
      else:
        break
    tok.strongSpaceA = 0
    if L.buf[pos] == '#' and tok.line < 0: commentIndent = indent
    if L.buf[pos] > ' ' and (L.buf[pos] != '#' or L.buf[pos+1] == '#'):
      tok.indent = indent
      L.currLineIndent = indent
      break
  of '#':
    # do not skip documentation comment:
    if L.buf[pos+1] == '#': break
    hasComment = true
    if tok.line < 0:
      tok.line = L.lineNumber

    if L.buf[pos+1] == '[':
      tok.literal.add "#["
      skipMultiLineComment(L, tok, pos+2, false)
      pos = L.bufpos
    else:
      tokenBegin(tok, pos)
      while L.buf[pos] notin {CR, LF, nimlexbase.EndOfFile}:
        tok.literal.add L.buf[pos]
        inc(pos)
      tokenEndIgnore(tok, pos+1)
      tok.commentOffsetB = L.offsetBase + pos + 1
  else:
    break                   # EndOfFile also leaves the loop
"""

let str5 = """
while true:
  # code comment
  echo 12
"""

let node = parseString1(str4)


# echo node.treeRepr()
echo node
