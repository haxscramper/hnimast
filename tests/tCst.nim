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
proc parseStmt(p: var Parser): CstNode =
  #| stmt = (IND{>} complexOrSimpleStmt^+(IND{=} / ';') DED)
  #|      / simpleStmt ^+ ';'
  if p.tok.indent > p.currInd:
    # nimpretty support here
    result = newNodeP(nkStmtList, p)
    withInd(p):
      while true:
        if p.tok.indent == p.currInd:
          discard
        elif p.tok.tokType == tkSemiColon:
          getTok(p)
          if p.tok.indent < 0 or p.tok.indent == p.currInd: discard
          else: break
        else:
          if p.tok.indent > p.currInd and p.tok.tokType != tkDot:
            parMessage(p, errInvalidIndentation)
          break
        if p.tok.tokType in {tkCurlyRi, tkParRi, tkCurlyDotRi, tkBracketRi}:
          # XXX this ensures tnamedparamanonproc still compiles;
          # deprecate this syntax later
          break
        p.hasProgress = false
        if p.tok.tokType in {tkElse, tkElif}:
          break # Allow this too, see tests/parser/tifexprs

        let a = complexOrSimpleStmt(p)
        if a.kind == nkEmpty and not p.hasProgress:
          parMessage(p, errExprExpected, p.tok)
          break
        else:
          result.add a

        if not p.hasProgress and p.tok.tokType == tkEof: break
  else:
    # the case statement is only needed for better error messages:
    case p.tok.tokType
    of tkIf, tkWhile, tkCase, tkTry, tkFor, tkBlock, tkAsm, tkProc, tkFunc,
       tkIterator, tkMacro, tkType, tkConst, tkWhen, tkVar:
      parMessage(p, "nestable statement requires indentation")
      result = newEmptyCNode()
    else:
      if p.inSemiStmtList > 0:
        result = simpleStmt(p)
        if result.kind == nkEmpty: parMessage(p, errExprExpected, p.tok)
      else:
        result = newNodeP(nkStmtList, p)
        while true:
          if p.tok.indent >= 0:
            parMessage(p, errInvalidIndentation)
          p.hasProgress = false
          let a = simpleStmt(p)
          let err = not p.hasProgress
          if a.kind == nkEmpty: parMessage(p, errExprExpected, p.tok)
          result.add(a)
          if p.tok.tokType != tkSemiColon: break
          getTok(p)
          if err and p.tok.tokType == tkEof: break

  p.endNode(result)
"""

let str5 = """
while true:
  # code comment
  echo 12
"""

let node = parseString1(str4)


echo node.treeRepr()
echo node
