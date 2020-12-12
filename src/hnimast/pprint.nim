import hmisc/other/blockfmt
import hmisc/helpers
import std/[options, strutils, strformat, sequtils]
import compiler/[ast, idents, lineinfos, renderer]

proc str(n: PNode): string = renderer.`$`(n)

let
  txb = makeTextBlock
  vsb = makeStackBlock
  hsb = makeLineBlock
  ind = makeIndentBlock
  choice = makeChoiceBlock

type
  BuilderKind = enum
    blkLine
    blkStack
    blkText
    blkIndent
    blkSpace
    blkChoice

const
  H = blkLine
  V = blkStack
  T = blkText
  I = blkIndent
  S = blkSpace
  C = blkChoice

proc `[]`(b: static[BuilderKind], s: seq[Block]): Block =
  static: assert b in {blkLine, blkStack, blkChoice}

  case b:
    of blkLine: makeLineBlock(s)
    of blkStack: makeStackBlock(s)
    of blkChoice: makeChoiceBlock(s)
    else:
      raiseAssert("#[ IMPLEMENT ]#")


proc `[]`(b: static[BuilderKind], bl: Block, args: varargs[Block]): Block =
  b[@[ bl ] & toSeq(args)]

proc `[]`(b: static[BuilderKind], a: string): Block =
  static: assert b == blkText
  return makeTextBlock(a)

proc `[]`(b: static[BuilderKind], tlen: int = 1): Block =
  static: assert b == blkSpace
  return makeTextBlock(" ".repeat(tlen))

proc `[]`(b: static[BuilderKind], i: int, bl: Block): Block =
  static: assert b == blkIndent
  return makeIndentBlock(bl, i)

func `&?`(bl: Block, added: tuple[condOk: bool, bl: Block]): Block =
  result = bl
  if added.condOk:
    result.add added.bl

func `[]`(n: ast.PNode, sl: HSlice[int, BackwardsIndex]): seq[PNode] =
  var idx = sl.a
  let maxl = n.len - sl.b.int
  while sl.a <= idx and idx <= maxl:
    result.add n[idx]
    inc idx

func high(n: PNode): int = n.len - 1

import hpprint

proc toBlock(n: PNode): Block =
  case n.kind:
    of nkProcDef:
      var alts: seq[Block]

      block:
        var buf: seq[Block]
        buf.add H[T["proc"], S[], T[$n[0]], T["("]]
        let argPad = n[3][1..^1].maxIt(len($it[0]) + 2)
        for idx, arg in n[3][1..^1]:
          var hor = H[T[alignLeft($arg[0] & ": ", argPad)], T[arg[1].str]]
          if idx < n[3].high - 1:
            hor &= T[","]

          buf.add I[4, hor]

        buf.add H[
          T[")"],
          if n[3][0].kind == nkEmpty:
            T[" ="]
          else:
            echov n[3][0].kind
            H[T[": "], toBlock(n[3][0]), T[" ="]]
        ]

        alts.add V[buf]

      result = C[alts]

      # result.add txb(")")

      # pprint result
      # result.add choice(argAlts)
    else:
      return makeTextBlock(n.str)


proc lyt(bl: Block): string =
  var bl = bl
  let sln = none(Solution).withResIt do:
    bl.doOptLayout(it, defaultFormatOpts).get()

  var c = Console()
  sln.layouts[0].printOn(c)
  return c.text

func codegenRepr*(inBl: Block): string =
  func aux(bl: Block, level: int): string =
    let pref = repeat("  ", level)
    let name =
      case bl.kind:
        of bkLine: "hsb"
        of bkChoice: "choice"
        of bkText: "txb"
        of bkWrap: "wrap"
        of bkStack: "vsb"
        of bkVerb: "verb"

    case bl.kind:
      of bkLine, bkChoice, bkStack, bkWrap:
        result = pref & name & "([\n"
        for isLast, elem in itemsIsLast(bl.elements):
          result &= elem.aux(level + 1) & (if isLast: "\n" else: ",\n")

        result &= pref & "])"
      of bkText:
        result = &"{pref}txb(\"{bl.text}\")"
      of bkVerb:
        result = pref & name & "([\n"
        for isLast, line in itemsIsLast(bl.textLines):
          result &= &"{pref}  \"{line}\"" & (if isLast: "\n" else: ",\n")

        result &= pref & "])"

  return "str(" & aux(inBl, 0) & ")"


proc toPString*(n: PNode): string =
  var blocks = n.toBlock()
  # echo blocks
  # echo blocks.codegenRepr()
  let sln = none(Solution).withResIt do:
    blocks.doOptLayout(it, defaultFormatOpts).get()

  var c = Console()
  sln.layouts[0].printOn(c)
  return c.text
    # echo c.text

# echo hsb(@["a".txb, "b".txb, nl(), "b".txb]).lyt
# echo hsb(@["a".txb, "b".txb, "b".txb]).lyt
