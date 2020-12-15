import hmisc/other/blockfmt
import hmisc/helpers
import std/[options, strutils, strformat, sequtils, streams, sugar]
import compiler/[ast, idents, lineinfos, renderer]

proc str(n: PNode): string = renderer.`$`(n)

let
  txb = makeTextBlock
  vsb = makeStackBlock
  hsb = makeLineBlock
  ind = makeIndentBlock
  choice = makeChoiceBlock

const
  H = blkLine
  V = blkStack
  T = blkText
  I = blkIndent
  S = blkSpace
  C = blkChoice



func `[]`(n: ast.PNode, sl: HSlice[int, BackwardsIndex]): seq[PNode] =
  var idx = sl.a
  let maxl = n.len - sl.b.int
  while sl.a <= idx and idx <= maxl:
    result.add n[idx]
    inc idx



func high(n: PNode): int = n.len - 1

proc toBlock(n: PNode): Block =
  case n.kind:
    of nkProcDef:

      var vertArgsLyt: Block

      block:
        var buf: seq[Block]
        let argPad = n[3][1..^1].maxIt(len($it[0]) + 2)
        for idx, arg in n[3][1..^1]:
          var hor = H[T[alignLeft($arg[0] & ": ", argPad)], T[$arg[1]]]
          if idx < n[3].high - 1:
            hor &= T[","]

          buf.add I[4, hor]

        vertArgsLyt = V[buf]

      var horizArgsLyt: Block
      block:
        var buf: seq[Block]
        for idx, arg in n[3][1..^1]:
          var hor = H[T[$arg[0]], T[": "], T[$arg[1]]]
          if idx < n[3].high - 1:
            hor &= T[", "]

          buf.add hor

        horizArgsLyt = H[buf]

      let (retLyt, hasRett) =
        if n[3][0].kind == nkEmpty:
          (T[""], false)
        else:
          (H[toBlock(n[3][0])], true)

      let pragmaLyt = toBlock(n[4])

      let comment =
        if n.comment.len == 0:
          ""
        else:
          n.comment.split('\n').mapIt("  ## " & it).join("\n")

      # n.comment.split("\n").mapIt("")

      let headLyt = H[T["proc"], S[], T[$n[0]], T[$n[2]], T["("]]
      let implLyt = V[toBlock(n[6]), T[comment]]
      let postArgs = if hasRett: T["): "] else: T[")"]
      let eq = if n[6].kind == nkEmpty: T[""] else: T[" = "]

      result = C[
        # proc q*(a: B): C {.d.} = e
        H[headLyt, horizArgsLyt, postArgs, retLyt, pragmaLyt, eq, implLyt],

        # proc q*(a: B): C {.d.} =
        #   e
        V[H[headLyt, horizArgsLyt, postArgs, retLyt, pragmaLyt, eq], implLyt],

        # proc q*(a: B):
        #     C {.d.} =
        #   e
        V[H[headLyt, horizArgsLyt, postArgs],
          I[2, H[retLyt, pragmaLyt, eq]], implLyt],


        # proc q*(a: B):
        #     C
        #     {.d.} =
        #   e
        V[H[headLyt, horizArgsLyt, postArgs],
          I[2, retLyt],
          I[2, H[pragmaLyt, eq]],
          implLyt
        ],

        # proc q*(
        #     a: B
        #   ): C {.d.} =
        #     e
        V[
          headLyt,
          vertArgsLyt,
          H[postArgs, retLyt, pragmaLyt, eq],
          implLyt
        ],

        # proc q*(
        #     a: B
        #   ):
        #       C {.d.} =
        #     e
        V[
          headLyt,
          vertArgsLyt,
          postArgs,
          I[2, H[retLyt, pragmaLyt, eq]],
          implLyt
        ],

        # proc q*(
        #       a: B
        #   ):
        #     C
        #     {.d.} =
        #   e
        V[
          headLyt,
          vertArgsLyt,
          postArgs,
          I[2, retLyt],
          I[2, H[pragmaLyt, eq]],
          implLyt
        ]
      ]

    of nkStmtList:
      result = V[n.mapIt(toBlock(it))]
    else:
      return makeTextBlock(n.str)


proc lyt(bl: Block): string =
  var bl = bl
  let sln = none(Solution).withResIt do:
    bl.doOptLayout(it, defaultFormatOpts).get()

  var c = Console()
  sln.layouts[0].printOn(c)
  return c.text

proc layoutBlockRepr*(n: PNode): Layout =
  var blocks = if n.isNil(): T[""] else: n.toBlock()

  let sln = none(Solution).withResIt do:
    blocks.doOptLayout(it, defaultFormatOpts).get()

  return sln.layouts[0]

proc pprintWrite*(s: Stream | File, n: PNode, indent: int = 0) =
  s.write(layoutBlockRepr(n), indent = indent)


proc toPString*(n: PNode): string =
  var blc = layoutBlockRepr(n)
  var c = Console()
  blc.printOn(c)
  return c.text
