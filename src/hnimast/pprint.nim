import hmisc/other/blockfmt
import hmisc/helpers
import hmisc/hexceptions
import hmisc/macros/cl_logic

import ../hnimast, nim_decl

import std/[options, strutils, strformat, sequtils, streams, sugar, macros]
import compiler/[ast, idents, lineinfos]

proc str(n: PNode): string = `$`(n)

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

proc toLytBlock(n: PNode, level: int): LytBlock =
  let ind = level * 2
  case n.kind:
    of nkProcDef, nkLambda:

      var vertArgsLyt: LytBlock

      block:
        var buf: seq[LytBlock]
        let argPad = n[3][1..^1].maxIt(len($it[0]) + 2)
        for idx, arg in n[3][1..^1]:
          var hor = H[T[alignLeft($arg[0] & ": ", argPad)], T[$arg[1]]]
          if idx < n[3].high - 1:
            hor &= T[","]

          buf.add I[4, hor]

        vertArgsLyt = V[buf]

      var horizArgsLyt: LytBlock
      block:
        var buf: seq[LytBlock]
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
          (H[toLytBlock(n[3][0], 0)], true)

      let pragmaLyt = toLytBlock(n[4], 0)

      let comment =
        if n.comment.len == 0:
          ""
        else:
          n.comment.split('\n').mapIt("  ## " & it).join("\n")

      # n.comment.split("\n").mapIt("")

      let headLyt = H[T["proc"], S[], T[$n[0]], T[$n[2]], T["("]]
      let implLyt = V[toLytBlock(n[6], level + 1), T[comment]]
      let postArgs = if hasRett: T["): "] else: T[")"]
      let eq = if n[6].kind == nkEmpty: T[""] else: T[" = "]


      result = makeChoiceBlock([])

      # proc q*(a: B): C {.d.} = e
      result.add I[ind,
        H[headLyt, horizArgsLyt, postArgs, retLyt, pragmaLyt, eq, implLyt]]

      # proc q*(a: B): C {.d.} =
      #   e
      result.add V[
        I[ind,
          H[headLyt, horizArgsLyt, postArgs, retLyt, pragmaLyt, eq]],
        implLyt]

      # proc q*(a: B):
      #     C {.d.} =
      #   e
      result.add V[I[ind, H[headLyt, horizArgsLyt, postArgs]],
        I[ind + 2, H[retLyt, pragmaLyt, eq]], implLyt]


      # proc q*(a: B):
      #     C
      #     {.d.} =
      #   e
      result.add V[I[ind, H[headLyt, horizArgsLyt, postArgs]],
        I[ind + 2, retLyt],
        I[ind + 2, H[pragmaLyt, eq]],
        implLyt
      ]

      if vertArgsLyt.len > 0:
        # proc q*(
        #     a: B
        #   ): C {.d.} =
        #     e
        result.add V[
          I[ind, headLyt],
          I[ind, vertArgsLyt],
          I[ind, H[postArgs, retLyt, pragmaLyt, eq]],
          I[ind, implLyt]
        ]

        # proc q*(
        #     a: B
        #   ):
        #       C {.d.} =
        #     e
        result.add V[
          I[ind, headLyt],
          I[ind, vertArgsLyt],
          I[ind, postArgs],
          I[ind + 2, H[retLyt, pragmaLyt, eq]],
          I[ind,implLyt]
        ]

        # proc q*(
        #       a: B
        #   ):
        #     C
        #     {.d.} =
        #   e
        result.add V[
          I[ind, headLyt],
          tern(vertArgsLyt.len == 0, T[""], I[ind, vertArgsLyt]),
          I[ind, postArgs],
          I[ind + 2, retLyt],
          I[ind + 2, H[pragmaLyt, eq]],
          I[ind, implLyt]
        ]

    of nkStmtList:
      result = V[n.mapIt(toLytBlock(it, level))]

    of nkForStmt:
      result = V[
        I[ind, H[
          T["for "], toLytBlock(n[0], 0),
          T[" in "], toLytBlock(n[^2], 0),
          T[":"]
        ]],
        toLytBlock(n[^1], level + 1)
      ]

      # echo result.ptreeRepr()

    of nkIfStmt:
      result = makeStackBlock([])
      for isFirst, branch in itemsIsFirst(n):
        if branch.kind == nkElse:
          result.add V[
            I[ind, T["else: "]],
            toLytBlock(branch[0], level + 1),
            T[""]
          ]

        else:
          result.add V[
            I[
              ind,
              H[
                T[if isFirst: "if " else: "elif "],
                toLytBlock(branch[0], 0),
                T[":"]
              ]
            ],
            toLytBlock(branch[1], level + 1),
            T[""]
          ]

    of nkLetSection, nkConstSection, nkVarSection:
      result = V[I[ind, T[
        cond(n.kind,
            (nkLetSection, "let"),
            (nkVarSection, "var"),
            (nkConstSection, "const"),
            (_, $n.kind)
        )
      ]]]

      for le in n:
        result.add toLytBlock(le, level + 1)

    of nkIdentDefs:
      if n[2].kind == nkLambda:
        result = V[
          I[ind, tern(
            n[1].kind == nkEmpty,
            H[T[n[0].str], T[" = "]],
            H[T[n[0].str], T[" : "], toLytBlock(n[1], 0), T[" = "]]
          )],
          toLytBlock(n[2], level + 1)
        ]
      else:
        result = I[ind,
                   H[T[n[0].str],
                     tern(
                       n[1].kind == nkEmpty, T[""], H[T[": "], toLytBlock(n[1], 0)]
                     ),
                     tern(
                       n[2].kind == nkEmpty, T[""], H[T[" = "], toLytBlock(n[2], 0)]
                     )
                   ]
                 ]

    of nkTypeSection:
      result = V[I[ind, T["type"]]]
      for def in n:
        result.add toLytBlock(def, level + 1)
        result.add T[""]

    of nkTypeDef:
      result = V[I[ind, H[
        T[n[0].str],
        T[" = "],
        T[cond(n[2].kind,
              (nkObjectTy, "object"),
              (nkEnumTy, "enum"),
              ($n[2].kind))]
      ]]]

      for fld in n[2]:
        if fld.kind != nkEmpty:
          result.add toLytBlock(fld, level + 1)

    of nkRecList:
      result = makeStackBlock([])

      for fld in n:
        result.add toLytBlock(fld, level)

    else:
      result = I[ind, T[n.str]]


proc lyt(bl: LytBlock): string = bl.toString()

proc layoutBlockRepr*(n: PNode, indent: int = 0): Layout =
  var blocks = if n.isNil(): T[""] else: n.toLytBlock(indent)

  let sln = none(LytSolution).withResIt do:
    blocks.doOptLayout(it, defaultFormatOpts).get()

  return sln.layouts[0]

proc pprintWrite*(s: Stream | File, n: PNode, indent: int = 0) =
  s.write(layoutBlockRepr(n), indent = indent)


proc toPString*(n: PNode, indent: int = 0): string =
  var blc = layoutBlockRepr(n, indent = indent)
  var c = LytConsole()
  blc.printOn(c)
  return c.text

proc write*(
  s: Stream | File, pd: AnyNimDecl[PNode],
    pprint: bool = true,
    standalone: bool = true,
    indent: int = 0
  ) =

  let pref = " ".repeat(indent)
  s.writeLine(&"\n\n{pref}# Declaration created in: {pd.iinfo}\n")
  if pd.codeComment.len > 0:
    for line in split(pd.codeComment, "\n"):
      s.writeLine(&"{pref}# {line}")

  if pprint:
    s.pprintWrite(pd.toNNode(standalone = standalone), indent = indent)
  else:
    for line in (str(pd.toNNode(standalone = standalone))).split('\n'):
      s.write(pref)
      s.writeLine(line)

    # s.writeLine(pd.toNNode(standalone = standalone))

  s.write("\n")

proc write*(
    s: Stream | File, nd: NimDecl[PNode],
    standalone: bool = true,
    pprint: bool = false
  ) =

  case nd.kind:
    of nekProcDecl:
      s.write(nd.procdecl, pprint = pprint)

    of nekEnumDecl:
      s.write(nd.enumdecl, pprint = pprint, standalone = standalone)

    of nekObjectDecl:
      s.write(nd.objectdecl, pprint = pprint, standalone = standalone)

    of nekAliasDecl:
      s.write(nd.aliasdecl, pprint = pprint, standalone = standalone)

    of nekPasstroughCode:
      if pprint:
        s.pprintWrite(nd.passthrough)
      else:
        s.writeLine($nd)

      s.write("\n\n")

    of nekMultitype:
      if nd.typedecls.len == 0:
        return

      s.write("\ntype")
      for elem in nd.typedecls:
        case elem.kind:
          of ntdkEnumDecl:
            s.write(
              elem.enumDecl, standalone = false,
              pprint = pprint, indent = 2
            )

          of ntdkObjectDecl:
            s.write(
              elem.objectDecl, standalone = false,
              pprint = pprint, indent = 2
            )

          of ntdkAliasDecl:
            s.write(
              elem.aliasDecl, standalone = false,
              pprint = pprint, indent = 2
            )

      s.write("\n\n")

proc write*(s: Stream, ed: EnumDecl[PNode], pprint: bool = true) =
  if pprint:
    s.pprintWrite(ed.toNNode())

  else:
    s.write($ed.toNNode())
