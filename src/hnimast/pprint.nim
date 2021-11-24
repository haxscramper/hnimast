import
  hmisc/other/blockfmt,
  hmisc/core/[all, code_errors],
  hmisc/algo/[htemplates, halgorithm],
  hmisc/macros/argpass

import
  ../hnimast,
  nim_decl

import
  std/[options, strutils, strformat, sequtils, macros]

import
  compiler/[ast]

proc str(n: PNode): string = `$`(n)

initBlockFmtDsl()



func `[]`(n: ast.PNode, sl: HSlice[int, BackwardsIndex]): seq[PNode] =
  var idx = sl.a
  let maxl = n.len - sl.b.int
  while sl.a <= idx and idx <= maxl:
    result.add n[idx]
    inc idx

func high(n: PNode): int = n.len - 1

type
  NimFormatFlag* = enum
    nffAllowMultilineProcHead

    nffHorizontalPackedOf
    nffVerticalPackedOf

    nffAddIInfo

  NimFormatConf* = object
    flags*: set[NimFormatFlag]
    baseIndent*: int

const
  defaultNimFormatConf* = NimFormatConf(
    flags: {
      nffAllowMultilineProcHead,
      nffAddIInfo,
      nffHorizontalPackedOf,
      nffVerticalPackedOf
    }
  )

macro nformatConf*(body: varargs[untyped]): untyped =
  result = withFieldAssignsTo(
    ident("defaultNimFormatConf"), body,
    withTmp = true,
    asExpr = true
  )

func contains*(conf: NimFormatConf, flag: NimFormatFlag): bool =
  flag in conf.flags

func contains*(conf: NimFormatConf, flags: set[NimFormatFlag]): bool =
  len(flags * conf.flags) == len(flags)


proc toLytBlock(n: PNode, conf: NimFormatConf): LytBlock
template `~`(node: PNode): untyped = toLytBlock(node, conf)

proc lytInfix(
    n: PNode, conf: NimFormatConf, spacing: bool = true): LytBlock =

  if n.kind == nnkInfix:
    if spacing:
      result = H[
        lytInfix(n[1], conf),
        T[" " & n[0].getStrVal() & " "],
        lytInfix(n[2], conf)]

    else:
      result = H[
        lytInfix(n[1], conf),
        T[n[0].getStrVal()],
        lytInfix(n[2], conf)]

  else:
    result = toLytBlock(n, conf)

proc lytFormalParams(
    n: PNode,
    vertical: bool,
    conf: NimFormatConf
  ): LytBlock =

  assertKind(n, {nkFormalParams})
  result = tern(vertical, V[], H[])
  let argPad = tern(vertical, n[1..^1].maxIt(len($it[0]) + 2), 0)
  for idx, arg in n[1..^1]:
    var hor = H[T[alignLeft($arg[0] & ": ", argPad)], T[$arg[1]]]
    if not(arg[2] of nkEmpty):
      hor.add T[" = "]
      hor.add toLytBlock(arg[2], conf)

    if idx < n.high - 1:
      hor &= T[tern(vertical, ",", ", ")]

    result.add hor

proc lytFormalReturnClose(n: PNode, conf: NimFormatConf): LytBlock =
  assertKind(n, {nkFormalParams})
  if n[0] of nkEmpty:
    T[")"]

  else:
    H[T["): "], toLytBlock(n[0], conf)]


proc lytDocComment(n: PNode, prefix: string = ""): LytBlock =
  if n.comment.len > 0:
    result = V[]
    for line in n.comment.split('\n'):
      result.add T[prefix & "## " & line]

  else:
    result = E[]

proc lytCsv(n: PNode | seq[PNode], vertical: bool, conf: NimFormatConf): LytBlock =
  result = tern(vertical, V[], H[])
  if vertical:
    for idx, item in n:
      result.add tern(
        idx < len(n) - 1,
        H[toLytBlock(item, conf), T[", "]],
        toLytBlock(item, conf)
      )

  else:
    for idx, item in n:
      result.add tern(
        idx > 0,
        H[T[", "], toLytBlock(item, conf)],
        toLytBlock(item, conf)
      )

proc lytTypedefHead(n: PNode, conf: NimFormatConf): LytBlock =
  if n[0] of nkPragmaExpr:
    H[~n[0][0], ~n[1], T[" "], ~n[0][1]]

  else:
    H[~n[0], ~n[1]]

const
  nkTypeAliasKinds = {
    nkIdent, nkPtrTy, nkRefTy, nkBracketExpr}


proc lytTypedef(n: PNode, conf: NimFormatConf): LytBlock =
  var head = lytTypedefHead(n, conf)
  head.add T[" = "]

  case n[2].kind:
    of nkObjectTy:
      head.add T["object"]
      var body: seq[seq[LytBlock]]
      var resBody = V[]

      template flush(): untyped =
        if ?body:
          resBody.add makeAlignedGrid(
            body, [sadLeft, sadLeft, sadLeft])

          body.clear()

      for field in n[2][2]:
        case field.kind:
          of nkEmpty:
            discard

          of nkRecCase:
            flush()
            resBody.add S[]
            resBody.add ~field

          of nkIdentDefs:
            body.add @[
              H[~field[0], T[": "]],
              ~field[1],
              lytDocComment(field, prefix = " ")]

          of nkCommentStmt:
            flush()
            resBody.add lytDocComment(field, prefix = "")

          else:
            raise newImplementKindError(field)

      flush()
      result = V[head, I[2, resBody]]

    of nkEnumTy:
      head.add T["enum"]
      var body: seq[seq[LytBlock]]
      for field in n[2]:
        case field.kind:
          of nkIdent:
            let f = ~field
            body.add @[f, T[""], T[""]]

          of nkEnumFieldDef:
            body.add @[~field[0], T[" = "], ~field[1]]

          of nkEmpty:
            discard

          else:
            raise newUnexpectedKindError(field)

        if field.kind != nkEmpty:
          body.last().add lytDocComment(field, prefix = " ")

      result = V[head, I[2, makeAlignedGrid(
        body, [sadLeft, sadCenter, sadLeft, sadLeft])]]

    of nkTypeAliasKinds:
      head.add ~n[2]
      result = head

    of nkProcTy:
      result = V[head, I[2, ~n[2]]]

    of nkDistinctTy:
      result = H[head, T["distinct "], ~n[2][0]]

    else:
      raise newImplementKindError(n[2], $n.treeRepr())


proc toLytBlock(n: PNode, conf: NimFormatConf): LytBlock =
  assertRef n

  case n.kind:
    of nkProcTy:
      result = V[
        H[
          T["proc("],
          lytFormalParams(n[0], true, conf),
          lytFormalReturnClose(n[0], conf),
          T[" "],
          ~n[1]
        ]]

    of nkAccQuoted:
      result = H[T["`"]]
      for arg in n:
        result.add ~arg

      result.add T["`"]

    of nkProcDef, nkLambda, nkConverterDef, nkFuncDef:
      result = makeChoiceBlock([])

      let kindName =
        case n.kind:
          of nkProcDef: "proc"
          of nkConverterDef: "converter"
          of nkLambda: ""
          of nkFuncDef: "func"
          else: raise newImplementKindError(n)

      # proc q*(a: B): C {.d.} =
      #   e
      result.add V[
        H[
          H[T[kindName], S[], ~n[0], ~n[1], ~n[2], T["("]],
          lytFormalParams(n[3], false, conf),
          lytFormalReturnClose(n[3], conf),
          if n[4] of nkEmpty: T[""] else: H[T[" "], ~n[4]],
          if n[6] of nkEmpty: T[""] else: T[" = "]
        ],
        V[lytDocComment(n), I[2, ~n[6]]],
        S[]
      ]


      if n[3].len > 1 and nffAllowMultilineProcHead in conf:
        # proc q*(
        #     a: B
        #   ): C {.d.} =
        #     e
        result.add V[
          H[T[kindName], S[], ~n[0], ~n[1], ~n[2], T["("]],
          I[4, lytFormalParams(n[3], true, conf)],
          H[
            I[2, lytFormalReturnClose(n[3], conf)],
            if n[4] of nkEmpty: T[""] else: H[T[" "], ~n[4]],
            if n[6] of nkEmpty: T[""] else: T[" = "]
          ],
          lytDocComment(n),
          I[2, ~n[6]],
          S[]
        ]

      when false:
        # proc q*(a: B):
        #     C {.d.} =
        #   e
        result.add V[H[headLyt, horizArgsLyt, postArgs],
          I[2, H[retLyt, pragmaLyt, eq]], implLyt]

        # proc q*(a: B):
        #     C
        #     {.d.} =
        #   e
        result.add V[H[headLyt, horizArgsLyt, postArgs],
          I[2, retLyt],
          I[2, H[pragmaLyt, eq]],
          implLyt
        ]

        if vertArgsLyt.len > 0:
          # proc q*(
          #     a: B
          #   ): C {.d.} =
          #     e
          result.add V[
            headLyt,
            I[4, vertArgsLyt],
            I[2, H[postArgs, retLyt, pragmaLyt, eq]],
            S[],
            I[2, implLyt]
          ]

          # proc q*(
          #       a: B
          #   ):
          #     C
          #     {.d.} =
          #   e
          result.add V[
            headLyt,
            tern(vertArgsLyt.len == 0, E[], vertArgsLyt),
            postArgs,
            I[2, retLyt],
            I[2, H[pragmaLyt, eq]],
            implLyt
          ]

    of nkStmtList:
      result = V[]
      var hadReal = false
      for sub in items(n):
        if sub of nnkEmpty and not hadReal:
          discard

        else:
          hadReal = true
          result.add ~sub

    of nkForStmt:
      result = V[
        H[
          T["for "], ~n[0], # IMPLEMENT multiple identifiers
          T[" in "], ~n[^2],
          T[":"]
        ],
        I[2, ~n[^1]]
      ]

    of nkWhileStmt:
      result = V[
        H[T["while "], ~n[0], T[":"]],
        I[2, ~n[1]]
      ]

    of nkCaseStmt, nkRecCase:
      var regular = V[]
      if nffVerticalPackedOf in conf:
        var arms = V[]
        for arm in n[1..^1]:
          arms.add ~arm

        if n of nkRecCase:
          regular = V[H[T["case "], ~n[0]], I[2, arms]]

        else:
          regular = V[H[T["case "], ~n[0], T[":"]], I[2, arms]]

      var grid = V[]

      if nffHorizontalPackedOf in conf:
        var ofarms: seq[seq[LytBlock]]
        var elsearms: seq[LytBlock]

        for arm in n[1 .. ^1]:
          if arm of nkOfBranch:
            ofarms.add @[
              H[T["of "], lytCsv(arm[0 .. ^2], false, conf), T[": "]],
              ~arm[^1]
            ]

          else:
            elsearms.add ~arm

        grid = V[
          H[T["case "], ~n[0], T[":"]],
          I[2,
            V[
              makeAlignedGrid(ofarms, @[sadLeft, sadLeft]),
              V[elsearms]
            ]
          ]
        ]

      if {nffHorizontalPackedOf, nffVerticalPackedOf} in conf:
        result = C[regular, grid]

      elif nffHorizontalPackedOf in conf:
        result = grid

      else:
        result = regular
      # result = grid

    of nkElse:
      result = V[T["else:"], I[2, ~n[0]]]

    of nkOfBranch:
      let expr = joinItLine(n[0..^2], ~it, T[", "])
      let b = ~n[^1]

      case n[^1].kind:
        of nkRecList:
          result = V[H[T["of "], expr, T[":"]], b]

        else:
          result = V[H[T["of "], expr, T[":"]], I[2, b]]

    of nkIfStmt, nkWhenStmt:
      result = V[]
      for isFirst, branch in itemsIsFirst(n):
        if branch.kind == nkElse:
          result.add V[
            T["else:"],
            I[2, ~branch[0]],
            T[""]
          ]

        else:
          result.add V[
            H[T[tern(
              isFirst,
              tern(n of nkIfStmt, "if ", "when "),
              "elif ")], ~branch[0], T[":"]],

            I[2, ~branch[1]],
            T[""]
          ]

    of nkLetSection, nkConstSection, nkVarSection:
      var decls: seq[LytBlock]

      for le in n:
        decls.add ~le


      let name = mapEnum(n.kind, {
        nkLetSection: "let",
        nkVarSection: "var",
        nkConstSection: "const"
      })

      if decls.len == 1:
        result = H[T[name & " "], decls[0]]

      else:
        result = H[T[name], I[2, V[decls]]]


    of nkIdentDefs, nkConstDef:
      if n[2].kind == nkLambda:
        result = V[
          tern(
            n[1].kind == nkEmpty,
            H[T[n[0].str], T[" = "]],
            H[T[n[0].str], T[" : "], ~n[1], T[" = "]]
          ),
          ~n[2]
        ]
      else:
        result = H[T[n[0].str],
           tern(n[1] of nkEmpty, T[""], H[T[": "], ~n[1]]),
           tern(n[2] of nkEmpty, T[""], H[T[" = "], ~n[2]]),
           lytDocComment(n, " ")
         ]

    of nkEnumFieldDef:
      result = H[~n[0], T[" = "], ~n[1]]

    of nkTypeSection:
      if len(n) == 0:
        result = E[]

      else:
        result = V[]
        var buffer: seq[seq[LytBlock]]
        for idx, def in n:
          if def[2] of nkTypeAliasKinds:
            buffer.add @[lytTypedefHead(def, conf), T[" = "], ~def[2]]
            buffer.add @[S[]]

          if not(def[2] of nkTypeALiasKinds) or idx == len(n) - 1:
            if ?buffer:
              result.add makeAlignedGrid(buffer, [sadLeft, sadLeft, sadLeft])
              result.add S[]

              buffer.clear()

          if not(def[2] of nkTypeAliasKinds):
            result.add ~def
            result.add S[]

        result = V[T["type"], I[2, result]]

    of nkTypeDef:
      result = lytTypedef(n, conf)

    of nkPragmaExpr:
      result = H[~n[0], T[" "], ~n[1]]

    of nkRecList:
      result = V[lytDocComment(n)]
      for fld in n:
        result.add ~fld

      result = I[2, result]

    of nkPragma:
      result = H[]
      result.add T["{."]
      var idx = 0
      while idx < len(n):
        var res: LytBlock
        let item = n[idx]
        if item of nkIdent and item.getStrVal() == "push":
          let next = n[idx + 1]
          res = H[~item, T[" "], tern(
            next of nkExprColonExpr,
            H[~next[0], T[":"], ~next[1]], ~next)]

          inc idx

        else:
          res = ~item

        result.add tern(idx < n.len - 1, H[res, T[", "]], res)
        inc idx

      result.add T[".}"]

    of nkImportStmt:
      var imports = V[]
      for idx, path in n:
        if path of nnkInfix:
          imports.add H[
            lytInfix(path, conf, spacing = false),
            tern(idx < n.len - 1, T[","], T[""])]

        else:
          imports.add ~path

      result = V[T["import"], I[2, imports]]

    of nkExportStmt:
      result = H[T["export "]]
      for idx, exp in n:
        if idx > 0:
          result.add H[T[", "], ~exp]

        else:
          result.add ~exp

    of nkCommentStmt:
      result = V[]
      for line in split(n.comment, '\n'):
        result.add H[T["## " & line]]

    of nkExprEqExpr: result = H[~n[0], T[" = "], ~n[1]]

    of nkExprColonExpr: result = H[~n[0], T[": "], ~n[1]]
    of nkPrefix: result        = H[~n[0], ~n[1]]
    of nkPostfix: result       = H[~n[1], ~n[0]]
    of nkInfix: result         = lytInfix(n, conf)
    of nkIdent: result         = T[n.getStrVal()]
    of nkDotExpr: result       = H[~n[0], T["."], ~n[1]]
    of nkEmpty: result         = T[""]
    of nkIntLit: result        = T[$n.intVal]
    of nkPtrTy: result         = H[T["ptr "], ~n[0]]
    of nkStrLit: result        = T[n.getStrVal().escape()]
    of nkNilLit: result        = T["nil"]
    of nkReturnStmt: result    = H[T["return "], ~n[0]]
    of nkBreakStmt: result     = H[T["break "], ~n[0]]
    of nkDiscardStmt: result   = H[T["discard "], ~n[0]]
    of nkAsgn: result = H[~n[0], T[" = "], ~n[1]]

    of nkBracket:
      result = C[
        H[T["["], lytCsv(n, false, conf), T["]"]],
        V[T["["], I[2, lytCsv(n, true, conf)], T["]"]]
      ]

    of nkGenericParams:
      result = H[T["["], lytCsv(n, false, conf), T["]"]]

    of nkCast:
      if n[0] of nkEmpty:
        result = H[T["cast("], ~n[1], T[")"]]

      else:
        result = H[T["cast["], ~n[0], T["]("], ~n[1], T[")"]]


    of nkCurly:
      if len(n) > 6:
        result = V[T["{"], I[2, lytCsv(n, true, conf)], T["}"]]

      else:
        result = H[T["{"], lytCsv(n, false, conf), T["}"]]


    of nkBlockStmt:
      result = V[
        H[T["block"], tern(n[0].isEmptyNode(), E[], H[T[" "], ~n[0]]), T[":"]],
        I[2, ~n[1]]
      ]

    of nkBracketExpr:
      result = H[~n[0], T["["], lytCsv(n[1..^1], false, conf), T["]"]]

    of nkPar:
      result = H[T["("], lytCsv(n[0..^1], false, conf), T[")"]]

    of nkCommand:
      result = H[~n[0], T[" "], lytCsv(n[1..^1], false, conf)]

    of nkCall:
      result = H[~n[0], T["("], lytCsv(n[1..^1], false, conf), T[")"]]

    of nkPragmaBlock:
      result = V[
        H[~n[0], T[":"]],
        I[2, ~n[1]]
      ]

    else:
      raise newImplementKindError(
        n, treeRepr(n, maxdepth = 3))

  assertRef result, $n.kind


proc toPString*(n: PNode, conf: NimFormatConf = defaultNimFormatConf): string =
  proc aux(node: PNode): LytBlock =
    if node.isNil() or (node of {nnkStmtList} and len(node) == 0):
      return E[]

    else:
      return node.toLytBlock(conf)

  if n of nkStmtList:
    for item in n:
      let bl = aux(item)
      if not(bl of bkEmpty):
        result.add toString(bl).stripLines().toPlainString()
        result.add "\n\n"

  else:
    result = aux(n).toString(rightMargin = 120).
      stripLines().toPlainString()


proc toPString*(
    pd: AnyNimDecl[PNode],
    pprint: bool = true,
    standalone: bool = true,
    conf: NimFormatConf = defaultNimFormatConf
  ): string =

  if nffAddIINfo in conf:
    result.add &"\n\n# Declaration created in: {pd.iinfo}"

  if pd.codeComment.len > 0:
    for line in split(pd.codeComment, "\n"):
      result.add &"# {line}"

  if pprint:
    result.add toPstring(
      pd.toNNode(standalone = standalone), conf = conf)

  else:
    for line in (str(pd.toNNode(standalone = standalone))).split('\n'):
      result.add "\n"

  result.add("\n")

proc toPString*(
    nd: NimDecl[PNode],
    standalone: bool = true,
    pprint: bool = false,
    conf: NimFormatConf = defaultNimFormatConf
  ): string =

  case nd.kind:
    of nekFieldDecl:
      result = toPString(
        nd.fieldDecl, pprint = pprint, conf = conf)

    of nekProcDecl:
      result = toPString(
        nd.procdecl, pprint = pprint, conf = conf)

    of nekEnumDecl:
      result = toPString(
        nd.enumdecl, pprint = pprint,
        standalone = standalone, conf = conf)

    of nekObjectDecl:
      result = toPString(
        nd.objectdecl, pprint = pprint,
        standalone = standalone, conf = conf)

    of nekAliasDecl:
      result = toPString(
        nd.aliasdecl, pprint = pprint,
        standalone = standalone, conf = conf)

    of nekPassthroughCode:
      if pprint:
        result = toPString(nd.passthrough, conf = conf)

      else:
        result = $nd
        result.add "\n"

      result.add("\n\n")

    of nekMultitype:
      if nd.typedecls.len == 0:
        return

      result.add("\ntype")
      let conf = conf.withIt do:
        it.baseIndent += 2

      for elem in nd.typedecls:
        case elem.kind:
          of ntdkEnumDecl:
            result.add toPString(
              elem.enumDecl, standalone = false,
              pprint = pprint, conf = conf
            )

          of ntdkObjectDecl:
            result.add toPString(
              elem.objectDecl, standalone = false,
              pprint = pprint, conf = conf
            )

          of ntdkAliasDecl:
            result.add toPString(
              elem.aliasDecl, standalone = false,
              pprint = pprint, conf = conf
            )

      result.add("\n\n")
