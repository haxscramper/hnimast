import
  hmisc/other/blockfmt,
  hmisc/core/all,
  hmisc/macros/cl_logic,
  hmisc/algo/[htemplates, halgorithm]

import
  ../hnimast,
  nim_decl

import
  std/[options, strutils, strformat, sequtils, streams, macros]

import
  compiler/[ast, lineinfos]

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
    nffAddIInfo

  NimFormatConf* = object
    flags*: set[NimFormatFlag]
    baseIndent*: int

const
  defaultNimFormatConf* = NimFormatConf(
    flags: {
      nffAllowMultilineProcHead,
      nffAddIInfo
    }
  )

func contains*(conf: NimFormatConf, flag: NimFormatFlag): bool =
  flag in conf.flags

func contains*(conf: NimFormatConf, flags: set[NimFormatFlag]): bool =
  len(flags * conf.flags) == len(flags)


proc toLytBlock(n: PNode, conf: NimFormatConf): LytBlock

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
  for idx, item in n:
    if idx > 0:
      result.add H[T[tern(vertical, ",", ", ")], toLytBlock(item, conf)]

    else:
      result.add toLytBlock(item, conf)

proc toLytBlock(n: PNode, conf: NimFormatConf): LytBlock =
  assertRef n
  template `~`(node: PNode): untyped = toLytBlock(node, conf)

  case n.kind:
    of nkProcTy:
      result = V[
        H[
          T["proc("],
          lytFormalParams(n[0], false, conf),
          lytFormalReturnClose(n[0], conf),
          ~n[1]
        ]]

    of nkProcDef, nkLambda:
      result = makeChoiceBlock([])

      # proc q*(a: B): C {.d.} =
      #   e
      result.add V[
        H[
          H[T["proc"], S[], ~n[0], ~n[2], T["("]],
          lytFormalParams(n[3], false, conf),
          lytFormalReturnClose(n[3], conf),
          if n[4] of nkEmpty: T[""] else: H[T[" "], ~n[4]],
          if n[6] of nkEmpty: T[""] else: T[" = "]
        ],
        V[lytDocComment(n), ~n[6]]]


      if n[3].len > 1:
        # proc q*(
        #     a: B
        #   ): C {.d.} =
        #     e
        result.add V[
          H[T["proc"], S[], ~n[0], ~n[2], T["("]],
          I[4, lytFormalParams(n[3], true, conf)],
          H[
            I[2, lytFormalReturnClose(n[3], conf)],
            if n[4] of nkEmpty: T[""] else: H[T[" "], ~n[4]],
            if n[6] of nkEmpty: T[""] else: T[" = "]
          ],
          lytDocComment(n),
          ~n[6]
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
      result = V[n.mapIt(~it)]

    of nkForStmt:
      result = V[
        H[
          T["for "], ~n[0], # IMPLEMENT multiple identifiers
          T[" in "], ~n[^2],
          T[":"]
        ],
        ~n[^1]
      ]

    of nkCaseStmt:
      var arms = V[]
      for arm in n[1..^1]:
        arms.add ~arm

      result = V[H[T["case "], ~n[0], T[":"]], I[2, arms]]

    of nkOfBranch:
      result = V[H[T["of "], ~n[0], T[":"]], I[2, ~n[1]]]

    of nkIfStmt, nkWhenStmt:
      result = V[]
      for isFirst, branch in itemsIsFirst(n):
        if branch.kind == nkElse:
          result.add H[V[T["else: "]], I[2, ~branch[0]], T[""]]

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


    of nkBracketExpr:
      result = H[~n[0], T["["], lytCsv(n[1..^1], false, conf), T["]"]]

    of nkCommand:
      result = H[~n[0], T[" "], lytCsv(n[1..^1], false, conf)]

    of nkCall:
      result = H[~n[0], T["("], lytCsv(n[1..^1], false, conf), T[")"]]

    of nkIdentDefs:
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
        for def in n:
          result.add ~def
          result.add S[]

        result = V[T["type"], I[2, result]]

    of nkTypeDef:
      var head = H[T[n[0].str], T[" = "]]
      var isTypedef = false
      case n[2].kind:
        of nkObjectTy:
          head.add T["object"]

        of nkEnumTy:
          head.add T["enum"]

        of nkIdent, nkProcTy:
          head.add ~n[2]
          isTypedef = true

        else:
          raise newImplementKindError(n[2], $n.treeRepr())

      if isTypedef:
        result = head

      else:
        var body = V[]
        for fld in n[2]:
          if fld.kind != nkEmpty:
            if fld of nkRecList:
              body.add ~fld

            else:
              body.add H[~fld, lytDocComment(fld, prefix = " ")]

        if n[2] of nkObjectTy:
          result = V[head, body]

        else:
          result = V[head, I[2, body]]

    of nkRecList:
      result = V[lytDocComment(n)]
      for fld in n:
        result.add ~fld

      result = I[2, result]

    of nkPragma:
      result = H[]
      result.add T["{."]
      for idx, item in n:
        result.add tern(idx < n.len - 1, H[~item, T[", "]], ~item)

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

    of nkExprColonExpr: result = H[~n[0], T[": "], ~n[1]]
    of nkPrefix: result        = H[~n[0], ~n[1]]
    of nkPostfix: result       = H[~n[1], ~n[0]]
    of nkInfix: result         = lytInfix(n, conf)
    of nkIdent: result         = T[n.getStrVal()]
    of nkDotExpr: result       = H[~n[0], T["."], ~n[1]]
    of nkEmpty: result         = T[""]
    of nkIntLit: result        = T[$n.intVal]
    of nkPtrTy: result         = H[T["ptr "], ~n[0]]
    of nkStrLit: result = T["\"" & n.getStrVal() & "\""]

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
        result.add toString(bl)
        result.add "\n\n"

  else:
    result = aux(n).toString()


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
      result = toPString(nd.fieldDecl, pprint = pprint)

    of nekProcDecl:
      result = toPString(nd.procdecl, pprint = pprint)

    of nekEnumDecl:
      result = toPString(nd.enumdecl, pprint = pprint, standalone = standalone)

    of nekObjectDecl:
      result = toPString(nd.objectdecl, pprint = pprint, standalone = standalone)

    of nekAliasDecl:
      result = toPString(nd.aliasdecl, pprint = pprint, standalone = standalone)

    of nekPassthroughCode:
      if pprint:
        result = toPString(nd.passthrough)

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
