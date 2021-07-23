import
  compiler/[ast, lineinfos, idents]

import
  hnimast/hast_common

import
  ./cst_lexer

import
  std/[macros, with, strformat, sequtils]

import
  hmisc/[helpers, hexceptions, base_errors, hdebug_misc],
  hmisc/types/colorstring,
  hmisc/algo/[halgorithm, clformat],
  hmisc/other/blockfmt



type
  CstPoint* = object
    tokenIdx*: int
    lineInfo*: TLineInfo

  CstRange = object
    startPoint*, endPoint*: CstPoint

  CstComment = object
    rangeInfo*: CstRange
    text*: string

  CstNode* = ref CstNodeObj
  CstNodeObj* = object
    rangeInfo*: CstRange
    comment*: CstComment
    flags*: set[TNodeFlag]
    baseTokens*: ref seq[Token]

    case kind*: TNodeKind
      of nkCharLit..nkUInt64Lit:
        intVal*: BiggestInt

      of nkFloatLit..nkFloat128Lit:
        floatVal*: BiggestFloat

      of nkStrLit..nkTripleStrLit:
        strVal*: string

      of nkIdent, nkSym:
        ident*: PIdent

      else:
        subnodes*: seq[CstNode]

macro wrapSeqContainer*(
    main: typed,
    fieldType: typed,
    isRef: static[bool] = false,
    withIterators: static[bool] = true
  ) =

  ## - TODO :: Generate kind using `assertKind`

  let
    mainType = main[0]
    field = main[1]
    mutType = if isRef: mainType else: nnkVarTy.newTree(mainType)

  let
    indexOp = ident("[]")
    indexAsgn = ident("[]=")

  result = quote do:
    proc len*(main: `mainType`): int = len(main.`field`)
    proc high*(main: `mainType`): int = high(main.`field`)
    proc add*(main: `mutType`, other: `mainType` | seq[`mainType`]) =
      add(main.`field`, other)

    proc `indexOp`*(main: `mainType`, index: IndexTypes): `fieldType` =
      main.`field`[index]

    proc `indexOp`*(main: `mainType`, slice: SliceTypes): seq[`fieldType`] =
      main.`field`[slice]

    proc `indexAsgn`*(
        main: `mainType`, index: IndexTypes, value: `fieldType`) =

      main.`field`[index] = value

  if withIterators:
    result.add quote do:
      iterator pairs*(main: `mainType`): (int, `fieldType`) =
        for item in pairs(main.`field`):
          yield item

      iterator items*(main: `mainType`): `fieldType` =
        for item in items(main.`field`):
          yield item

      iterator pairs*(main: `mainType`, slice: SliceTypes):
        (int, `fieldType`) =
        let slice = clamp(slice, main.`field`.high)
        for idx in slice:
          yield (idx, main.`field`[idx])

      iterator items*(main: `mainType`, slice: SliceTypes): `fieldType` =
        for idx, item in pairs(main, slice):
          yield item

macro wrapStructContainer*(
    main: untyped,
    fieldList: untyped,
    isRef: static[bool] = false
  ): untyped =

  assertKind(main, {nnkDotExpr})

  let
    mainType = main[0]
    structField = main[1]
    mutType = if isRef: mainType else: nnkVarTy.newTree(mainType)

  result = newStmtList()

  var prev: seq[NimNode]
  for field in fieldList:
    if field.kind != nnkExprColonExpr:
      prev.add field

    else:
      for name in prev & field[0]:
        assertNodeKind(name, {nnkIdent})
        let fieldType = field[1]
        assertNodeKind(fieldType, {nnkIdent, nnkBracketExpr})

        let asgn = ident(name.strVal() & "=")

        result.add quote do:
          func `name`*(n: `mainType`): `fieldType` =
            n.`structField`.`name`

          func `asgn`*(n: `mutType`, value: `fieldType`) =
            n.`structField`.`name` = value

      prev = @[]

wrapStructContainer(
  CstNode.rangeInfo, { startPoint, endPoint: CstPoint }, isRef = true)

wrapSeqContainer(CstNode.subnodes, CstNode, isRef = true)


func getStrVal*(p: CstNode, doRaise: bool = true): string =
  ## Get string value from `PNode`
  case p.kind:
    of nkIdent, nkSym: p.ident.s
    of nkStringKinds: p.strVal
    else:
      if doRaise:
        raiseArgumentError(
          "Cannot get string value from node of kind " & $p.kind)

      else:
        ""

func newEmptyCNode*(): CstNode = CstNode(kind: nkEmpty)
func add*(comm: var CstComment, str: string) = comm.text.add str
func newNodeI*(
    kind: TNodeKind, point: CstPoint, base: ref seq[Token]): CstNode =
  CstNode(
    baseTokens: base,
    kind: kind,
    rangeInfo: CstRange(startPoint: point))

proc newTreeI*(
    kind: TNodeKind; info: CstPoint;
    base: ref seq[Token],
    children: varargs[CstNode]
  ): CstNode =

  result = newNodeI(kind, info, base)
  if children.len > 0:
    result.startPoint = children[0].startPoint

  result.subnodes = @children


template transitionNodeKindCommon(k: TNodeKind) =
  let obj {.inject.} = n[]
  n[] = CstNodeObj(
    kind: k,
    rangeInfo: obj.rangeInfo,
    comment: obj.comment,
    flags: obj.flags
  )

  when defined(useNodeIds):
    n.id = obj.id

proc transitionSubnodesKind*(n: CstNode, kind: range[nkComesFrom..nkTupleConstr]) =
  transitionNodeKindCommon(kind)
  n.subnodes = obj.subnodes

proc transitionIntKind*(n: CstNode, kind: range[nkCharLit..nkUInt64Lit]) =
  transitionNodeKindCommon(kind)
  n.intVal = obj.intVal

proc transitionNoneToSym*(n: CstNode) =
  transitionNodeKindCommon(nkSym)

proc startToken*(node: CstNode): Token =
  node.baseTokens[][node.startPoint.tokenIdx]

proc relIndent*(node: CstNode, idx: IndexTypes): int =
  let mainIndent = node.startToken.indent
  let subIndent = node.subnodes[idx].startToken.indent

proc newProcNode*(
    kind: TNodeKind, info: CstPoint, body: CstNode,
    params, name, pattern, genericParams, pragmas, exceptions: CstNode
  ): CstNode =

  result = newNodeI(kind, info, body.baseTokens)
  result.subnodes = @[
    name, pattern, genericParams, params, pragmas, exceptions, body]

func `$`*(point: CstPoint): string =
  with result:
    add hshow(point.lineInfo.line)
    add ":"
    add hshow(point.lineInfo.col)
    add "@", tcGrey27.fg + tcDefault.bg
    add hshow(point.tokenIdx)

func treeRepr*(
    pnode: CstNode,
    colored: bool = true,
    pathIndexed: bool = false,
    positionIndexed: bool = true,
    maxdepth: int = 120,
    maxlen: int = 30
  ): string =

  var p = addr result
  template res(): untyped = p[]

  proc aux(n: CstNode, level: int, idx: seq[int]) =
    if pathIndexed:
      res &= idx.join("", ("[", "]")) & "    "

    elif positionIndexed:
      if level > 0:
        res &= "  ".repeat(level - 1) & "\e[38;5;240m#" & $idx[^1] & "\e[0m" &
          "\e[38;5;237m/" & alignLeft($level, 2) & "\e[0m" & " "

      else:
        res &= "    "

    else:
      res.addIndent(level)

    if level > maxdepth:
      res &= " ..."
      return
    elif isNil(n):
      res &= toRed("<nil>", colored)
      return

    with res:
      add ($n.kind)[2..^1]
      add " "
      add $n.startPoint()
      add ".."
      add $n.endPoint()

    if n.comment.text.len > 0:
      res.add "\n"
      for line in split(n.comment.text, '\n'):
        res.add "  # " & toCyan(line) & "\n"

    else:
      res.add " "


    case n.kind:
      of nkStringKinds: res &= "\"" & toYellow(n.getStrVal(), colored) & "\""
      of nkIntKinds: res &= toBlue($n.intVal, colored)
      of nkFloatKinds: res &= toMagenta($n.floatVal, colored)
      of nkIdent, nkSym: res &= toGreen(n.getStrVal(), colored)
      of nkCommentStmt: discard
      else:
        if n.len > 0: res &= "\n"
        for newIdx, subn in n:
          aux(subn, level + 1, idx & newIdx)
          if level + 1 > maxDepth: break
          if newIdx > maxLen: break
          if newIdx < n.len - 1: res &= "\n"

  aux(pnode, 0, @[])

initBlockFmtDsl()


proc toFmtBlock*(node: CstNode): LytBlock

proc lytIdentDefs(n: CstNode): tuple[idents, itype, default: LytBlock] =
  result.idents = H[joinItBlock(bkLine, n[0 ..^ 3], toFmtBlock(it), T[", "])]

  if n[^2].kind != nkEmpty:
    result.idents.add T[": "]
    result.itype = toFmtBlock(n[^2])

  else:
    result.itype = E[]

  if n[^1].kind != nkEmpty:
    result.default = H[T[" = "], toFmtBlock(n[^1])]

  else:
    result.default = E[]

proc lytIdentList(idents: seq[CstNode]): LytBlock =
  var argBlocks = mapIt(idents, lytIdentDefs(it))
  let nameW = mapIt(argBlocks, it.idents.minWidth).sorted()[^2]
  let typeW = maxIt(argBlocks, it.itype.minWidth)

  for (idents, itype, _) in mitems(argBlocks):
    idents.add T[repeat(" ", clampIdx(nameW - idents.minWidth))]
    itype.add T[repeat(" ", clampIdx(typeW - itype.minWidth))]

  result = V[]
  for idx, (idents, itype, default) in pairs(argBlocks):
    if idx < argBlocks.high:
      result.add H[idents, itype, default, T[", "]]

    else:
      result.add H[idents, itype, default]



proc toFmtBlock*(node: CstNode): LytBlock =
  proc aux(n: CstNode): LytBLock =
    case n.kind:
      of nkStmtList:
        result = V[]
        for sub in n:
          result.add aux(sub)

      of nkIdent:
        result = T[n.getStrVal()]

      of nkIntLit:
        result = T[$n.intVal]

      of nkStrLit:
        result = T[&"\"{n.strVal}\""]

      of nkElse:
        result = V[T["else:"], I[2, aux(n[0])], S[]]

      of nkOfBranch:
        var head = H[T["of "]]
        for idx, expr in pairs(n, 0 ..^ 2):
          if idx > 0:
            head.add T[", "]

          head.add aux(expr)

        head.add T[":"]
        result = V[head, I[2, aux(n[^1])], S[]]

      of nkCommand:
        var head = H[aux(n[0]), T[" "]]
        var body = V[]
        var commandBody = false
        for sub in items(n, 1 ..^ 1):
          if sub.kind in { nkOfBranch, nkStmtList, nkElse }:
            if not commandBody:
              head.add T[":"]

            commandBody = true

          if commandBody:
            body.add aux(sub)

          else:
            head.add aux(sub)

        if not commandBody:
          result = head

        else:
          result = V[head, I[2, body]]

      of nkInfix:
        result = H[aux(n[1]), T[" "], aux(n[0]), T[" "], aux(n[2])]

      of nkPrefix:
        result = H[aux(n[0]), aux(n[1])]

      of nkBracket:
        result = H[T["["]]
        result.addItBlock n, aux(it), T[", "]
        result.add T["]"]

      of nkPostfix:
        result = H[aux(n[1]), aux(n[0])]

      of nkPar:
        result = H[T["("]]
        result.addItBlock n, aux(it), T[", "]
        result.add T[")"]

      of nkBracketExpr:
        result = H[aux(n[0]), T["["]]
        result.addItBLock n[1..^1], aux(it), T[", "]
        result.add T["]"]


      of nkDotExpr:
        result = H[aux(n[0]), T["."], aux(n[1])]

      of nkAccQuoted:
        var txt = "`"
        for item in n:
          txt.add item.getStrVal()

        txt.add "`"

        result = T[txt]

      of nkCall:
        result = H[aux(n[0]), T["("]]
        for idx, arg in n[1 ..^ 1]:
          if idx > 0: result.add T[", "]
          result.add aux(arg)

        result.add T[")"]

      of nkEmpty:
        result = T[""]

      of nkIdentDefs:
        let (idents, itype, default) = lytIdentDefs(n)
        result = H[idents, itype, default]

      of nkForStmt:
        var head = H[T["for "]]
        head.addItBlock(n[0 ..^ 3], aux(it), T[", "])
        head.add T[" in "]
        head.add aux(n[^2])
        result = V[H[head], I[2, aux(n[^1])]]

      of nkYieldStmt:
        result = H[T["yield "], aux(n[0])]

      of nkDiscardStmt:
        result = H[T["discard "], aux(n[0])]

      of nkNilLit:
        result = T["nil"]

      of nkLetSection:
        if n.len == 1:
          result = H[T["let "], aux(n[0])]

        else:
          result = V[T["let"], I[2, V[mapIt(n, aux(it))]]]

      of nkProcDeclKinds:
        let name =
          case n.kind:
            of nkIteratorDef: "iterator "
            of nkProcDef: "proc "
            else: raise newImplementKindError(n)

        var alts: seq[LytBlock]

        block:
          var alt = H[T[name], aux(n[0]), aux(n[1]), aux(n[2]), T["("]]
          alt.addItBlock n[3][1..^1], aux(it), T[", "]
          alt.add T["): "]
          alt.add aux(n[3][0])
          alt.add T[" = "]
          alts.add alt

        block:
          var alt = V[H[T[name], aux(n[0]), aux(n[1]), aux(n[2]), T["("]]]
          alt.add I[4, lytIdentList(n[3][1..^1])]
          alt.add H[T["  ): "], aux(n[3][0]), T[" = "]]
          alt.add S[]
          alts.add alt


        result = V[C[alts], I[2, aux(n[6])], S[]]


      else:
        raise newImplementKindError(n, n.treeRepr())

    assertRef result, $n.kind

  return aux(node)

proc `$`*(node: CstNode): string =
  let blc = toFmtBlock(node)
  return blc.toString()
