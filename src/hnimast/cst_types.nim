import
  compiler/[ast, lineinfos, idents]

import
  hnimast/hast_common

import
  ./cst_lexer

import
  std/[macros, with, strformat, sequtils, strutils, algorithm]

import
  hmisc/core/all,
  hmisc/types/colorstring,
  hmisc/algo/[halgorithm, clformat],
  hmisc/other/blockfmt,
  hmisc/macros/wrapfields



type
  CstPoint* = object
    tokenIdx*: int
    lineInfo*: TLineInfo

  CstRange* = object
    startPoint*, endPoint*: CstPoint

  CommentKind = enum
    ckNone
    ckLine ## Line comment for a single line
    ckInline ## Inline coment
    ckMultilineLine ## Line coment that spans multiple lines
    ckMultilineInline ## Inline comment that spans multiple lines

  CstComment* = object
    kind*: CommentKind
    isRawComment*: bool
    rangeInfo*: CstRange
    text*: string

  CstNode* = ref CstNodeObj
  CstNodeObj* = object
    rangeInfo*: CstRange
    docComment*: CstComment
    nextComment*: CstComment
    flags*: set[TNodeFlag]
    baseTokens*: ref seq[Token]

    height* {.requiresinit.}: int ## Max height of the tree
    size* {.requiresinit.}: int ## Total number of subnodes

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



func len*(main: CstNode): int =
  result = len(main.subnodes)

func high*(main: CstNode): int =
  result = high(main.subnodes)

func `[]`*(main: CstNode; index: IndexTypes): CstNode =
  main.subnodes[index]

func `[]`*(main: CstNode; slice: SliceTypes): seq[CstNode] =
  main.subnodes[slice]

func `[]=`*(main: CstNode; index: IndexTypes;
           value: CstNode) =
  main.subnodes[index] = value

iterator rpairs*(main: CstNode): (int, CstNode) =
  var idx = high(main.subnodes)
  while (
    0 <= idx):
    yield (idx, main.subnodes[idx])
    dec idx, 1

iterator pairs*(main: CstNode): (int, CstNode) =
  for idx in 0 ..< len(main):
    yield (idx, main.subnodes[idx])

iterator pairs*(main: CstNode; slice: SliceTypes): (int, CstNode) =
  let slice = clamp(slice, main.subnodes.high)
  var resIdx = 0
  for idx in slice:
    yield (resIdx, main.subnodes[idx])
    inc resIdx

iterator ritems*(main: CstNode): CstNode =
  var idx = high(main.subnodes)
  while (
    0 <= idx):
    yield main.subnodes[idx]
    dec idx, 1

iterator items*(main: CstNode): CstNode =
  for item in items(main.subnodes):
    yield item

iterator items*(main: CstNode; slice: SliceTypes): CstNode =
  let slice = clamp(slice, main.subnodes.high)
  for idx in slice:
    yield main.subnodes[idx]

wrapKindAst(CstNode, TNodeKind)

wrapStructContainer(
  CstNode.rangeInfo, { startPoint, endPoint: CstPoint }, isRef = true)

func add*(node: CstNode, other: CstNode) =
  node.subnodes.add other
  node.height = max(node.height, other.height + 1)
  node.size += other.size

func add*(node: CstNode, other: openarray[CstNode]) =
  for o in other:
    node.add o

func getStrVal*(p: CstNode, doRaise: bool = true): string =
  ## Get string value from `PNode`
  case p.kind:
    of nkIdent, nkSym: p.ident.s
    of nkStringKinds: p.strVal
    else:
      if doRaise:
        raise newArgumentError(
          "Cannot get string value from node of kind " & $p.kind)

      else:
        ""

func newEmptyCNode*(): CstNode =
  CstNode(kind: nkEmpty, size: 1, height: 1)

func add*(comm: var CstComment, str: string) = comm.text.add str
func newNodeI*(
    kind: TNodeKind, point: CstPoint, base: ref seq[Token]): CstNode =
  CstNode(
    size: 1,
    height: 1,
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
  result.height = maxIt(children, it.height) + 1
  result.size = sumIt(children, it.size) + 1


template transitionNodeKindCommon(k: TNodeKind) =
  let obj {.inject.} = n[]
  n[] = CstNodeObj(
    size: obj.size,
    height: obj.height,
    kind: k,
    rangeInfo: obj.rangeInfo,
    docComment: obj.docComment,
    nextComment: obj.nextComment,
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
    add $hshow(point.lineInfo.line)
    add ":"
    add $hshow(point.lineInfo.col)
    add "@", tcGrey27.fg + tcDefault.bg
    add $hshow(point.tokenIdx)

func treeRepr*(
    pnode: CstNode,
    opts: HDisplayOpts = defaultHDisplay,
    withSize: bool = false
  ): ColoredText =

  coloredResult()

  proc aux(n: CstNode, level: int, idx: seq[int]) =
    add joinPrefix(level, idx, opts.pathIndexed, opts.positionIndexed)

    if level > opts.maxdepth:
      add " ..."
      return

    elif isNil(n):
      add toRed("<nil>", opts.colored)
      return

    if withSize:
      add &"h{n.height}×s{n.size} "

    add ($n.kind)[2..^1]

    if opts.withRanges:
      add " "
      add $n.startPoint()
      add ".."
      add $n.endPoint()

    var hadComment = false
    if n.docComment.text.len > 0:
      add "\n"
      for line in split(n.docComment.text, '\n'):
        addIndent(level + 2)
        add "  ## " & toYellow(line) & "\n"

      hadComment = true

    if n.nextComment.text.len > 0:
      add "\n"
      for line in split(n.nextComment.text, '\n'):
        addIndent(level + 2)
        add "  # " & toCyan(line) & "\n"

      hadComment = true

    if not hadComment:
      add " "


    case n.kind:
      of nkStringKinds:
        add hshow(n.getStrVal(), opts)

      of nkIntKinds:
        add hshow(n.intVal, opts)

      of nkFloatKinds:
        add hshow(n.floatVal, opts)

      of nkIdent, nkSym:
        add toGreen(n.getStrVal(), opts.colored)

      of nkCommentStmt:
        discard

      else:
        if n.len > 0: add "\n"
        for newIdx, subn in pairs(n):
          aux(subn, level + 1, idx & newIdx)
          if level + 1 > opts.maxDepth: break
          if newIdx > opts.maxLen: break
          if newIdx < n.len - 1: add "\n"

  aux(pnode, 0, @[])

initBlockFmtDsl()


proc toFmtBlock*(node: CstNode): LytBlock

proc lytDocComment(n: CstNode, prefix: string = ""): LytBlock =
  if n.docComment.text.len > 0:
    result = V[]
    for line in n.docComment.text.split('\n'):
      result.add T[prefix & "## " & line]

  else:
    result = E[]


proc lytNextComment(n: CstNode, prefix: string = ""): LytBlock =
  if n.nextComment.text.len == 0:
    return E[]

  case n.nextComment.kind:
    of ckNone:
      result = T[prefix & n.nextComment.text]

    of ckLine:
      result = T["# " & n.nextComment.text]

    of ckInline:
      result = T["#[ " & n.nextComment.text & "]#"]

    else:
      raise newImplementKindError(n.nextComment)


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

proc lytSplitExpression(n: CstNode, spaces: bool = true):
    tuple[start: LytBlock, middle: seq[LytBlock], final: LytBlock] =

  case n.kind:
    of nkCurly:
      result.start = (T["{ "], T["{"]) ?? spaces
      result.middle = mapIt(n, toFmtBlock(it))
      result.final = (T[" }"], T["}"]) ?? spaces

    of nkBracket:
      result.start = (T["[ "], T["["]) ?? spaces
      result.middle = mapIt(n, toFmtBlock(it))
      result.final = (T[" ]"], T["]"]) ?? spaces

    else:
      raise newImplementError()

proc lytStmtHead(start: LytBlock, middle: CstNode, final: LytBlock): LytBlock =
  result = C[]
  result.add H[start, toFmtBlock(middle), final]

  if middle =~ nkInfix and
     middle[2].size > 10:

    let (start, splitMiddle, final) = lytSplitExpression(
      middle[2], spaces = false)

    result.add V[
      H[T["if "], toFmtBlock(middle[1]), T[" "], toFmtBlock(middle[0]), T[" "], start],
      I[2, W[splitMiddle, ", "]],
      H[final, T[":"]]
    ]




proc lytIdentList(idents: seq[CstNode]): LytBlock =
  var argBlocks = mapIt(idents, lytIdentDefs(it))
  let nameW = mapIt(argBlocks, it.idents.minWidth).sorted().getClamped(^2)
  let typeW = maxIt(argBlocks, it.itype.minWidth)

  for (idents, itype, default) in mitems(argBlocks):
    idents.add T[repeat(" ", clampIdx(nameW - idents.minWidth))]
    if not isEmpty(default):
      itype.add T[repeat(" ", clampIdx(typeW - itype.minWidth))]

  result = V[]
  for idx, (idents, itype, default) in pairs(argBlocks):
    if idx < argBlocks.high:
      result.add H[idents, itype, default, T[", "]]

    else:
      result.add H[idents, itype, default]

func isSimpleExprList(list: seq[CstNode]): bool =
  result = true
  for expr in list:
    if expr.kind notin nkTokenKinds:
      return false



proc toFmtBlock*(node: CstNode): LytBlock =
  proc aux(n: CstNode): LytBLock =
    case n.kind:
      of nkStmtList:
        result = V[]
        var lastLet: CstNode
        for sub in n:
          if sub.kind == nkLetSection:
            if isNil(lastLet):
              lastLet = sub

            else:
              lastLet.add sub[0..^1]

          else:
            if not isNil(lastLet):
              result.add aux(lastLet)
              lastLet = nil

            result.add aux(sub)

      of nkIdent:
        result = H[T[n.getStrVal()], lytNextComment(n, " ")]

      of nkIntLit:
        result = T[$n.intVal]

      of nkStrLit:
        result = T[&"\"{n.strVal}\""]

      of nkCharLit:
        var buf = "'"
        buf.addEscapedChar(n.intVal.int.char)
        buf.add '\''
        result = T[buf]

      of nkElse:
        result = V[T["else:"], I[2, aux(n[0])], S[]]

      of nkImportStmt, nkExportStmt:
        # TODO collect list of imports for a file ... group import
        # sections. Then split them again, grouping by package name. This
        # would enforce `std/` prefix, as otherwise all imports would be
        # scattered over standalone imports.
        if n.has(1):
          result = V[]
          for imp in n:
            if imp =~ nkInfix and imp[^1] =~ nkBracket:
              let (start, middle, final) = lytSplitExpression(imp[^1])
              result.add V[
                H[aux(imp[0]), start],
                I[2, H[W[middle, ", "], final, T[", "]]]]

            else:
              result.add H[aux(imp), T[","]]



          result = V[T["import"], I[2, result]]

        else:
          result = H[T["import "], aux(n[0])]

      of nkOfBranch:
        var alts = C[]
        block:
          var alt = H[]
          for idx, expr in pairs(n, 0 ..^ 2):
            if idx > 0:
              alt.add T[", "]

            alt.add aux(expr)

          alts.add alt

        if isSimpleExprList(n[0 ..^ 2]):
          alts.add joinItBlock(bkWrap, n[0..^2], aux(it), T[", "])

        result = V[H[T["of "], alts, T[":"]], I[2, aux(n[^1])], S[]]

      of nkCommand, nkCall:
        let isCall = n.kind == nkCall
        if n.kind == nkCall and
           n.len == 2 and
           n[0].kind == nkIdent and
           n[0].getStrVal() in ["inc", "dec", "echo"]:
          result = H[aux(n[0]), T[" "], aux(n[1])]


        var head = H[aux(n[0]), (T["("], T[" "]) ?? isCall]
        var body = V[]
        var commandBody = false
        for sub in items(n, 1 ..^ 1):
          if sub.kind in { nkOfBranch, nkStmtList, nkElse }:
            if not commandBody:
              head.add (T["):"], T[":"]) ?? isCall

            commandBody = true

          if commandBody:
            body.add aux(sub)

          else:
            head.add aux(sub)

        if not commandBody:
          if isCall: head.add T[")"]
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

      of nkEmpty:
        result = lytNextComment(n)

      of nkIdentDefs:
        let (idents, itype, default) = lytIdentDefs(n)
        result = H[
          idents, itype, default,
          lytDocComment(n, " "),
          lytNextComment(n, " ")
        ]

      of nkForStmt:
        var head = H[T["for "]]
        head.addItBlock(n[0 ..^ 3], aux(it), T[", "])
        head.add T[" in "]
        head.add aux(n[^2])
        result = V[H[head], I[2, aux(n[^1])]]

      of nkWhileStmt:
        result = V[
          H[T["while "], aux(n[0]), T[":"]],
          I[2, aux(n[1])]
        ]

      of nkCaseStmt:
        result = V[
          H[T["case "], aux(n[0]), T[":"]],
          I[2, joinItBlock(bkStack, n[1 ..^ 1], aux(it), S[])]
        ]


      of nkYieldStmt:
        result = H[T["yield "], aux(n[0])]

      of nkDiscardStmt:
        result = H[T["discard "], aux(n[0])]

      of nkReturnStmt:
        result = H[T["return "], aux(n[0])]

      of nkBreakStmt:
        result = H[T["break "], aux(n[0])]

      of nkCurly:
        let isSet = allIt(n, it.kind != nkExprColonExpr)

        if isSet:
          var alts: seq[LytBlock]
          block:
            var alt = H[T["{ "]]
            alt.addItBlock(n, aux(it), T[", "])
            alt.add T[" }"]
            alts.add alt

          result = C[alts]

        else:
          raise newImplementError()

      of nkVarTy:
        result = H[T["var "], aux(n[0])]

      of nkTypeSection:
        var types = V[]
        for t in n:
          types.add aux(t)
          types.add S[]

        result = V[T["type"], I[2, types]]

      of nkRecList:
        result = V[]
        for item in n:
          if item.kind != nkEmpty:
            result.add aux(item)

      of nkTypeDef:
        var body = V[]
        for field in n[2]:
          if field.kind != nkEmpty:
            body.add aux(field)

        case n[2].kind:
          of nkObjectTy:
            result = V[H[aux(n[0]), T[" = object"]], I[2, body]]

          else:
            raise newImplementKindError(n[2])

      of nkCommentStmt:
        result = lytDocComment(n)

      of nkIfStmt:
        result = V[]
        for idx, branch in n:
          if idx == 0:
            result.add V[
              lytStmtHead(T["if "], branch[0], T[":"]),
              I[2, aux(branch[1])],
              S[]]

          else:
            if branch.kind == nnkElifBranch:
              result.add V[
                H[T["elif "], aux(branch[0]), T[":"]],
                I[2, aux(branch[1])],
                S[]]

            else:
              result.add V[
                H[T["else:"]],
                I[2, aux(branch[0])],
                S[]]

        # result.add S[]

      of nkNilLit:
        result = T["nil"]

      of nkAsgn:
        result = H[aux(n[0]), T[" = "], aux(n[1])]

      of nkLetSection, nkVarSection:
        let word = if n.kind == nkLetSection: "let" else: "var"
        if n.len == 1:
          result = H[T[word & " "], aux(n[0])]

        else:
          result = V[T[word], I[2, V[mapIt(n, aux(it))]]]

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
          alts.add alt


        result = V[C[alts], I[2, aux(n[6])], S[]]


      else:
        raise newImplementKindError(
          n, n.treeRepr(hdisplay(maxdepth = 4), true))

    assertRef result, $n.kind

  return aux(node)

proc `$`*(node: CstNode): string =
  let blc = toFmtBlock(node)
  return blc.toString().toString(color = false)
