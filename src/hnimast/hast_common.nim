import std/[macros, sequtils, strformat, strutils, tables, sets]
import compiler/[ast, idents, lineinfos, renderer]
import hmisc/types/colorstring
import hmisc/helpers

export ast, macros

template `[]`*(node: PNode, slice: HSLice[int, BackwardsIndex]): untyped =
  ## Get range of subnodes from `PNode`
  `[]`(node.sons, slice)



const
  nnkStrKinds* = { nnkStrLit .. nnkTripleStrLit }
  nnkIntKinds* = { nnkCharLit .. nnkUInt64Lit }
  nnkFloatKinds* = { nnkFloatLit .. nnkFloat128Lit }
  nnkLiteralKinds* = nnkStrKinds + nnkIntKinds + nnkFloatKinds
  nnkTokenKinds* = nnkLiteralKinds + {nnkIdent, nnkSym}

  nnkProcKinds* = {
    nnkProcTy,
  }

  dekTypeKinds* = {
    nnkObjectTy
  }

  nnkProcDeclKinds* = {
    nnkProcDef,
    nnkFuncDef,
    nnkIteratorDef,
    nnkTemplateDef,
    nnkMacroDef,
    nnkMethodDef,
    nnkConverterDef
  }


  nkStrKinds* = { nkStrLit .. nkTripleStrLit }
  nkIntKinds* = { nkCharLit .. nkUInt64Lit }
  nkFloatKinds* = { nkFloatLit .. nkFloat128Lit }
  nkLiteralKinds* = nkStrKinds + nkIntKinds + nkFloatKinds + {
    nkNilLit}

  nkTokenKinds* = nkLiteralKinds + {nkIdent, nkSym}


  nkProcDeclKinds* = {
    nkProcDef,
    nkFuncDef,
    nkIteratorDef,
    nkTemplateDef,
    nkMacroDef,
    nkMethodDef,
    nkConverterDef
  }

type
  ObjectAnnotKind* = enum
    ## Position of annotation (most likely pragma) attached.
    oakCaseOfBranch ## Annotation on case branch, not currently suppported
    oakObjectToplevel ## Toplevel annotaion for object
    oakObjectField ## Annotation for object field


template currIInfo*(): untyped =
  let (file, line, col) = instantiationInfo()
  LineInfo(filename: file, line: line, column: col)

const defaultIInfo* = LineInfo()

proc getInfo*(n: NimNode): LineInfo = n.lineInfoObj
proc getInfo*(n: PNode): TLineInfo = n.info

func dropPar1*(nn: NimNode): NimNode =
  if nn.kind == nnkPar: nn[0] else: nn



#==========================  String conversion  ==========================#

func `$!`*(n: NimNode): string =
  ## NimNode stringification that does not blow up in your face on
  ## 'invalid node kind'
  n.toStrLit().strVal()


func `$!`*(n: PNode): string =
  ## PNode stringification that does not blow up in your face on
  ## 'invalid node kind'
  {.cast(noSideEffect).}:
    renderer.`$`(n)

proc `$`*(n: PNode): string =
  ## Convert `PNode` back to code.
  {.cast(noSideEffect).}:
    renderer.`$`(n)

proc `&`*(n: PNode, str: string): PNode =
  if n.kind in nkStrKinds + {nkIdent}:
    result = n
    result.strVal &= str

  else:
    raiseArgumentError(
      "Cannot concatentate non-string node with string")

func getStrVal*(n: NimNode): string =
  ## Get string value from `NimNode` that can have it - e.g. strings,
  ## identifiers etc.
  n.strVal()

func getStrVal*(p: PNode): string =
  ## Get string value from `PNode`
  case p.kind:
    of nkIdent:    p.ident.s
    of nkSym:      p.sym.name.s
    of nkStrKinds: p.strVal
    of nkOpenSymChoice: p[0].sym.name.s
    of nkAccQuoted: ($p)[1..^2]
    else:
      raiseArgumentError(
        "Cannot get string value from node of kind " & $p.kind)


func dropStmtList*(p: PNode): PNode =
  case p.kind:
    of nkStmtList:
      p[0]
    else:
      p

func toString*(n: NimNode): string =
  ## Convert any node to string without side effects
  n.toStrLit().strVal()

func toString*(p: PNode): string =
  ## Convert any node to string without side effects
  {.noSideEffect.}:
    $p

func toStr*(
    info: LineInfo | tuple[filename: string, line: int, column: int],
    shortPath: bool = true
  ): string =

  if shortPath:
    let spl = info.filename.split("/")[^1]
    return &"{info.line}:{info.column}:{spl}"

  else:
    return &"{info.line}:{info.column}:{info.filename}"


func toShow*[N](node: N): string = "'" & toString(node) & "'"

#==============  Uniform operations for PNode and NimNode  ===============#

func subnodes*(p: PNode): seq[PNode] =
  ## Get subnodes as a sequence
  p.sons

func subnodes*(n: NimNode): seq[NimNode] =
  ## Get subnodes as a sequence
  toSeq(n.children)

func skipNil*(n: NimNode): NimNode =
  ## If node `n` is `nil` generated new empty node, otherwise return
  ## `n`
  if n == nil: newEmptyNode() else: n

func nilToDiscard*(n: NimNode): NimNode =
  ## If node `n` is `nil` generate new discard node, otherwise return
  ## `n`
  if n == nil: nnkDiscardStmt.newTree(newEmptyNode()) else: n


func toNK*(kind: NimNodeKind): TNodeKind =
  TNodeKind(kind)

func toNNK*(kind: TNodeKind): NimNodeKind = NimNodeKind(kind)
func toNNK*(kind: NimNodeKind): NimNodeKind = kind

func `==`*(k1: TNodeKind, k2: NimNodeKind): bool = k1.toNNK() == k2


func expectKind*(expr: PNode, kind: NimNodeKind): void =
  ## Raise assertion error of `expr` kind is not equal to `kind`
  if expr.kind != kind.toNK():
    raiseArgumentError(
      &"Unexpected node kind: got {expr.kind}, but expected {kind}")

#==========================  Tree construction  ==========================#

func newTree*(kind: NimNodeKind, subnodes: seq[PNode]): PNode =
  ## Create new `PNode` tree with `subnodes` as child elements. `kind`
  ## will be converted to corresponding `TNodeKind`
  kind.toNK().newTree(subnodes)

func newAccQuoted*(args: varargs[NimNode]): NimNode =
  nnkAccQuoted.newTree(args)

func newAccQuoted*(args: varargs[string]): NimNode =
  nnkAccQuoted.newTree(args.mapIt(ident it))

proc newPIdent*(str: string): PNode =
  ## Create new `nkIdent` pnode
  newIdentNode(PIdent(s: str), TLineInfo())


func newInfix*(op: string, lhs, rhs: NimNode): NimNode =
  ## Create new `nnkInfix` node
  nnkInfix.newTree(ident op, lhs, rhs)

func newPrefix*(op: string, expr: NimNode): NimNode =
  ## Create new `nnkPrefix` node
  nnkPrefix.newTree(@[ident op, expr])

func newPrefix*(op: string, expr: PNode): PNode =
  ## Create new `nkPrefix` node
  nnkPrefix.newTree(@[newPIdent op, expr])

func newReturn*(expr: NimNode): NimNode =
  ## Create new return statement
  nnkReturnStmt.newTree(@[expr])

func newReturn*(expr: PNode): PNode =
  ## Create new return stetement
  nnkReturnStmt.newTree(@[expr])


func newNIdent*[NNode](str: string): NNode =
  ## Create new `nnkIdent` node of type `NNode`
  when NNode is NimNode:
    newIdentNode(str)

  else:
    newPIdent(str)

func newNTree*[NNode](
  kind: NimNodeKind, subnodes: varargs[NNode]): NNode =
  ## Create new tree with `subnodes` and `kind`
  # STYLE rename to `toNNode`
  when NNode is NimNode:
    newTree(kind, subnodes)

  else:
    newTree(kind.toNK(), subnodes)

func newPTree*(kind: NimNodeKind, subnodes: varargs[PNode]): PNode =
  ## Create new `PNode` tree
  if kind in nnkTokenKinds:
    if subnodes.len > 0:
      raiseArgumentError(
        &"Cannot create node of kind {kind} with subnodes")

    else:
      newNode(kind.toNK())

  else:
    newTree(kind.toNK(), subnodes)

func newCommentStmtNNode*[NNode](comment: string): NNode =
  ## Create new `nnkCommentStmt` node
  when NNode is NimNode:
    return newCommentStmtNode(comment)
  else:
    result = newNTree[NNode](nnkCommentStmt)
    result.comment = comment

template addPositionComment*[N](node: N): untyped =
  newNTree[N](
    nnkStmtList,
    newCommentStmtNNode[N](toStr(instantiationInfo())),
    node
  )

template newPositionPComment*(
    pos:
      LineInfo |
      tuple[filename: string, line: int, column: int]
  ): untyped {.dirty.} =

  newCommentStmtNNode[PNode]($pos)

func newEmptyNNode*[NNode](): NNode =
  ## Create new empty node of type `NNode`
  when NNode is NimNode:
    newEmptyNode()
  else:
    newTree(nkEmpty)

func newEmptyPNode*(): PNode =
  ## Create new empty PNode
  newEmptyNNode[PNode]()

func newPLit*(i: int): PNode =
  ## Create new integer literal `PNode`
  newIntTypeNode(BiggestInt(i), PType(kind: tyInt))

func newPLit*(i: BiggestInt): PNode =
  ## Create new integer literal `PNode`
  newIntTypeNode(i, PType(kind: tyInt))

func newPLit*(n: typeof(nil)): PNode =
  PNode(kind: nkNilLit)

func newPLit*(b: bool): PNode =
  if b: newPident("true") else: newPident("false")
  # newIntTypeNode(BiggestInt(b), PType(kind: tyBool))

func newPLit*(c: char): PNode =
  newIntTypeNode(BiggestInt(c), PType(kind: tyChar))

func newPLit*(f: float): PNode =
  newFloatNode(nkFloatLit, f)

func newPLit*(i: string): PNode =
  ## Create new string literal `PNode`
  newStrNode(nkStrLit, i)

func newRStrLit*(st: string): PNode =
  result = nnkRStrLit.newPTree()
  result.strVal = st

func toStrLit*(node: PNode): PNode =
  {.noSideEffect.}:
    result = newPLit($node)


func lineIInfo*(node: NimNode): NimNode =
  ## Create tuple literal for `{.line: .}` pragma
  let iinfo = node.lineInfoObj()
  newLit((filename: iinfo.filename, line: iinfo.line))

func newPIdentColonString*(key, value: string): PNode =
  nnkExprColonExpr.newPTree(newPIdent(key), newPLit(value))


func newExprColonExpr*(key, value: PNode): PNode =
  nnkExprColonExpr.newPTree(key, value)

template newNNLit*[NNode](val: untyped): untyped =
  when NNode is PNode:
    newPLit(val)
  else:
    newLit(val)



func newPTree*(kind: NimNodeKind, val: string): PNode =
  result = PNode(kind: kind.toNk())
  result.strVal = val

func newPTree*(kind: NimNodeKind, val: SomeInteger): PNode =
  result = PNode(kind: kind.toNK())
  result.intVal = BiggestInt(val)

func newPCall*(call: string, args: varargs[PNode]): PNode =
  result = nnkCall.newPTree()
  result.add newPIdent(call)
  for arg in args:
    result.add arg



func toBracket*(elems: seq[NimNode]): NimNode =
  ## Create `nnkBracket` with elements
  # TODO use `NNode`
  nnkBracket.newTree(elems)

func toBracketSeq*(elems: seq[NimNode]): NimNode =
  ## Create `nnkBracket` with `@` prefix - sequence literal
  ## `@[<elements>]`
  # TODO use `NNode`
  nnkPrefix.newTree(ident "@", nnkBracket.newTree(elems))

func setPosition*[N](target: var N, source: N) =
  when N is NimNode:
    target.copyLineInfo(source)

  else:
    target.info = source.info

#=======================  Misc helper algorithms  ========================#


func flattenInfix*[N](inNode: N, infix: string): seq[N] =
  func aux(node: N): seq[N] =
    if node.kind == nnkInfix and node[0].getStrVal() == infix:
      result = aux(node[1]) & aux(node[2])

    else:
      result = @[node]

  return aux(inNode)

func foldInfix*[N](inNodes: seq[N], infix: string): N =
  func aux(nodes: seq[N]): N =
    if nodes.len == 1:
      result = nodes[0]

    else:
      result = newNTree[N](
        nnkInfix,
        newNIdent[N](infix),
        nodes[0],
        aux(nodes[1..^1])
      )

  return aux(inNodes)

#===========================  Pretty-printing  ===========================#




proc pprintCalls*(node: NimNode, level: int): void =
  # TODO:DOC
  let pref = "  ".repeat(level)
  let pprintKinds = {nnkCall, nnkPrefix, nnkBracket}
  case node.kind:
    of nnkCall:
      if ($node[0].toStrLit()).startsWith("make"):
        echo pref, "make", (($node[0].toStrLit())[4..^1]).toGreen()

      else:
        echo pref, $node[0].toStrLit()

      if node[1..^1].noneOfIt(it.kind in pprintKinds):
        echo pref, "  ",
          node[1..^1].mapIt($it.toStrLit()).join(", ").toYellow()

      else:
        for arg in node[1..^1]:
          pprintCalls(arg, level + 1)

    of nnkPrefix:
      echo pref, node[0]
      pprintCalls(node[1], level)

    of nnkBracket:
      for subn in node:
        pprintCalls(subn, level + 1)

    of nnkIdent:
      echo pref, ($node).toGreen()

    else:
      echo ($node.toStrLit()).indent(level * 2)

proc treeRepr*(
    pnode: PNode, colored: bool = true,
    indexed: bool = false, maxdepth: int = 120
  ): string =

  proc aux(n: PNode, level: int, idx: seq[int]): string =
    let pref =
      if indexed:
        idx.join("", ("[", "]")) & "    "
      else:
        "  ".repeat(level)

    if isNil(n):
      return pref & toRed("<nil>", colored)

    if level > maxdepth:
      return pref & " ..."



    result &= pref & ($n.kind)[2..^1]
    if n.comment.len > 0:
      result.add "\n"
      for line in split(n.comment, '\n'):
        result.add pref & " " & toCyan(line) & "\n"

    case n.kind:
      of nkStrKinds:
        result &= " \"" & toYellow(n.getStrVal(), colored) & "\""

      of nkIntKinds:
        result &= " " & toBlue($n.intVal, colored)

      of nkFloatKinds:
        result &= " " & toMagenta($n.floatVal, colored)

      of nkIdent, nkSym:
        result &= " " & toGreen(n.getStrVal(), colored)

      of nkCommentStmt:
        let lines = split(n.comment, '\n')
        if lines.len > 1:
          result &= "\n"
          for idx, line in pairs(lines):
            if idx != 0:
              result &= "\n"

            result &= pref & toYellow(line)

        else:
          result &= toYellow(n.comment)

      else:
        if n.len > 0:
          result &= "\n"

        for newIdx, subn in n:
          result &= aux(subn, level + 1, idx & newIdx)
          if newIdx < n.len - 1:
            result &= "\n"

  return aux(pnode, 0, @[])

func idxTreeRepr*(inputNode: NimNode): string =
  ## `treeRepr` with indices for subnodes
  ## .. code-block::
  ##                 TypeDef
  ##     [0]            PragmaExpr
  ##     [0][0]            Postfix
  ##     [0][0][0]            Ident *
  ##     [0][0][1]            Ident Hello
  ##     [0][1]            Pragma

  func aux(node: NimNode, parent: seq[int]): seq[string] =
    result.add parent.mapIt(&"[{it}]").join("") &
      "  ".repeat(6) &
      ($node.kind)[3..^1] &
      (node.len == 0).tern(" " & node.toStrLit().strVal(), "")

    for idx, subn in node:
      result &= aux(subn, parent & @[idx])

  return aux(inputNode, @[]).join("\n")




#=======================  Init calls construction  =======================#

func makeInitCalls*[T](val: T): NimNode =
  # TODO:DOC
  when T is enum:
    ident($val)

  else:
    newLit(val)

func makeInitAllFields*[T](val: T): NimNode =
  # TODO:DOC
  result = newCall("init" & $typeof(T))
  for name, val in fieldPairs(val):
    result.add nnkExprEqExpr.newTree(
      ident(name), makeInitCalls(val))

func makeConstructAllFields*[T](val: T): NimNode =
  # TODO:DOC
  when val is seq:
    result = val.mapPairs(
      rhs.makeConstructAllFields()).toBracketSeq()

  elif val is int | float | string | bool | enum | set:
    result = newLit(val)

  else:
    when val is Option:
      when val is Option[void]:
        result = newCall(ident "none", ident "void")

      else:
        if val.isSome():
          result = newCall(ident "none", parseExpr $typeof(T))

        else:
          result = newCall(ident "some", makeConstructAllFields(val.get()))

    else:
      result = nnkObjConstr.newTree(parseExpr $typeof(T))
      for name, fld in fieldPairs(val):
        when (fld is Option) and not (fld is Option[void]):
          # debugecho name, " ", typeof(fld)
          if fld.isSome():
            result.add nnkExprColonExpr.newTree(
              ident(name),
              newCall("some", makeConstructAllFields(fld.get())))

        else:
          result.add nnkExprColonExpr.newTree(
            ident(name), makeConstructAllFields(fld))

func makeInitCalls*[A, B](table: Table[A, B]): NimNode =
  # TODO:DOC
  mixin makeInitCalls
  result = nnkTableConstr.newTree()
  for key, val in table:
    result.add newColonExpr(key.makeInitCalls, val.makeInitCalls)

  result = newCall(
    nnkBracketExpr.newTree(
      ident("toTable"),
      parseExpr($typeof(A)),
      parseExpr($typeof(B))
    ),
    result
  )

func makeInitCalls*[A](hset: HashSet[A]): NimNode =
  # TODO:DOC
  mixin makeInitCalls
  result = nnkBracket.newTree()
  for val in hset:
    result.add val.makeInitCalls()

  result = newCall("toHashSet", result)

#=======================  Enum set normalization  ========================#
func normalizeSetImpl[NNode](node: NNode): seq[NNode] =
   case node.kind.toNNK():
    of nnkIdent, nnkIntLit, nnkCharLit, nnkDotExpr:
      return @[ node ]

    of nnkCurly:
      mixin items
      for subnode in items(node):
        result &= normalizeSetImpl(subnode)

    of nnkInfix:
      assert node[0].getStrVal() == ".."
      result = @[ node ]

    else:
      {.cast(noSideEffect).}:

        when node is PNode:
          let str = hast_common.`$`(node)

        else:
          let str = `$`(node)

        raiseArgumentError(
          "Cannot normalize set: " & str & " - unknown kind")




func normalizeSet*[NNode](node: NNode, forcebrace: bool = false): NNode =
  ## Convert any possible set representation (e.g. `{1}`, `{1, 2}`,
  ## `{2 .. 6}` as well as `2, 3` (in case branches). Return
  ## `nnkCurly` node with all values listed one-by-one (if identifiers
  ## were used) or in ranges (if original node contained `..`)
  let vals = normalizeSetImpl(node)
  if vals.len == 1 and not forcebrace:
    return vals[0]

  else:
    return newNTree[NNode](nnkCurly, vals)

func joinSets*[NNode](nodes: seq[NNode]): NNode =
  ## Concatenate multiple sets in one element. Result will be wrapped
  ## in `Curly` node.
  let vals = nodes.mapIt(it.normalizeSetImpl()).concat()
  result = newTree[NNode](nnkCurly, vals)

proc parseEnumSet*[Enum](
  node: NimNode,
  namedSets: Table[string, set[Enum]] =
      initTable[string, set[Enum]]()): set[Enum] =
  ## Parse `NimNode` into set of `Enum` values. `namedSets` is an
  ## ident-set mapping for additional identifiers that might be used
  ## as set values.
  case node.kind:
    of nnkIdent:
      try:
        return {parseEnum[Enum]($node)}
      except ValueError:
        if $node in namedSets:
          namedSets[$node]
        else:
          raise newException(
            ValueError,
            "Invalid enum value '" & $node & "' for expression " &
              posString(node) &
              " and no such named set exists (available ones: " &
              namedSets.mapPairs(lhs).joinq() & ")"
          )
    of nnkInfix:
      assert node[0] == ident("..")
      return {parseEnum[Enum]($node[1]) ..
              parseEnum[Enum]($node[2])}
    of nnkCurly:
      for subnode in node.children:
        result.incl parseEnumSet[Enum](subnode, namedSets)

    else:
      # QUESTION there was something useful or what? Do I need it
      # here?
      discard

proc parseIdentName*[N](node: N): tuple[exported: bool, name: N] =
  case node.kind.toNNK():
    of nnkPragmaExpr:
      case node[0].kind.toNNK():
        of nnkPostfix:
          result.name = node[0][1]
          result.exported = true

        else:
          result.name = node[0]

    of nnkPostfix:
      result.name = node[1]
      result.exported = true

    else:
      result.name = node
