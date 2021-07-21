import std/[macros, sequtils, strformat, strutils,
            tables, sets, options, math]
import compiler/[ast, idents, lineinfos, renderer]
import hmisc/types/colorstring
import hmisc/helpers

export macros

template `[]`*(node: PNode, slice: HSLice[int, BackwardsIndex]): untyped =
  ## Get range of subnodes from `PNode`
  `[]`(node.sons, slice)

proc `?`*(node: PNode): bool =
  not isNil(node) and (node.len > 0)

proc `[]`*(node: PNode, idx: int, kinds: set[TNodeKind]): PNode =
  result = node[idx]
  assertKind(result, kinds)


proc add*(n: PNode, sub: seq[PNode]) =
  for node in sub:
    n.add node


const
  nnkStrKinds* = { nnkStrLit .. nnkTripleStrLit }
  nnkStringKinds* = nnkStrKinds
  nnkIntKinds* = { nnkCharLit .. nnkUInt64Lit }
  nnkFloatKinds* = { nnkFloatLit .. nnkFloat128Lit }
  nnkLiteralKinds* = nnkStrKinds + nnkIntKinds + nnkFloatKinds
  nnkTokenKinds* = nnkLiteralKinds + {nnkIdent, nnkSym}
  nnkIdentKinds* = {nnkIdent, nnkSym}
  nnkWrapTy* = { nnkRefTy, nnkPtrTy }


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

  nnkDeclKinds* = nnkProcDeclKinds + { nnkTypeDef }

  nkStrKinds* = { nkStrLit .. nkTripleStrLit }
  nkStringKinds* = nkStrKinds
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

  nkStmtBlockKinds* = {
    nkIfExpr,
    nkIfStmt,
    nkWhenStmt,
    nkWhenExpr,
    nkForStmt,
    nkBlockStmt
  }

  nkIdentDeclKinds* = {
    nkLetSection,
    nkVarSection,
    nkConstSection,
    nkIdentDefs
  }


  nkAllDeclKinds* = nkProcDeclKinds + nkIdentDeclKinds

  skProcDeclKinds* = {
    skProc,
    skTemplate,
    skMethod,
    skMacro,
    skIterator,
    skConverter,
    skFunc
  }

type
  ProcDeclNode*[N: NimNode | PNode] = distinct N

func asProcDecl*[N](n: N): ProcDeclNode[N] =
  when n is NimNode:
    assertKind(n, nnkProcDeclKinds)

  else:
    assertKind(n, nkProcDeclKinds)

  result = ProcDeclNode(n)

func asNode*(decl: ProcDeclNode[NimNode]): NimNode = NimNode(decl)
func asNode*(decl: ProcDeclNode[PNode]): PNode = PNode(decl)

func name*[N](decl: ProcDeclNode[N]): N = decl.asNode()[namePos]
func pattern*[N](decl: ProcDeclNode[N]): N = decl.asNode()[patternPos]
func genericParams*[N](decl: ProcDeclNode[N]): N = decl.asNode()[genericParamsPos]
func params*[N](decl: ProcDeclNode[N]): N = decl.asNode()[paramsPos]
func returnType*[N](decl: ProcDeclNode[N]): N = decl.asNode()[paramsPos][0]
func argumentList*[N](decl: ProcDeclNode[N]): seq[N] =
  for node in decl.asNode()[paramsPos][1 .. ^1]:
    result.add node

func body*[N](decl: ProcDeclNode[N]): N = decl.asNode()[bodyPos]
func pragmas*[N](decl: ProcDeclNode[N]): N = decl.asNode()[pragmasPos]


type
  ObjectAnnotKind* = enum
    ## Position of annotation (most likely pragma) attached.
    oakCaseOfBranch ## Annotation on case branch, not currently suppported
    oakObjectToplevel ## Toplevel annotaion for object
    oakObjectField ## Annotation for object field


template currLInfo*(): untyped =
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

func getStrVal*(p: PNode, doRaise: bool = true): string =
  ## Get string value from `PNode`
  case p.kind:
    of nkIdent:    p.ident.s
    of nkSym:      p.sym.name.s
    of nkStrKinds: p.strVal
    of nkOpenSymChoice: p[0].sym.name.s
    of nkAccQuoted: ($p)[1..^2]
    else:
      if doRaise:
        raiseArgumentError(
          "Cannot get string value from node of kind " & $p.kind)

      else:
        ""

func safeStrVal*(n: PNode): string = getStrVal(n, false)

func getIntVal*(n: PNode): BiggestInt = n.intVal
func getIntVal*(n: NimNode): BiggestInt = n.intVal()


proc getStrVal*(s: PSym): string = s.name.s

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
  TNodeKind(kind.int)

func toNNK*(kind: TNodeKind): NimNodeKind = NimNodeKind(kind.int)
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

func newNTree*[NNode: NimNode or PNode](
  kind: NimNodeKind, subnodes: varargs[NNode]): NNode =
  ## Create new tree with `subnodes` and `kind`
  # STYLE rename to `toNNode`
  when NNode is NimNode:
    newTree(kind, toSeq(subnodes))

  else:
    newTree(kind.toNK(), toSeq(subnodes))

func newReturn*[N](expr: N): N = newNTree[N](nnkReturnStmt, expr)
func newRaise*[N](expr: N): N = newNTree[N](nnkRaiseStmt, expr)
func newStmtListExpr*[N](args: varargs[N]): N =
  newNTree[N](nnkStmtListExpr, args)

func newNIdent*[NNode](str: string): NNode =
  ## Create new `nnkIdent` node of type `NNode`
  when NNode is NimNode:
    newIdentNode(str)

  else:
    newPIdent(str)

func newNIdent*[N](n: N): N = n


func newDiscardStmt*[N](expr: N): N =
  newNTree[N](nnkDiscardStmt, expr)

func newDiscardStmt*(): NimNode = newDiscardStmt(newEmptyNode())


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

template addPositionComment*[N](node: N, msg: string = ""): untyped =
  newNTree[N](
    nnkStmtList,
    newCommentStmtNNode[N](toStr(instantiationInfo()) & " " & msg),
    node
  )

template addPositionEcho*[N](node: N, msg: string = ""): untyped =
  newNTree[N](
    nnkStmtList,
    newNTree[N](
      nnkCall, newNIdent[N]("debugecho"),
      newNLit[N, string](toStr(instantiationInfo()) & " " & msg)),
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

proc newPLit*(e: enum): PNode =
  proc enumToStr(x: enum): string {.magic: "EnumToStr", noSideEffect.}
  return nnkDotExpr.newPTree(
    newPIdent($typeof(e)), newPIdent(enumToStr(e)))

proc newPLit*[T](s: set[T]): PNode =
  result = nnkCurly.newPTree()
  for value in s:
    result.add newPLit(value)

proc newLit*[T](s: set[T]): NimNode =
  result = newTree(nnkCurly)
  for value in s:
    result.add nnkDotExpr.newTree(
      ident($typeof(T)), ident(toString(value)))

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



proc newIdent*(str: string): NimNode = newIdentNode(str)

proc newDot*[N: NimNode | PNode](self: N, name: string): N =
  newNTree[N](nnkDotExpr, self, newNIdent[N](name))

proc newPar*[N](arg: N): N = newNTree[N](nnkPar, arg)

proc newSet*[N](elements: varargs[N]): N = newNTree[N](nnkCurly, elements)
proc newDot*[N](lhs, rhs: N): N = newNTree[N](nnkDotExpr, lhs, rhs)
proc newBracketExpr*[N](lhs: N, rhs: varargs[N]): N =
  result = newNTree[N](nnkBracketExpr, lhs)
  for arg in rhs:
    result.add arg


proc newExprColon*[N](lhs, rhs: N): N =
  newNTree[N](nnkExprColonExpr, lhs, rhs)

proc newExprEq*[N](lhs, rhs: N): N =
  newNTree[N](nnkExprEqExpr, lhs, rhs)


proc newCall*[N](arg1: N, name: string, args: varargs[N]): N =
  ## Create new `Call` node using `arg1` as a first argumen, `name` as a
  ## function name. This is a convenience function for constructing chained
  ## one-or-more argument calls using
  ## `obj.newCall("callName").newCall("anotherCall")`. NOTE that it does
  ## not create `DotExpr` node.
  result = newNTree[N](nnkCall, newNIdent[N](name))
  result.add arg1
  for arg in args:
    result.add arg

proc newWhile*[N](expr: N, body: varargs[N]): N =
  result = newNTree[N](
    nnkWhileStmt, expr, newNtree[N](nnkStmtList, body))

proc addArgument*[N](n: N, name: string, expr: N) =
  n.add newNTree[N](nnkExprEqExpr, newIdent(name), expr)

proc newAnd*[N](a, b: N): N =
  newNTree[N](nnkInfix, newNIdent[N]("and"), a, b)

proc newOr*[N](a, b: N): N =
  newNTree[N](nnkInfix, newNIdent[N]("or"), a, b)

proc newNot*[N](a: N): N =
  newNTree[N](nnkPrefix, newNIdent[N]("not"), a)


proc newBreak*(target: NimNode = newEmptyNode()): NimNode =
  newTree(nnkBreakStmt, target)

proc wrapStmtList*[N](nodes: varargs[N]): NimNode =
  newNTree[N](nnkStmtList, nodes)


proc newIf*[N](cond, body: N, orElse: N = nil): N =
  result = newNTree[N](nnkIfStmt, newNTree[N](nnkElifBranch, cond, body))
  if not isNil(orElse):
    result.add newNTree[N](nnkElse, orElse)

proc newIfStmt*[N](cond, body: N, orElse: N = nil): N
  {.deprecated: "Use `newIf`".} =
  newIf(cond, body, orElse)

proc newWhen*[N](cond, body: N, orElse: N = nil): N =
  result = newNTree[N](nnkWhenStmt, newNTree[N](nnkElifBranch, cond, body))
  if not isNil(orElse):
    result.add newNTree[N](nnkElse, orElse)

proc newIfPStmt*(): PNode = newPTree(nnkIfStmt)
proc newIfNStmt*(): NimNode = newTree(nnkIfStmt)

proc isEmptyNode*[N](node: N): bool =
  result = true
  if isNil(node):
    return true

  case node.kind.toNNK():
    of nnkEmpty:
      return true

    of nnkDiscardStmt:
      return node[0].kind.toNNK() == nnkEmpty

    of nnkStmtList:
      for subnode in node:
        if not isEmptyNode(subnode):
          return false

    else:
      return false

proc isEmptyNode*[N](nodes: seq[N]): bool =
  result = true
  for node in nodes:
    if not isEmptyNode(node):
      return false

proc fixEmptyStmt*[N](node: N): N =
  if isEmptyNode(node):
    newNTree[N](nnkDiscardStmt, newEmptyNNode[N]())

  else:
    node

proc newXCall*[N](
      head: N, args: seq[N] = @[], generics: seq[N] = @[]): N =
  ## Improved version of `newCall` that allows to uniformly treat
  ## construction of the dot expressions, infix, prefix and postfix
  ## operators, array expressions (`[]` and `{}=`)
  let str =
    if head.kind.toNNK() == nnkIdent:
      head.getStrVal()

    else:
      ""

  # let (callhead, hasGen) =
  #   if generics.len == 0:
  #     (head, false)

  #   else:
  #     (, true)

  if generics.len > 0:
    var callparams: seq[N]
    let head =
      if allIt(str, it in IdentChars):
        newBracketExpr(head, generics)

      else:
        newBracketExpr(newNTree[N](nnkAccQuoted, head), generics)

    result = newNTree[N](nnkCall, head)
    result.add args

  else:
    case str:
      of ".":
        result = newNTree[N](nnkDotExpr, args)

      of "[]":
        result = newNTree[N](nnkBracketExpr, args)

      of "{}":
        result = newNTree[N](nnkCurlyExpr, args)

      of "[]=", "{}=":
        let head = if str == "[]=": nnkBracketExpr else: nnkCurlyExpr

        if args.len == 2:
          result = newNTree[N](
            nnkAsgn,
            newNTree[N](head, args[0]), args[1])

        else:
          result = newNTree[N](
            nnkAsgn,
            newNTree[N](head, args[0], args[1]), args[2])

      elif allIt(str, it in IdentChars) and
           str notin [
             "and", "or", "not", "xor", "shl",
             "shr", "div", "mod", "in", "notin",
             "is", "isnot", "of", "as", "from"
           ]:
        result = newNTree[N](nnkCall, newNIdent[N](head) & args)

      else:
        case args.len:
          of 0:
            raise newArgumentError(
              &"Cannot create new call for '{head}' with no arguments")

          of 1:
            result = newNTree[N](
              nnkPrefix, head, newNTree[N](
                # HACK due to bugs with rendering of `not x` add paren here
                nnkPar, args[0]))

          of 2:
            result = newNTree[N](nnkInfix, head, args[0], args[1])

          else:
            result = newNTree[N](
              nnkCall, newNTree[N](nnkAccQuoted, head) & args)


proc newXCall*[N: NimNode or PNode](
    head: string, arg1: N, other: varargs[N]): N =

  newXCall(newNident[N](head), arg1 & toSeq(other))

proc newNCall*(head: string, args: varargs[NimNode]): NimNode =
  newXCall[NimNode](newNIdent[NimNode](head), toSeq(args))

proc newPCall*(head: string, args: varargs[PNode]): PNode =
  newXCall[PNode](newPIdent(head), toSeq(args))

proc callTypeof*[N](head: N): N = newXCall("typeof", head)


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

proc lispRepr*(
    typ: PType, colored: bool = true, symkind: bool = true): string =
  result = "ty:" & toMagenta(($typ.kind)[2..^1], colored)
  if not isNil(typ.sym) and symkind:
    result &= " sk:" & toCyan(($typ.sym.kind)[2..^1], colored)

  if not isNil(typ.n):
    let t = $typ.n
    if '\n' notin t:
      result &= " " & toRed(t, colored)

func treeRepr*(
    pnode: PNode, colored: bool = true,
    pathIndexed: bool = false,
    positionIndexed: bool = true,
    maxdepth: int = 120,
    maxlen: int = 30
  ): string =

  # raise newImplementError()

  proc aux(n: PNode, level: int, idx: seq[int]): string =
    let pref =
      if pathIndexed:
        idx.join("", ("[", "]")) & "    "

      elif positionIndexed:
        if level > 0:
          "  ".repeat(level - 1) & "\e[38;5;240m#" & $idx[^1] & "\e[0m" &
            "\e[38;5;237m/" & alignLeft($level, 2) & "\e[0m" & " "

        else:
          "    "

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
        result.add pref & "  # " & toCyan(line) & "\n"

      result.add pref

    else:
      result.add " "

    # if n.kind == nkSym and notNil(n.sym.ast):
    #   debugecho n.sym.ast


    case n.kind:
      of nkStrKinds:
        result &= "\"" & toYellow(n.getStrVal(), colored) & "\""

      of nkIntKinds:
        result &= toBlue($n.intVal, colored)

      of nkFloatKinds:
        result &= toMagenta($n.floatVal, colored)

      of nkIdent:
        result &= toGreen(n.getStrVal(), colored)

      of nkSym:
        result &= [
          toGreen(n.getStrVal(), colored),
          " sk:", toBlue(($n.sym.kind)[2 ..^ 1], colored),
          " ", tern(
            isNil(n.sym.typ),
            "<no-type>",
            n.sym.typ.lispRepr(colored, symkind = false))]

        if n.sym.flags.len > 0:
          result &= " flags:" & to8Bit($n.sym.flags, 2, 0, 3)

        if n.sym.magic != mNone:
          result &= " magic:" & to8Bit($n.sym.magic, 2, 0, 5)



      of nkCommentStmt:
        discard

      else:
        if not isNil(n.typ):
          result &= n.typ.lispRepr(colored)

        if n.len > 0:
          result &= "\n"

        for newIdx, subn in n:
          result &= aux(subn, level + 1, idx & newIdx)
          if level + 1 > maxDepth:
            break

          if newIdx > maxLen:
            break

          if newIdx < n.len - 1:
            result &= "\n"

  return aux(pnode, 0, @[])


proc treeRepr1*(
    pnode: PNode,
    colored: bool = true,
    pathIndexed: bool = false,
    positionIndexed: bool = true,
    maxdepth: int = 120,
  ): string =

  ## - TODO :: optionally show node positions
  ## - TODO :: make output identical to `treeRepr1` for `NimNode`

  treeRepr(
    pnode, colored,
    maxdepth = maxdepth,
    pathIndexed = pathIndexed,
    positionIndexed = positionIndexed
  )

type
  EnumFieldDef*[N] = object
    decl*: N
    name*: string
    strVal*: string
    intVal*: BiggestInt

  EnumValueGroup*[N] = object
    wrapConvert*: Option[string]
    enumFields*: seq[EnumFieldDef[N]]
    enumConsts*: Table[string, seq[EnumFieldDef[N]]]

proc splitEnumImpl*[N](impl: N): seq[EnumFieldDef[N]] =
  var fNum = BiggestInt(0)
  for field in impl:
    var fStr: string
    var fName: string
    case field.kind
      of nnkEmpty: continue # skip first node of `enumTy`
      of nnkSym:
        fStr = field.strVal()
        fName = field.strVal()

      of nnkIdent:
        fStr = field.strVal()
        fName = field.strVal()

      of nnkEnumFieldDef:
        fName = field[0].strVal()
        case field[1].kind
          of nnkStrLit:
            fStr = field[1].strVal

          of nnkTupleConstr:
            fStr = field[1][1].strVal
            fNum = field[1][0].intVal

          of nnkIntLit:
            fStr = field[0].strVal
            fNum = field[1].intVal

          else:
            discard

      else:
        discard

    result.add EnumFieldDef[N](
      decl: field, strVal: fStr, name: fName, intVal: fNum)

    inc fNum




proc typeLispRepr*(node: NimNode, colored: bool = true): string =
  case node.kind:
    of nnkSym:
      case node.symKind:
        of nskType:
          result = toStrLit(node).strVal().toRed(colored)

        of nskField:
          let inst = node.getType()
          case inst.kind:
            of nnkEnumTy:
              result = toBlue("enum/", colored)

            else:
              discard

          result &= "typ: " & node.getTypeInst().typeLispRepr(colored)

        of nskEnumField:
          let impl = node.getType().getTypeInst().getImpl()[2]

          for field in impl.splitEnumImpl():
            if field.name == node.strVal():
              if field.name == field.strVal:
                return $field.intVal

              else:
                return &["(", $field.intVal, ", ", field.strVal, ")"]

        of nskTemplate:
          let impl = node.getImpl()
          return impl.toStrLit().strVal().toYellow(colored)

        of nskConst:
          return node.getImpl().toStrLit().strVal().toBlue(colored)

        of nskProc:
          return node.getTypeImpl().toStrLit().strVal().toBlue(colored)

        else:
          return toGreen($node.symKind, colored)

    of nnkEnumTy:
      result = "enum".toRed(colored)

    else:
      result = node.lispRepr().toGreen(colored)
      # raiseImplementKindError(node, node.treeRepr())

proc treeRepr1*(
    pnode: NimNode,
    colored: bool = true,
    pathIndexed: bool = false,
    positionIndexed: bool = true,
    maxdepth: int = 120,
  ): string =
  ## Advanced `treeRepr` version.
  ##
  ## - show symbol kinds and types
  ## - use colored representation for literals and comments
  ## - support max depth limit using @arg{maxdepth}
  ## - optionally show full index path for each entry
  ## - show node position index
  ## - differentiate between `NilLit` and *actually* `nil` nodes

  proc aux(n: NimNode, level: int, idx: seq[int]): string =
    let pref =
      if pathIndexed:
        idx.join("", ("[", "]")) & "    "

      elif positionIndexed:
        if level > 0:
          "  ".repeat(level - 1) & to8Bit(
            alignLeft("#" & $idx[^1], 3), 10) &
            to8Bit("/" & alignLeft($level, 2), 20) & " "

        else:
          "    "

      else:
        "  ".repeat(level)

    if isNil(n):
      return pref & toRed("<nil>", colored)

    if level > maxdepth:
      return pref & " ..."

    result &= pref & ($n.kind)[3 ..^ 1]

    case n.kind:
      of nnkStrKinds:
        result &= " \"" & toYellow(n.getStrVal(), colored) & "\""

      of nnkIntKinds:
        result &= " " & toCyan($n.intVal, colored)

      of nnkFloatKinds:
        result &= " " & toMagenta($n.floatVal, colored)

      of nnkIdent:
        result &= " " & toGreen(n.strVal(), colored)

      of nnkSym:
        result &= [
          " ", toBlue(($n.symKind())[3..^1], colored),
          " ", toGreen(n.strVal(), colored),
          " <", n.typeLispRepr(), ">"
        ]

      of nnkCommentStmt:
        let lines = split(n.strVal(), '\n')
        if lines.len > 1:
          result &= "\n"
          for idx, line in pairs(lines):
            if idx != 0:
              result &= "\n"

            result &= pref & toYellow(line)

        else:
          result &= toYellow(n.strVal())

      else:
        if n.len > 0:
          result &= "\n"

        for newIdx, subn in n:
          result &= aux(subn, level + 1, idx & newIdx)
          if level + 1 > maxDepth:
            break

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

  elif val is int | float | string | bool | enum:
    result = newLit(val)

  elif val is set:
    result = hast_common.newLit(val)

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
      for name, fld in fieldPairs(when val is ref: val[] else: val):
        when (fld is Option) and not (fld is Option[void]):
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
func valuesInRange*[N](
    lowVal, highVal: N, group: EnumValueGroup[N]): seq[EnumFieldDef[N]] =

  var values: seq[EnumFieldDef[N]]
  var inRange: bool = false

  for value in group.enumFields:
    case lowVal.kind.toNNK():
      of nnkIdentKinds:
        if value.name == lowVal.getStrVal():
          inRange = true

      of nnkIntKinds:
        if lowVal.getIntVal() == value.intVal:
          inRange = true

      else:
        raiseImplementKindError(lowVal)



    if inRange:
      values.add value

    case highVal.kind.toNNK():
      of nnkIdentKinds:
        if value.name == highVal.getStrVal():
          inRange = false
          break

      of nnkIntKinds:
        if highVal.getIntVal() == value.intVal:
          inRange = false
          break

      else:
        raiseImplementKindError(highVal)

  return values


func flattenSet*[N](node: N, group: Option[EnumValueGroup[N]]): seq[N] =
  case node.kind.toNNK():
    of nnkIdent:
      if group.isSome() and node.getStrVal() in group.get().enumConsts:
        for value in group.get().enumConsts[node.getStrVal()]:
          result &= newNIdent[N](value.strVal)

      else:
        result &= node


    of nnkIntLit, nnkCharLit, nnkDotExpr:
      return @[ node ]

    of nnkCurly:
      mixin items
      for subnode in items(node):
        result &= flattenSet(subnode, group)

    of nnkInfix:
      let lowVal = node[1]
      let highVal = node[2]
      assert node[0].getStrVal() == ".."
      if group.isSome() and
         lowVal.kind.toNNK() in nnkIdentKinds and
         highVal.kind.toNNK() in nnkIdentKinds:

        for val in valuesInRange(lowVal, highVal, group.get()):
          result.add val.decl


      else:
        result = @[ node ]

    else:
      {.cast(noSideEffect).}:

        when node is PNode:
          let str = hast_common.`$`(node)

        else:
          let str = `$`(node)

        raiseArgumentError(
          "Cannot normalize set: " & str & " - unknown kind")

  if group.isSome() and group.get().wrapConvert.isSome():
    let convert = group.get().wrapConvert.get()
    var res: seq[N]
    for item in result:
      res.add newNTree(nnkCall, newNIdent[N](convert), item)

    return res




func normalizeSet*[N](nodes: seq[N], group: EnumValueGroup[N]): N =
  var vals: seq[N]
  for n in nodes:
    vals.add flattenSet(n, group)

  return newNTree[N](nnkCurly, vals)

func normalizeSet*[N](
    node: N, group: EnumValueGroup[N], forcebrace: bool = false): N =
  ## Convert any possible set representation (e.g. `{1}`, `{1, 2}`,
  ## `{2 .. 6}` as well as `2, 3` (in case branches). Return
  ## `nnkCurly` node with all values listed one-by-one (if identifiers
  ## were used) or in ranges (if original node contained `..`)
  let vals = flattenSet(node, group)
  if vals.len == 1 and not forcebrace:
    return vals[0]

  else:
    return newNTree[N](nnkCurly, vals)

func joinSets*[NNode](nodes: seq[NNode], group: EnumValueGroup[NNode]): NNode =
  ## Concatenate multiple sets in one element. Result will be wrapped
  ## in `Curly` node.
  let vals = nodes.mapIt(it.flattenSet(group)).concat()
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

    of nnkIdentDefs:
      result = parseIdentName(node[0])

    else:
      result.name = node



proc addBranch*[N](main: var N, expr: N | seq[N], body: varargs[N]) =

  case main.kind.toNNK():
    of nnkCaseStmt, nnkIfStmt, nnkWhenStmt, nnkTryStmt:
      if body.len == 0:
        case main.kind.toNNK():
          of nnkTryStmt:
            if isEmptyNode(expr):
              main.add newNTree[N](nnkExceptBranch, expr)

            else:
              main.add newNTree[N](nnkFinally, expr)

          else:
            main.add newNTree[N](nnkElse, expr)

      else:
        when expr isnot seq:
          let expr = @[expr]

        let kind =
          case main.kind.toNNK():
            of nnkCaseStmt: nnkOfBranch
            of nnkTryStmt: nnkExceptBranch
            else: nnkElifBranch

        main.add newNTree[N](
          kind, expr & newNTree[N](
            nnkStmtList, newEmptyNNode[N]() & toSeq(body)))

    else:
      raise newImplementKindError(main)

proc newNLit*[N, T](item: T): N =
  when N is NimNode:
    when item is set:
      hast_common.newLit(item)

    else:
      newLit(item)

  else:
    newPLit(item)


proc newBracketExpr*[N](lhs: N, rhs: SomeInteger): N =
  newNTree[N](nnkBracketExpr, lhs, newNLit[N, typeof(rhs)](rhs))

proc newIn*[N; E: enum](a: N, b: set[E]): N =
  newNTree[N](nnkInfix, newNIdent[N]("in"), a, newNLit[N, set[E]](b))



proc addBranch*[N](main: var N, expr: enum, body: varargs[N]) =
  addBranch(main, newNLit[N, typeof(expr)](expr), body)

proc addBranch*[N](main: var N, expr: string, body: varargs[N]) =
  addBranch(main, newNLit[N, string]($expr), body)

proc addBranch*[N](main: var N, expr: seq[string], body: varargs[N]) =
  addBranch(main, mapIt(expr, newNLit[N, string](it)), body)

proc addBranch*[N, E](main: var N, expr: set[E], body: varargs[N]) =
  addBranch(main, newNLit[N, set[E]](expr), body)

proc newAsgn*[N](lhs: string, rhs: N): N =
  newNTree[N](nnkAsgn, newNIdent[N](lhs), rhs)

proc newAsgn*[N](lhs, rhs: N): N =
  newNTree[N](nnkAsgn, lhs, rhs)

proc toPNode*(node: PNode): PNode = node
proc toPNode*(val: string): PNode = newPLit(val)
proc newCaseStmt*[N](expr: N): N {.deprecated: "Use newCase".} =
  newNTree[N](nnkCaseStmt, expr)

proc newCase*[N](expr: N): N = newNTree[N](nnkCaseStmt, expr)
proc newTry*[N](expr: N): N = newNTree[N](nnkTryStmt, expr)

proc newFor*[N](forVars: openarray[N], expr: N, body: varargs[N]): N =
  newNTree[N](nnkForStmt, toSeq(forVars) & expr & wrapStmtList(body))

proc newFor*[N](forvar, expr: N, body: varargs[N]): N =
  newNTree[N](nnkForStmt, forvar, expr, wrapStmtList(body))

proc withPrivate*[N](
    target: N, fieldName: string,
    fieldIdent, expr: N,
    isRef: bool = false
  ): N =

  let
    name = newNIdent[N]("fieldName")

  newFor(
    [name, fieldIdent], newXCall("fieldPairs",
      tern(isRef, newXCall("[]", target), target)),
    newWhen(
      newXCall("==", name, newNLit[N, string](fieldName)),
      expr))

proc compactCase*[N](caseNode: N): N =
  if caseNode.kind.toNNK() != nnkCaseStmt:
    return caseNode

  result = newCase(caseNode[0])
  var
    emptyCond: seq[N]
    elseBranch: N

  # echo caseNode.treeRepr()
  for branch in caseNode[1 ..^ 1]:
    if branch.kind.toNNK() == nnkElse:
      if not branch.isEmptyNode():
        elseBranch = branch

    else:
      if branch[1].isEmptyNode():
        emptyCond.add branch[0]

      else:
        result.add branch

  if result.len == 1:
    # No fillers for case statment branches
    return newStmtList()

  else:
    if isNil(elseBranch):
      # Empty else branch, we can reuse it
      result.addBranch(newDiscardStmt[N]())

    else:
      if emptyCond.len > 0:
        emptyCond.add newDiscardStmt[N]()
        result.add newNTree[N](nnkOfBranch, emptyCond)

      result.add elseBranch

  echo result.repr




proc newPStmtList*(args: varargs[PNode]): PNode =
  newNTree[PNode](nnkStmtList, args)

proc newBlock*[N](args: varargs[N]): N =
  newNTree[N](nnkBlockStmt, newEmptyNNode[N](), newNTree[N](nnkStmtList, args))

proc newPBreak*(): PNode =
  newPTree(nnkBreakStmt, newEmptyPNode())

proc newPDotExpr*(lhs, rhs: PNode | string): PNode =
  newPTree(nnkDotExpr, toPNode(lhs), toPNode(rhs))

proc newPDotFieldExpr*(lhs, rhs: PNode | string): PNode =
  result = newPTree(
    nnkDotExpr, (when lhs is PNode: lhs else: newPident(lhs)))

  when rhs is PNode:
    result.add rhs

  else:
    result.add newPIdent(rhs)

proc newPDotCall*(main: PNode, callName: string, args: varargs[PNode]):
  PNode =
  newPTree(nnkDotExpr, toPNode(main), newPCall(callName, args))


proc newPDotCall*(main: string, callName: string, args: varargs[PNode]):
  PNode =
  newPTree(nnkDotExpr, newPIdent(main), newPCall(callName, args))

proc isObject*(node: NimNode): bool =
  case node.kind:
    of nnkObjectTy:
      true

    of nnkEnumTy:
      false

    of nnkRefTy, nnkPtrTy:
      node[0].kind in {nnkObjectTy}

    of nnkTypeDef:
      isObject(node[2])

    else:
      raiseImplementKindError(node)



proc getDocComment*[N](node: N): string =
  when node is NimNode:
    if node.kind notin {nnkCommentStmt} + nnkProcDeclKinds:
      return ""

  case node.kind.toNNK():
    of nnkCommentStmt:
      when node is NimNode:
        return node.getStrVal()

      else:
        return node.comment

    of nnkTypeDef:
      return getDocComment(node[2])

    of nnkObjectTy, nnkIdentDefs, nnkEnumTy:
      when node is PNode:
        return node.comment

    of nnkWrapTy:
      return getDocComment(node[0])

    of nnkProcDeclKinds:
      # echo node.treeRepr1()
      when node is PNode:
        result.add node.comment
        result.add "\n"

      for subnode in node[6]:
        result.add subnode.getDocComment()

    of nnkAsgn, nnkStmtListExpr, nnkStmtList:
      for subnode in node:
        result.add getDocComment(subnode)

    else:
      discard

proc getSomeBase*[N](node: N): Option[N] =
  case node.kind.toNNK():
    of nnkWrapTy:
      result = getSomeBase(node[0])

    of nnkObjectTy:
      result = getSomeBase(node[1])

    of nnkOfInherit:
      result = some node[0]

    of nnkEmpty:
      discard

    else:
      discard

func eqIdent*(node: PNode, str: string): bool =
  node.getStrVal(false)[0] == str[0] and
  node.getStrVal(false).normalize() == str.normalize()
