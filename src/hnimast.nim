## Statically typed nim ast representation with large number of helper
## functions - skipping nil nodes, normalizing set literals,
## generating and working with pragma annotations, parsing object
## defintions etc.

import hmisc/helpers
import hmisc/types/colorstring
import sequtils, colors, macros, tables, strutils,
       terminal, options, parseutils, sets, strformat, sugar

import compiler/[ast, idents, lineinfos, renderer]

import hnimast/pnode_parse
export pnode_parse, options

# type NNode = NimNode | PNode

func `$!`*(n: NimNode): string =
  ## NimNode stringification that does not blow up in your face on
  ## 'invalid node kind'
  n.toStrLit().strVal()

proc `$`*(n: PNode): string =
  ## Convert `PNode` back to code.
  renderer.`$`(n)

func getStrVal*(n: NimNode): string =
  ## Get string value from `NimNode` that can have it - e.g. strings,
  ## identifiers etc.
  n.strVal()

func getStrVal*(p: PNode): string =
  ## Get string value from `PNode`
  case p.kind:
    of nkIdent:
      p.ident.s
    else:
      p.strVal

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

func expectKind*(expr: PNode, kind: NimNodeKind): void =
  ## Raise assertion error of `expr` kind is not equal to `kind`
  if expr.kind != kind.toNK():
    raiseAssert(
      &"Unexpected node kind: got {expr.kind}, but expected {kind}")


func newNIdent*[NNode](str: string): NNode =
  ## Create new `nnkIdent` node of type `NNode`
  when NNode is NimNode:
    newIdentNode(str)
  else:
    newPIdent(str)

func newNTree*[NNode](
  kind: NimNodeKind, subnodes: varargs[NNode]): NNode =
  ## Create new tree with `subnodes` and `kind`
  when NNode is NimNode:
    newTree(kind, subnodes)
  else:
    newTree(kind.toNK(), subnodes)

const
  NkStrNodes* = { nkStrLit .. nkTripleStrLit }
  NkIntNodes* = { nkCharLit .. nkUInt64Lit }
  NkFloatNodes* = { nkFloatLit .. nkFloat128Lit }

  NNkStrNodes* = { nnkStrLit .. nnkTripleStrLit }
  NNkIntNodes* = { nnkCharLit .. nnkUInt64Lit }
  NNkFloatNodes* = { nnkFloatLit .. nnkFloat128Lit }

func newPTree*(kind: NimNodeKind, subnodes: varargs[PNode]): PNode =
  ## Create new `PNode` tree
  if kind in NNkStrNodes + NNkIntNodes + NNkFloatNodes:
    if subnodes.len > 0:
      raiseAssert(&"Cannot create node of kind {kind} with subnodes")
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

func newPLit*(c: char): PNode =
  newIntTYpeNode(BiggestInt(c), PType(kind: tyChar))

func newPLit*(i: string): PNode =
  ## Create new string literal `PNode`
  newStrNode(nkStrLit, i)

func newRStrLit*(st: string): PNode =
  result = nnkRStrLit.newPTree()
  result.strVal = st


func newPIdentColonString*(key, value: string): PNode =
  nnkExprColonExpr.newPTree(newPIdent(key), newPLit(value))


func newExprColonExpr*(key, value: PNode): PNode =
  nnkExprColonExpr.newPTree(key, value)

template newNNLit[NNode](val: untyped): untyped =
  when NNode is PNode:
    newPLit(val)
  else:
    newLit(val)

type
  ObjectAnnotKind* = enum
    ## Position of annotation (most likely pragma) attached.
    oakCaseOfBranch ## Annotation on case branch, not currently suppported
    oakObjectToplevel ## Toplevel annotaion for object
    oakObjectField ## Annotation for object field



#*************************************************************************#
#****************************  Ast reparsing  ****************************#
#*************************************************************************#

#=======================  Enum set normalization  ========================#

proc normalizeSetImpl[NNode](node: NNode): seq[NNode] =
   case node.kind.toNNK():
    of nnkIdent, nnkIntLit, nnkCharLit:
      return @[ node ]
    of nnkCurly:
      mixin items
      for subnode in items(node):
        result &= normalizeSetImpl(subnode)
    of nnkInfix:
      assert node[0].strVal == ".."
      result = @[ node ]
    else:
      when NNode is PNode:
        raiseAssert("Cannot normalize set: ")
      else:
        raiseAssert("Cannot normalize set: " & $node.lispRepr())


proc normalizeSet*[NNode](node: NNode, forcebrace: bool = false): NNode =
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
  # debugecho $!result

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

#==================  Helper procs for ast construction  ==================#

func toBracket*(elems: seq[NimNode]): NimNode =
  ## Create `nnkBracket` with elements
  # TODO use `NNode`
  nnkBracket.newTree(elems)

func toBracketSeq*(elems: seq[NimNode]): NimNode =
  ## Create `nnkBracket` with `@` prefix - sequence literal
  ## `@[<elements>]`
  # TODO use `NNode`
  nnkPrefix.newTree(ident "@", nnkBracket.newTree(elems))

#*************************************************************************#
#*****************  Pragma - pragma annotation wrapper  ******************#
#*************************************************************************#
#===========================  Type definition  ===========================#
type
  Pragma*[NNode] = object
    ## Body of pragma annotation;
    kind*: ObjectAnnotKind ## Position in object - no used when
                           ## generatic functions etc.
    elements*: seq[NNode] ## List of pragma elements. For annotation
                         ## like `{.hello, world.}` this will contain
                         ## `@[hello, world]`

  NPragma* = Pragma[NimNode] ## Pragma with nim node
  PPragma* = Pragma[PNode] ## Pragma with pnode

#===============================  Getters  ===============================#
func getElem*(pragma: NPragma, name: string): Option[NimNode] =
  ## Get element named `name` if it is present.
  ## `getElem({.call.}, "call") -> call`
  ## `getElem({.call(arg).}, "call") -> call(arg)`
  for elem in pragma.elements:
    case elem.kind:
      of nnkIdent:
        if elem.eqIdent(name):
          return some(elem)
      of nnkCall:
        if elem[0].eqIdent(name):
          return some(elem)
      else:
        raiseAssert("#[ IMPLEMENT ]#")

func getElem*(optPragma: Option[NPragma], name: string): Option[NimNode] =
  ## Get element from optional annotation
  if optPragma.isSome():
    return optPragma.get().getElem(name)

func len*[NNode](pragma: Pragma[NNode]): int =
  pragma.elements.len

#============================  constructors  =============================#
func newNNPragma*[NNode](): Pragma[NNode] = discard

func newNPragma*(names: varargs[string]): NPragma =
  ## Create pragma using each string as separate name.
  ## `{.<<name1>, <name2>, ...>.}`
  NPragma(elements: names.mapIt(ident it))

func newPPragma*(names: varargs[string]): PPragma =
  ## Create pragma using each string as separate name.
  ## `{.<<name1>, <name2>, ...>.}`
  PPragma(elements: names.mapIt(newPIdent(it)))


func newNPragma*(names: varargs[NimNode]): NPragma =
  ## Create pragma using each node in `name` as separate name
  NPragma(elements: names.mapIt(it))


func newPPragma*(names: varargs[PNode]): PPragma =
  ## Create pragma using each node in `name` as separate name
  PPragma(elements: names.mapIt(it))

#========================  Other implementation  =========================#

func toNNode*[NNode](pragma: Pragma[NNode]): NNode =
  ## Convert pragma to `NNode`. If pragma has no elements empty node
  ## (`nnkEmptyNode`) will be returned.
  if pragma.elements.len == 0:
    newEmptyNNode[NNode]()
  else:
    newTree[NNode](nnkPragma, pragma.elements)


func toNimNode*(pragma: NPragma): NimNode =
  ## Convert pragma to nim node. If pragma contains no elements
  ## `EmptyNode` is generated.
  toNNode[NimNode](pragma)



#*************************************************************************#
#**********************  NType - nim type wrapper  ***********************#
#*************************************************************************#
#===========================  Type definition  ===========================#

type
  NTypeKind* = enum
    ## Type kind
    ntkIdent ## Generic identifier, possibly with parameters: `G[A, C]`
    ntkProc ## Procedure type: `proc(a: int, b: float) {.cdecl.}`
    ntkRange ## Range type: `range[1..10]`
    ntkGenericSpec ## Constrained generic: `A: B | C | D`

  NType*[NNode] = object
    ## Representation of generic nim type;
    case kind*: NTypeKind
      of ntkIdent, ntkGenericSpec:
        head*: string ## Type name `head[...]` or `head: .. | ..`
        genParams*: seq[NType[NNode]] ## Parameters or alternatives:
        ## `[@genParams]` or `..: alt1 | alt2 ..`
      of ntkProc:
        rType*: Option[SingleIt[NType[NNode]]] ## Optional return type
        arguments*: seq[NIdentDefs[NNode]] ## Sequence of argument identifiers
        pragma*: Pragma[NNode] ## Pragma annotation for proc
      of ntkRange:
        discard ## TODO

  # PType* = NType[PNode]

  NVarDeclKind* = enum
    ## Kind of variable declaration
    # TODO static parameters?
    nvdLet
    nvdVar
    nvdConst

  NIdentDefs*[NNode] = object
    ## Identifier declaration
    varname*: string ## Variable name
    kind*: NVarDeclKind
    vtype*: NType[NNode] ## Variable type
    value*: Option[NNode] ## Optional initialization value

  PIdentDefs* = NIdentDefs[PNode]

#==============================  Accessors  ==============================#
func arg*[NNode](t: NType[NNode], idx: int): NIdentDefs[NNode] =
  assert t.kind == ntkProc
  t.arguments[idx]


#=============================  Predicates  ==============================#
func `==`*(l, r: NType): bool =
  l.kind == r.kind and (
    case l.kind:
      of ntkIdent, ntkGenericSpec:
        (l.head == r.head) and (l.genParams == r.genParams)
      of ntkProc:
        (l.rType == r.rType) and (l.arguments == r.arguments)
      of ntkRange:
        true
  )

func `rType=`*[NNode](t: var NType[NNode], val: NType[NNode]): void =
    t.rtype = some(newIt(val))

func setRType*[NNode](t: var NType[NNode], val: NType[NNode]): void =
  t.rtype = some(newIt(val))

#============================  Constructors  =============================#
func toNIdentDefs*[NNode](
  args: openarray[tuple[
    name: string,
    atype: NType[NNode]]]): seq[NIdentDefs[NNode]] =
  ## Convert array of name-type pairs into sequence of `NIdentDefs`.
  ## Each identifier will be immutable (e.g. no `var` annotation).
  for (name, atype) in args:
    result.add NIdentDefs[NNode](varname: name, vtype: atype)

func toNIdentDefs*[NNode](
  args: openarray[tuple[
    name: string,
    atype: NType[NNode],
    nvd: NVarDeclKind
     ]]): seq[NIdentDefs[NNode]] =
  ## Convert array of name-type pairs into sequence of `NIdentDefs`.
  ## Each identifier must supply mutability parameter (e.g `nvdLet` or
  ## `vndVar`)
  for (name, atype, nvd) in args:
    result.add NIdentDefs[NNode](varname: name, vtype: atype, kind: nvd)



func toNFormalParam*[NNode](nident: NIdentDefs[NNode]): NNode

func toNNode*[NNode](ntype: NType[NNode]): NNode =
  ## Convert to NNode
  case ntype.kind:
    of ntkProc:
      result = newNTree[NNode](nnkProcTy)

      let renamed: seq[NIdentDefs[NNode]] = ntype.arguments.mapPairs:
        rhs.withIt do:
          it.varname = "a" & $idx

      result.add newNTree[NNode](
        nnkFormalParams,
        @[
          if ntype.rtype.isSome():
            ntype.rtype.get().getIt().toNNode()
          else:
            newEmptyNNode[NNode]()
        ] & renamed.mapIt(it.toNFormalParam()))

      result.add toNNode(ntype.pragma)


    else:
      if ntype.genParams.len == 0:
        return newNIdent[NNode](ntype.head)
      else:
        result = newNTree[NNode](nnkBracketExpr, newNIdent[NNode](ntype.head))
        for param in ntype.genParams:
          result.add toNNode[NNode](param)

func toNimNode*(ntype: NType): NimNode =
  ## Convert `NType` to nim node
  toNNode[NimNode](ntype)

func toPNode*(ntype: NType): PNode =
  ## Convert `NType` to `PNode`
  toNNode[PNode](ntype)



func toNFormalParam*[NNode](nident: NIdentDefs[NNode]): NNode =
  ## Convert to `nnkIdentDefs`
  let typespec =
    case nident.kind:
      of nvdVar: newNTree[NNode](
        nnkVarTy, toNNode[NNode](nident.vtype))

      of nvdLet: toNNode[NNode](nident.vtype)

      of nvdConst: newNTree[NNode](
        nnkConstTy, toNNode[NNode](nident.vtype))

  newNTree[NNode](
    nnkIdentDefs,
    newNIdent[NNode](nident.varname),
    typespec,
    newEmptyNNode[NNode]()
  )

func toFormalParam*(nident: NIdentDefs[NimNode]): NimNode =
  ## Convert to `nnkIdentDefs`
  toNFormalParam[NimNode](nident)


func newNType*(name: string, gparams: seq[string] = @[]): NType[NimNode] =
  ## Make `NType` with `name` as string and `gparams` as generic
  ## parameters
  NType[NimNode](
    kind: ntkIdent, head: name, genParams: gparams.mapIt(newNType(it, @[])))

func newPType*(name: string, gparams: seq[string] = @[]): NType[PNode] =
  ## Make `NType` with `name` as string and `gparams` as generic
  ## parameters
  NType[PNode](
    kind: ntkIdent, head: name, genParams: gparams.mapIt(newPType(it, @[])))

func newNNType*[NNode](
  name: string, gparams: seq[string] = @[]): NType[NNode] =
  when NNode is NimNode:
    newNType(name, gparams)
  else:
    newPType(name, gparams)

func newNType*[NNode](
  name: string, gparams: openarray[NType[NNode]]): NType[NNode] =
  ## Make `NType`
  NType[NNode](kind: ntkIdent, head: name, genParams: toSeq(gparams))

func newProcNType*[NNode](
  args: seq[NType[NNode]],
  rtype: NType[NNode], pragma: Pragma[NNode]): NType[NNode] =

  NType[NNode](
    kind: ntkProc,
    arguments: toNIdentDefs[NNode](args.mapIt(("", it))),
    pragma: pragma,
    rType: some(newIt(rtype)))


func newProcNType*[NNode](args: seq[NType[NNode]]): NType[NNode] =
  ## CRreate procedure type with arguments types `args`, no return type and
  ## no pragma annotations.
  NType[NNode](
    kind: ntkProc,
    arguments: toNIdentDefs[NNode](args.mapIt(("", it))),
    rtype: none(SingleIt[NType[NNode]]),
    pragma: newNNPragma[NNode]()
  )

func newNTypeNNode*[NNode](impl: NNode): NType[NNode] =
  ## Convert type described in `NimNode` into `NType`
  case impl.kind.toNNK():
    of nnkBracketExpr:
      let head = impl[0].strVal
      when NNode is PNode:
        newNType(head, impl.sons[1..^1].mapIt(newNTypeNNode(it)))
      else:
        newNType(head, impl[1..^1].mapIt(newNTypeNNode(it)))
    of nnkSym:
      newNNType[NNode](impl.strVal)
    of nnkIdent:
      when NNode is PNode:
        newPType(impl.ident.s)
      else:
        newNType(impl.strVal)
    else:
      # debugecho impl.treeRepr
      raiseAssert("#[ IMPLEMENT ]#")

template `[]`*(node: PNode, slice: HSLice[int, BackwardsIndex]): untyped =
  ## Get range of subnodes from `PNode`
  `[]`(node.sons, slice)

func newNType*(impl: NimNode): NType[NimNode] =
  ## Convert type described in `NimNode` into `NType`
  newNTypeNNode(impl)

func newNType*(impl: PNode): NType[PNode] =
  ## Convert type described in `NimNode` into `NType`
  newNTypeNNode(impl)

func newVarDecl*(name: string, vtype: NType,
                kind: NVarDeclKind = nvdLet): NIdentDefs[NimNode] =
  ## Declare varaible `name` of type `vtype`
  # TODO initalization value, pragma annotations and `isGensym`
  # parameter
  NIdentDefs[NimNode](varname: name, kind: kind, vtype: vtype)

func newVarStmt*(varname: string, vtype: NType, val: NimNode): NimNode =
  nnkVarSection.newTree(
    nnkIdentDefs.newTree(
      ident varname, vtype.toNimNode(), val))


func newVarDeclNode*(name: string, vtype: NType,
                    kind: NVarDeclKind = nvdLet): NimNode =
  ## Create variable declaration `name` of type `vtype`
  newVarDecl(name, vtype, kind).toFormalParam()


func newNTypeNode*(name: string, gparams: seq[string]): NimNode =
  ## Create `NimNode` for type `name[@gparams]`
  newNType(name, gparams).toNimNode()

func newNTypeNode*[NNode](
  name: string, gparams: varargs[NType[NNode]]): NNode =
  ## Create `NimNode` for type `name[@gparams]`
  newNType(name, gparams).toNNode()


func newCallNode*(
  dotHead: NimNode, name: string,
  args: seq[NimNode], genParams: seq[NType[NimNode]] = @[]): NimNode =
  ## Create node `dotHead.name[@genParams](genParams)`
  let dotexpr = nnkDotExpr.newTree(dotHead, ident(name))
  if genParams.len > 0:
    result = nnkCall.newTree()
    result.add nnkBracketExpr.newTree(
      @[ dotexpr ] & genParams.mapIt(it.toNimNode))
  else:
    result = nnkCall.newTree(dotexpr)

  for arg in args:
    result.add arg

func newCallNode*(
  name: string,
  args: seq[NimNode],
  genParams: seq[NType[NimNode]] = @[]): NimNode =
  ## Create node `name[@genParams](@args)`
  if genParams.len > 0:
    result = nnkCall.newTree()
    result.add nnkBracketExpr.newTree(
      @[ newIdentNode(name) ] & genParams.mapIt(it.toNimNode()))

  else:
    result = nnkCall.newTree(ident name)

  for node in args:
    result.add node


func newCallNode*(name: string,
                 gentypes: openarray[NType],
                 args: varargs[NimNode]): NimNode =
  ## Create node `name[@gentypes](@args)`. Overload with more
  ## convinient syntax if you have predefined number of genric
  ## parameters - `newCallNode("name", [<param>](arg1, arg2))` looks
  ## almost like regular `quote do` interpolation.
  newCallNode(name, toSeq(args), toSeq(genTypes))

func newCallNode*(
  arg: NimNode, name: string,
  gentypes: openarray[NType[NimNode]] = @[]): NimNode =
  ## Create call node `name[@gentypes](arg)`
  newCallNode(name, @[arg], toSeq(genTypes))

func newCallNode*(
  dotHead: NimNode, name: string,
  gentypes: openarray[NType],
  args: seq[NimNode]): NimNode =
  ## Create call node `dotHead.name[@gentypes](@args)`
  newCallNode(dotHead, name, toSeq(args), toSeq(genTypes))


#========================  Other implementation  =========================#



func toNTypeAst*[T](): NType =
  let str = $typeof(T)
  let expr = parseExpr(str)

#===========================  Pretty-printing  ===========================#
func `$`*[NNode](nt: NType[NNode]): string =
  ## Convert `NType` to texual representation
  case nt.kind:
    of ntkIdent:
      if nt.genParams.len > 0:
        nt.head & "[" & nt.genParams.mapIt($it).join(", ") & "]"
      else:
        nt.head

    of ntkGenericSpec:
      if nt.genParams.len > 0:
        nt.head & ": " & nt.genParams.mapIt($it).join(" | ")
      else:
        nt.head

    of ntkProc:
      {.noSideEffect.}:
        let rtype: string = nt.rtype.getSomeIt($it & ": ", "")
        let pragma: string =
          if nt.pragma.len == 0:
            ""
          else:
            toString(nt.pragma.toNNode()) & " "

        let args: string = nt.arguments.mapIt($it).join(", ")
        &"proc ({args}){pragma}{rtype}"

    of ntkRange:
      raiseAssert("#[ IMPLEMENT ]#")


#*************************************************************************#
#*******************  Enum - enum declaration wrapper  *******************#
#*************************************************************************#
#===========================  Type definition  ===========================#
type
  EnumFieldVal* = enum
    efvNone
    efvIdent
    efvOrdinal
    efvString
    efvOrdString

  RTimeOrdinalKind* = enum
    rtokInt
    rtokBool
    rtokChar

  RTimeOrdinal = object
    case kind*: RTimeOrdinalKind
      of rtokInt:
        intVal*: BiggestInt
      of rtokBool:
        boolVal*: bool
      of rtokChar:
        charVal*: char

  EnumField*[NNode] = object
    comment*: string
    name*: string
    value*: Option[NNode]

    case kind*: EnumFieldVal
      of efvNone:
        discard
      of efvIdent:
        ident*: NNode
      of efvOrdinal:
        ordVal*: RtimeOrdinal
      of efvString:
        strval*: string
      of efvOrdString:
        ordStr*: tuple[ordVal: RtimeOrdinal, strval: string]


  Enum*[NNode] = object
    ## Enum declaration wrapper
    comment*: string
    name*: string
    values*: seq[EnumField[NNode]]
    exported*: bool
    pragma*: Pragma[NNode]

  NEnum* = Enum[NimNode]
  PEnum* = Enum[PNode]

#=============================  Predicates  ==============================#
func isEnum*(en: NimNode): bool =
  ## Check if `typeImpl` for `en` is `enum`
  en.getTypeImpl().kind == nnkEnumTy

#===============================  parsers  ===============================#

func makeEnumField*[NNode](
  name: string,
  value: Option[NNode] = none(NNode),
  comment: string = ""): EnumField[NNode] =
  EnumField[NNode](name: name, value: value, comment: comment)



func parseEnumField*[NNode](fld: NNode): EnumField[NNode] =
  case fld.kind.toNNK():
    of nnkEnumFieldDef:
      let val = fld[1]
      result = case val.kind.toNNK():
        of nnkCharLit..nnkUInt64Lit:
          EnumField[NNode](kind: efvOrdinal,
                           ordVal: val.parseRTimeOrdinal())
        of nnkPar:
          val[1].expectKind nnkStrLit
          EnumField[NNode](
            kind: efvOrdString, ordStr: (
              ordVal: val[0].parseRTimeOrdinal(),
              strval: val[1].getStrVal()))
        of nnkStrLit:
          EnumField[NNode](kind: efvString, strval: val.strVal)
        of nnkIdent, nnkSym:
          EnumField[NNode](kind: efvIdent, ident: val)
        else:
          # when NNode is NimNode:
          #   debugecho fld.treeRepr()
          raiseAssert(&"Unexpected node kind for enum field: {val.kind}")

      result.name = fld[0].getStrVal
    of nnkSym:
      return makeEnumField(
        name = fld.getStrVal,
        value = none(NNode)
      )
    else:
      raiseAssert(&"#[ IMPLEMENT {fld.kind} ]#")



#============================  Constructors  =============================#
func parseRTimeOrdinal*[NNode](nnode: NNode): RTimeOrdinal =
  let kind = nnode.kind.toNNK()
  case kind:
    of nnkIntLit .. nnkUInt64Lit:
      RTimeOrdinal(kind: rtokInt, intval: nnode.intVal)
    of nnkCharLit:
      RTimeOrdinal(kind: rtokChar, charval: char(nnode.intVal))
    of nnkIdent:
      let val = case nnode.getStrVal():
        of "off", "false":
          false
        of "on", "true":
          true
        else:
          raiseAssert("Unexpected identifier for parsing RTimeOrdinal")


      RTimeOrdinal(kind: rtokBool, boolVal: val)

    else:
      raiseAssert(&"Unexpected node kind for parsing RTimeOrdinal: {kind}")

func makeRTOrdinal*(ival: int): RTimeOrdinal =
  RTimeOrdinal(kind: rtokInt, intval: BiggestInt(ival))

func makeRTOrdinal*(ival: BiggestInt): RTimeOrdinal =
  RTimeOrdinal(kind: rtokInt, intval: ival)

func makeRTOrdinal*(cval: char): RTimeOrdinal =
  RTimeOrdinal(kind: rtokChar, charVal: cval)

# func parseEnumField*[NNode](enval: NNode): EnumField[NNode] =
#   let kind = nnode.kind.toNNK()
#   case kind:
#     of nnkEmpty:

func toNNode*[NNode](ro: RTimeOrdinal): NNode =
  case ro.kind:
    of rtokInt:
      newNNLit[NNode](ro.intVal)
    of rtokChar:
      newNNLit[NNode](ro.charVal)
    of rtokBool:
      if ro.boolVal:
        newNident[NNode]("true")
      else:
        newNident[NNode]("false")


func toNNode*[NNode](fld: EnumField[NNode]): NNode =
  let fldVal: Option[NNode] = case fld.kind:
    of efvNone:
      none(NNode)
    of efvIdent:
      some fld.ident
    of efvString:
      some newNNLit[NNode](fld.strval)
    of efvOrdinal:
      some toNNode[NNode](fld.ordval)
    of efvOrdString:
      some newNTree[NNode](
        nnkPar,
        toNNode[NNode](fld.ordStr.ordVal),
        newNNLit[NNode](fld.ordStr.strVal)
      )

  if fldVal.isSome():
    newNTree[NNode](
      nnkEnumFieldDef,
      newNIdent[NNode](fld.name),
      fldVal.get()).withIt do:
        when NNode is PNode:
          it.comment = fld.comment
  else:
    when NNode is PNode:
      newPIdent(fld.name).withIt do:
        it.comment = fld.comment
    else:
      # TODO generate documentation comments for NimNode
      ident(fld.name)


func toNNode*[NNode](en: Enum[NNode], standalone: bool = false): NNode =
  ## Convert enum definition to `NNode`. If `standalone` is true wrap
  ## result in `nnkTypeSection`, otherwise generate `nnkTypeDef` only.
  let flds = collect(newSeq):
    for val in en.values:
      toNNode(val)

  let head =
    if en.exported:
      newNTree[NNode](nnkPostfix,
        newNIdent[NNode]("*"),
        newNIdent[NNode](en.name)
      )
    else:
      newNIdent[NNode](en.name)


  result = newNTree[NNode](
    nnkTypeDef,
    head,
    newEmptyNNode[NNode](),
    newNTree[NNode](nnkEnumTy, @[ newEmptyNNode[NNode]() ] & flds))

  when NNode is PNode:
    result.comment = en.comment

  if standalone:
    result = newNTree[NNode](
      nnkTypeSection,
      result
    )



func parseEnumImpl*[NNode](en: NNode): Enum[NNode] =
  # echov en.kind
  # debugecho en.treeRepr()
  case en.kind.toNNK():
    of nnkSym:
      when NNode is PNode:
        raiseAssert("Parsing of enum implementation from " &
          "Sym node is not support for PNode")
      else:
        let impl = en.getTypeImpl()
        # echov impl.kind
        case impl.kind:
          of nnkBracketExpr:
            # let impl = impl.getTypeInst()[1].getImpl()
            return parseEnumImpl(impl.getTypeInst()[1].getImpl())
          of nnkEnumTy:
            result = parseEnumImpl(impl)
          else:
            raiseAssert(&"#[ IMPLEMENT {impl.kind} ]#")
    of nnkTypeDef:
      result = parseEnumImpl(en[2])
      result.name = en[0].getStrVal
    of nnkEnumTy:
      for fld in en[1..^1]:
        result.values.add parseEnumField(fld)
    of nnkTypeSection:
      result = parseEnumImpl(en[0])
    else:
      raiseAssert(&"#[ IMPLEMENT {en.kind} ]#")


#========================  Other implementation  =========================#
func getEnumPref*(en: NimNode): string =
  ## Get enum prefix. As per `Nep style guide<https://nim-lang.org/docs/nep1.html#introduction-naming-conventions>`_
  ## it is recommended for members of enums should have an identifying
  ## prefix, such as an abbreviation of the enum's name. This functions
  ## returns this prefix.
  let impl = en.parseEnumImpl()
  # echov impl
  let
    name = impl.values[0].name
    pref = name.parseUntil(result, {'A' .. 'Z', '0' .. '9'})

macro enumPref*(a: typed): string =
  ## Generate string literal with enum prefix
  newLit(getEnumPref(a))

func getEnumNames*(en: NimNode): seq[string] =
  ## Get list of enum identifier names
  en.parseEnumImpl().values.mapIt(it.name)

macro enumNames*(en: typed): seq[string] =
  ## Generate list of enum names
  newLit en.getEnumNames()


#*************************************************************************#
#***************  Procedure declaration & implementation  ****************#
#*************************************************************************#
#==========================  Type definitions  ===========================#

type
  # TODO different keyword types: `method`, `iterator`, `proc`,
  # `func`, `template` etc.
  ProcKind* = enum
    ## Procedure kind
    pkRegular ## Regular proc: `hello()`
    pkOperator ## Operator: `*`
    pkHook ## Destructor/sink (etc.) hook: `=destroy`
    pkAssgn ## Assignment proc `field=`

  ProcDecl*[NNode] = object
    exported*: bool
    name*: string
    kind*: ProcKind
    signature*: NType[NNode] ## Signature of the proc as `ntProc` NType
    comment*: string ## Documentation string
    genParams*: seq[NType[NNode]] ## Generic parameters for proc
    impl*: NNode ## Implementation body

  PProcDecl* = ProcDecl[PNode]
  NProcDecl* = ProcDecl[NimNode]

# ~~~~ Predicates ~~~~ #

func `==`*[NNode](lhs, rhs: ProcDecl[NNode]): bool =
  lhs.name == rhs.name and
  lhs.exported == rhs.exported and
  lhs.signature == rhs.signature


# ~~~~ proc declaration ~~~~ #

func createProcType*(p, b: NimNode, annots: NPragma): NimNode =
  ## Copy-past of `sugar.createProcType` with support for annotations
  result = newNimNode(nnkProcTy)
  var formalParams = newNimNode(nnkFormalParams)

  formalParams.add b

  case p.kind
  of nnkPar, nnkTupleConstr:
    for i in 0 ..< p.len:
      let ident = p[i]
      var identDefs = newNimNode(nnkIdentDefs)
      case ident.kind
      of nnkExprColonExpr:
        identDefs.add ident[0]
        identDefs.add ident[1]
      else:
        identDefs.add newIdentNode("i" & $i)
        identDefs.add(ident)
      identDefs.add newEmptyNode()
      formalParams.add identDefs
  else:
    var identDefs = newNimNode(nnkIdentDefs)
    identDefs.add newIdentNode("i0")
    identDefs.add(p)
    identDefs.add newEmptyNode()
    formalParams.add identDefs

  result.add formalParams
  result.add annots.toNimNode()

macro `~>`*(a, b: untyped): untyped =
  ## Construct proc type with `noSideEffect` annotation.
  result = createProcType(a, b, newNPragma("noSideEffect"))


func toNNode*[NNode](pr: ProcDecl[NNode]): NNode =
  let headSym = case pr.kind:
    of pkRegular: newNIdent[NNode](pr.name)
    of pkHook: newNTree[NNode](
      nnkAccQuoted,
      newNIdent[NNode]("="),
      newNIdent[NNode](pr.name))
    of pkAssgn: newNTree[NNode](
      nnkAccQuoted,
      newNIdent[NNode](pr.name),
      newNIdent[NNode]("="))
    of pkOperator: newNTree[NNode](
      nnkAccQuoted, newNIdent[NNode](pr.name))

  let head =
    if pr.exported: newNTree[NNode](
      nnkPostfix, newNIdent[NNode]("*"), headSym)
    else:
      headSym

  let genParams =
    if pr.genParams.len == 0:
      newEmptyNNode[NNode]()
    else:
      newNTree[NNode](nnkGenericParams, pr.genParams.mapIt(toNNode[NNode](it)))


  let rettype =
    if pr.signature.rType.isSome():
      toNNode[NNode](pr.signature.rtype.get().getIt())
    else:
      newEmptyNNode[NNode]()

  let impl =
    if pr.impl == nil:
      newEmptyNNode[NNode]()
    else:
      pr.impl


  result = newNTree[NNode](
    nnkProcDef,
    head,
    newEmptyNNode[NNode](),
    genParams,
    newNTree[NNode](
      nnkFormalParams,
      @[ rettype ] & pr.signature.arguments.mapIt(it.toNFormalParam())
    ),
    toNNode[NNode](pr.signature.pragma),
    newEmptyNNode[NNode](),
    impl
  )

  when NNode is PNode:
    result.comment = pr.comment



func newProcDeclNNode*[NNode](
  procHead: NNode,
  rtype: Option[NType[NNode]],
  args: seq[NIdentDefs[NNode]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  ## Generate procedure declaration
  ##
  ## ## Parameters
  ##
  ## :procHead: head of the procedure
  ## :rtype: Optional return type
  ## :args: Proc arguments
  ## :impl: Proc implementation body
  ## :pragma: Pragma annotation for proc
  ## :exported: Whether or not procedure is exported

  let procHead =
    if exported:
      newNTree[NNode](nnkPostfix, newNIdent[NNode]("*"), procHead)
    else:
      procHead

  let impl =
    if comment.len > 0:
      newNTree[NNode](
        nnkStmtList,
        newCommentStmtNNode[NNode](comment),
        impl
      )
    else:
      impl



  result = newNTree[NNode](
    nnkProcDef,
    procHead,
    newEmptyNNode[NNode](),
    newEmptyNNode[NNode](),  # XXXX generic type parameters,
    newNTree[NNode]( # arguments
      nnkFormalParams,
      @[
        rtype.isSome().tern(
          toNNode[NNode](rtype.get()),
          newEmptyNNode[NNode]()
        )
      ] &
      args.mapIt(toNFormalParam[NNode](it))
    ),
    toNNode[NNode](pragma),
    newEmptyNNode[NNode](), # XXXX reserved slot,
  )

  # if impl.kind.toNNK() != nnkEmpty:
  result.add impl



func newProcDeclNode*(
  head: NimNode, rtype: Option[NType[NimNode]], args: seq[NIdentDefs[NimNode]],
  impl: NimNode, pragma: NPragma = NPragma(), exported: bool = true,
  comment: string = ""): NimNode =

  newProcDeclNNode[NimNode](
    head, rtype, args, impl, pragma, exported, comment)


func newProcDeclNode*(
  head: PNode, rtype: Option[NType[PNode]], args: seq[PIdentDefs],
  impl: PNode, pragma: Pragma[PNode] = Pragma[PNode](),
  exported: bool = true, comment: string = ""): PNode =

  newProcDeclNNode[PNode](
    head, rtype, args, impl, pragma, exported, comment)

func newProcDeclNode*[NNode](
  head: NNode,
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  newProcDeclNNode(
    head,
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  accq: openarray[NNode],
  rtype: NType,
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  newProcDeclNNode(
    newNTree[NNode](nnkAccQuoted, accq),
    some(rtype),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  accq: openarray[NNode],
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  newProcDeclNNode(
    newNTree[NNode](nnkAccQuoted, accq),
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  head: NNode,
  rtype: NType[NNode],
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  newProcDeclNNode(
    head,
    some(rtype),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )

func newProcDeclNode*[NNode](
  head: NNode,
  args: openarray[tuple[
    name: string,
    atype: NType[NNode],
    nvd: NVarDeclKind]
  ],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode =
  newProcDeclNNode(
    head,
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )

#===========================  Pretty-printing  ===========================#

#*************************************************************************#
#*****************  Object - object declaration wrapper  *****************#
#*************************************************************************#
#===========================  Type definition  ===========================#
type
  ParseCb*[NNode, Annot] = proc(
    pragma: NNode, kind: ObjectAnnotKind): Annot
  ObjectBranch*[Node, Annot] = object
    ## Single branch of case object
    annotation*: Option[Annot]
    flds*: seq[ObjectField[Node, Annot]] ## Fields in the case branch
    case isElse*: bool ## Whether this branch is placed under `else` in
                  ## case object.
      of true:
        notOfValue*: Node
      of false:
        ofValue*: Node ## Match value for case branch



  ObjectField*[NNode, Annot] = object
    # TODO:DOC
    ## More complex representation of object's field - supports
    ## recursive fields with case objects.
    annotation*: Option[Annot]
    value*: Option[NNode]
    exported*: bool
    case isTuple*: bool # REVIEW REFACTOR move tuples into separate
                        # object instead of mixing them into `object`
                        # wrapper.
      of true:
        tupleIdx*: int
      of false:
        name*: string

    fldType*: NType[NNode] ## Type of field value
    case isKind*: bool
      of true:
        selected*: int ## Index of selected branch
        branches*: seq[ObjectBranch[NNode, Annot]] ## List of all
        ## branches as `value-branch` pairs.
      of false:
        discard

  Object*[NNode, Annot] = object
    # TODO:DOC
    # TODO `flatFields` iterator to get all values with corresponding
    # parent `ofValue` branches. `for fld, ofValues in obj.flatFields()`
    exported*: bool
    annotation*: Option[Annot]
    # namedObject*: bool ## This object's type has a name? (tuples
    # ## does not have name for a tyep)
    # namedFields*: bool ## Fields have dedicated names? (anonymous
    # ## tuple does not have a name for fields)
    name*: NType[NNode] ## Name for an object
    # TODO rename to objType
    flds*: seq[ObjectField[NNode, Annot]]

  # FieldBranch*[Node] = ObjectBranch[Node, void]
  # Field*[Node] = ObjectField[Node, void]

  ObjectPathElem*[NNode, Annot] = object
    kindField*: ObjectField[NNode, Annot]
    case isElse*: bool
      of true:
        notOfValue*: NNode
      of false:
        ofValue*: NNode


  NBranch*[A] = ObjectBranch[NimNode, A]
  NPathElem*[A] = ObjectPathElem[NimNode, A]
  NField*[A] = ObjectField[NimNode, A]
  NObject*[A] = Object[NimNode, A]
  NPath*[A] = seq[NPathElem[A]]

  PObject* = Object[PNode, Pragma[PNode]]
  PField* = ObjectField[PNode, Pragma[PNode]]

  # PragmaField*[Node] = ObjectField[Node, Pragma[Node]]
  # NPragmaField* = PragmaField[NimNode]

const noParseCb*: ParseCb[NimNode, void] = nil
const noParseCbPNode*: ParseCb[PNode, void] = nil



#=============================  Predicates  ==============================#
func markedAs*(fld: NField[NPragma], str: string): bool =
  fld.annotation.getElem(str).isSome()

#===============================  Getters  ===============================#

# ~~~~ each field mutable ~~~~ #

func eachFieldMut*[NNode, A](
  obj: var Object[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void

func eachFieldMut*[NNode, A](
  branch: var ObjectBranch[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in mutable object branch,
  ## recursively.
  for fld in mitems(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)


func eachFieldMut*[NNode, A](
  obj: var Object[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in mutable object, recursively.
  for fld in mitems(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)

# ~~~~ each annotation mutable ~~~~ #

func eachAnnotMut*[NNode, A](
  branch: var ObjectBranch[NNode, A], cb: (var Option[A] ~> void)): void =
  ## Execute callback on each annotation in mutable branch,
  ## recursively - all fields in all branches are visited.
  for fld in mitems(branch.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachAnnotMut(branch, cb)

func eachAnnotMut*[NNode, A](
  obj: var Object[NNode, A], cb: (var Option[A] ~> void)): void =
  ## Execute callback on each annotation in mutable object,
  ## recurisively - all fields and subfields are visited. Callback
  ## runs on both kind and non-kind fields. Annotation is not
  ## guaranteed to be `some`, and it might be possible for callback to
  ## make it `none` (removing unnecessary annotations for example)

  cb(obj.annotation)

  for fld in mitems(obj.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in mitems(fld.branches):
        branch.eachAnnotMut(cb)


# ~~~~ each field immutable ~~~~ #

func eachField*[NNode, A](
  obj: Object[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void

func eachField*[NNode, A](
  branch: ObjectBranch[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in branch, recursively
  for fld in items(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)


func eachField*[NNode, A](
  obj: Object[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in object, recurisively.
  for fld in items(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)

# ~~~~ each alternative in case object ~~~~ #

func eachCase*[A](
  fld: NField[A], objId: NimNode, cb: (NField[A] ~> NimNode)): NimNode =
  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId, ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        result.add nnkElse.newTree(
          branch.flds.mapIt(it.eachCase(objId, cb))
        )
      else:
        result.add nnkOfBranch.newTree(
          branch.ofValue,
          branch.flds.mapIt(
            it.eachCase(objId, cb)).newStmtList()
        )

    let cbRes = cb(fld)
    if cbRes != nil:
      result = newStmtList(cb(fld), result)
  else:
    result = newStmtList(cb(fld))

func eachCase*[A](
  objId: NimNode, obj: NObject[A], cb: (NField[A] ~> NimNode)): NimNode =
  ## Recursively generate case statement for object. `objid` is and
  ## identifier for object - case statement will use `<objid>.<fldId>`.
  ## `obj` is a description for structure. Callback `cb` will be executed
  ## on all fields - both `isKind` or not.

  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachCase(objid, cb)

func eachParallelCase*[A](
  fld: NField[A], objId: (NimNode, NimNode),
  cb: (NField[A] ~> NimNode)): NimNode =
  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId[0], ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        result.add nnkElse.newTree(
          branch.flds.mapIt(it.eachParallelCase(objId, cb))
        )
      else:
        result.add nnkOfBranch.newTree(
          branch.ofValue,
          branch.flds.mapIt(
            it.eachParallelCase(objId, cb)).newStmtList()
        )

    let
      fldId = ident fld.name
      lhsId = objId[0]
      rhsId = objId[1]

    let cbRes = cb(fld)
    result = quote do:
      `cbRes`
      if `lhsId`.`fldId` == `rhsId`.`fldId`:
        `result`

  else:
    result = newStmtList(cb(fld))

func eachParallelCase*[A](
  objid: (NimNode, NimNode), obj: NObject[A], cb: (NField[A] ~> NimNode)): NimNode =
  ## Generate parallel case statement for two objects in `objid`. Run
  ## callback on each field. Generated case statement will have form
  ## `if lhs.fld == rhs.fld: case lhs.fld`
  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachParallelCase(objid, cb)



# ~~~~ each annotation immutable ~~~~ #

func eachAnnot*[Node, A](
  branch: ObjectBranch[Node, A], cb: (Option[A] ~> void)): void =
  for fld in items(branch.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in items(fld.branches):
        eachAnnot(branch, cb)

func eachAnnot*[Node, A](
  obj: Object[Node, A], cb: (Option[A] ~> void)): void =

  cb(obj.annotation)

  for fld in items(obj.flds):
    cb(fld.annotation.get())
    if fld.isKind:
      for branch in items(fld.branches):
        branch.eachAnnot(cb)


# ~~~~ Each path in case object ~~~~ #
func eachPath*[A](
  fld: NField[A], self: NimNode, parent: NPath[A],
  cb: ((NPath[A], seq[NField[A]]) ~> NimNode)): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(self, ident fld.name))
    for branch in fld.branches:
      var branchBody = newStmtList()
      let nobranch = (fld.withIt do: it.branches = @[])
      let thisPath =
        if branch.isElse:
          parent & @[NPathElem[A](
            isElse: true, kindField: nobranch, notOfValue: branch.notOfValue)]
        else:
          parent & @[NPathElem[A](
            isElse: false, kindField: nobranch, ofValue: branch.ofValue)]

      let cbRes = cb(thisPath, branch.flds).nilToDiscard()
      if branch.isElse:
        branchBody.add nnkElse.newTree(cbRes)
      else:
        branchBody.add nnkOfBranch.newTree(branch.ofValue, cbRes)

      for fld in branch.flds:
        branchBody.add fld.eachPath(self, thisPath, cb)


func eachPath*[A](
  self: NimNode,
  obj: NObject[A], cb: ((NPath[A], seq[NField[A]]) ~> NimNode)): NimNode =
  ## Visit each group of fields in object described by `obj` and
  ## generate case statement with all possible object paths. Arguments
  ## for callback - `NPath[A]` is a sequence of kind field values that
  ## *must be active in order for execution to reach this path* in
  ## case statement. Second argument is a list of fields that can be
  ## accessed at that path.
  ## TODO:DOC add example

  result = newStmtList cb(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.eachPath(self, @[], cb)


func onPath*[A](self: NimNode, path: NPath[A]): NimNode =
  ## Generate check for object `self` to check if it is currently on
  ## path.
  var checks: seq[NimNode]
  for elem in path:
    if elem.isElse:
      checks.add newInfix(
        "notin", newDotExpr(self, ident elem.kindField.name),
        normalizeSet(elem.notOfValue, forceBrace = true))
    else:
      checks.add newInfix(
        "in", newDotExpr(self, ident elem.kindField.name),
        normalizeSet(elem.ofValue, forceBrace = true))

  if checks.len == 0:
    return newLit(true)
  else:
    result = checks.foldl(newInfix("and", a, b))


#===============================  Setters  ===============================#

#============================  Constructors  =============================#

#========================  Other implementation  =========================#
func toNNode*[NNode, A](
  fld: ObjectField[NNode, A], annotConv: A ~> NNode): NNode

func toNNode*[NNode, A](
  branch: ObjectBranch[NNode, A], annotConv: A ~> NNode): NNode =
  if branch.isElse:
    newNTree[NNode](
      nnkElse,
      nnkRecList.newTree(branch.flds.mapIt(it.toNNode(annotConv))))
  else:
    newNTree[NNode](
      nnkOfBranch,
      branch.ofValue,
      nnkRecList.newTree(branch.flds.mapIt(it.toNNode(annotConv))))


func toNNode*[NNode, A](
  fld: ObjectField[NNode, A], annotConv: A ~> NNode): NNode =

  let head =
    if fld.exported:
      newNTree[NNode](nnkPostfix,
                      newNIdent[NNode]("*"),
                      newNIdent[NNode](fld.name))
    else:
      newNIdent[NNode](fld.name)

  let fieldName =
    if fld.annotation.isSome():
      let pragma = annotConv(fld.annotation.get())
      newNTree[NNode](nnkPragmaExpr, head, pragma)
    else:
      head


  let selector = newNTree[NNode](
    nnkIdentDefs,
    fieldName,
    toNNode[NNode](fld.fldType),
    newEmptyNNode[NNode]()
  )

  if fld.isKind:
    return nnkRecCase.newTree(
      @[selector] & fld.branches.mapIt(toNNode[NNode](it, annotConv)))
  else:
    return selector

func toExported*[NNode](ntype: NType[NNode], exported: bool): tuple[
  head, genparams: NNode] =
  result.head =
    if exported:
      newNTree[NNode](
        nnkPostfix,
        newNIdent[NNode]("*"),
        newNIdent[NNode](ntype.head)
      )
    else:
      newNIdent[NNode](ntype.head)

  result.genparams =
    block:
      let maps = ntype.genParams.mapIt(toNNode[NNode](it))
      if maps.len == 0:
        newEmptyNNode[NNode]()
      else:
        newNTree[NNode](nnkGenericParams, maps)



func toNNode*[NNode, A](obj: Object[NNode, A], annotConv: A ~> NNode): NNode =
  let (head, genparams) = obj.name.toExported(obj.exported)
  let header =
    if obj.annotation.isSome():
      let node = annotConv obj.annotation.get()
      if node.kind != nnkEmpty:
        newNTree[NNode](nnkPragmaExpr, head, node)
      else:
        head
    else:
      head

  result = newNTree[NNode](
    nnkTypeDef,
    header,
    genparams,
    newNTree[NNode](
      nnkObjectTy,
      newEmptyNNode[NNode](),
      newEmptyNNode[NNOde](),
      newNTree[NNode](
        nnkRecList,
        obj.flds.mapIt(toNNode(it, annotConv))))) # loud LISP sounds

  # echov result.treeRepr()

func toNNode*[NNode](
  obj: Object[NNode, PRagma[NNode]], standalone: bool = false): NNode =
  result = toNNode[NNode](
    obj, annotConv =
      proc(pr: Pragma[NNode]): NNode {.closure.} =
        return toNNode[NNode](pr)
  )

  if standalone:
    result = newNTree[NNode](
      nnkTypeSection,
      result
    )

func toNimNode*(obj: NObject[NPragma]): NimNode =
  # static: echo typeof obj
  toNNode[NimNode](obj)

#===========================  Pretty-printing  ===========================#







#*************************************************************************#
#*******  ObjTree - 'stringly typed' object value representation  ********#
#*************************************************************************#
#===========================  Type definition  ===========================#
type
  ObjKind* = enum
    # TODO:DOC
    okConstant ## Literal value
    okSequence ## Sequence of items
    okTable ## List of key-value pairs with single types for keys and
    ## values
    okComposed ## Named list of field-value pairs with possilby
    ## different types for fields (and values). List name is optional
    ## (unnamed object), field name is optional (unnamed fields)

  ObjRelationKind = enum
    # TODO:DOC
    orkComposition
    orkReference
    orkPointer

  ObjAccs = object
    # TODO:DOC
    case isIdx*: bool
      of true:
        idx*: int
      of false:
        name*: string

  ObjPath = seq[ObjAccs]

  ObjTree* = object
    ##[

## Fields

:isPrimitive: Value is primitve or not?

  Primitive value will be added to graphviz node export as part of the
  table (in regular export) as oppposed to non-primitive value (it
  will be rendered as separate node). By default primitive values are
  `int`, `string`, `float` etc. types, tuples/objects that are (1)
  composed only from primitive types (`(int, int)`), (2) have four
  fields or less. Also tables/sequences with four elements or less are
  considered primitive if (1) both keys and values are primitive (2)
  container has four elements or less.

    ]##
    path*: seq[int] ## Path of object in original tree
    objId*: int ## Unique object id
    isPrimitive*: bool ## Whether or not value can be considered primitive
    annotation*: string ## String annotation for object
    styling* {.requiresinit.}: PrintStyling ## Print styling for object
    # NOTE styling is currently unused
    case kind*: ObjKind
      of okConstant:
        constType*: string ## Type of the value
        strlit*: string ## Value representation in string form
      of okSequence:
        itemType*: string ## Type of the sequence item
        valItems*: seq[ObjTree] ## List of values
      of okTable:
        keyType*: string ## Type of table key
        valType*: string ## TYpe of value key
        valPairs*: seq[tuple[key: string, val: ObjTree]] ## List of
        ## key-value pairs for table
        # XXXX TODO TEST used `ObjTree` for key too. Non-trivial types
        # can be used. Write unit tests for this functionality.

        # NOTE REFACTOR use `value` for enum field.
      of okComposed:
        namedObject*: bool ## This object's type has a name? (tuples
        ## does not have name for a tyep)
        namedFields*: bool ## Fields have dedicated names? (anonymous
        ## tuple does not have a name for fields)
        name*: string ## Name for an object
        # TODO Add field type
        fldPairs*: seq[tuple[name: string, value: ObjTree]] ## Sequence
        ## of field-value pairs for object representation



  ObjElem*[Conf] = object
    # TODO:DOC
    case isValue: bool
      of true:
        text*: string
        config*: Conf
      of false:
        relType*: ObjRelationKind
        targetId*: int


type
  ValField* = ObjectField[ObjTree, void]
  ValFieldBranch* = ObjectBranch[ObjTree, void]


func newOType*(name: string, gparams: seq[string] = @[]): NType[ObjTree] =
  NType[ObjTree](
    kind: ntkIdent,
    head: name,
    genParams: gparams.mapIt(newOType(it, @[]))
  )

proc prettyPrintConverter*(val: PNode, path: seq[int] = @[0]): ObjTree =
  # TODO can add syntax hightlight to string literal generated from
  #      nim node
  ObjTree(
    styling: initPrintStyling(),
    kind: okConstant,
    constType: "PNode",
    strLit: $val
  )



#=============================  Predicates  ==============================#
func `==`*[Node, A](lhs, rhs: ObjectField[Node, A]): bool

func `==`*(lhs, rhs: ObjTree): bool =
  lhs.kind == rhs.kind and
    (
      case lhs.kind:
        of okConstant:
          lhs.constType == rhs.constType and
          lhs.strLit == rhs.strLit
        of okSequence:
          lhs.itemType == rhs.itemType and
          subnodesEq(lhs, rhs, valItems)
        of okTable:
          lhs.keyType == rhs.keyType and
          lhs.valType == rhs.valType and
          zip(lhs.valPairs, rhs.valPairs).allOfIt(
            (it[0].key == it[1].key) and (it[0].val == it[1].val)
          )
        of okComposed:
          lhs.namedObject == rhs.namedObject and
          lhs.namedFields == rhs.namedFields and
          lhs.name == rhs.name and
          subnodesEq(lhs, rhs, fldPairs)
    )

func `==`*[Node, A](lhs, rhs: ObjectField[Node, A]): bool =
  lhs.isKind == rhs.isKind and
    (
      case lhs.isKind:
        of true:
          lhs.name == rhs.name and
          lhs.fldType == rhs.fldType and
          (when A is void: true else: subnodesEq(lhs, rhs, branches))
        of false:
          true
    )

#===============================  Getters  ===============================#

#===============================  Setters  ===============================#

#============================  Constructors  =============================#
func makeObjElem*[Conf](text: string, conf: Conf): ObjElem[Conf] =
  # TODO:DOC
  ObjElem[Conf](isValue: true, text: text, config: conf)

func initObjTree*(): ObjTree =
  # TODO:DOC
  ObjTree(styling: initPrintStyling())

#========================  Other implementation  =========================#

#===========================  Pretty-printing  ===========================#





#==============================  operators  ==============================#


#*************************************************************************#
#***********************  Annotation and styling  ************************#
#*************************************************************************#

func annotate*(tree: var ObjTree, annotation: string): void =
  # TODO:DOC
  tree.annotation = annotation

func stylize*(tree: var ObjTree, conf: PrintStyling): void =
  # TODO:DOC
  tree.styling = conf

func styleTerm*(str: string, conf: PrintStyling): string =
  # TODO:DOC
  $ColoredString(str: str, styling: conf)

#*************************************************************************#
#*****************************  Path access  *****************************#
#*************************************************************************#

func objAccs*(idx: int): ObjAccs =
  # TODO:DOC
  ObjAccs(isIdx: true, idx: idx)
func objAccs*(name: string): ObjAccs =
  # TODO:DOC
  ObjAccs(isIdx: false, name: name)

func objPath*(path: varargs[ObjAccs, `objAccs`]): ObjPath =
  # TODO:DOC
  toSeq(path)

func getAtPath*(obj: var ObjTree, path: ObjPath): var ObjTree =
  # TODO:DOC
  case obj.kind:
    of okComposed:
      if path.len < 1:
        return obj
      else:
        if path[0].isIdx:
          return obj.fldPairs[path[0].idx].value.getAtPath(path[1..^1])
        else:
          if obj.namedFields:
            for fld in mitems(obj.fldPairs):
              if fld.name == path[0].name:
                 return fld.value.getAtPath(path[1..^1])

            raisejoin(@["Cannot get field name '", path[0].name,
              "' from object - no such field found"])
          else:
            raisejoin(@["Cannot get field name '", path[0].name,
              "' from object with unnamed fields"])
    of okConstant:
      if path.len > 1:
        raiseAssert(msgjoin(
          "Attempt to access subelements of constant value at path ",
          path))
      else:
        return obj
    of okSequence:
      if path.len == 0:
        return obj

      if not path[0].isIdx:
        raiseAssert(msgjoin(
          "Cannot access sequence elements by name, path", path,
          "starts with non-index"))
      elif path.len == 1:
        return obj.valItems[path[0].idx]
      else:
        return obj.valItems[path[0].idx].getAtPath(path[1..^1])

    else:
      raiseAssert("#[ IMPLEMENT ]#")




#*************************************************************************#
#***********************  Init call construction  ************************#
#*************************************************************************#
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

#*************************************************************************#
#***********************  Helper proc procedures  ************************#
#*************************************************************************#
