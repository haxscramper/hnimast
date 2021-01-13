## Statically typed nim ast representation with large number of helper
## functions - skipping nil nodes, normalizing set literals,
## generating and working with pragma annotations, parsing object
## defintions etc.

import hmisc/[helpers, base_errors]
export base_errors

import hmisc/types/colorstring
import std/[
  sequtils, colors, macros, tables, strutils, streams,
  terminal, options, parseutils, sets, strformat, sugar
]

import compiler/[ast, idents, lineinfos, renderer]

import hnimast/[pnode_parse]
export pnode_parse, options, NimNodeKind

export ast
export PNode

# type NNode = NimNode | PNode

template currIInfo*(): untyped =
  let (file, line, col) = instantiationInfo()
  LineInfo(filename: file, line: line, column: col)

const defaultIInfo* = LineInfo()



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
    raiseArgumentError(
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
  nnkStrKinds* = { nnkStrLit .. nnkTripleStrLit }
  nnkIntKinds* = { nnkCharLit .. nnkUInt64Lit }
  nnkFloatKinds* = { nnkFloatLit .. nnkFloat128Lit }

  nnkTokenKinds* = nnkStrKinds + nnkIntKinds + nnkFloatKinds + {
    nnkIdent,
    nnkSym
  }


  nkStrKinds* = { nkStrLit .. nkTripleStrLit }
  nkIntKinds* = { nkCharLit .. nkUInt64Lit }
  nkFloatKinds* = { nkFloatLit .. nkFloat128Lit }

  nkTokenKinds* = nkStrKinds + nkIntKinds + nkFloatKinds + {
    nkIdent,
    nkSym
  }


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

func newPLit*(f: float): PNode =
  newFloatNode(nkFloatLit, f)

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



func dropPar1*(nn: NimNode): NimNode =
  if nn.kind == nnkPar: nn[0] else: nn


func quoteAux(body: NimNode, resCall: string): NimNode =
  if body.kind == nnkPrefix and
     body[0].eqIdent("@@@!"):
    return body[1]

  elif body.kind == nnkInfix and
       body[0].eqIdent(".@@@!"):
    return newCall(
      resCall, ident "nnkDotExpr",
      quoteAux(body[1], resCall),
      body[2].dropPar1()
    )


  result = newCall(resCall, ident $body.kind)

  case body.kind:
    of nnkAccQuoted:
      if body[0].kind == nnkIdent and
         not body[0].strVal().validIdentifier(): # Special case
         # operators `[]` - most of the time you would want to
         # declare `` proc `[]` `` rather than interpolate `[]`
         # (which is not valid variable name even)
        let bodyLit = newLit body[0].strVal()
        return quote do:
          newPTree(nnkAccQuoted, newPIdent(`bodyLit`))
      else:
        var res: string
        for node in body:
          res &= node.repr

        return parseExpr(res)
    of nnkStrKinds:
      result.add newLit body.strVal

    of nnkFloatKinds:
      result.add newLit body.floatVal

    of nnkIntKinds:
      result.add newLit body.intVal

    of nnkIdent, nnkSym:
      result = newCall("newPIdent", newLit(body.strVal))

    else:
      var hasSplices = false

      block findSplices:
        for subnode in body:
          if subnode.kind == nnkPrefix and
             subnode[0].eqIdent("@@@"):

             hasSplices = true
             break findSplices

          for node in subnode:
            if node.kind == nnkPrefix and
               node[0].eqIdent("@@@^"):

              # IdentDefs     <- subnode
              #   Ident "arg" <- node
              #   Prefix      <- necessary prefix
              #     Ident "@@@^"
              #     Ident "nArgList"
              #   Empty

              hasSplices = true
              break findSplices


      if hasSplices:
        let kind = ident $body.kind
        result = newStmtList()

        var tree = ident "tree"

        result.add quote do:
          var `tree` = newPTree(`kind`)

        for subnode in body:
          var splice = false

          for node in subnode:
            if node.kind == nnkPrefix and
               node[0].eqIdent("@@@^"):
              let impl = node[1]

              result.add quote do:
                for val in `impl`:
                  `tree`.add val

              splice = true
              break


          if not splice:
            if subnode.kind == nnkPrefix and
               subnode[0].eqIdent("@@@"):
              let impl = subnode[1]
              result.add quote do:
                for val in `impl`:
                  `tree`.add val
            else:
              let builder = quoteAux(subnode, resCall)
              result.add quote do:
                `tree`.add `builder`

        result.add quote do:
          `tree`

        result = quote do:
          ((
            block:
              `result`
          ))

      else:
        for subnode in body:
          result.add quoteAux(subnode, resCall)


macro pquote*(mainBody: untyped): untyped =
  ## `quote` macro to generate `PNode` builder. Similarly to `superquote`
  ## from `macroutils` allows to use any expressions for interpolation.
  ## Additionally, to circumvent some limitations of how AccQuoted is
  ## parsed, you can use `@@@`, `@@@!` and `@@@^` prefixes for
  ## interpolation of the arguments directly.
  ##
  ## - `@@@!` - interpolate arguments directly. This is what you should
  ##    use instead of backticks
  ## - `@@@` - *splice* arguments into list. Adding more than one subnode
  ##   to generated code - `[1, 2, 3, @@@(moreArgs)]` - will insert result
  ##   of evaluation for `moreArgs` into `nnkBracketExpr` subnodes.
  ## - `@@@^` - splice arguments into *parent* list. This should be used in
  ##   cases where arbitrary expressions are not allowed, namely function
  ##   parameter list, field declarations etc. You now can do
  ##   `proc(a: int, b: @@@^(moreArgs))` to append to argument list. `b` in
  ##   this case only used as dummy node, since `proc(a: int, @@@(args))`
  ##   is not a valid syntax.
  ##
  ## NOTE - recommended way of using intrinsic DSL prefixes is
  ## `@@@(argument)` and not `@@@argument`. It clearly distinguishes
  ## between prefix and what should be spliced. Also allows for things like
  ## `@@@([arg1, arg2])` if needed.


  result = quoteAux(mainBody, "newPTree")

macro nquote*(mainBody: untyped): untyped =
  ## DSL and set of features is identical to `pquote`, but generates
  ## `NimNode` instead of `PNode`.
  result = quoteAux(mainBody, "newTree")


type
  ObjectAnnotKind* = enum
    ## Position of annotation (most likely pragma) attached.
    oakCaseOfBranch ## Annotation on case branch, not currently suppported
    oakObjectToplevel ## Toplevel annotaion for object
    oakObjectField ## Annotation for object field


proc treeRepr*(
    pnode: PNode, colored: bool = true, indexed: bool = false
  ): string =

  proc aux(n: PNode, level: int, idx: seq[int]): string =
    let pref =
      if indexed:
        idx.join("", ("[", "]")) & "    "
      else:
        "  ".repeat(level)

    result &= pref & ($n.kind)[2..^1]
    case n.kind:
      of nkStrKinds:
        result &= " \"" & toYellow(n.getStrVal(), colored) & "\"\""

      of nkIntKinds:
        result &= " " & toBlue(n.getStrVal(), colored)

      of nkFloatKinds:
        result &= " " & toMagenta(n.getStrVal(), colored)

      of nkIdent, nkSym:
        result &= " " & toGreen(n.getStrVal(), colored)

      else:
        if n.len > 0:
          result &= "\n"

        for newIdx, subn in n:
          result &= aux(subn, level + 1, idx & newIdx)
          if newIdx < n.len - 1:
            result &= "\n"

  return aux(pnode, 0, @[0])


#*************************************************************************#
#****************************  Ast reparsing  ****************************#
#*************************************************************************#

#=======================  Enum set normalization  ========================#
func normalizeSetImpl[NNode](node: NNode): seq[NNode] =
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
      {.cast(noSideEffect).}:

        when node is PNode:
          let str = hnimast.`$`(node)

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
        raiseImplementError("<>")

func getElem*(optPragma: Option[NPragma], name: string): Option[NimNode] =
  ## Get element from optional annotation
  if optPragma.isSome():
    return optPragma.get().getElem(name)

func len*[NNode](pragma: Pragma[NNode]): int =
  pragma.elements.len

func add*[NNode](pragma: var Pragma[NNode], node: NNode) =
  pragma.elements.add node

func clear*[N](pragma: var PRagma[N]) =
  pragma.elements = @[]

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

func add*[NNode](ntype: var NType[NNode], nt: NType[NNode]) =
  if ntype.head in ["ref", "ptr", "var"]:
    ntype.genParams[0].add nt
  else:
    ntype.genParams.add nt

func add*[NNode](ntype: var NType[NNode], nt: varargs[NType[NNode]]) =
  for arg in nt:
    ntype.add arg

func toNNode*[NNode](ntype: NType[NNode]): NNode =
  ## Convert to NNode
  case ntype.kind:
    of ntkProc:
      result = newNTree[NNode](nnkProcTy)

      let renamed: seq[NIdentDefs[NNode]] = ntype.arguments.mapPairs:
        rhs.withIt do:
          if it.varname.len == 0:
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
        if ntype.head in ["ref", "ptr", "var"]:
          # TODO handle `lent`, `sink` and other things like that
          if ntype.genParams.len != 1:
            let args = join(ntype.genParams.mapIt($!toNNode[NNode](it)), " ",)
            argumentError:
              "Expected single generic parameter for `ref/ptr`"
              "type, but got [{args}]"

          var ty: NimNodeKind
          case ntype.head:
            of "ref": ty = nnkRefTy
            of "ptr": ty = nnkPtrTy
            of "var": ty = nnkVarTy

          result = newNTree[NNode](
            ty,
            toNNode[NNode](ntype.genParams[0])
          )

        else:
          result = newNTree[NNode](
            nnkBracketExpr, newNIdent[NNode](ntype.head))
          for param in ntype.genParams:
            result.add toNNode[NNode](param)

func newNIdentDefs*[N](
    vname: string,
    vtype: NType[N],
    kind: NVarDeclKind = nvdLet,
    value: Option[N] = none(N)
  ): NIdentDefs[N] =
  NIdentDefs[N](varname: vname, vtype: vtype, value: value, kind: kind)

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

  result = newNTree[NNode](
    nnkIdentDefs,
    newNIdent[NNode](nident.varname),
    typespec
  )

  if nident.value.isNone():
    result.add newEmptyNNode[NNode]()

  else:
    result.add nident.value.get()

func toFormalParam*(nident: NIdentDefs[NimNode]): NimNode =
  ## Convert to `nnkIdentDefs`
  toNFormalParam[NimNode](nident)


func newNType*(name: string, gparams: seq[string] = @[]): NType[NimNode] =
  ## Make `NType` with `name` as string and `gparams` as generic
  ## parameters
  NType[NimNode](
    kind: ntkIdent, head: name, genParams: gparams.mapIt(newNType(it, @[])))

func newPType*(name: string, gparams: openarray[string] = @[]): NType[PNode] =
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
  args: seq[(string, NType[NNode])],
  rtype: NType[NNode], pragma: Pragma[NNode]): NType[NNode] =

  NType[NNode](
    kind: ntkProc,
    arguments: toNIdentDefs[NNode](args),
    pragma: pragma,
    rType: some(newIt(rtype)))

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
      raiseImplementError("")

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
      raiseImplementError("")


#*************************************************************************#
#*******************  Enum - enum declaration wrapper  *******************#
#*************************************************************************#
#===========================  Type definition  ===========================#
type
  DeclMetainfo = object
    iinfo*: LineInfo
    docComment*: string
    comment*: string


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

  RTimeOrdinal* = object
    case kind*: RTimeOrdinalKind
      of rtokInt:
        intVal*: BiggestInt
      of rtokBool:
        boolVal*: bool
      of rtokChar:
        charVal*: char

  EnumField*[NNode] = object
    docComment*: string
    codeComment*: string
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


  EnumDecl*[NNode] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    ## Enum declaration wrapper
    meta*: DeclMetainfo

    name*: string
    values*: seq[EnumField[NNode]]
    exported*: bool
    pragma*: Pragma[NNode]

  NEnumDecl* = EnumDecl[NimNode]
  PEnumDecl* = EnumDecl[PNode]

#=============================  Predicates  ==============================#
func isEnum*(en: NimNode): bool =
  ## Check if `typeImpl` for `en` is `enum`
  en.getTypeImpl().kind == nnkEnumTy

#===============================  parsers  ===============================#

func makeEnumField*[NNode](
  name: string,
  value: Option[NNode] = none(NNode),
  comment: string = ""): EnumField[NNode] =
  EnumField[NNode](name: name, value: value, docComment: comment)

func newPEnumDecl*(
    name:        string,
    docComment:  string        = "",
    codeComment: string        = "",
    exported:    bool          = true,
    pragma:      Pragma[PNode] = Pragma[PNode](),
    iinfo:       LineInfo      = defaultIInfo
  ): EnumDecl[PNode] =

  result.name = name
  result.docComment = docComment
  result.codeComment = codeComment
  result.exported = exported
  result.pragma = pragma
  result.iinfo = iinfo

func addField*[N](
    en: var EnumDecl[N],
    name: string,
    value: Option[N] = none(N),
    docComment: string = ""
  ) =

  en.values.add makeEnumField(name, value, docComment)



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
          raiseArgumentError(
            &"Unexpected node kind for enum field: {val.kind}")

      result.name = fld[0].getStrVal

    of nnkSym:
      return makeEnumField(name = fld.getStrVal, value = none(NNode))

    else:
      raiseImplementError(&"#[ IMPLEMENT {fld.kind} ]#")



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
          raiseArgumentError(
            "Unexpected identifier for parsing RTimeOrdinal " &
              nnode.getStrVal())


      RTimeOrdinal(kind: rtokBool, boolVal: val)

    else:
      raiseArgumentError(
        &"Unexpected node kind for parsing RTimeOrdinal: {kind}")


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
  var fldVal: Option[NNode] = case fld.kind:
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

  if fldVal.isNone():
    fldVal = fld.value

  if fldVal.isSome():
    newNTree[NNode](
      nnkEnumFieldDef,
      newNIdent[NNode](fld.name),
      fldVal.get()).withIt do:
        when NNode is PNode:
          it.comment = fld.docComment

  else:
    when NNode is PNode:
      newPIdent(fld.name).withIt do:
        it.comment = fld.docComment

    else:
      # TODO generate documentation comments for NimNode
      ident(fld.name)


func toNNode*[NNode](en: EnumDecl[NNode], standalone: bool = false): NNode =
  ## Convert enum definition to `NNode`. If `standalone` is true wrap
  ## result in `nnkTypeSection`, otherwise generate `nnkTypeDef` only.
  let flds = collect(newSeq):
    for val in en.values:
      toNNode(val)

  var head =
    if en.exported:
      newNTree[NNode](nnkPostfix,
        newNIdent[NNode]("*"),
        newNIdent[NNode](en.name)
      )

    else:
      newNIdent[NNode](en.name)

  if en.pragma.len > 0:
    head = newNTree[NNode](
      nnkPragmaExpr,
      head,
      toNNode[NNode](en.pragma)
    )

  # echov en.pragma.len
  # echov toNNode[NNode](en.pragma)
  # echov head

  result = newNTree[NNode](
    nnkTypeDef,
    head,
    newEmptyNNode[NNode](),
    newNTree[NNode](nnkEnumTy, @[ newEmptyNNode[NNode]() ] & flds))

  when NNode is PNode:
    result.comment = en.docComment

  if standalone:
    result = newNTree[NNode](
      nnkTypeSection,
      result
    )


func parseEnumImpl*[NNode](en: NNode): EnumDecl[NNode] =
  case en.kind.toNNK():
    of nnkSym:
      when NNode is PNode:
        raiseImplementError(
          "Parsing of enum implementation from " &
          "Sym node is not yet support for PNode")

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
            raiseImplementError(&"#[ IMPLEMENT {impl.kind} ]#")

    of nnkTypeDef:
      result = parseEnumImpl(en[2])
      result.name = en[0].getStrVal

    of nnkEnumTy:
      for fld in en[1..^1]:
        result.values.add parseEnumField(fld)

    of nnkTypeSection:
      result = parseEnumImpl(en[0])

    else:
      raiseImplementError(&"#[ IMPLEMENT {en.kind} ]#")


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

  ProcDeclType* = enum
    ptkProc
    ptkFunc
    ptkIterator
    ptkConverter
    ptkMethod
    ptkTemplate
    ptkMacro

  ProcDecl*[NNode] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    declType*: ProcDeclType
    exported*: bool
    name*: string
    kind*: ProcKind
    signature*: NType[NNode] ## Signature of the proc as `ntProc` NType
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


func toNNode*[NNode](
  pr: ProcDecl[NNode], standalone: bool = true): NNode =
  if pr.signature.kind != ntkProc:
    argumentError:
      "Invalid proc declaration - signature type has kind of"
      "{pr.signature.kind}. Proc declaration location: {pr.iinfo}"


  let headSym = case pr.kind:
    of pkRegular:
      newNIdent[NNode](pr.name)

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

  # if

  let prdecl =
    case pr.declType:
      of ptkProc: nnkProcDef
      of ptkFunc: nnkFuncDef
      of ptkIterator: nnkIteratorDef
      of ptkConverter: nnkConverterDef
      of ptkMethod: nnkMethodDef
      of ptkTemplate: nnkTemplateDef
      of ptkMacro: nnkMacroDef

  result = newNTree[NNode](
    prdecl,
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
    result.comment = pr.docComment
    # debugecho result.comment


func newPProcDecl*(
    name:        string,
    args:        openarray[(string, NType[PNode])] = @[],
    rtyp:        Option[NType[PNode]]              = none(NType[PNode]),
    impl:        PNode                             = nil,
    exported:    bool                              = true,
    pragma:      Pragma[PNode]                     = Pragma[PNode](),
    genParams:   seq[NType[PNode]]                 = @[],
    iinfo:       LineInfo                          = defaultIInfo,
    declType:    ProcDeclType                      = ptkProc,
    docComment:  string                            = "",
    codeComment: string                            = "",
    kind: ProcKind                                 = pkRegular,
  ): ProcDecl[PNode] =

  result.name = name
  result.exported = exported
  result.signature = NType[PNode](
    kind: ntkProc,
    arguments: toNIdentDefs(args)
  )

  result.declType         = declType
  result.signature.pragma = pragma
  result.genParams        = genParams
  result.docComment       = docComment
  result.codeComment      = codeComment
  result.iinfo            = iinfo
  result.kind             = kind

  if rtyp.isSome():
    result.signature.setRtype rtyp.get()

  result.impl = impl

func newNProcDecl*(
    name:     string,
    args:        openarray[(string, NType[NimNode])] = @[],
    rtyp:        Option[NType[NimNode]]              = none(NType[NimNode]),
    impl:        NimNode                             = nil,
    exported:    bool                                = true,
    pragma:      Pragma[NimNode]                     = Pragma[NimNode](),
    iinfo:       LineInfo                            = defaultIInfo,
    declType:    ProcDeclType                        = ptkProc,
    docComment:  string                              = "",
    codeComment: string                              = "",
  ): ProcDecl[NimNode] =

  result.declType    = declType
  result.name        = name
  result.exported    = exported
  result.docComment  = docComment
  result.codeComment = codeComment
  result.iinfo       = iinfo


  result.signature = NType[NimNode](
    kind: ntkProc,
    arguments: toNIdentDefs(args)
  )

  result.signature.pragma = pragma
  if rtyp.isSome():
    result.signature.setRtype rtyp.get()

  result.impl = impl


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
    docComment*: string
    codeComment*: string

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

  ObjectDecl*[NNode, Annot] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

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


  NObjectBranch*[A] = ObjectBranch[NimNode, A]
  NObjectPathElem*[A] = ObjectPathElem[NimNode, A]
  NObjectField*[A] = ObjectField[NimNode, A]
  NObjectDecl*[A] = ObjectDecl[NimNode, A]
  NObjectPath*[A] = seq[NObjectPathElem[A]]

  PObjectDecl* = ObjectDecl[PNode, Pragma[PNode]]
  PObjectField* = ObjectField[PNode, Pragma[PNode]]

  # PragmaField*[Node] = ObjectField[Node, Pragma[Node]]
  # NPragmaField* = PragmaField[NimNode]

const noParseCb*: ParseCb[NimNode, void] = nil
const noParseCbPNode*: ParseCb[PNode, void] = nil

# import std/with

proc newPObjectDecl*(
  name: string,
  flds: seq[tuple[name: string, ftype: NType[PNode]]] = @[],
  exported: bool = true,
  annotate: PPragma = PPragma(),
  docComment: string = "",
  codeComment: string = "",
  genParams: seq[NType[PNode]] = @[],
  iinfo: LineInfo = defaultIInfo,
): PObjectDecl =


  result.name = newNType[PNode](name, genParams)
  result.docComment = docComment
  result.codeComment = codeComment
  result.iinfo = iinfo
  result.annotation = some annotate
  result.exported = exported


func addField*[N](
    obj: var ObjectDecl[N, Pragma[N]],
    name: string,
    cxtype: NType[N],
    docComment: string = "",
    codeComment: string = "",
    exported: bool = true
  ) =

  obj.flds.add PObjectField(
    isTuple: false,
    isKind: false,
    name: name,
    fldType: cxtype,
    docComment: codeComment,
    codeComment: codeComment,
    exported: exported
  )

#=============================  Predicates  ==============================#
func markedAs*(fld: NObjectField[NPragma], str: string): bool =
  fld.annotation.getElem(str).isSome()

#===============================  Getters  ===============================#

# ~~~~ each field mutable ~~~~ #

func eachFieldMut*[NNode, A](
  obj: var ObjectDecl[NNode, A],
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
  obj: var ObjectDecl[NNode, A],
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
  obj: var ObjectDecl[NNode, A], cb: (var Option[A] ~> void)): void =
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
  obj: ObjectDecl[NNode, A],
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
  obj: ObjectDecl[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in object, recurisively.
  for fld in items(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)

# ~~~~ each alternative in case object ~~~~ #

func eachCase*[A](
  fld: NObjectField[A], objId: NimNode, cb: (NObjectField[A] ~> NimNode)): NimNode =
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
  objId: NimNode, obj: NObjectDecl[A], cb: (NObjectField[A] ~> NimNode)): NimNode =
  ## Recursively generate case statement for object. `objid` is and
  ## identifier for object - case statement will use `<objid>.<fldId>`.
  ## `obj` is a description for structure. Callback `cb` will be executed
  ## on all fields - both `isKind` or not.

  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachCase(objid, cb)

func eachParallelCase*[A](
  fld: NObjectField[A], objId: (NimNode, NimNode),
  cb: (NObjectField[A] ~> NimNode)): NimNode =
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
  objid: (NimNode, NimNode), obj: NObjectDecl[A], cb: (NObjectField[A] ~> NimNode)): NimNode =
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
  obj: ObjectDecl[Node, A], cb: (Option[A] ~> void)): void =

  cb(obj.annotation)

  for fld in items(obj.flds):
    cb(fld.annotation.get())
    if fld.isKind:
      for branch in items(fld.branches):
        branch.eachAnnot(cb)


# ~~~~ Each path in case object ~~~~ #
func eachPath*[A](
  fld: NObjectField[A], self: NimNode, parent: NObjectPath[A],
  cb: ((NObjectPath[A], seq[NObjectField[A]]) ~> NimNode)): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(self, ident fld.name))
    for branch in fld.branches:
      var branchBody = newStmtList()
      let nobranch = (fld.withIt do: it.branches = @[])
      let thisPath =
        if branch.isElse:
          parent & @[NObjectPathElem[A](
            isElse: true, kindField: nobranch, notOfValue: branch.notOfValue)]
        else:
          parent & @[NObjectPathElem[A](
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
  obj: NObjectDecl[A], cb: ((NObjectPath[A], seq[NObjectField[A]]) ~> NimNode)): NimNode =
  ## Visit each group of fields in object described by `obj` and
  ## generate case statement with all possible object paths. Arguments
  ## for callback - `NObjectPath[A]` is a sequence of kind field values that
  ## *must be active in order for execution to reach this path* in
  ## case statement. Second argument is a list of fields that can be
  ## accessed at that path.
  ## TODO:DOC add example

  result = newStmtList cb(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.eachPath(self, @[], cb)


func onPath*[A](self: NimNode, path: NObjectPath[A]): NimNode =
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



func toNNode*[NNode, A](
  obj: ObjectDecl[NNode, A], annotConv: A ~> NNode): NNode =

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
  obj: ObjectDecl[NNode, PRagma[NNode]], standalone: bool = false): NNode =
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

func toNimNode*(obj: NObjectDecl[NPragma]): NimNode =
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
    case kind*: ObjKind
      of okConstant:
        constType*: string ## Type of the value
        strlit*: string ## Value representation in string form
      of okSequence:
        itemType*: string ## Type of the sequence item
        valItems*: seq[ObjTree] ## List of values
      of okTable:
        keyStyling* {.requiresinit.}: PrintStyling
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

            argumentError:
              "Cannot get field name '{path[0].name}'"
              "from object - no such field found"

          else:
            argumentError:
              "Cannot get field name '{path[0].name}'"
              "from object with unnamed fields"

    of okConstant:
      if path.len > 1:
        argumentError:
          "Attempt to access subelements of constant value at path {path}"

      else:
        return obj
    of okSequence:
      if path.len == 0:
        return obj

      if not path[0].isIdx:
        argumentError:
          "Cannot access sequence elements by name, path {path}"
          "starts with non-index"

      elif path.len == 1:
        return obj.valItems[path[0].idx]

      else:
        return obj.valItems[path[0].idx].getAtPath(path[1..^1])

    else:
      raiseImplementError("")




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
#*************************************************************************#
#***********************  Common declaration type  ***********************#
#*************************************************************************#
type
  NimDeclKind* = enum
    nekPasstroughCode
    nekProcDecl
    nekObjectDecl
    nekEnumDecl
    nekAliasDecl
    nekMultitype

  AliasDecl*[N] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    isDistinct*: bool
    isExported*: bool
    newType*: Ntype[N]
    oldType*: Ntype[N]

  NimTypeDeclKind = enum
    ntdkEnumDecl
    ntdkObjectDecl
    ntdkAliasDecl

  NimTypeDecl*[N] = object
    case kind*: NimTypeDeclKind:
      of ntdkEnumDecl:
        enumDecl*: EnumDecl[N]
      of ntdkObjectDecl:
        objectDecl*: ObjectDecl[N, Pragma[N]]
      of ntdkAliasDecl:
        aliasDecl*: AliasDecl[N]

  NimDecl*[N] = object
    case kind*: NimDeclKind
      of nekProcDecl:
        procdecl*: ProcDecl[N]
      of nekEnumDecl:
        enumdecl*: EnumDecl[N]
      of nekObjectDecl:
        objectdecl*: ObjectDecl[N, Pragma[N]]
      of nekAliasDecl:
        aliasDecl*: AliasDecl[N]
      of nekPasstroughCode:
        passthrough*: N
      of nekMultitype:
        typedecls*: seq[NimTypeDecl[N]]

  PNimTypeDecl* = NimTypeDecl[Pnode]

  PNimDecl* = NimDecl[Pnode]
  PAliasDecl* = NimDecl[PNode]
  NAliasDecl* = NimDecl[NimNode]

  AnyNimDecl[N] =
          ProcDecl[N] |
          AliasDecl[N] |
          ProcDecl[N] |
          ObjectDecl[N, Pragma[N]] |
          EnumDecl[N] |
          AliasDecl[N] |
          NimTypeDecl[N]

func `==`*[N, A](a, b: ObjectBranch[N, A]): bool =
  a.isElse == b.isElse and
  a.flds == b.flds and
  a.annotation == b.annotation and
  (
    case a.isElse:
      of true: a.notOfValue == b.notOfValue
      of false: a.ofValue == b.ofValue
  )

func `==`*[N](a, b: EnumField[N]): bool =
  a.kind        == b.kind        and
  a.docComment  == b.docComment  and
  a.codeComment == b.codeComment and
  a.name        == b.name        and
  a.value       == b.value       and
  (
    case a.kind:
      of efvNone: true
      of efvIdent: a.ident == b.ident
      of efvOrdinal: a.ordVal == b.ordVal
      of efvString: a.strval == b.strval
      of efvOrdString: a.ordStr == b.ordStr
  )

func `==`*(a, b: RTimeOrdinal): bool =
  a.kind == b.kind and
  (
    case a.kind:
      of rtokInt: a.intVal == b.intVal
      of rtokBool: a.boolVal == b.boolVal
      of rtokChar: a.charVal == b.charVal
  )


func `==`*[N](a, b: NimTypeDecl[N]): bool =
  a.kind == b.kind and (
    case a.kind:
      of ntdkEnumDecl: a.enumDecl == b.enumDecl
      of ntdkObjectDecl: a.objectDecl == b.objectDecl
      of ntdkAliasDecl: a.aliasDecl == b.aliasDecl
  )

func `==`*[N](a, b: NimDecl[N]): bool =
  a.kind == b.kind and (
    case a.kind:
      of nekProcDecl: a.procdecl == b.procdecl
      of nekEnumDecl: a.enumdecl == b.enumdecl
      of nekObjectDecl: a.objectdecl == b.objectdecl
      of nekAliasDecl: a.aliasdecl == b.aliasdecl
      of nekPasstroughCode: a.passthrough == b.passthrough
      of nekMultitype:
        a.typedecls.len == b.typedecls.len and
        zip(a.typedecls, b.typedecls).allOfIt(it[0] == it[1])
  )


func toNNode*[N](entry: NimDecl[N], standalone: bool = true): N =
  case entry.kind:
    of nekProcDecl:
      return toNNode[N](entry.procdecl)
    of nekEnumDecl:
      return toNNode[N](entry.enumdecl, standalone = standalone)
    of nekObjectDecl:
      return toNNode[N](entry.objectdecl, standalone = standalone)
    of nekAliasDecl:
      return toNNode[N](entry.aliasDecl)
    of nekPasstroughCode:
      return entry.passthrough
    of nekMultitype:
      result = newNTree[N](nnkTypeSection)
      for elem in entry.typedecls:
        case elem.kind:
          of ntdkEnumDecl:
            result.add toNNode[N](elem.enumDecl, standalone = false)
          of ntdkObjectDecl:
            result.add toNNode[N](elem.objectDecl, standalone = false)
          of ntdkAliasDecl:
            result.add toNNode[N](elem.aliasDecl, standalone = false)



func toNimTypeDecl*[N](odc: ObjectDecl[N, Pragma[N]]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkObjectDecl, objectdecl: odc)

func toNimTypeDecl*[N](adc: AliasDecl[N]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkAliasDecl, aliasDecl: adc)

func toNimTypeDecl*[N](edc: EnumDecl[N]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkEnumDecl, enumdecl: edc)

func toNimTypeDecl*[N](entry: NimDecl[N]): NimTypeDecl[N] =
  case entry.kind:
    of nekEnumDecl:
      return toNimTypeDecl[N](entry.enumdecl)
    of nekObjectDecl:
      return toNimTypeDecl[N](entry.objectdecl)
    of nekAliasDecl:
      return toNimTypeDecl[N](entry.aliasDecl)
    else:
     raiseAssert(&"Cannot convert to NimTypeDecl for kind {entry.kind}")

func toNimDecl*[N](prd: ProcDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekProcDecl, procdecl: prd)

func toNimDecl*[N](odc: ObjectDecl[N, Pragma[N]]): NimDecl[N] =
  NimDecl[N](kind: nekObjectDecl, objectdecl: odc)

func toNimDecl*[N](adc: AliasDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekAliasDecl, aliasDecl: adc)

func toNimDecl*[N](edc: EnumDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekEnumDecl, enumdecl: edc)

func toNimDecl*[N](decl: N): NimDecl[N] =
  NimDecl[N](kind: nekPasstroughCode, passthrough: decl)

func toNimDecl*[N](decl: seq[NimTypeDecl[N]]): NimDecl[N] =
  NimDecl[N](kind: nekMultitype, typedecls: decl)

func add*[N](declSeq: var seq[NimDecl[N]], decl: AnyNimDecl[N]) =
  declSeq.add toNimDecl(decl)

# func add*[N](declSeq: var seq[NimDecl[N]], decl: N) =
#   declSeq.add NimDecl(kind: nekPasstroughCode, passthrough: decl)

func newAliasDecl*[N](
    t1, t2: NType[N],
    isDistinct: bool = true,
    isExported: bool = true,
    iinfo:     LineInfo                          = defaultIInfo,
    docComment: string = "",
    codeComment: string = "",
  ): AliasDecl[N] =

  AliasDecl[N](
    oldType: t2,
    newType: t1,
    isExported: isExported,
    isDistinct: isDistinct,
    iinfo: iinfo,
    docComment: docComment,
    codeComment: codeComment
  )


func `$`*[N](nd: NimDecl[N]): string =
  {.cast(noSideEffect).}:
    when N is NimNode:
      $toNNode(nd)
    else:
      hnimast.`$`(toNNode(nd))

func toNNode*[N](alias: AliasDecl[N], standalone: bool = true): N =
  let pr = (alias.isDistinct, alias.isExported)
  let
    aType = toNNode[N](alias.newType)
    bType = toNNode[N](alias.oldType)

  if pr == (false, false):
    result = newNTree[N](nnkTypeDef, aType, newEmptyNNode[N](), bType)
  elif pr == (true, false):
    result = newNTree[N](
      nnkTypeDef,
      aType,
      newEmptyNNode[N](),
      newNTree[N](nnkDistinctTy, bType)
    )
  elif pr == (false, true):
    result = newNTree[N](
      nnkTypeDef,
      newNTree[N](nnkPostfix, newNIdent[N]("*"), aType),
      newEmptyNNode[N](),
      bType
    )
  elif pr == (true, true):
    result = newNTree[N](
      nnkTypeDef,
      newNTree[N](nnkPostfix, newNIdent[N]("*"), aType),
      newEmptyNNode[N](),
      newNTree[N](nnkDistinctTy, bType)
    )

  if standalone:
    result = newNTree[N](nnkTypeSection, result)


func `$`*[N](nd: seq[NimDecl[N]]): string =
  mapIt(nd, $it).join("\n")

proc `iinfo=`*[N](nd: var NimDecl[N], iinfo: LineInfo) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.iinfo = iinfo
    of nekEnumDecl:       nd.enumdecl.iinfo = iinfo
    of nekObjectDecl:     nd.objectdecl.iinfo = iinfo
    of nekAliasDecl:      nd.aliasdecl.iinfo = iinfo
    of nekMultitype:      discard
    of nekPasstroughCode: discard


proc addCodeComment*[N](nd: var AnyNimDecl[N], comm: string) =
  nd.codeComment &= comm

proc addCodeComment*[N](nd: var NimDecl[N], comm: string) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.codeComment &= comm
    of nekEnumDecl:       nd.enumdecl.codeComment &= comm
    of nekObjectDecl:     nd.objectdecl.codeComment &= comm
    of nekAliasDecl:      nd.aliasdecl.codeComment &= comm
    of nekMultitype:      discard
    of nekPasstroughCode: discard
