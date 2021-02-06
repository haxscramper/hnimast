import std/[options, sequtils, strutils, strformat, sugar]
import hmisc/helpers
import pragmas, hast_common

type
  NTypeKind* = enum
    ## Type kind
    ntkNone
    ntkIdent ## Generic identifier, possibly with parameters: `G[A, C]`
    ntkProc ## Procedure type: `proc(a: int, b: float) {.cdecl.}`
    ntkRange ## Range type: `range[1..10]`
    ntkGenericSpec ## Constrained generic: `A: B | C | D`
    ntkAnonTuple ## Unnaped tuple: `(int, string)`
    ntkNamedTuple ## Named tuple: `tuple[name: string, value: int]`
    ntkVarargs ## `varargs[Type, Converter]`
    ntkValue ## Value as type argument
    ntkCurly ## Term rewriting patterns

  NType*[NNode] = object
    ## Representation of generic nim type;
    declNode*: Option[NNode]
    module*: Option[NNode]
    case kind*: NTypeKind
      of ntkIdent, ntkGenericSpec, ntkAnonTuple:
        head*: string ## Type name `head[...]` or `head: .. | ..`
        genParams*: seq[NType[NNode]] ## Generic parametrs for procs,
        ## alternatives for constrained types or anonymous tuple types.
        ##
        ## - `head[T0, T1]` :: Regular generic type
        ## - `T0 | T1` :: Constrained generic alternatives
        ## - `(T0, T1)` :: Anonymous tuples

      of ntkProc, ntkNamedTuple:
        rType*: Option[SingleIt[NType[NNode]]] ## Optional return type
        arguments*: seq[NIdentDefs[NNode]] ## Sequence of argument identifiers
        pragma*: Pragma[NNode] ## Pragma annotation for proc

      of ntkRange:
        rngStart*, rngEnd*: NNode

      of ntkVarargs:
        vaTypeIt: SingleIt[NType[NNode]]
        vaConverter*: Option[NNode]

      of ntkValue:
        value*: NNode

      of ntkCurly:
        curlyHead: NNode
        curlyArgs: seq[NNode]

      of ntkNone:
        discard

  # PType* = NType[PNode]

  NVarDeclKind* = enum
    ## Kind of variable declaration
    # TODO static parameters?
    nvdLet
    nvdVar
    nvdConst

  NIdentDefs*[NNode] = object
    ## Identifier declaration
    idents*: seq[NNode]
    # varname* {.deprecated.}: string ## Variable name
    kind*: NVarDeclKind
    vtype*: NType[NNode] ## Variable type
    value*: Option[NNode] ## Optional initialization value

  PIdentDefs* = NIdentDefs[PNode]

#==============================  Accessors  ==============================#
func arg*[NNode](t: NType[NNode], idx: int): NIdentDefs[NNode] =
  assert t.kind == ntkProc
  t.arguments[idx]

func `vaType=`*[N](t: var NType[N], vat: NType[N]) =
  t.vaTypeIt = newIt(vat)

func vaType*[N](t: NType[N]): NType[N] = getIt(t.vaTypeIt)

func `returnType=`*[N](t: var NType[N], val: NType[N]) =
  t.rType = some(newIt(val))

func returnType*[N](t: NType[N]): Option[NType[N]] =
  if t.rType.isSome():
    result = some(t.rtype.get().getIt())


#=============================  Predicates  ==============================#
func `==`*(l, r: NType): bool =
  l.kind == r.kind and (
    case l.kind:
      of ntkIdent, ntkGenericSpec, ntkAnonTuple:
        (l.head == r.head) and (l.genParams == r.genParams)

      of ntkProc, ntkNamedTuple:
        (l.rType == r.rType) and (l.arguments == r.arguments)

      of ntkRange:
        l.rngStart == r.rngStart and
        l.rngEnd == r.rngEnd

      of ntkVarargs:
        l.vaTypeIt == r.vaTypeIt and
        l.vaConverter == r.vaConverter

      of ntkValue:
        l.value == r.value

      of ntkCurly:
        l.curlyHead == r.curlyHead and
        l.curlyArgs == r.curlyArgs

      of ntkNone:
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
    result.add NIdentDefs[NNode](
      idents: @[newNIdent[NNode](name)], vtype: atype)

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
    result.add NIdentDefs[NNode](
      idents: @[newNIdent[NNode](name)],
      vtype: atype,
      kind: nvd
    )



func toNFormalParam*[NNode](nident: NIdentDefs[NNode]): NNode

func toNNode*[NNode](nident: NIdentDefs[NNode]): NNode =
  toNFormalParam(nident)

func add*[NNode](ntype: var NType[NNode], nt: NType[NNode]) =
  if ntype.head in ["ref", "ptr", "var"]:
    ntype.genParams[0].add nt
  else:
    ntype.genParams.add nt

func add*[NNode](ntype: var NType[NNode], nt: varargs[NType[NNode]]) =
  for arg in nt:
    ntype.add arg

func contains*(arg: set[NimNodeKind], pkind: TNodeKind): bool =
  pkind.toNNK() in arg

func toNNode*[NNode](ntype: NType[NNode]): NNode =
  ## Convert to NNode
  case ntype.kind:
    of ntkProc:
      result = newNTree[NNode](nnkProcTy)

      var renamed: seq[NIdentDefs[NNode]]
      var cnt = 0
      for arg in ntype.arguments:
        var arg = arg
        for name in mitems(arg.idents):
          if name.kind in {nnkEmpty}:
            name = newNIdent[NNode]("arg" & $cnt)


          inc cnt

        renamed.add arg

      result.add newNTree[NNode](
        nnkFormalParams,
        @[
          if ntype.rtype.isSome():
            ntype.rtype.get().getIt().toNNode()
          else:
            newEmptyNNode[NNode]()
        ] & renamed.mapIt(it.toNFormalParam()))

      result.add toNNode(ntype.pragma)

    of ntkRange:
      result = newNTree[NNode](
        nnkBracketExpr,
        newNIdent[NNode]("range"),
        newNTree[NNode](
          nnkInfix,
          newNIdent[NNode](".."),
          ntype.rngStart,
          ntype.rngEnd
        )
      )

    of ntkCurly:
      result = newNTree[NNode](nnkCurlyExpr)
      result.add ntype.curlyHead
      for it in ntype.curlyArgs:
        result.add it

    of ntkNone:
      result = newEmptyNNode[NNode]()

    of ntkValue:
      result = ntype.value

    of ntkAnonTuple:
      result = newNTree[NNode](nnkPar)
      for param in items(ntype.genParams):
        result.add toNNode[NNode](param)

    of ntkNamedTuple:
      result = newNTree[NNode](nnkBracketExpr, newNIdent[NNode]("tuple"))
      for field in items(ntype.arguments):
        result.add toNNode[NNode](field)

    of ntkGenericSpec:
      var buf: seq[NNode]
      for entry in items(ntype.genParams):
        buf.add toNNode[NNode](entry)

      result = foldInfix(buf, "|")

    of ntkVarargs:
      result = newNTree[NNode](nnkBracketExpr, newNIdent[NNode]("varargs"))
      result.add toNNode[NNode](ntype.vaType)
      if ntype.vaConverter.isSome():
        result.add ntype.vaConverter.get()

    of ntkIdent:
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

        elif ntype.head == "nil":
          result = newNTree[NNode](nnkNilLit)

        else:
          result = newNTree[NNode](
            nnkBracketExpr, newNIdent[NNode](ntype.head))
          for param in ntype.genParams:
            result.add toNNode[NNode](param)



proc toNNode*[N](ntype: Option[NType[N]]): N =
  if ntype.isNone():
    newNTree[N](nnkEmpty)

  else:
    toNNode[N](ntype.get())

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

  result = newNTree[NNode](nnkIdentDefs, nident.idents & @[typespec])

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

func parseNidentDefs*[N](node: N): NIdentDefs[N]
func newNTypeNNode*[NNode](node: NNode): NType[NNode] =
  # REFACTOR rename to `parseNType`
  ## Convert type described in `NimNode` into `NType`
  case node.kind.toNNK():
    of nnkBracketExpr:
      let head = node[0].getStrVal()
      if head == "range":
        result = NType[NNode](
          kind: ntkRange, rngStart: node[1][1], rngEnd: node[1][2])

      elif head == "varargs":
        result = NType[NNode](kind: ntkVarargs)
        result.vaType = newNTypeNNode(node[1])
        if node.len == 3:
          result.vaConverter = some(node[2])

      else:
        when NNode is PNode:
          result = newNType(head, node.sons[1..^1].mapIt(newNTypeNNode(it)))

        else:
          result = newNType(head, node[1..^1].mapIt(newNTypeNNode(it)))



    of nnkSym:
      result = newNNType[NNode](node.getStrVal())

    of nnkIdent:
      when NNode is PNode:
        result = newPType(node.ident.s)

      else:
        result = newNType(node.getStrVal())

    of nnkPar, nnkTupleConstr:
      result = NType[NNode](kind: ntkAnonTuple)
      for subnode in items(node):
        result.genParams.add newNTypeNNode(subnode)

    of nnkRefTy: result = newNType("ref", @[newNTypeNNode(node[0])])
    of nnkPtrTy: result = newNType("ptr", @[newNTypeNNode(node[0])])
    of nnkVarTy: result = newNType("var", @[newNTypeNNode(node[0])])

    of nnkObjectTy: result = newNNType[NNode]("object")
    of nnkTupleClassTy: result = newNNType[NNode]("tuple")
    of nnkIteratorTy: result = newNNType[NNode]("iterator")

    of nnkCurlyExpr: result = NType[NNode](
      kind: ntkCurly,
      curlyHead: node[0],
      curlyArgs: toSeq(node[1..^1])
    )

    of nnkCommand:
      result = newNType(node[0].getStrVal(), @[newNTypeNNode(node[1])])

    of nnkInfix:
      if node[0].getStrVal() in ["|", "or"]:
        result = NType[NNode](
          kind: ntkGenericSpec,
          genParams: node.flattenInfix("|").mapIt(newNTypeNNode(it))
        )

      elif node[0].getStrVal() in [".."]:
        result = NType[NNode](kind: ntkRange, rngStart: node[1], rngEnd: node[2])

      else:
        result = NType[NNode](kind: ntkValue, value: node[0])
        # raiseArgumentError(
        #   "Unexpected infix node for type: " & toShow(node[0])
        # )

    of nnkCall:
      if node[0].getStrVal() in ["type", "sink", "owned", "out"]:
        result = newNType(node[0].getStrVal(), @[newNTypeNNode(node[1])])

      elif node[0].getStrVal() in ["[]"]:
        result = newNType(node[1].getStrVal(), @[newNTypeNNode(node[2])])

      else:
        raiseArgumentError(
          "Unexpected call node for type: " & toShow(node[0]))

    of nnkPrefix:
      if node[0].getStrVal() in ["not"]:
        result = newNType("not", @[newNTypeNNode(node[1])])

      else:
        raiseArgumentError(
          "Unexpected prefix node for type: " & toShow(node[0]))

    of nnkNilLit:
      result = newNType("nil", newSeq[NType[NNode]]())

    of nnkTupleTy:
      result = NType[NNode](kind: ntkNamedTuple)
      for field in items(node):
        result.arguments.add parseNIdentDefs(field)

    of nnkProcTy:
       result = NType[NNode](kind: ntkProc)
       for arg in items(node[0][1..^1]):
         result.arguments.add parseNIdentDefs(arg)

       if node[0][0].kind != nnkEmpty:
         result.returnType = newNType(node[0][0])

       result.pragma = parsePragma(node[1])

    of nnkIntLit:
      result = NType[NNode](kind: ntkValue, value: node)

    of nnkEnumTy:
      result = newNNType[NNode]("enum")

    of nnkDotExpr:
      result = newNTypeNNode(node[1])
      result.module = some(node[0])

    else:
      raiseImplementError(
        &"Implement NType conversion for '{node.kind}' '" &
          node.toStrLit().getStrVal() & "' " &
          $node.getInfo()
      )

  result.declNode = some(node)

func newNType*(impl: NimNode): NType[NimNode] =
  ## Convert type described in `NimNode` into `NType`
  newNTypeNNode(impl)

# proc newNType*(typ: PType): NType[PNode] =


func newNType*(impl: PNode): NType[PNode] =
  ## Convert type described in `NimNode` into `NType`
  newNTypeNNode(impl)

func newVarDecl*(name: string, vtype: NType,
                kind: NVarDeclKind = nvdLet): NIdentDefs[NimNode] =
  ## Declare varaible `name` of type `vtype`
  # TODO initalization value, pragma annotations and `isGensym`
  # parameter
  NIdentDefs[NimNode](idents: @[newNIdent[NimNode](name)],
                      kind: kind, vtype: vtype)

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

func toNTypeAst*[T](): NType =
  let str = $typeof(T)
  let expr = parseExpr(str)


func parseNidentDefs*[N](node: N): NIdentDefs[N] =
  if node.kind.toNNK() in {nnkSym, nnkIdent}:
    result.idents.add node
    return

  for arg in node[0..^3]:
    result.idents.add arg

  if node[^2].kind != nnkEmpty:
    result.vtype = newNType(node[^2])

  else:
    # FIXME just putting `N` for `NType` results in 'object constructor
    # needs an object type' that I can't understand at all.
    when node is PNode:
      result.vtype = NType[PNode](kind: ntkNone)

    else:
      result.vtype = NType[NimNode](kind: ntkNone)

  if node[^1].kind != nnkEmpty:
    result.value = some(node[^1])




#===========================  Pretty-printing  ===========================#
func `$`*[NNode](nt: NType[NNode]): string =
  ## Convert `NType` to texual representation
  case nt.kind:
    of ntkNone:
      result = ""

    of ntkValue:
      {.cast(noSideEffect).}:
        result = $nt.value

    of ntkVarargs:
      result = "varargs[" & $nt.vaType
      if nt.vaConverter.isSome():
        {.cast(noSideEffect).}:
          result &= ", " & $nt.vaConverter.get()

      result &= "]"

    of ntkCurly:
      {.cast(noSideEffect).}:
        result = $nt.curlyHead & "{" &
          nt.curlyArgs.mapIt($it).join(", ") & "}"

    of ntkIdent:
      if nt.genParams.len > 0:
        result = nt.head & "[" & nt.genParams.mapIt($it).join(", ") & "]"

      else:
        result = nt.head

    of ntkGenericSpec:
      if nt.genParams.len > 0:
        result = nt.head & ": " & nt.genParams.mapIt($it).join(" | ")

      else:
        result = nt.head

    of ntkProc:
      {.cast(noSideEffect).}:
        let rtype: string = nt.rtype.getSomeIt($it & ": ", "")
        let pragma: string =
          if nt.pragma.len > 0:
            toString(nt.pragma.toNNode()) & " "

          else:
            ""

        let args: string = nt.arguments.mapIt($it).join(", ")

        result = &"proc ({args}){pragma}{rtype}"

    of ntkAnonTuple:
      result = nt.genParams.mapIt($it).join(", ").wrap("()")

    of ntkNamedTuple:
      let args = collect(newSeq):
        for arg in nt.arguments:
          {.cast(noSideEffect).}:
            arg.idents.mapIt($it).join(", ") & ": " & $arg.vtype

      result = args.join(", ").wrap(("tuple[", "]"))

    of ntkRange:
      {.cast(noSideEffect).}:
        result = $nt.rngStart & ".." &  $nt.rngEnd

func newCallNode*(
  dotHead: NimNode, name: string,
  args: seq[NimNode], genParams: seq[NType[NimNode]] = @[]): NimNode {.deprecated.} =
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
