import hast_common
import compiler/[ast]
import std/[macros, options, tables, sequtils]
import hmisc/helpers

type
  Pragma*[N] = object
    ## Body of pragma annotation;
    kind*: ObjectAnnotKind ## Position in object - no used when
                           ## generatic functions etc.
    elements*: seq[N] ## List of pragma elements. For annotation
                         ## like `{.hello, world.}` this will contain
                         ## `@[hello, world]`

  NPragma* = Pragma[NimNode] ## Pragma with nim node
  PPragma* = Pragma[PNode] ## Pragma with pnode

#===============================  Getters  ===============================#
func indexOf*[N](pragma: PRagma[N], name: string): int =
  result = -1
  for idx, elem in pairs(pragma.elements):
    case elem.kind:
      of nnkIdent:
        if elem.eqIdent(name):
          return idx

      of nnkCall:
        if elem[0].eqIdent(name):
          return idx

      else:
        raiseImplementKindError(elem)


func getElem*(pragma: NPragma, name: string): Option[NimNode] =
  ## Get element named `name` if it is present.
  ## `getElem({.call.}, "call") -> call`
  ## `getElem({.call(arg).}, "call") -> call(arg)`
  let idx = pragma.indexOf(name)
  if idx != -1:
    return some pragma.elements[idx]

func hasElem*[N](pragma: Pragma[N], name: string): bool =
  pragma.indexOf(name) != -1

func getElem*(optPragma: Option[NPragma], name: string): Option[NimNode] =
  ## Get element from optional annotation
  if optPragma.isSome():
    return optPragma.get().getElem(name)

func removeElement*[N](pragma: var Pragma[N], name: string) =
  var idx = pragma.indexOf(name)
  if idx != -1:
    pragma.elements.delete(idx)

func len*[N](pragma: Pragma[N]): int =
  pragma.elements.len

func add*[N](pragma: var Pragma[N], node: N) =
  pragma.elements.add node

func clear*[N](pragma: var PRagma[N]) =
  pragma.elements = @[]

#============================  constructors  =============================#
func newNNPragma*[N](): Pragma[N] = discard

func parsePragma*[N](node: N): Pragma[N] =
  case toNNK(node.kind):
    of nnkPragma:
      for entry in items(node):
        result.elements.add entry


    of nnkPragmaExpr:
      result = parsePragma(node[1])

    else:
      raiseUnexpectedKindError(node, node.treeRepr())


func parseSomePragma*[N](node: N): Option[Pragma[N]] =
  case node.kind.toNNK():
    of nnkIdent, nnkSym:
      discard

    of nnkPostfix:
      return parseSomePragma(node[1])

    of nnkPragmaExpr:
      return some parsePragma(node[1])

    else:
      raiseImplementKindError(node, node.treeRepr())


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

func toNNode*[N](pragma: Pragma[N]): N =
  ## Convert pragma to `N`. If pragma has no elements empty node
  ## (`nnkEmptyNode`) will be returned.
  if pragma.elements.len == 0:
    newEmptyNNode[N]()
  else:
    newTree[N](nnkPragma, pragma.elements)


func toNimNode*(pragma: NPragma): NimNode =
  ## Convert pragma to nim node. If pragma contains no elements
  ## `EmptyNode` is generated.
  toNNode[NimNode](pragma)



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
