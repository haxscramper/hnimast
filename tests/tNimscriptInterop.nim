import ./vm_common, ./common_test

import
  compiler/[nimeval, llstream, ast, renderer, vmdef, vm]

import
  hnimast/[compiler_aux, gencode]

import
  hnimast,
  hnimast/store_decl,
  hmisc/other/[oswrap],
  hmisc/[base_errors, hdebug_misc]

import
  std/[tables]

starthaxComp()

proc fromVm*(t: var char, node: PNode) =
  assertKind(node, nkIntKinds)
  t = node.intVal.char

proc fromVm*[P: proc](p: var P, node: PNode) =
  # I suppose it is possible to pass procedure implementaitons across
  # interpreter boundary, but it would require whole new level of hacking
  # around.
  p = nil

proc fromVm*(p: var pointer, node: PNode) =
  # This is an interesting one - I'm pretty sure it would be possible to
  # get this data from VM (since it supports some kind of symbolic pointer
  # implementation). Alteritantively - if pointer is used as reference to
  # some opaque data blob that is handled only by underlying
  # implementation, we can just copy it as is.
  p = nil

proc fromVm*(t: var bool, node: PNode) =
  assertKind(node, nkIntKinds)
  t = (node.intVal != 0)

proc fromVm*[E: enum](e: var E, node: PNode) =
  assertKind(node, nkIntKinds)
  e = E(node.intVal)

proc fromVm*(t: var int, node: PNode) =
  assertKind(node, nkIntKinds)
  t = node.intVal.int

proc fromVm*(t: var float, node: PNode) =
  assertKind(node, nkFloatKinds)
  t = node.floatVal

proc fromVm*(t: var string, node: PNode) =
  assertKind(node, nkStringKinds)
  t = node.strVal

genNewProcForType(VmVariant)

macro fromVmImpl*(obj: typedesc, vmNode: PNode): untyped =
  let
    vmNode = copyNimNode(vmNode)
    impl = getObjectStructure(obj)
    field = newIdent("field")
    res = newIdent("res")
    constr = impl.newCall(genericParams(obj))
    nameSwitch = newDot(newBracketExpr(field, 0), ident("getStrVal"))

  proc vmget(idx: int): NimNode =
    newBracketExpr(newBracketExpr(vmNode, idx), 1)


  var
    declareKind = newStmtList()
    loadKind = newStmtList()

  var fieldIdx: Table[string, int]

  block:
    var idx = 1
    for implField in iterateFields(impl):
      fieldIdx[implField.name] = idx
      inc idx

  # Collect kind field variables and their respective unpack positions.
  for implField in iterateFields(impl):
    let fieldGet = vmget(fieldIdx[implField.name])
    if implField.isKind:
      let
        accs = newDot(res, newIdent(implField.name))
        name = newIdent(implField.name)

      declareKind.add newVar(implField.name, implField.fieldType)
      loadKind.add newCall("fromVm", name, fieldGet)

      constr.add newExprEq(name, name)

  # Construct nested case for unpacking other fields
  let unpackCase = impl.mapItGroups(res.newDot(path[^1].name)):
    var mapRes = newStmtList()
    for implField in group:
      if not implField.isKind:
        let fieldGet = vmget(fieldIdx[implField.name])
        let asgn =
          if implField.isExported:
            # Exported fields can be accessed directly, so we call `fromVm`
            # on them
            newCall("fromVm", newDot(res, ident(implField.name)), fieldGet)

          else:
            # Private fields have to be accessed using hack with mutable
            # `fieldPairs`.
            res.withPrivate(
              implField.name,
              newIdent("tmp"),
              newCall("fromVm", newIdent("tmp"), fieldGet),
              isRef = impl.isRef
            )

        mapRes.add asgn

    mapRes

  result = quote do:
    block:
      `declareKind`
      `loadKind`

      var `res` = `constr`
      `unpackCase`
      `res`

  echo result.repr

proc fromVm*[T: object or ref object](t: var T, node: PNode) =
  t = fromVmImpl(T, node)


proc toVm*(f: float | int | string | char | BiggestInt): PNode = newPLit(f)

proc toVm*[T: object](obj: T): PNode =
  result = nkObjConstr.newTree()
  result.add nkEmpty.newTree()
  for name, field in fieldPairs(obj):
    result.add nkExprColonExpr.newTree(
      newPIdent(name), toVm(field))


proc main() =
  let stdlib = getStdPath()

  let intr = createInterpreter(
    "scriptname.nims",
    toSeqString(@[
      stdlib,
      stdlib / "pure",
      stdlib / "core",
      currentSourceDir()
  ]))

  intr.implementRoutine("*", "scriptname", "readVmVariant",
    proc(args: VmArgs) {.nimcall, gcsafe.} =
      echo "Reading vm variant"
      let data = args.getNode(0)
      echov data.treeRepr()
      var parsed: VmVariant
      fromVm(parsed, data)
      echov parsed[]
  )

  intr.implementRoutine("*", "scriptname", "dump",
    proc(args: VmArgs) {.nimcall, gcsafe.} =
      let slot = args.slots[args.rb + 1]
      case slot.kind:
        of rkNode:
          let data = args.getNode(0)
          # echo data.treeRepr()
          args.setResult data

        of rkFloat:
          let flt = args.getFloat(0)
          args.setResult flt.toVm()

        of rkInt:
          let intv = args.getInt(0)
          args.setResult intv.toVm()

        else:
          assert false, $slot.kind
  )

  intr.evalScript(llStreamOpen(
    readFile(currentSourceDir() /. "vm_common.nim") & """
import std/tables

proc dump[T](arg: T): T = discard
proc readVmVariant(arg: VmVariant) = discard

# for name, value in fieldPairs(VmVariant()):
#   echo "> ", name

let data = VmVariant(
  kind: vmkSecond,
  field2: "Set value in the VM side",
  tableField: initVmPrivateImpl[string]("Non-default argument passed to private field")
)

readVmVariant(data)
echo dump(data)[]


"""))

startHax()
main()
