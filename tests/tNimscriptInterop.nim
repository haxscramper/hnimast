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

proc fromVm*(t: typedesc[char], node: PNode): char =
  assertKind(node, nkIntKinds)
  return node.intVal.char

proc fromVm*[P: proc](p: typedesc[P], node: PNode): P =
  # I suppose it is possible to pass procedure implementaitons across
  # interpreter boundary, but it would require whole new level of hacking
  # around.
  nil

proc fromVm*(p: typedesc[pointer], node: PNode): pointer =
  # This is an interesting one - I'm pretty sure it would be possible to
  # get this data from VM (since it supports some kind of symbolic pointer
  # implementation). Alteritantively - if pointer is used as reference to
  # some opaque data blob that is handled only by underlying
  # implementation, we can just copy it as is.
  nil

proc fromVm*(t: typedesc[bool], node: PNode): bool =
  assertKind(node, nkIntKinds)
  return node.intVal != 0

proc fromVm*[E: enum](e: typedesc[E], node: PNode): E =
  assertKind(node, nkIntKinds)
  return E(node.intVal)

proc fromVm*(t: typedesc[int], node: PNode): int =
  assertKind(node, nkIntKinds)
  return node.intVal.int

proc fromVm*(t: typedesc[float], node: PNode): float =
  assertKind(node, nkFloatKinds)
  node.floatVal

proc fromVm*(t: typedesc[string], node: PNode): string =
  assertKind(node, nkStringKinds)
  node.strVal

genNewProcForType(VmVariant)

macro fromVm*[T: object](obj: typedesc[T], vmNode: PNode): untyped =
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

      loadKind.add newAsgn(name, newCall(
        "fromVm", implField.fieldType.toNNode(), fieldGet))

      constr.add newExprEq(name, name)

  # Construct nested case for unpacking other fields
  let unpackCase = impl.mapItGroups(res.newDot(path[^1].name)):
    var mapRes = newStmtList()
    for implField in group:
      if not implField.isKind:
        let fieldGet = vmget(fieldIdx[implField.name])
        let asgn =
          if implField.isExported:
            let accs = newDot(res, ident(implField.name))
            newAsgn(accs, newCall("fromVm", accs.callTypeof(), fieldGet))

          else:
            setPrivate(
              res, implField.name, newCall(
                "fromVm", implField.fieldType.toNNode(), fieldGet))

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
      echo data.treeRepr()
      let parsed = fromVm(VmVariant, data)
      echov parsed
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
  tableField: initVmPrivateImpl[string]()
)

readVmVariant(data)
echo dump(data)


"""))

startHax()
main()
