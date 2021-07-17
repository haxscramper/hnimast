import ./vm_common, ./common_test

import
  compiler/[nimeval, llstream, ast, renderer, vmdef, vm]

import
  std/[os]

import
  hnimast/[compiler_aux, gencode]

import
  hnimast,
  hnimast/store_decl,
  hmisc/other/[hpprint, oswrap],
  hmisc/base_errors

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
    impl = getObjectStructure(obj)
    field = newIdent("field")
    res = newIdent( "res")
    constr = impl.newCall()

  var unpackCase = nnkCaseStmt.newTree(
    newDot(newBracketExpr(field, 0), ident("getStrVal")))

  for implField in iterateFields(impl):
    let implAccess = newDot(res, ident(implField.name))
    unpackCase.add nnkOfBranch.newTree(
      newLit(implField.name),
      newAsgn(implAccess, newCall(
        "fromVm", newCall("typeof", implAccess), newBracketExpr(field, 1)))
    )

  result = quote do:
    var `res` = `constr`
    for `field` in `vmNode`[1 .. ^1]:
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
  )

  intr.implementRoutine("*", "scriptname", "dump",
    proc(args: VmArgs) {.nimcall, gcsafe.} =
      let slot = args.slots[args.rb + 1]
      case slot.kind:
        of rkNode:
          let data = args.getNode(0)
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

proc dump[T](arg: T): T = discard
proc readVmVariant(arg: VmVariant) = discard

for name, value in fieldPairs(VmVariant()):
  echo "> ", name

readVmVariant(VmVariant())
echo dump(VmVariant())


"""))

main()
