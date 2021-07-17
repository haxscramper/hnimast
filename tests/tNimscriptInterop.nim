import ./vm_common, ./common_test

import
  compiler/[nimeval, llstream, ast, renderer, vmdef, vm]

import
  std/[os]

import
  hnimast/compiler_aux

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

macro fromVm*[T: object](obj: typedesc[T], vmNode: PNode): untyped =
  let
    impl = getObjectStructure(obj)
    field = genSym(nskForVar, "field")
    res = genSym(nskVar, "res")
    constr = nnkObjConstr.newTree(ident(impl.name.head))

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

  intr.implementRoutine("*", "scriptname", "dump",
    proc(args: VmArgs) {.nimcall, gcsafe.} =
      let slot = args.slots[args.rb + 1]
      case slot.kind:
        of rkNode:
          let data = args.getNode(0)
          echo data.treeRepr()
          case data.kind:
            of nkObjConstr:
              let obj = fromVm(VmObject, data)
              pprint obj
              args.setResult obj.toVm()

            else:
              args.setResult data

        of rkFloat:
          let flt = args.getFloat(0)
          echo flt
          args.setResult flt.toVm()

        of rkInt:
          pprint args
          let intv = args.getInt(0)
          echo intv
          args.setResult intv.toVm()

        else:
          assert false, $slot.kind
  )

  intr.evalScript(llStreamOpen(
    readFile(currentSourceDir() /. "vm_common.nim") & """

proc dump[T](arg: T): T = discard

echo "\e[41m*========\e[49m  object  \e[41m========*\e[49m"
echo dump(VmObject(field1: 123123))

# echo "\e[41m*====\e[49m  object variant  \e[41m====*\e[49m"
# echo dump(VmVariant())

echo "\e[41m*========\e[49m  tuple  \e[41m=========*\e[49m"
echo dump((var t: VmTuple; t))

# echo "\e[41m*=========\e[49m  enum  \e[41m=========*\e[49m"
# echo dump((var e: VmKind; e))

echo "\e[41m*=\e[49m  sequence of integers  \e[41m=*\e[49m"
echo dump(@[1,2,3,4])

"""))

main()
