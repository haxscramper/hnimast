import
  ./object_decl,
  ./proc_decl,
  ./hast_common,
  ./obj_field_macros,
  ./store_decl,
  ./idents_types

import hmisc/other/hpprint

proc genNewProcImpl*[N](
    impl: ObjectDecl[N],
    initFields: bool = true,
    useDefault: bool = true,
    skip: seq[string] = @[]
  ): N =

  result = newStmtList()

  let newObj = impl.mapItPath(newIdent(path[^1].name)):
    if path.len > 0 and path[^1].isFinalBranch():
      var res = newCaseStmt(newIdent(path[0].kindField.name))
      var newCall = nnkObjConstr.newTree(newIdent(impl.name.head))
      for v1 in path[0].ofValue:
        newCall.add newExprColon(newIdent(path[0].kindField.name), v1)
        if path.len > 1:
          newCall.add newExprColon(newIdent(path[^1].kindField.name),
                                   newIdent(path[^1].kindField.name))

        res.addBranch(v1, newAsgn(newIdent("result"), newCall))

      res.addBranch(newDiscardStmt())

      return res

  result.add newObj

  if initFields:
    let init = impl.mapItGroups("result".newDot(path[^1])):
      var res = newStmtList()
      for field in group:
        if field.isExported.not() or
           field.isKind or
           field.name in skip:
          discard

        elif field.value.isSome() and useDefault:
          res.add newAsgn(newIdent("result").newDot(field), field.value.get())

        else:
          res.add newAsgn(
            newDot("result", field), newIdent(field.name))

      res

    result.add init.compactCase()


proc genNewProc*[N](impl: ObjectDecl[N]): ProcDecl[N] =
  result = newProcDecl[N](impl.getNewProcName())

  var skippedFields: seq[string]
  for doKind in [true, false]:
    for field in iterateFields(impl):

      if field.isExported and (
        (doKind and field.isKind) or
        (doKind.not() and field.isKind.not())
      ):

        let argExported =
          field.fieldType.declNode.isNone() or
          field.fieldType.declNode.get().
            baseImplSym(passSym = true).isExported()

        if argExported:
          result.addArgument(
            field.name,
            field.fieldType,
            value =
              if field.value.isSome():
                field.value

              else:
                some newXCall(
                  newNIdent[N]("default"),
                  @[field.fieldType.toNNode()]))

        else:
          skippedFields.add field.name

  result.impl = genNewProcImpl(impl, useDefault = false, skip = skippedFields)
  result.returnType = impl.name

macro genNewProcForType*[T](InType: typedesc[T]): untyped =
  result = genNewProc(getObjectStructure(InType)).toNNode()
  # echo result.repr
