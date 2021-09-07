import
  ./wrap_store,
  ../hast_common

import
  hmisc/core/all,
  hmisc/macros/argpass,
  std/[macros, sequtils]

proc toNNode*[N](t: CxxType): N =
  case t.kind:
    of ctkIdent:
      result = ident(t.nimName)

    of ctkPtr:
      result = newTree(nnkPtrTy, toNNode[N](t.wrapped))

    else:
      raise newImplementKindError(t)

proc toNNode*[N](arg: CxxArg): N =
  nnkIdentDefs.newTree(ident(arg.nimName), toNNode[N](arg.nimType), newEmptyNode())

proc toNNode*[N](header: CxxHeader): N =
  case header.kind:
    of chkGlobal: newLit(header.global)
    of chkAbsolute: newLit(header.file.string)
    of chkPNode: newLit(header.other)


proc toNNode*[N](def: CxxProc, onConstructor: CxxTypeKind = ctkIdent): N =
  let source =
    if def.header.isSome():
      newEcE("header", toNNode[N](def.header.get()))

    else:
      newEmptyNode()

  nnkProcDef.newTree(
    nnkPostfix.newTree(ident("*"), ident(def.nimName)),
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      toNNode[N](def.getReturn(onConstructor)) & def.arguments.map(toNNode[N])),
    nnkPragma.newTree(
      newEcE("importcpp", def.icpp.newLit()), source),
    newEmptyNode(),
    newEmptyNode())


proc toNNode*[N](entry: CxxEntry): N =
  result = newStmtList()
  case entry.kind:
    of cekObject:
      var fieldList = nnkRecList.newTree()
      let obj = entry.cxxObject
      result.add nnkTypeDef.newTree(
        nnkPragmaExpr.newTree(
          ident(obj.nimName),
          nnkPragma.newTree(
              ident("inheritable"),
              ident("byref"),
              newEcE("header", toNNode[N](obj.header.get())),
              newEcE("importcpp", obj.icpp.newLit()))),
        newEmptyNode(),
        nnkObjectTy.newTree(
          newEmptyNode(),
          tern(
            obj.parent.len == 0,
            newEmptyNode(),
            nnkOfInherit.newTree(toNNode[N](obj.parent[0]))),
          fieldList))


      for meth in obj.methods:
        result.add toNNode[N](meth, ctkPtr)

      for n in obj.nested:
        result.add toNNode[N](n)

    of cekProc:
      result = toNNode[N](entry.cxxProc)

    else:
      raise newImplementKindError(entry)

proc toNNode*[N](entries: seq[CxxEntry]): N =
  var types: seq[N]
  var other: seq[N]
  for item in entries:
    for conv in toNNode[N](item):
      if conv.nnKind() == nnkTypeDef:
        types.add conv

      else:
        other.add conv

  result = newNTree[N](nnkStmtList, newTree[N](nnkTypeSection, types))
  result.add other
