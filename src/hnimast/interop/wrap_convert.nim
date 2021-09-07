proc toNNode(t: CxxType): NimNode =
  case t.kind:
    of ctkIdent:
      result = ident(t.nimName)

    of ctkPtr:
      result = nnkPtrTy.newTree(t.wrapped.toNNode())

    else:
      raise newImplementKindError(t)

proc toNNode(arg: CxxArg): NimNode =
  nnkIdentDefs.newTree(ident(arg.nimName), arg.nimType.toNNode(), newEmptyNode())

proc toNNode(header: CxxHeader): NimNode =
  case header.kind:
    of chkGlobal: newLit(header.global)
    of chkAbsolute: newLit(header.file.string)
    of chkPNode: newLit(header.other)


proc toNNode(def: CxxProc, onConstructor: CxxTypeKind = ctkIdent): NimNode =
  let source =
    if def.header.isSome():
      newEcE("header", def.header.get().toNNode())

    else:
      newEmptyNode()

  nnkProcDef.newTree(
    nnkPostfix.newTree(ident("*"), ident(def.nimName)),
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      def.getReturn(onConstructor).toNNode() & def.arguments.map(toNNode)),
    nnkPragma.newTree(
      newEcE("importcpp", def.icpp.newLit()), source),
    newEmptyNode(),
    newEmptyNode())


proc toNNode*(entry: CxxEntry): NimNode =
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
              newEcE("header", obj.header.get().toNNode()),
              newEcE("importcpp", obj.icpp.newLit()))),
        newEmptyNode(),
        nnkObjectTy.newTree(
          newEmptyNode(),
          tern(
            obj.parent.len == 0,
            newEmptyNode(),
            nnkOfInherit.newTree(obj.parent[0].toNNode())),
          fieldList))


      for meth in obj.methods:
        result.add meth.toNNode(ctkPtr)

      for n in obj.nested:
        result.add n.toNNode()

    of cekProc:
      result = entry.cxxProc.toNNode()

    else:
      raise newImplementKindError(entry)

proc toNNode*(entries: seq[CxxEntry]): NimNode =
  var types: seq[NimNode]
  var other: seq[NimNode]
  for item in entries:
    for conv in item.toNNode():
      if conv.kind == nnkTypeDef:
        types.add conv

      else:
        other.add conv

  result = newStmtList(nnkTypeSection.newTree(types))
  result.add other
