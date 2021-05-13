import macroutils
import hmisc/hexceptions

import std/[options, sets, options, tables,
            strutils, strformat, macros, sequtils]

export options
import compiler/ast
import hmisc/algo/[halgorithm, htree_mapping, namegen]
import hmisc/helpers
import hmisc/types/colorstring
import object_decl, idents_types, hast_common, pragmas
import hmisc/hdebug_misc
export pragmas

# TODO support multiple fields declared on the same line - `fld1, fld2: Type`

type
  SymTable[N] = object
    ## Mapping of type symbol names to the symbols themselves
    table: Table[string, N]
    enumCache: Table[string, EnumValueGroup[N]]

proc addConst*[N](sym: var SymTable[N], c: N) =
  case c.kind.toNNK():
    of nnkTupleConstr:
      let name = c[0].getStrVal()
      var val = c[1]
      let inst = val.getTypeInst()

      if val.kind.toNNK() == nnkSym:
        val = val.getImpl()


      var
        enumName: string

      case inst.kind.toNNK():
        of nnkBracketExpr:
          assert inst[0].getStrVal() == "set"
          enumName = inst[1].getStrVal()

        of nnkSym:
          enumName = inst.getStrVal()

        else:
          raiseImplementKindError(inst)


      case val.kind.toNNK():
        of nnkCurly:
          var values: seq[EnumFieldDef[N]]
          for item in val:
            if item.kind.toNNK() == nnkRange:
              values.add valuesInRange(
                item[0], item[1], sym.enumCache[enumName])

            else:
              values.add valuesInRange(
                item, item, sym.enumCache[enumName])

          sym.enumCache[enumName].enumConsts[name] = values

        of nnkIntLit:
          sym.enumCache[enumName].enumConsts[name] = valuesInRange(
            val, val, sym.enumCache[enumName])

        else:
          raiseImplementKindError(val)

    else:
      raiseImplementKindError(c)

proc fieldTypeNode*[N](field: N): N =
  case field.kind.toNNK():
    of nnkRecCase:
      return fieldTypeNode(field[0])

    of nnkIdentDefs:
      return field[1]

    else:
      raiseUnexpectedKindError(field, field.treeRepr())

proc enumValueGroup*[N](
    sym: SymTable[N], field: N): EnumValueGroup[N] =

  ## Get list of enum fields associated with enum @arg{enumName}
  ##
  ## - NOTE :: If `enumName` is not in the symbol table empty value group
  ##   is returned and no exception is raised.
  let enumName = field.fieldTypeNode().getStrVal()

  if enumName in sym.enumCache:
    return sym.enumCache[enumName]

  else:
    if isReservedNimType(enumName):
      return EnumValueGroup[N](wrapConvert: some(enumName))

proc getFields*[N](
    node: N, isCheckedOn: Option[N], sym: SymTable[N], level: int = 0
  ): seq[ObjectField[N]]

proc getBranches*[N](
  node: N, isCheckedOn: Option[N], sym: SymTable[N]): seq[ObjectBranch[N]] =

  assert node.kind.toNNK() == nnkRecCase, &"Cannot get branches from node kind {node.kind}"
  let caseType = $node[0][1]
  var ofValues: seq[N]
  for branch in node[1..^1]:
    case branch.kind.toNNK():
      of nnkOfBranch:
        let ofSet = (newTree(nnkCurly, branch[0..^2])).flattenSet(
          sym.enumValueGroup(isCheckedOn.get()))
        ofValues.add ofSet
        result.add ObjectBranch[N](
          docComment: branch.getDocComment(),
          declNode: some(branch),
          ofValue: ofSet,
          flds: branch[^1].getFields(isCheckedOn, sym),
          isElse: false
        )

      of nnkElse:
        result.add ObjectBranch[N](
          docComment: branch.getDocComment(),
          declNode: some(branch),
          flds: branch[0].getFields(isCheckedOn, sym),
          isElse: true,
          notOfValue: ofValues
        )

      else:
        raiseAssert(&"Unexpected branch kind {branch.kind}")



type
  FieldDesc[N] = object
    decl: N
    name: string
    fldType: NType[N]
    exported: bool
    value: Option[N]
    # pragma: Option[PRagma[N]]
    pragma: seq[Pragma[N]] # For some reason this shits blows (cannot
                           # instantiate my ass) up when I try to use
                           # `Option` - I don't fucking care what kind of
                           # compiler semcheck vomit lead to this, but for
                           # now I use `seq`.

proc getFieldDescriptions[N](node: N): seq[FieldDesc[N]] =
  case node.kind.toNNK():
    of nnkIdentDefs:
      let fldType = parseNType(node[^2])
      for ident in node[0 ..^ 3]:
        let (exported, name) = parseIdentName(ident)

        var field = FieldDesc[N](
          decl: ident,
          name: $name,
          fldType: fldType,
          exported: exported,
          value: none(N)
        )

        let val = parseSomePragma(ident)
        if val.isSome():
          field.pragma.add val

        result.add(field)

      if node[2].kind.toNNK() != nnkEmpty:
        result[^1].value = some(node[2])


    of nnkRecCase:
      return getFieldDescriptions(node[0])

    of nnkSym:
      var fldType: NType[N]
      when node is PNode:
        if node.sym.notNil() and
           node.sym.typ.notNil() and
           node.sym.typ.n.notNil():

          fldType = parseNType(node.sym.typ.n)

        else:
          if node.sym.notNil(): echo node.sym
          if node.sym.notNil() and node.sym.typ.notNil():
            echo "type is not nil"

          fldType = newNNType[N]("TYPE_DETECTION_ERROR")
          raiseImplementError(node.treeRepr())
          # echo node
          # fldType.declNode = some node

      else:
        fldTYpe = newNNType[N]("TYPE_DETECTION_ERROR")

      result.add(
        FieldDesc[N](
          decl: node,
          name: $node,
          fldType: fldType,
          exported: false,
          value: none(N)))

    else:
      raiseAssert(
        &"Cannot get field description from node of kind {node.kind}." &
          &"{node.getInfo()}"
      )

proc getFields*[N](
    node: N, isCheckedOn: Option[N], sym: SymTable[N], level: int = 0
  ): seq[ObjectField[N]] =
  # TODO ignore `void` fields
  case node.kind.toNNK():
    of nnkObjConstr:
      return getFields(node[0], isCheckedOn, sym, level + 1)

    of nnkSym, nnkCall, nnkDotExpr:
      when node is PNode:
        if level == 0:
          raiseAssert(
            "Parsing PNode from symbol on the first level is not supported " & $level
          )
        else:
          if node.kind.toNNK() == nnkSym:
            for descr in getFieldDescriptions(node):
              result.add ObjectField[N](
                docComment: node.getDocComment(),
                declNode:  some(node),
                isTuple:   false,
                isKind:    false,
                isChecked: isCheckedOn.isSome(),
                name:      descr.name,
                fldType:   descr.fldType,
                isExported:  descr.exported,
                value:     descr.value
              )

              if descr.pragma.len > 0:
                result[^1].pragma = some descr.pragma[0]

          else:
            raiseImplementError("")

      else:
        let kind = node.getTypeImpl().kind
        case kind:
          of nnkBracketExpr:
            let typeSym = node.getTypeImpl()[1]
            result = getFields(typeSym.getTypeImpl(), isCheckedOn, sym, level + 1)

          of nnkObjectTy, nnkRefTy, nnkTupleTy, nnkTupleConstr:
            result = getFields(node.getTypeImpl(), isCheckedOn, sym, level + 1)

          else:
            raiseAssert("Unknown parameter kind: " & $kind)

    of nnkObjectTy:
      return node[2].getFields(none(N), sym, level + 1)

    of nnkRefTy, nnkPtrTy:
      when node is PNode:
        if node[0].kind.toNNK() == nnkObjectTy:
          return getFields(node[0], none(N), sym, level)

        else:
          raiseImplementKindError(node[0])

      else:
        if node[0].kind == nnkObjectTy:
          return getFields(node[0], none(N), sym, level)

        else:
          return node.getTypeImpl()[0].getImpl()[2][0].getFields(
            none(N), sym, level + 1)

    of nnkRecList:
      mixin items
      for elem in items(node):
        if elem.kind.toNNK() == nnkRecWhen:
          # TODO 'when' branches must be tracked somehow for `haxdoc`
          # parsing, but they are largely unnecessary when it comes to
          # codegen things.
          result.add getFields(elem, none(N), sym, level + 1)

        elif elem.kind.toNNK() notin {nnkRecList, nnkNilLit}:
          case elem.kind.toNNK():
            of nnkRecCase: # Case field
              for descr in getFieldDescriptions[N](elem):
                var field = ObjectField[N](
                  docComment: elem.getDocComment(),
                  declNode:   some(elem),
                  isTuple:    false,
                  isKind:     true,
                  isChecked:  isCheckedOn.isSome(),
                  branches:   getBranches(elem, some(elem), sym),
                  name:       descr.name,
                  isExported: descr.exported,
                  fldType:    descr.fldType,
                )

                if descr.pragma.len > 0:
                  field.pragma = some descr.pragma[0]

                result.add field

            of nnkIdentDefs: # Regular field definition
              result.add getFields(elem, isCheckedOn, sym, level + 1)

            else:
              discard

    of nnkTupleTy:
      for fld in items(node):
        result.add fld.getFields(isCheckedOn, sym, level + 1)

    of nnkTupleConstr:
      for idx, sym in pairs(node):
        result.add ObjectField[N](
          docComment: sym.getDocComment(),
          declNode: some(sym),
          isTuple: true,
          isChecked: isCheckedOn.isSome(),
          tupleIdx: idx# , value: initObjTree[NimNode]()
        )

    of nnkIdentDefs:
      let descr = getFieldDescriptions(node)
      for idx, desc in descr:
        # if desc.name == "fDebugTrigger":
        #   raiseImplementError("")

        var field = ObjectField[N](
          docComment: node.getDocComment(),
          declNode:  some(desc.decl),
          isTuple:   false,
          isKind:    false,
          isChecked: isCheckedOn.isSome(),
          isExported:  desc.exported,
          name:      desc.name,
          fldType:   desc.fldType,
          value:     desc.value,
        )

        if descr[0].pragma.len > 0:
          field.pragma = some descr[0].pragma[0]

        result.add field

      if node[0].kind == nnkPragmaExpr:
        result[^1].pragma = parseSomePragma(node[0])

    of nnkEmpty:
      discard

    of nnkRecWhen:
      discard
      # WARNING ignoring `when` fields, need to provide IR representation
      # and handle edge cases. NOTE this one broke on `options` from the
      # stdlib.

      # TypeDef
      #   Sym Type Option
      #   GenericParams
      #     Sym Type T
      #   ObjectTy
      #     Empty
      #     Empty
      #     RecList
      #       RecWhen
      #         ElifBranch
      #           Infix
      #             Sym Proc is
      #             Sym Type T
      #             Type
      #           Sym Field val
      #         Else
      #           RecList
      #             Sym Field val
      #             Sym Field has


      # for subnode in items(node):
      #   result.add getFields(subnode, isCheckedOn, sym, level + 1)

    of nnkElifBranch:
      # WARNING condition is dropped
      result.add getFields(node[1], isCheckedOn, sym, level + 1)

    of nnkElse:
      result.add getFields(node[0], isCheckedOn, sym, level + 1)

    of nnkNilLit:
      # Explicit `nil`
      discard

    else:
      raiseImplementKindError(node)

template filterIt2(op, body: untyped): untyped = filterIt(body, op)

proc getKindFields*[Node](
  flds: seq[ObjectField[Node]]): seq[ObjectField[Node]] =
  for fld in flds:
    if fld.isKind:
      var fld =  ObjectField[Node](
        docComment: fld.docComment,
        declNode: fld.declNode,
        isTuple: false,
        isKind: true,
        name: fld.name,
        fldType: fld.fldType
      )

      for it in fld.branches:
        if it.flds.len > 0:
          if it.isElse:
            fld.branches.add ObjectBranch[Node](
              docComment: it.docComment,
              declNode: it.declNode,
              notOfValue: it.notOfValue,
              isElse: true,
              flds: it.flds.getKindFields()
            )

          else:
            fld.branches.add ObjectBranch[Node](
              docComment: it.docComment,
              declNode: it.declNode,
              ofValue: it.ofValue,
              isElse: false,
              flds: it.flds.getKindFields()
            )

      result.add fld

proc getKindFields*[N](obj: ObjectDecl[N]): seq[ObjectField[N]] =
  ## Get *full* flattened list of all discriminant switch fields.
  proc aux(field: ObjectField[N]): seq[ObjectField[N]] =
    if field.isKind:
      result.add field
      for branch in field.branches:
        for subfield in branch.flds:
          result.add aux(subfield)

  for field in obj.flds:
    result.add aux(field)

proc isTaggedWith*(obj: ObjectField[NimNode], name: string): bool =
  obj.pragma.isSome() and obj.pragma.get().hasElem(name)

# proc isTaggedWith*(obj: ObjectField[PNode, PPragma], name: string): bool =
#   obj.annotation.isSome() and obj.annotation.get().hasElem(name)

proc getSubfields*[N](field: ObjectField[N]): seq[ObjectField[N]] =
  for branch in field.branches:
    for field in branch.flds:
      result.add field

iterator iterateFields*[N](
    objDecl: ObjectDecl[N], preorder: bool = true): ObjectField[N] =
  ## - @arg{preorder} :: Iterate fields in preorder (default, `true`) or
  ##   postorder. Preorder iteration yields kind fields first, postorder
  ##   last.
  let order = if preorder: dfsPreorder else: dfsPostorder
  for field in objDecl.flds:
    iterateItDFS(field, it.getSubfields(), it.isKind, order):
      yield it


proc getBranchFields*[N](
    objDecl: ObjectDecl[N], preorder: bool = true): seq[ObjectField[N]] =
  ## - @arg{preorder} :: @pass{[[code:iterateFields().preorder]]}
  for field in iterateFields(objDecl, preorder):
    if field.isKind:
      result.add field

proc getFlatFields*[N](
    objDecl: ObjectDecl[N], preorder: bool = true): seq[ObjectField[N]] =
  ## - @arg{preorder} :: @pass{[[code:iterateFields().preorder]]}
  for field in iterateFields(objDecl, preorder):
    result.add field



proc discardNimNode*(ntype: NType[NimNode]): NType[ObjTree] =
  result = NType[ObjTree](
    kind: ntkIdent,
    head: ntype.head,
    genParams: ntype.genparams.mapIt(it.discardNimNode())
  )

proc discardNimNode(input: seq[ObjectField[NimNode]]): seq[ValField] =
  for fld in input:
    case fld.isKind:
      of true:
        result.add ValField(
          # value: initObjTree[void](),
          isTuple: false,
          isKind: true,
          name: fld.name,
          fldType: fld.fldType.discardNimNode(),
          selected: fld.selected,
          branches: fld.branches.mapIt(
            block:
              if it.isElse:
                ValFieldBranch(
                  isElse: true,
                  flds: it.flds.discardNimNode(),
                  notOfValue: @[ObjTree(
                    styling: initPrintStyling(),
                    # TODO save set representation
                  )]
                )
              else:
                ValFieldBranch(
                  ofValue: @[ObjTree(
                    styling: initPrintStyling(),
                    kind: okConstant,
                    constType: $fld.fldType,
                    strLit: it.ofValue.mapIt($it.toStrLit()).join(", ")
                  )],
                  isElse: false,
                  flds: it.flds.discardNimNode())
            ))

      of false:
        result.add ValField(
          # value: initObjTree[void](),
          isTuple: false,
          isKind: false,
          name: fld.name,
          fldType: fld.fldType.discardNimNode()
        )

func parsePragma*[N](node: N, position: ObjectAnnotKind): Pragma[N] =
  result.kind = position
  case position:
    of oakObjectField:
      node.expectKind nnkIdentDefs
      result.elements = toSeq(node[0][1].subnodes)

    else:
      node.expectKind nnkPragma
      result.elements = toSeq(node.subnodes)


func parseNimPragma*(node: NimNode, position: ObjectAnnotKind): NPragma =
  parsePragma(node, position)

func parsePPragma*(node: PNode, position: ObjectAnnotKind): Pragma[PNode] =
  parsePragma(node, position)


func getTypeImplBody*(node: NimNode, getImpl: bool): NimNode =
  case node.kind:
    of nnkSym:
      if getImpl:
        result = getTypeImplBody(node.getTypeImpl(), getImpl)

      else:
        let inst = node.getTypeInst()
        case inst.kind:
          of nnkBracketExpr:
            result = getTypeImplBody(inst[1].getImpl(), getImpl)

          else:
            raiseImplementKindError(inst)

    of nnkIdent:
      raiseImplementError("Cannot get type implementation from ident")

    of nnkBracketExpr:
      result = getTypeImplBody(node[1], getImpl)

    of nnkObjectTy, nnkTypeDef:
      return node

    of nnkRefTy:
      result = getTypeImplBody(node[0], getImpl)

    else:
      raiseImplementKindError(node, node.treeRepr())

proc bodySymTable*(inNode: NimNode): SymTable[NimNode] =
  ## Return list of unique symbols used in node
  var symcache: HashSet[string]
  var symtable: SymTable[NimNode]
  proc aux(node: NimNode) =
    case node.kind:
      of nnkSym:
        case node.symKind:
          of nskType:
            let impl = node.getType()
            let hash = signatureHash(node)

            if impl.kind == nnkEnumTy:
              let impl2 = node.getTypeInst().getImpl()[2]
              if hash notin symcache:
                symcache.incl hash
                symtable.table[$node] = node
                if impl.kind == nnkEnumTy:
                  symtable.enumCache[$node] = EnumValueGroup[NimNode](
                    enumFields: splitEnumImpl(impl2))

            else:
              discard

          else:
            discard

      of nnkTokenKinds - {nnkSym}:
        discard

      else:
        for subnode in items(node):
          aux(subnode)

  aux(inNode)
  return symtable

proc parseObject*[N](
    inNode: N, parseImpl: bool = true,
    constList: seq[N] = @[]): ObjectDecl[N] =
  ## Parse object implementation
  ##
  ## - @arg{parseImpl} :: If `inNode` is a symbol used to selecting between
  ##   `getTypeImpl` and `getTypeInst`. Latter one is a default and it
  ##   parses object definition based on how it was *defined in source* -
  ##   with all original `{.pragma.}` annotations for fields etc. So the
  ##   actual final type might be different from what `getTypeInst`
  ##   returns.
  ##
  ## - @arg{constList} :: List of `Sym` nodes for constants used in object
  ##   body. not required, but allows to provide full branch set
  ##   normalization - when some `const` was used for `of` branch it would
  ##   be converted to correct list of enum values.

  let node =
    case inNode.kind.toNNK():
      of nnkStmtList:
        inNode[0].expectKind nnkTypeSection
        inNode[0][0]

      of nnkSym:
        when N is PNode:
          raiseImplementError(
            "Parsing PNode from symbol on the first level is not supported")

        else:
          inNode.getTypeImplBody(parseImpl)

      else:
        inNode

  var sym: SymTable[N]
  when N is NimNode:
    sym = inNode.getTypeImplBody(true).bodySymTable()

    for c in constList:
      sym.addConst(c)

  if node.kind notin {nnkTypeDef, nnkObjectTy}:
    raiseImplementKindError(node, node.treeRepr())

  let declBody = tern(node.kind == nnkTypeDef, node[2], node)

  result = ObjectDecl[N](
    docComment: node.getDocComment(),
    declNode: some(node),
    flds: declBody.getFields(none(N), sym))

  result.base = declBody.getSomeBase()

  if node.kind == nnkTypeDef:
    let (exported, name) = parseIdentName(node[0])

    result.exported = exported
    result.name = newNNType[N](name.getStrVal())


    if node[0].kind.toNNK() == nnkPragmaExpr:
      result.pragma = some parsePragma(node[0][1])

  elif inNode.kind == nnkSym:
    result.name = newNNtype[N](inNode.getStrVal())


macro makeFieldsLiteral*(node: typed): untyped =
  var sym: SymTable[NimNode]
  result = node.getFields(none(NimNode), sym).discardNimNode.makeConstructAllFields()

type
  GenParams = object
    lhsObj, rhsObj, lhsName, rhsName, idxName, valIdxName, isKindName, fldName: string
    hackFields: bool

proc unrollFieldLoop(
    flds: seq[ObjectField[NimNode]],
    body: NimNode,
    fldIdx: int,
    genParam: GenParams
  ): tuple[node: NimNode, fldIdx: int] =

  result.node = newStmtList()

  var fldIdx: int = fldIdx
  for fld in flds:
    var tmpRes = newStmtList()
    let lhsId = ident(genParam.lhsName)
    let rhsId = ident(genParam.rhsName)

    let valdefs =
      if fld.isTuple:
        let
          tupleIdx = newLit(fld.tupleIdx)
          fldName = newLit("Field" & $fldIdx)

        superquote do:
          let `lhsId` = `ident(genParam.lhsObj)`[`tupleIdx`]
          let `rhsId` = `ident(genParam.rhsObj)`[`tupleIdx`]
          const `ident(genParam.fldName)`: string = `fldName`

      else:
        let
          fldId = ident(fld.name)
          fldName = newLit(fld.name)

        if genParam.hackFields:
          let fldType = fld.fldType.toNimNode()
          let tmp = superquote do:
            const `ident(genParam.fldName)`: string = `fldName`
            let `lhsId`: `fldType` = block:
              var tmp: `fldType`
              for name, val in fieldPairs(`ident(genParam.lhsObj)`):
                when val is `fldType`:
                  if name == `fldName`:
                    tmp = val
                    break

              tmp

            let `rhsId`: `fldType` = block:
              var tmp: `fldType`
              for name, val in fieldPairs(`ident(genParam.rhsObj)`):
                when val is `fldType`:
                  if name == `fldName`:
                    tmp = val
                    break

              tmp

          tmp
        else:
          superquote do:
            let `lhsId` = `ident(genParam.lhsObj)`.`fldId`
            let `rhsId` = `ident(genParam.rhsObj)`.`fldId`
            const `ident(genParam.fldName)`: string = `newLit(fld.name)`

    tmpRes.add superquote do:
      const `ident(genParam.isKindName)`: bool = `newLit(fld.isKind)`
      let `ident(genParam.idxName)`: int = `newLit(fldIdx)`
      `valDefs`
      block:
        `body`
        inc `ident(genParam.valIdxName)`

    inc fldIdx
    if fld.isKind:
      # TODO check if two field kinds are identical
      var caseBlock = nnkCaseStmt.newTree(
        ident(genParam.lhsName)
        # newDotExpr(ident genParam.lhsObj, ident fld.name)
      )


      for branch in fld.branches:
        let (branchBody, lastIdx) =
          branch.flds.unrollFieldLoop(body, fldIdx, genParam)

        fldIdx = lastIdx
        if branch.isElse:
          caseBlock.add nnkElse.newTree(
            newStmtList(
              newCommentStmtNode(
                "Fallback for value `" & branch.ofValue.mapIt(
                  $it.toStrLit()).join(", ") &
                  "` of field " & fld.name),
              branchBody
            )
          )
        else:
          caseBlock.add nnkOfBranch.newTree(
            branch.ofValue &
            @[newStmtList(
              newCommentStmtNode(
                "Branch for value `" & branch.ofValue.
                  mapIt($it.toStrLit()).join(", ") &
                  "` of field " & fld.name),
              branchBody
            )]
          )

      caseBlock = newStmtList(
        newCommentStmtNode("Selector "),
        caseBlock)

      tmpRes.add do:
        if fld.isTuple:
          let fldIdx = newLit(fld.tupleIdx)
          superquote do:
            if `ident(genParam.lhsObj)`[`fldIdx`] == `ident(genParam.rhsObj)`[`fldIdx`]:
              `caseBlock`
        else:
          let fldId = ident(fld.name)
          superquote do:
            ## Case field comparison
            if `lhsId` == `rhsId`:
              `caseBlock`
            # if `ident(genParam.lhsObj)`.`fldId` == `ident(genParam.rhsObj)`.`fldId`:
            #   `caseBlock`

    let comment =
      if fld.isTuple:
        newCommentStmtNode("Tuple field idx: " & $fld.tupleIdx)
      else:
        newCommentStmtNode("Field: " & $fld.name)

    result.node.add quote do:
      block:
        `comment`
        `tmpRes`



  result.node = newBlockStmt(result.node)
  result.fldIdx = fldIdx


macro parallelFieldPairs*(lhsObj, rhsObj: typed, body: untyped): untyped =
  ##[

Iterate two objects in parallel. Works for case objects.

Similar to parallel `fieldPairs` but also works for case objects.
Allows to iterate two objects at once, while keeping track of `kind`
fields for each type. The body is unrolled and variables are injected
for each field.

* Injected variables

- @inject{name} :: name of the current field
- @inject{lhs}, @inject{rhs} :: value of current fields
- @inject{fldIdx} :: int. Index of current field in the object.
- @inject{valIdx} :: int. Index of current *value field* in the object
- @inject{lhsObj}, @inject{rhsObj} :: Original objects being iterated. [fn:1]
- @inject{isKind} :: bool. Whether or not current field is used as case
  parameter for object

[fn:1] Useful when iterating over results of expression

* Notes

** Limitations

- Private fields cannot be accessed directly - compilation will fail. Can
  be fixed by defining getter with the same name as a field (e.g for field
  `kind` define `func kind(t: T): KindType`). Dirty workaround is to use
  `hackPrivateParallelFieldPairs` - it can access private fields (but does
  not work if your private private field has a non-exported type)

** `fldIdx` and `valIdx`

Difference between `fldIdx` and `valIdx`. First one describes order of
fields **as defined** in object while second one shows order of fields **as
accessed** in object. For example, in object like this:

.. code-block:: nim
    type
      Case = object
        f1: int                # fldIdx - `0`, valIdx - `0`
        case kind: bool        # fldIdx - `1`, valIdx - `1`
          of true: f2: float   # fldIdx - `2`, valIdx - `2`
          of false: f3: string # fldIdx - `3`, valIdx - `2`

          # Fields `f2` and `f3` have the same `valIdx` because they
          # are located in different branches and cannot be accessed
          # at the same time.

  ]##
  # TODO optionally ignore private fields

  let genParams = GenParams(
    lhsObj: "lhsObj",
    rhsObj: "rhsObj",
    lhsName: "lhs",
    rhsName: "rhs",
    idxName: "fldIdx",
    valIdxName: "valIdx",
    isKindName: "isKind",
    fldName: "name"
  )

  var sym: SymTable[NimNode]
  let (unrolled, _) = getFields(lhsObj, none(NimNode), sym).
    unrollFieldLoop(body, 0, genParams)

  result = superquote do:
    block: ## Toplevel
      var `ident(genParams.valIdxName)`: int = 0
      let `ident(genParams.lhsObj)` = `lhsObj`
      let `ident(genParams.rhsObj)` = `rhsObj`
      `unrolled`



macro hackPrivateParallelFieldPairs*(lhsObj, rhsObj: typed, body: untyped): untyped =
  ## Same API as `parallelFieldPairs` but uses HACK to access private
  ## fields. NOT: due to HACK being used compilation is even slower.
  let genParams = GenParams(
    lhsObj:     "lhsObj",
    rhsObj:     "rhsObj",
    lhsName:    "lhs",
    rhsName:    "rhs",
    idxName:    "fldIdx",
    valIdxName: "valIdx",
    isKindName: "isKind",
    fldName:    "name",
    hackFields: true
  )


  var sym: SymTable[NimNode]
  let (unrolled, _) = getFields(lhsObj, none(NimNode), sym).
    unrollFieldLoop(body, 0, genParams)

  let section = newCommentStmtNode(
    "Type: " & $lhsObj.getTypeInst().toStrLit())
  result = superquote do:
    block: ## Toplevel
      `section`
      var `ident(genParams.valIdxName)`: int = 0
      let `ident(genParams.lhsObj)` = `lhsObj`
      let `ident(genParams.rhsObj)` = `rhsObj`
      `unrolled`

  # result.colorPrint()
