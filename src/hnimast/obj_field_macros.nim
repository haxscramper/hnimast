import macroutils, sugar, options
import strutils, strformat, macros, sequtils
import hmisc/hexceptions

import compiler/ast
import hmisc/algo/[halgorithm, htree_mapping]
import hmisc/helpers
import hmisc/types/colorstring
import object_decl, idents_types, hast_common, pragmas
import hmisc/hdebug_misc
export pragmas

# TODO support multiple fields declared on the same line - `fld1, fld2: Type`

proc getFields*[NNode, A](
  node: NNode, cb: ParseCb[NNode, A],
  level: int = 0): seq[ObjectField[NNode, A]]

proc getBranches*[NNode, A](
  node: NNode, cb: ParseCb[NNode, A]): seq[ObjectBranch[NNode, A]] =
  assert node.kind.toNNK() == nnkRecCase, &"Cannot get branches from node kind {node.kind}"
  let caseType = $node[0][1]
  var ofValues: seq[NNode]
  for branch in node[1..^1]:
    case branch.kind.toNNK():
      of nnkOfBranch:
        let ofSet = (newTree(nnkCurly, branch[0..^2])).normalizeSet()
        ofValues.add ofSet
        result.add ObjectBranch[NNode, A](
          declNode: some(branch),
          ofValue: ofSet,
          flds: branch[^1].getFields(cb),
          isElse: false
        )

      of nnkElse:
        result.add ObjectBranch[NNode, A](
          declNode: some(branch),
          flds: branch[0].getFields(cb),
          isElse: true,
          notOfValue: ofValues.joinSets()
        )

      else:
        raiseAssert(&"Unexpected branch kind {branch.kind}")


proc getFieldDescriptions[NNode](node: NNode):
  seq[tuple[name: string, fldType: NType[NNode],
            exported: bool, value: Option[NNode]]] =

  case node.kind.toNNK():
    of nnkIdentDefs:
      let fldType = parseNType(node[^2])
      for ident in node[0 ..^ 3]:
        var name: string
        var exported = false

        case ident.kind.toNNK():
          of nnkPostfix:
            exported = true
            name = $ident[1]

          of nnkPragmaExpr:
            if ident[0].kind.toNNK() == nnkPostfix:
              name = $ident[1]

            else:
              name = $ident[0]

          else:
            name = $ident

        result.add((name: name, fldType: fldType,
                    exported: exported, value: none(NNode)))

      if node[2].kind.toNNK() != nnkEmpty:
        result[^1].value = some(node[2])


    of nnkRecCase:
      return getFieldDescriptions(node[0])

    of nnkSym:
      var fldType: NType[NNode]
      when node is PNode:
        if node.sym.notNil() and
           node.sym.typ.notNil() and
           node.sym.typ.n.notNil()
          :

          fldType = newNType(node.sym.typ.n)

        else:
          fldTYpe = newNNType[NNode]("TYPE_DETECTION_ERROR")

      else:
        fldTYpe = newNNType[NNode]("TYPE_DETECTION_ERROR")

      result.add((name: $node, fldType: fldType,
                  exported: false, value: none(NNode)))

    else:
      raiseAssert(
        &"Cannot get field description from node of kind {node.kind}." &
          &"{node.getInfo()}"
      )

proc getFields*[NNode, A](
  node: NNode, cb: ParseCb[NNode, A], level: int = 0): seq[ObjectField[NNode, A]] =
  # TODO ignore `void` fields
  case node.kind.toNNK():
    of nnkObjConstr:
      return getFields(node[0], cb, level + 1)

    of nnkSym, nnkCall, nnkDotExpr:
      when NNode is PNode:
        if level == 0:
          raiseAssert(
            "Parsing PNode from symbol on the first level is not supported " & $level
          )
        else:
          if node.kind.toNNK() == nnkSym:
            let descr = getFieldDescriptions(node)[0]
            result = @[ObjectField[NNode, A](
              declNode: some(node),
              isTuple: false,
              isKind: false,
              name: descr.name,
              fldType: descr.fldType,
              exported: descr.exported,
              value: descr.value
            )]

            # if node.sym.notNil() and
            #    node.sym.typ.n.notNil():
            #   result[0].fldType = newNType(node.sym.typ.n)


          else:
            raiseImplementError("")

      else:
        let kind = node.getTypeImpl().kind
        case kind:
          of nnkBracketExpr:
            let typeSym = node.getTypeImpl()[1]
            result = getFields(typeSym.getTypeImpl(), cb, level + 1)

          of nnkObjectTy, nnkRefTy, nnkTupleTy, nnkTupleConstr:
            result = getFields(node.getTypeImpl(), cb, level + 1)

          else:
            raiseAssert("Unknown parameter kind: " & $kind)

    of nnkObjectTy:
      return node[2].getFields(cb, level  + 1)

    of nnkRefTy, nnkPtrTy:
      when NNode is PNode:
        if node[0].kind.toNNK() == nnkObjectTy:
          return getFields(node[0], cb, level)

        else:
          raiseImplementKindError(node[0])

      else:
        return node.getTypeImpl()[0].getImpl()[2][0].getFields(cb, level + 1)

    of nnkRecList:
      mixin items
      for elem in items(node):
        if elem.kind.toNNK() == nnkRecWhen:
          result.add getFields(elem, cb, level + 1)

        elif elem.kind.toNNK() notin {nnkRecList, nnkNilLit}:
          let descr = getFieldDescriptions(elem)
          case elem.kind.toNNK():
            of nnkRecCase: # Case field
              # NOTE possible place for `cb` callbac
              result.add ObjectField[NNode, A](
                declNode: some(elem),
                isTuple: false,
                isKind: true,
                branches: getBranches(elem, cb),
                name: descr[0].name,
                exported: descr[0].exported,
                fldType: descr[0].fldType,
              )

            of nnkIdentDefs: # Regular field definition
              result.add getFields(elem, cb, level + 1)[0]

            else:
              discard

    of nnkTupleTy:
      for fld in items(node):
        result.add fld.getFields(cb, level + 1)

    of nnkTupleConstr:
      for idx, sym in pairs(node):
        result.add ObjectField[NNode, A](
          declNode: some(sym),
          isTuple: true,
          tupleIdx: idx# , value: initObjTree[NimNode]()
        )

    of nnkIdentDefs:
      let descr = getFieldDescriptions(node)
      for idx, (name, fldType, exported, value) in descr:
        result.add ObjectField[NNode, A](
          declNode: some(node),
          isTuple: false,
          isKind: false,
          exported: exported,
          name: name,
          fldType: fldType,
          value: value
        )

      when not (A is void):
        if node[0].kind == nnkPragmaExpr and cb != nil:
          result[^1].annotation = some cb(node, oakObjectField)

    of nnkEmpty:
      discard

    of nnkRecWhen:
      for subnode in items(node):
        result.add getFields(subnode, cb, level + 1)

    of nnkElifBranch:
      # WARNING condition is dropped
      result.add getFields(node[1], cb, level + 1)

    of nnkElse:
      result.add getFields(node[0], cb, level + 1)

    of nnkNilLit:
      # Explicit `nil`
      discard

    else:
      raiseImplementKindError(node)

template filterIt2(op, body: untyped): untyped = filterIt(body, op)

proc getKindFields*[Node, A](
  flds: seq[ObjectField[Node, A]]): seq[ObjectField[Node, A]] =
  for fld in flds:
    if fld.isKind:
      var fld =  ObjectField[Node, A](
        declNode: fld.declNode,
        isTuple: false,
        isKind: true,
        name: fld.name,
        fldType: fld.fldType
      )

      for it in fld.branches:
        if it.flds.len > 0:
          if it.isElse:
            fld.branches.add ObjectBranch[Node, A](
              declNode: it.declNode,
              notOfValue: it.notOfValue,
              isElse: true,
              flds: it.flds.getKindFields()
            )

          else:
            fld.branches.add ObjectBranch[Node, A](
              declNode: it.declNode,
              ofValue: it.ofValue,
              isElse: false,
              flds: it.flds.getKindFields()
            )

        # branches:
        #   block:
        #     filterIt2(it.flds.len > 0):
        #       collect(newSeq):
        #         for it in fld.branches:


      result.add fld

proc getSubfields*[N, A](field: ObjectField[N, A]): seq[ObjectField[N, A]] =
  for branch in field.branches:
    for field in branch.flds:
      result.add field

iterator iterateFields*[N, A](objDecl: ObjectDecl[N, A]):
  ObjectField[N, A] =

  for field in objDecl.flds:
    iterateItDFS(field, it.getSubfields(), it.isKind, dfsPostorder):
      yield it

proc getBranchFields*[N, A](objDecl: ObjectDecl[N, A]):
  seq[ObjectField[N, A]] =

  for field in objDecl.flds:
    iterateItDFS(field, it.getSubfields(), it.isKind, dfsPostorder):
      if it.isKind:
        result.add it



proc discardNimNode*(ntype: NType[NimNode]): NType[ObjTree] =
  result = NType[ObjTree](
    kind: ntkIdent,
    head: ntype.head,
    genParams: ntype.genparams.mapIt(it.discardNimNode())
  )

proc discardNimNode(
  input: seq[ObjectField[NimNode, void]]): seq[ValField] =
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
                  notOfValue: ObjTree(
                    styling: initPrintStyling(),
                    # TODO save set representation
                  )
                )
              else:
                ValFieldBranch(
                  ofValue: ObjTree(
                    styling: initPrintStyling(),
                    kind: okConstant,
                    constType: $fld.fldType,
                    strLit: $it.ofValue.toStrLit()
                  ),
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

func parsePragma*[NNode](node: NNode, position: ObjectAnnotKind): Pragma[NNode] =
  result.kind = position
  case position:
    of oakObjectField:
      # debugecho node.idxTreeRepr
      node.expectKind nnkIdentDefs
      result.elements = toSeq(node[0][1].subnodes)

    else:
      node.expectKind nnkPragma
      result.elements = toSeq(node.subnodes)


func parseNimPragma*(node: NimNode, position: ObjectAnnotKind): NPragma =
  parsePragma(node, position)

func parsePPragma*(node: PNode, position: ObjectAnnotKind): Pragma[PNode] =
  parsePragma(node, position)


func getFuckingTypeImpl*(node: NimNode): NimNode =
  case node.kind:
    of nnkSym:
      getFuckingTypeImpl(node.getTypeImpl())

    of nnkIdent:
      raiseImplementError("Cannot get type implementation from ident")

    of nnkBracketExpr:
      getFuckingTypeImpl(node[1])

    of nnkObjectTy:
      return node

    else:
      raiseImplementKindError(node, node.treeRepr())

proc parseObject*[NNode, A](
    inNode: NNode,
    cb: ParseCb[NNode, A]
  ): ObjectDecl[NNode, A] =

  let node =
    case inNode.kind.toNNK():
      of nnkStmtList:
        inNode[0].expectKind nnkTypeSection
        inNode[0][0]

      of nnkSym:
        when NNode is PNode:
          raiseImplementError(
            "Parsing PNode from symbol on the first level is not supported")

        else:
          inNode.getFuckingTypeImpl()

      else:
        inNode

  if node.kind notin {nnkTypeDef, nnkObjectTy}:
    raiseImplementKindError(node, node.treeRepr())

  let declBody = tern(node.kind == nnkTypeDef, node[2], node)

  result = ObjectDecl[NNode, A](
    declNode: some(node),
    flds: declBody.getFields(cb)
  )




  if node.kind == nnkTypeDef:
    let (exported, name) = parseIdentName(node[0])

    result.exported = exported
    result.name = newNNType[NNode](name.getStrVal())


    when not (A is void):
      if node[0].kind.toNNK() == nnkPragmaExpr and cb != nil:
        result.annotation = some cb(node[0][1], oakObjectToplevel)

  elif inNode.kind == nnkSym:
    result.name = newNNtype[NNode](inNode.getStrVal())

  # else:
  #   result.name = newNNtype[NNode](node.getTypeImpl[0])
  #   echo node.treeRepr()



macro makeFieldsLiteral*(node: typed): untyped =
  result = node.getFields(
    noParseCb).discardNimNode.makeConstructAllFields()


type
  GenParams = object
    lhsObj, rhsObj, lhsName, rhsName, idxName, valIdxName, isKindName, fldName: string
    hackFields: bool

proc unrollFieldLoop[A](
  flds: seq[ObjectField[NimNode, A]],
  body: NimNode,
  fldIdx: int,
  genParam: GenParams): tuple[node: NimNode, fldIdx: int] =

  result.node = newStmtList()

  var fldIdx: int = fldIdx
  for fld in flds:
    var tmpRes = newStmtList()
    # echo &"Fld idx: {fldIdx} for {fld.name}"
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
          # echo tmp.toStrLit()
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
                "Fallback for value `" & $branch.ofValue.toStrLit() &
                  "` of field " & fld.name),
              branchBody
            )
          )
        else:
          caseBlock.add nnkOfBranch.newTree(
            branch.ofValue,
            newStmtList(
              newCommentStmtNode(
                "Branch for value `" & $branch.ofValue.toStrLit() &
                  "` of field " & fld.name),
              branchBody
            )
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

## Injected variables

:name: name of the current field
:lhs, rhs: value of current fields
:fldIdx: int. Index of current field in the object.
:valIdx: int. Index of current *value field* in the object
:lhsObj, rhsObj: Original objects being iterated. [1]_
:isKind:
  bool. Whether or not current field is used as case parameter for object

[1] Useful when iterating over results of expression

## Notes

### Limitations

- Private fields cannot be accessed directly - compilation will fail.
  Can be fixed by defining getter with the same name as a field (e.g
  for field `kind` define `func kind(t: T): KindType`). Dirty workaround
  is to use `hackPrivateParallelFieldPairs` - it can access private
  fields (but does not work if your private private field has a
  non-exported type)

### `fldIdx` and `valIdx`

Difference between `fldIdx` and `valIdx`. First one describes order of
fields **as defined** in object while second one shows order of fields
**as accessed** in object. For example, in object like this:

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

  let (unrolled, _) = getFields(
    lhsObj, noParseCb).unrollFieldLoop(body, 0, genParams)

  result = superquote do:
    block: ## Toplevel
      var `ident(genParams.valIdxName)`: int = 0
      let `ident(genParams.lhsObj)` = `lhsObj`
      let `ident(genParams.rhsObj)` = `rhsObj`
      `unrolled`

  # echo unrolled.repr


macro hackPrivateParallelFieldPairs*(lhsObj, rhsObj: typed, body: untyped): untyped =
  ## Same API as `parallelFieldPairs` but uses HACK to access private
  ## fields. NOT: due to HACK being used compilation is even slower.
  let genParams = GenParams(
    lhsObj: "lhsObj",
    rhsObj: "rhsObj",
    lhsName: "lhs",
    rhsName: "rhs",
    idxName: "fldIdx",
    valIdxName: "valIdx",
    isKindName: "isKind",
    fldName: "name",
    hackFields: true
  )

  let (unrolled, _) = getFields(
    lhsObj, noParseCb).unrollFieldLoop(body, 0, genParams)
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
