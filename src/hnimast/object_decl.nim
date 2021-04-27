import hast_common, idents_types, pragmas
import std/[macros, tables, options, strutils, sequtils]
import compiler/[ast, idents]
import hmisc/helpers
import hmisc/types/colorstring
import hast_common

type
  ObjectBranch*[N] = ref object
    ## Single branch of case object
    declNode*: Option[N]
    pragma*: Option[PRagma[N]]
    flds*: seq[ObjectField[N]] ## Fields in the case branch
    case isElse*: bool ## Whether this branch is placed under `else` in
                  ## case object.
      of true:
        notOfValue*: seq[N]
      of false:
        ofValue*: seq[N] ## Match value for case branch



  ObjectField*[N] = ref object
    declNode*: Option[N]
    docComment*: string
    codeComment*: string

    # TODO:DOC
    ## More complex representation of object's field - supports
    ## recursive fields with case objects.
    pragma*: Option[Pragma[N]]
    value*: Option[N]
    isExported*: bool
    case isTuple*: bool # REVIEW REFACTOR move tuples into separate
                        # object instead of mixing them into `object`
                        # wrapper.
      of true:
        tupleIdx*: int

      of false:
        name*: string

    fldType*: NType[N] ## Type of field value
    isChecked*: bool
    case isKind*: bool
      of true:
        selected*: int ## Index of selected branch
        branches*: seq[ObjectBranch[N]] ## List of all
        ## branches as `value-branch` pairs.
      of false:
        discard

  ObjectDecl*[N] = ref object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    # TODO:DOC
    # TODO `flatFields` iterator to get all values with corresponding
    # parent `ofValue` branches. `for fld, ofValues in obj.flatFields()`
    exported*: bool
    pragma*: Option[Pragma[N]]
    # namedObject*: bool ## This object's type has a name? (tuples
    # ## does not have name for a tyep)
    # namedFields*: bool ## Fields have dedicated names? (anonymous
    # ## tuple does not have a name for fields)
    name*: NType[N] ## Name for an object
    # TODO rename to objType
    flds*: seq[ObjectField[N]]
    declNode*: Option[N]

  # FieldBranch*[Node] = ObjectBranch[Node, void]
  # Field*[Node] = ObjectField[Node, void]

  ObjectPathElem*[N] = object
    kindField*: ObjectField[N]
    case isElse*: bool
      of true:
        notOfValue*: seq[N]

      of false:
        ofValue*: seq[N]


  ObjectPath*[N] = seq[ObjectPathElem[N]]
  NObjectBranch* = ObjectBranch[NimNode]
  NObjectPathElem* = ObjectPathElem[NimNode]
  NObjectField* = ObjectField[NimNode]
  NObjectDecl* = ObjectDecl[NimNode]
  NObjectPath* = seq[NObjectPathElem]

  PObjectDecl* = ObjectDecl[PNode]
  PObjectField* = ObjectField[PNode]
  PObjectBranch* = ObjectBranch[PNode]

proc newPObjectDecl*(
  name: string,
  flds: seq[tuple[name: string, ftype: NType[PNode]]] = @[],
  exported: bool = true,
  pragma: PPragma = PPragma(),
  docComment: string = "",
  codeComment: string = "",
  genParams: seq[NType[PNode]] = @[],
  iinfo: LineInfo = defaultIInfo,
): PObjectDecl =


  result.name = newNType[PNode](name, genParams)
  result.docComment = docComment
  result.codeComment = codeComment
  result.iinfo = iinfo
  result.pragma = some pragma
  result.exported = exported

func newObjectField*[N](
    name: string,
    cxtype: NType[N],
    docComment: string = "",
    codeComment: string = "",
    exported: bool = true
  ): ObjectField[N] =

  ObjectField[N](
    isTuple: false,
    isKind: false,
    name: name,
    fldType: cxtype,
    docComment: docComment,
    codeComment: codeComment,
    exported: exported
  )

func addField*[N](
    obj: var ObjectDecl[N],
    name: string,
    cxtype: NType[N],
    docComment: string = "",
    codeComment: string = "",
    exported: bool = true
  ) {.deprecated: "use .addField(newObjectField())".} =

  obj.flds.add newObjectField(
    name, cxtype, docComment, codeComment, exported)

func addField*[N](obj: var ObjectDecl[N], field: ObjectField[N]) =
  obj.flds.add field

func newObjectCaseField*[N](
    name: string,
    fieldType: NType[N],
    docComment: string = "",
    codeComment: string = "",
    exported: bool = true
  ): ObjectField[N] =

  ObjectField[N](
    isTuple: false,
    isKind: true,
    name: name,
    fldType: fieldType,
    docComment: docComment,
    codeComment: codeComment,
    exported: exported,
  )

func newObjectOfBranch*[N](ofValue: N): ObjectBranch[N] =
  ObjectBranch[N](isElse: false, ofValue: @[ ofValue ])

func newObjectOfBranch*[N](ofValue: seq[N]): ObjectBranch[N] =
  ObjectBranch[N](isElse: false, ofValue: ofValue)

func newObjectElseBranch*[N](): ObjectBranch[N] =
  ObjectBranch[N](isElse: true)

func addField*[N](
    branch: var ObjectBranch[N],
    field: ObjectField[N]
  ) = branch.flds.add field

func addBranch*[N](field: var ObjectField[N], branch: ObjectBranch[N]) =
  field.branches.add branch

func addBranch*[N](
    field: var ObjectField[N],
    ofValue: N | seq[N],
    fields: varargs[ObjectField[N]]
  ) =

  var branch = newObjectOfBranch(ofValue)
  for field in fields:
    branch.addField(field)

  field.addBranch(branch)


#=============================  Predicates  ==============================#
func isMarkedWith*(fld: NObjectField, str: string): bool =
  fld.pragma.getElem(str).isSome()

#===============================  Getters  ===============================#

# ~~~~ each field mutable ~~~~ #

proc eachFieldMut*[N](
  obj: var ObjectDecl[N],
  cb: proc(field: var ObjectField[N])): void

proc eachFieldMut*[N](
  branch: var ObjectBranch[N],
  cb: proc(field: var ObjectField[N])): void =
  ## Execute callback on each field in mutable object branch,
  ## recursively.
  for fld in mitems(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)


proc eachFieldMut*[N](
  obj: var ObjectDecl[N],
  cb: proc(field: var ObjectField[N])): void =
  ## Execute callback on each field in mutable object, recursively.
  for fld in mitems(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)

# ~~~~ each annotation mutable ~~~~ #

proc eachField*[N](
  obj: ObjectDecl[N],
  cb: proc(field: ObjectField[N])): void

proc eachField*[N](
    branch: ObjectBranch[N],
    cb: proc(field: ObjectField[N])
  ): void =
  ## Execute callback on each field in branch, recursively
  for fld in items(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)


proc eachField*[N](
    obj: ObjectDecl[N],
    cb: proc(field: ObjectField[N])
  ): void =
  ## Execute callback on each field in object, recurisively.
  for fld in items(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)

# ~~~~ each alternative in case object ~~~~ #
proc eachCase*(
    fld: NObjectField, objId: NimNode,
    cb: proc(field: NObjectField): NimNode
  ): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId, ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        var body = nnkElse.newTree()
        for field in branch.flds:
          body.add eachCase(field, objId, cb)

        if isEmptyNode(body):
          result.add newDiscardStmt()

        else:
          result.add body

      else:
        var body = newStmtList()
        for field in branch.flds:
          body.add eachCase(field, objId, cb)


        if isEmptyNode(body):
          result.add nnkOfBranch.newTree(
            nnkCurly.newTree(branch.ofValue),
            newDiscardStmt()
          )

        else:
          result.add nnkOfBranch.newTree(
            nnkCurly.newTree(branch.ofValue), body)

    let cbRes = cb(fld)
    if cbRes != nil:
      result = newStmtList(cbRes, result)

  else:
    result = newStmtList(cb(fld))

proc eachCase*(
    objId: NimNode, obj: NObjectDecl,
    cb: proc(field: NObjectField): NimNode
  ): NimNode =
  ## Recursively generate case statement for object. `objid` is and
  ## identifier for object - case statement will use `<objid>.<fldId>`.
  ## `obj` is a description for structure. Callback `cb` will be executed
  ## on all fields - both `isKind` or not.

  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachCase(objid, cb)

proc eachParallelCase*(
    fld: NObjectField, objId: (NimNode, NimNode),
    cb: proc(field: NObjectField): NimNode
  ): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId[0], ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        result.add nnkElse.newTree(
          branch.flds.mapIt(it.eachParallelCase(objId, cb))
        )
      else:
        result.add nnkOfBranch.newTree(
          nnkCurly.newTree(branch.ofValue),
          branch.flds.mapIt(
            it.eachParallelCase(objId, cb)).newStmtList())

    let
      fldId = ident fld.name
      lhsId = objId[0]
      rhsId = objId[1]

    let cbRes = cb(fld)
    result = quote do:
      `cbRes`
      if `lhsId`.`fldId` == `rhsId`.`fldId`:
        `result`

  else:
    result = newStmtList(cb(fld))

proc eachParallelCase*(
    objid: (NimNode, NimNode), obj: NObjectDecl,
    cb: proc(field: NObjectField): NimNode
  ): NimNode =
  ## Generate parallel case statement for two objects in `objid`. Run
  ## callback on each field. Generated case statement will have form
  ## `if lhs.fld == rhs.fld: case lhs.fld`
  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachParallelCase(objid, cb)



# ~~~~ each annotation immutable ~~~~ #

proc eachStaticPath*(
    kind: NimNode,
    obj: NObjectDecl,
    cb: proc(fields: seq[NObjectField]): NimNode
  ): NimNode =

  var topFlds: seq[NObjectField]
  var trailFlds: seq[NObjectField]

  var kindCount = 0


  for fld in items(obj.flds):
    if fld.isKind:
      inc kindCount
      if kindCount > 1:
        raiseArgumentError(
          "Found more than one top-level kind field. " &
            "Single-argument static path only supports one kind.")

    else:
      if kindCount == 0:
        topFlds.add fld

      else:
        trailFlds.add fld



  result = nnkWhenStmt.newTree()

  for fld in items(obj.flds):
    if fld.isKind:
      for branch in fld.branches:
        if branch.isElse:
          result.add nnkElse.newTree(
            cb(topFlds & branch.flds & trailFlds))

        else:
          result.add nnkElifBranch.newTree(
            nnkInfix.newTree(
              ident "in", kind,
              nnkCurly.newTree(branch.ofValue)),
            cb(topFlds & branch.flds & trailFlds))





# ~~~~ Each path in case object ~~~~ #
proc eachPath*(
    fld: NObjectField, self: NimNode, parent: NObjectPath,
    cb: proc(path: NObjectPath, fields: seq[NObjectField]): NimNode
  ): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(self, ident fld.name))
    for branch in fld.branches:
      var branchBody = newStmtList()
      let thisPath =
        if branch.isElse:
          parent & @[NObjectPathElem(
            isElse: true, kindField: fld,
            notOfValue: branch.notOfValue)]

        else:
          parent & @[NObjectPathElem(
            isElse: false, kindField: fld,
            ofValue: branch.ofValue)]

      let cbRes = cb(thisPath, branch.flds).nilToDiscard()
      if branch.isElse:
        branchBody.add nnkElse.newTree(cbRes)
      else:
        branchBody.add nnkOfBranch.newTree(
          nnkCurly.newTree(branch.ofValue), cbRes)

      for fld in branch.flds:
        branchBody.add fld.eachPath(self, thisPath, cb)


proc eachPath*(
    self: NimNode,
    obj: NObjectDecl,
    cb: proc(path: NObjectPath, fields: seq[NObjectField]): NimNode
  ): NimNode =
  ## Visit each group of fields in object described by `obj` and
  ## generate case statement with all possible object paths. Arguments
  ## for callback - `NObjectPath` is a sequence of kind field values that
  ## *must be active in order for execution to reach this path* in
  ## case statement. Second argument is a list of fields that can be
  ## accessed at that path.
  ## TODO:DOC add example

  result = newStmtList cb(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.eachPath(self, @[], cb)

proc eachPath*(
    self: NimNode,
    obj: NObjectDecl,
    cb: proc(fields: seq[NObjectField]): NimNode
  ): NimNode =

  return eachPath(
    self, obj,
    proc(path: NObjectPath, fields: seq[NObjectField]): NimNode =
      cb(fields)
  )


func onPath*(self: NimNode, path: NObjectPath): NimNode =
  ## Generate check for object `self` to check if it is currently on
  ## path.
  var checks: seq[NimNode]
  for elem in path:
    if elem.isElse:
      checks.add newInfix(
        "notin", newDotExpr(self, ident elem.kindField.name),
        nnkCurly.newTree(elem.notOfValue))

    else:
      checks.add newInfix(
        "in", newDotExpr(self, ident elem.kindField.name),
        nnkCurly.newTree(elem.ofValue))

  if checks.len == 0:
    return newLit(true)

  else:
    result = checks.foldl(newInfix("and", a, b))


#========================  Other implementation  =========================#
func toNNode*[N](fld: ObjectField[N]): N

func toNNode*[N](branch: ObjectBranch[N]): N =
  if branch.isElse:
    result = newNTree[N](
      nnkElse,
      nnkRecList.newTree(branch.flds.mapIt(toNNode(it))))

  else:
    result = newNTree[N](
      nnkOfBranch,
      branch.ofValue & nnkRecList.newTree(
        branch.flds.mapIt(toNNode(it))))



func toNNode*[N](fld: ObjectField[N]): N =
  let head =
    if fld.isExported:
      newNTree[N](nnkPostfix,
                      newNIdent[N]("*"),
                      newNIdent[N](fld.name))
    else:
      newNIdent[N](fld.name)

  let fieldName =
    if fld.pragma.isSome():
      let pragma = fld.pragma.get().toNNode()
      newNTree[N](nnkPragmaExpr, head, pragma)

    else:
      head

  var selector = newNTree[N](
    nnkIdentDefs,
    fieldName,
    toNNode[N](fld.fldType),
    newEmptyNNode[N]()
  )

  when N is PNode:
    selector.comment = fld.docComment

  if fld.isKind:
    result = nnkRecCase.newTree(
      @[selector] & fld.branches.mapIt(toNNode[N](it)))

  else:
    result = selector



func toExported*[N](ntype: NType[N], exported: bool): tuple[
  head, genparams: N] =
  result.head =
    if exported:
      newNTree[N](
        nnkPostfix,
        newNIdent[N]("*"),
        newNIdent[N](ntype.head)
      )
    else:
      newNIdent[N](ntype.head)

  result.genparams =
    block:
      let maps = ntype.genParams.mapIt(toNNode[N](it))
      if maps.len == 0:
        newEmptyNNode[N]()
      else:
        newNTree[N](nnkGenericParams, maps)



func toNNode*[N](obj: ObjectDecl[N], standalone: bool = false): N =
  let (head, genparams) = obj.name.toExported(obj.exported)
  let header =
    if obj.pragma.isSome():
      let node = toNNode(obj.pragma.get())
      if node.kind != nnkEmpty:
        newNTree[N](nnkPragmaExpr, head, node)

      else:
        head

    else:
      head


  var comment: seq[N]
  when N is PNode:
    if obj.docComment.len > 0:
      comment.add newCommentStmtNNode[N](obj.docComment)

  result = newNTree[N](
    nnkTypeDef,
    header,
    genparams,
    newNTree[N](
      nnkObjectTy,
      newEmptyNNode[N](),
      newEmptyNNode[N](),
      newNTree[N](
        nnkRecList,
        comment & obj.flds.mapIt(toNNode(it))))) # loud LISP sounds

  if standalone:
    result = newNTree[N](nnkTypeSection, result)



func toNimNode*(obj: NObjectDecl): NimNode =
  toNNode[NimNode](obj)

type
  ObjKind* = enum
    # TODO:DOC
    okConstant ## Literal value
    okSequence ## Sequence of items
    okTable ## List of key-value pairs with single types for keys and
    ## values
    okComposed ## Named list of field-value pairs with possilby
    ## different types for fields (and values). List name is optional
    ## (unnamed object), field name is optional (unnamed fields)

  ObjRelationKind = enum
    # TODO:DOC
    orkComposition
    orkReference
    orkPointer

  ObjAccessor* = object
    case kind*: ObjKind
      of okConstant:
        nil

      of okSequence:
        idx*: int

      of okComposed:
        name*: string

      of okTable:
        key*: string

  ObjPath* = seq[ObjAccessor]

  ObjTree* = object
    ##[

## Fields

:isPrimitive: Value is primitve or not?

  Primitive value will be added to graphviz node export as part of the
  table (in regular export) as oppposed to non-primitive value (it
  will be rendered as separate node). By default primitive values are
  `int`, `string`, `float` etc. types, tuples/objects that are (1)
  composed only from primitive types (`(int, int)`), (2) have four
  fields or less. Also tables/sequences with four elements or less are
  considered primitive if (1) both keys and values are primitive (2)
  container has four elements or less.

    ]##
    ignored*: bool
    path*: ObjPath ## Path of object in original tree
    objId*: int ## Unique object id
    isPrimitive*: bool ## Whether or not value can be considered primitive
    annotation*: string ## String annotation for object
    styling* {.requiresinit.}: PrintStyling ## Print styling for object
    case kind*: ObjKind
      of okConstant:
        constType*: string ## Type of the value
        strlit*: string ## Value representation in string form
      of okSequence:
        itemType*: string ## Type of the sequence item
        valItems*: seq[ObjTree] ## List of values
      of okTable:
        keyStyling* {.requiresinit.}: PrintStyling
        keyType*: string ## Type of table key
        valType*: string ## TYpe of value key
        valPairs*: seq[tuple[key: string, val: ObjTree]] ## List of
        ## key-value pairs for table
        # XXXX TODO TEST used `ObjTree` for key too. Non-trivial types
        # can be used. Write unit tests for this functionality.

        # NOTE REFACTOR use `value` for enum field.
      of okComposed:
        namedObject*: bool ## This object's type has a name? (tuples
        ## does not have name for a tyep)
        namedFields*: bool ## Fields have dedicated names? (anonymous
        ## tuple does not have a name for fields)
        name*: string ## Name for an object
        # TODO Add field type
        fldPairs*: seq[tuple[name: string, value: ObjTree]] ## Sequence
        ## of field-value pairs for object representation



  ObjElem*[Conf] = object
    # TODO:DOC
    case isValue: bool
      of true:
        text*: string
        config*: Conf
      of false:
        relType*: ObjRelationKind
        targetId*: int


type
  ValField* = ObjectField[ObjTree]
  ValFieldBranch* = ObjectBranch[ObjTree]

func fields*[N](objectDecl: OBjectDecl[N]): seq[OBjectField[N]] =
  objectDecl.flds

func newOType*(name: string, gparams: seq[string] = @[]): NType[ObjTree] =
  NType[ObjTree](
    kind: ntkIdent,
    head: name,
    genParams: gparams.mapIt(newOType(it, @[]))
  )

proc prettyPrintConverter*(val: PNode, path: seq[int] = @[0]): ObjTree =
  # TODO can add syntax hightlight to string literal generated from
  #      nim node
  ObjTree(
    styling: initPrintStyling(),
    kind: okConstant,
    constType: "PNode",
    strLit: $val
  )

#=============================  Predicates  ==============================#
func `==`*[Node](lhs, rhs: ObjectField[Node]): bool

func `==`*(lhs, rhs: ObjTree): bool =
  lhs.kind == rhs.kind and
    (
      case lhs.kind:
        of okConstant:
          lhs.constType == rhs.constType and
          lhs.strLit == rhs.strLit
        of okSequence:
          lhs.itemType == rhs.itemType and
          subnodesEq(lhs, rhs, valItems)
        of okTable:
          lhs.keyType == rhs.keyType and
          lhs.valType == rhs.valType and
          zip(lhs.valPairs, rhs.valPairs).allOfIt(
            (it[0].key == it[1].key) and (it[0].val == it[1].val)
          )
        of okComposed:
          lhs.namedObject == rhs.namedObject and
          lhs.namedFields == rhs.namedFields and
          lhs.name == rhs.name and
          subnodesEq(lhs, rhs, fldPairs)
    )

func `==`*[Node](lhs, rhs: ObjectField[Node]): bool =
  lhs.isKind == rhs.isKind and
    (
      case lhs.isKind:
        of true:
          lhs.name == rhs.name and
          lhs.fldType == rhs.fldType and
          subnodesEq(lhs, rhs, branches)
        of false:
          true
    )

#============================  Constructors  =============================#
func makeObjElem*[Conf](text: string, conf: Conf): ObjElem[Conf] =
  # TODO:DOC
  ObjElem[Conf](isValue: true, text: text, config: conf)

func initObjTree*(): ObjTree =
  # TODO:DOC
  ObjTree(styling: initPrintStyling())


#=======================  Annotation and styling  ========================#

func annotate*(tree: var ObjTree, annotation: string): void =
  # TODO:DOC
  tree.annotation = annotation

func stylize*(tree: var ObjTree, conf: PrintStyling): void =
  # TODO:DOC
  tree.styling = conf

func styleTerm*(str: string, conf: PrintStyling): string =
  # TODO:DOC
  $ColoredString(str: str, styling: conf)

#=============================  Path access  =============================#

func seqAccs*(idx: int): ObjAccessor =
  # TODO:DOC
  ObjAccessor(kind: okSequence, idx: idx)

func objAccs*(name: string): ObjAccessor =
  ObjAccessor(kind: okComposed, name: name)

func tableAccs*(name: string): ObjAccessor =
  ObjAccessor(kind: okTable, key: name)

func getAtPath*(obj: var ObjTree, path: ObjPath): var ObjTree =
  case obj.kind:
    of okComposed:
      if path.len < 1:
        return obj
      else:
        if path[0].kind == okSequence:
          return obj.fldPairs[path[0].idx].value.getAtPath(path[1..^1])

        else:
          if obj.namedFields:
            for fld in mitems(obj.fldPairs):
              if fld.name == path[0].name:
                 return fld.value.getAtPath(path[1..^1])

            argumentError:
              "Cannot get field name '{path[0].name}'"
              "from object - no such field found"

          else:
            argumentError:
              "Cannot get field name '{path[0].name}'"
              "from object with unnamed fields"

    of okConstant:
      if path.len > 1:
        argumentError:
          "Attempt to access subelements of constant value at path {path}"

      else:
        return obj
    of okSequence:
      if path.len == 0:
        return obj

      if path[0].kind != okSequence:
        argumentError:
          "Cannot access sequence elements by name, path {path}"
          "starts with non-index"

      elif path.len == 1:
        return obj.valItems[path[0].idx]

      else:
        return obj.valItems[path[0].idx].getAtPath(path[1..^1])

    else:
      raiseImplementError("")

func hasPragma*[N](decl: ObjectDecl[N], name: string): bool =
  decl.pragma.isSome() and decl.pragma.get().hasElem(name)

func getPragmaArgs*[N](decl: ObjectDecl[N], name: string): seq[N] =
  for arg in decl.pragma.getElem(name).get()[1 ..^ 1]:
    result.add arg

func eachPragmaMut*[N](
    branch: var ObjectBranch[N],
    cb: proc(opt: var Option[Pragma[N]])) =
  ## Execute callback on each annotation in mutable branch,
  ## recursively - all fields in all branches are visited.
  for fld in mitems(branch.flds):
    cb(fld.pragma)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachPragmaMut(branch, cb)

func eachPragmaMut*[N](
    obj: var ObjectDecl[N], cb: proc(pragma: var Option[Pragma[N]])) =
  ## Execute callback on each annotation in mutable object,
  ## recurisively - all fields and subfields are visited. Callback
  ## runs on both kind and non-kind fields. Annotation is not
  ## guaranteed to be `some`, and it might be possible for callback to
  ## make it `none` (removing unnecessary annotations for example)

  cb(obj.pragma)

  for fld in mitems(obj.flds):
    cb(fld.pragma)
    if fld.isKind:
      for branch in mitems(fld.branches):
        branch.eachPragmaMut(cb)

func eachPragma*[N](
    branch: ObjectBranch[N],
    cb: proc(pragma: Option[PRagma[N]])
  ) =

  for fld in items(branch.flds):
    cb(fld.pragma)
    if fld.isKind:
      for branch in items(fld.branches):
        eachPragma(branch, cb)

func eachPragma*[N](obj: ObjectDecl[N], cb: proc(opt: Option[Pragma[N]])) =
  cb(obj.pragma)
  for fld in items(obj.flds):
    cb(fld.pragma)
    if fld.isKind:
      for branch in items(fld.branches):
        branch.eachPragma(cb)
