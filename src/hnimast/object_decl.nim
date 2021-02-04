import hast_common, idents_types, pragmas
import std/[macros, tables, options, strutils, sequtils]
import compiler/[ast, idents]
import hmisc/helpers
import hmisc/types/colorstring
import hast_common

type
  ParseCb*[NNode, Annot] = proc(
    pragma: NNode, kind: ObjectAnnotKind): Annot

  ObjectBranch*[NNode, Annot] = object
    ## Single branch of case object
    declNode*: Option[NNode]
    annotation*: Option[Annot]
    flds*: seq[ObjectField[NNode, Annot]] ## Fields in the case branch
    case isElse*: bool ## Whether this branch is placed under `else` in
                  ## case object.
      of true:
        notOfValue*: NNode
      of false:
        ofValue*: NNode ## Match value for case branch



  ObjectField*[NNode, Annot] = object
    declNode*: Option[NNode]
    docComment*: string
    codeComment*: string

    # TODO:DOC
    ## More complex representation of object's field - supports
    ## recursive fields with case objects.
    annotation*: Option[Annot]
    value*: Option[NNode]
    exported*: bool
    case isTuple*: bool # REVIEW REFACTOR move tuples into separate
                        # object instead of mixing them into `object`
                        # wrapper.
      of true:
        tupleIdx*: int

      of false:
        name*: string

    fldType*: NType[NNode] ## Type of field value
    case isKind*: bool
      of true:
        selected*: int ## Index of selected branch
        branches*: seq[ObjectBranch[NNode, Annot]] ## List of all
        ## branches as `value-branch` pairs.
      of false:
        discard

  ObjectDecl*[NNode, Annot] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    # TODO:DOC
    # TODO `flatFields` iterator to get all values with corresponding
    # parent `ofValue` branches. `for fld, ofValues in obj.flatFields()`
    exported*: bool
    annotation*: Option[Annot]
    # namedObject*: bool ## This object's type has a name? (tuples
    # ## does not have name for a tyep)
    # namedFields*: bool ## Fields have dedicated names? (anonymous
    # ## tuple does not have a name for fields)
    name*: NType[NNode] ## Name for an object
    # TODO rename to objType
    flds*: seq[ObjectField[NNode, Annot]]
    declNode*: Option[NNode]

  # FieldBranch*[Node] = ObjectBranch[Node, void]
  # Field*[Node] = ObjectField[Node, void]

  ObjectPathElem*[NNode, Annot] = object
    kindField*: ObjectField[NNode, Annot]
    case isElse*: bool
      of true:
        notOfValue*: NNode
      of false:
        ofValue*: NNode


  NObjectBranch*[A] = ObjectBranch[NimNode, A]
  NObjectPathElem*[A] = ObjectPathElem[NimNode, A]
  NObjectField*[A] = ObjectField[NimNode, A]
  NObjectDecl*[A] = ObjectDecl[NimNode, A]
  NObjectPath*[A] = seq[NObjectPathElem[A]]

  PObjectDecl* = ObjectDecl[PNode, Pragma[PNode]]
  PObjectField* = ObjectField[PNode, Pragma[PNode]]

const noParseCb*: ParseCb[NimNode, void] = nil
const noParseCbPNode*: ParseCb[PNode, void] = nil

proc newPObjectDecl*(
  name: string,
  flds: seq[tuple[name: string, ftype: NType[PNode]]] = @[],
  exported: bool = true,
  annotate: PPragma = PPragma(),
  docComment: string = "",
  codeComment: string = "",
  genParams: seq[NType[PNode]] = @[],
  iinfo: LineInfo = defaultIInfo,
): PObjectDecl =


  result.name = newNType[PNode](name, genParams)
  result.docComment = docComment
  result.codeComment = codeComment
  result.iinfo = iinfo
  result.annotation = some annotate
  result.exported = exported


func addField*[N](
    obj: var ObjectDecl[N, Pragma[N]],
    name: string,
    cxtype: NType[N],
    docComment: string = "",
    codeComment: string = "",
    exported: bool = true
  ) =

  obj.flds.add PObjectField(
    isTuple: false,
    isKind: false,
    name: name,
    fldType: cxtype,
    docComment: codeComment,
    codeComment: codeComment,
    exported: exported
  )

#=============================  Predicates  ==============================#
func markedAs*(fld: NObjectField[NPragma], str: string): bool =
  fld.annotation.getElem(str).isSome()

#===============================  Getters  ===============================#

# ~~~~ each field mutable ~~~~ #

func eachFieldMut*[NNode, A](
  obj: var ObjectDecl[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void

func eachFieldMut*[NNode, A](
  branch: var ObjectBranch[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in mutable object branch,
  ## recursively.
  for fld in mitems(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)


func eachFieldMut*[NNode, A](
  obj: var ObjectDecl[NNode, A],
  cb: (var ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in mutable object, recursively.
  for fld in mitems(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachFieldMut(branch, cb)

# ~~~~ each annotation mutable ~~~~ #

func eachAnnotMut*[NNode, A](
  branch: var ObjectBranch[NNode, A], cb: (var Option[A] ~> void)): void =
  ## Execute callback on each annotation in mutable branch,
  ## recursively - all fields in all branches are visited.
  for fld in mitems(branch.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in mitems(fld.branches):
        eachAnnotMut(branch, cb)

func eachAnnotMut*[NNode, A](
  obj: var ObjectDecl[NNode, A], cb: (var Option[A] ~> void)): void =
  ## Execute callback on each annotation in mutable object,
  ## recurisively - all fields and subfields are visited. Callback
  ## runs on both kind and non-kind fields. Annotation is not
  ## guaranteed to be `some`, and it might be possible for callback to
  ## make it `none` (removing unnecessary annotations for example)

  cb(obj.annotation)

  for fld in mitems(obj.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in mitems(fld.branches):
        branch.eachAnnotMut(cb)


# ~~~~ each field immutable ~~~~ #

func eachField*[NNode, A](
  obj: ObjectDecl[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void

func eachField*[NNode, A](
  branch: ObjectBranch[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in branch, recursively
  for fld in items(branch.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)


func eachField*[NNode, A](
  obj: ObjectDecl[NNode, A],
  cb: (ObjectField[NNode, A] ~> void)): void =
  ## Execute callback on each field in object, recurisively.
  for fld in items(obj.flds):
    cb(fld)
    if fld.isKind:
      for branch in items(fld.branches):
        eachField(branch, cb)

# ~~~~ each alternative in case object ~~~~ #

func eachCase*[A](
  fld: NObjectField[A], objId: NimNode, cb: (NObjectField[A] ~> NimNode)): NimNode =
  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId, ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        result.add nnkElse.newTree(
          branch.flds.mapIt(it.eachCase(objId, cb))
        )
      else:
        result.add nnkOfBranch.newTree(
          branch.ofValue,
          branch.flds.mapIt(
            it.eachCase(objId, cb)).newStmtList()
        )

    let cbRes = cb(fld)
    if cbRes != nil:
      result = newStmtList(cb(fld), result)
  else:
    result = newStmtList(cb(fld))

func eachCase*[A](
  objId: NimNode, obj: NObjectDecl[A], cb: (NObjectField[A] ~> NimNode)): NimNode =
  ## Recursively generate case statement for object. `objid` is and
  ## identifier for object - case statement will use `<objid>.<fldId>`.
  ## `obj` is a description for structure. Callback `cb` will be executed
  ## on all fields - both `isKind` or not.

  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachCase(objid, cb)

func eachParallelCase*[A](
  fld: NObjectField[A], objId: (NimNode, NimNode),
  cb: (NObjectField[A] ~> NimNode)): NimNode =
  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(objId[0], ident fld.name))
    for branch in fld.branches:
      if branch.isElse:
        result.add nnkElse.newTree(
          branch.flds.mapIt(it.eachParallelCase(objId, cb))
        )
      else:
        result.add nnkOfBranch.newTree(
          branch.ofValue,
          branch.flds.mapIt(
            it.eachParallelCase(objId, cb)).newStmtList()
        )

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

func eachParallelCase*[A](
  objid: (NimNode, NimNode), obj: NObjectDecl[A], cb: (NObjectField[A] ~> NimNode)): NimNode =
  ## Generate parallel case statement for two objects in `objid`. Run
  ## callback on each field. Generated case statement will have form
  ## `if lhs.fld == rhs.fld: case lhs.fld`
  result = newStmtList()
  for fld in obj.flds:
    result.add fld.eachParallelCase(objid, cb)



# ~~~~ each annotation immutable ~~~~ #

func eachAnnot*[Node, A](
  branch: ObjectBranch[Node, A], cb: (Option[A] ~> void)): void =
  for fld in items(branch.flds):
    cb(fld.annotation)
    if fld.isKind:
      for branch in items(fld.branches):
        eachAnnot(branch, cb)

func eachAnnot*[Node, A](
  obj: ObjectDecl[Node, A], cb: (Option[A] ~> void)): void =

  cb(obj.annotation)

  for fld in items(obj.flds):
    cb(fld.annotation.get())
    if fld.isKind:
      for branch in items(fld.branches):
        branch.eachAnnot(cb)


# ~~~~ Each path in case object ~~~~ #
func eachPath*[A](
  fld: NObjectField[A], self: NimNode, parent: NObjectPath[A],
  cb: ((NObjectPath[A], seq[NObjectField[A]]) ~> NimNode)): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(newDotExpr(self, ident fld.name))
    for branch in fld.branches:
      var branchBody = newStmtList()
      let nobranch = (fld.withIt do: it.branches = @[])
      let thisPath =
        if branch.isElse:
          parent & @[NObjectPathElem[A](
            isElse: true, kindField: nobranch, notOfValue: branch.notOfValue)]
        else:
          parent & @[NObjectPathElem[A](
            isElse: false, kindField: nobranch, ofValue: branch.ofValue)]

      let cbRes = cb(thisPath, branch.flds).nilToDiscard()
      if branch.isElse:
        branchBody.add nnkElse.newTree(cbRes)
      else:
        branchBody.add nnkOfBranch.newTree(branch.ofValue, cbRes)

      for fld in branch.flds:
        branchBody.add fld.eachPath(self, thisPath, cb)


func eachPath*[A](
  self: NimNode,
  obj: NObjectDecl[A], cb: ((NObjectPath[A], seq[NObjectField[A]]) ~> NimNode)): NimNode =
  ## Visit each group of fields in object described by `obj` and
  ## generate case statement with all possible object paths. Arguments
  ## for callback - `NObjectPath[A]` is a sequence of kind field values that
  ## *must be active in order for execution to reach this path* in
  ## case statement. Second argument is a list of fields that can be
  ## accessed at that path.
  ## TODO:DOC add example

  result = newStmtList cb(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.eachPath(self, @[], cb)


func onPath*[A](self: NimNode, path: NObjectPath[A]): NimNode =
  ## Generate check for object `self` to check if it is currently on
  ## path.
  var checks: seq[NimNode]
  for elem in path:
    if elem.isElse:
      checks.add newInfix(
        "notin", newDotExpr(self, ident elem.kindField.name),
        normalizeSet(elem.notOfValue, forceBrace = true))
    else:
      checks.add newInfix(
        "in", newDotExpr(self, ident elem.kindField.name),
        normalizeSet(elem.ofValue, forceBrace = true))

  if checks.len == 0:
    return newLit(true)
  else:
    result = checks.foldl(newInfix("and", a, b))


#========================  Other implementation  =========================#
func toNNode*[NNode, A](
  fld: ObjectField[NNode, A], annotConv: A ~> NNode): NNode

func toNNode*[NNode, A](
  branch: ObjectBranch[NNode, A], annotConv: A ~> NNode): NNode =
  if branch.isElse:
    newNTree[NNode](
      nnkElse,
      nnkRecList.newTree(branch.flds.mapIt(it.toNNode(annotConv))))

  else:
    newNTree[NNode](
      nnkOfBranch,
      branch.ofValue,
      nnkRecList.newTree(branch.flds.mapIt(it.toNNode(annotConv))))


func toNNode*[NNode, A](
  fld: ObjectField[NNode, A], annotConv: A ~> NNode): NNode =

  let head =
    if fld.exported:
      newNTree[NNode](nnkPostfix,
                      newNIdent[NNode]("*"),
                      newNIdent[NNode](fld.name))
    else:
      newNIdent[NNode](fld.name)

  let fieldName =
    if fld.annotation.isSome():
      let pragma = annotConv(fld.annotation.get())
      newNTree[NNode](nnkPragmaExpr, head, pragma)
    else:
      head


  let selector = newNTree[NNode](
    nnkIdentDefs,
    fieldName,
    toNNode[NNode](fld.fldType),
    newEmptyNNode[NNode]()
  )

  if fld.isKind:
    return nnkRecCase.newTree(
      @[selector] & fld.branches.mapIt(toNNode[NNode](it, annotConv)))

  else:
    return selector

func toExported*[NNode](ntype: NType[NNode], exported: bool): tuple[
  head, genparams: NNode] =
  result.head =
    if exported:
      newNTree[NNode](
        nnkPostfix,
        newNIdent[NNode]("*"),
        newNIdent[NNode](ntype.head)
      )
    else:
      newNIdent[NNode](ntype.head)

  result.genparams =
    block:
      let maps = ntype.genParams.mapIt(toNNode[NNode](it))
      if maps.len == 0:
        newEmptyNNode[NNode]()
      else:
        newNTree[NNode](nnkGenericParams, maps)



func toNNode*[NNode, A](
  obj: ObjectDecl[NNode, A], annotConv: A ~> NNode): NNode =

  let (head, genparams) = obj.name.toExported(obj.exported)
  let header =
    if obj.annotation.isSome():
      let node = annotConv obj.annotation.get()
      if node.kind != nnkEmpty:
        newNTree[NNode](nnkPragmaExpr, head, node)

      else:
        head

    else:
      head

  result = newNTree[NNode](
    nnkTypeDef,
    header,
    genparams,
    newNTree[NNode](
      nnkObjectTy,
      newEmptyNNode[NNode](),
      newEmptyNNode[NNOde](),
      newNTree[NNode](
        nnkRecList,
        obj.flds.mapIt(toNNode(it, annotConv))))) # loud LISP sounds

  # echov result.treeRepr()

func toNNode*[NNode](
  obj: ObjectDecl[NNode, PRagma[NNode]], standalone: bool = false): NNode =
  result = toNNode[NNode](
    obj, annotConv =
      proc(pr: Pragma[NNode]): NNode {.closure.} =
        return toNNode[NNode](pr)
  )

  if standalone:
    result = newNTree[NNode](
      nnkTypeSection,
      result
    )

func toNimNode*(obj: NObjectDecl[NPragma]): NimNode =
  # static: echo typeof obj
  toNNode[NimNode](obj)


func toNNode*[N](fld: ObjectField[N, PRagma[N]]): N =
  result = toNNode[N](
    fld, annotConv =
      proc(pr: Pragma[N]): N {.closure.} =
        return toNNode[N](pr)
  )


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

  ObjAccs = object
    # TODO:DOC
    case isIdx*: bool
      of true:
        idx*: int
      of false:
        name*: string

  ObjPath = seq[ObjAccs]

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
    path*: seq[int] ## Path of object in original tree
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
  ValField* = ObjectField[ObjTree, void]
  ValFieldBranch* = ObjectBranch[ObjTree, void]


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
func `==`*[Node, A](lhs, rhs: ObjectField[Node, A]): bool

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

func `==`*[Node, A](lhs, rhs: ObjectField[Node, A]): bool =
  lhs.isKind == rhs.isKind and
    (
      case lhs.isKind:
        of true:
          lhs.name == rhs.name and
          lhs.fldType == rhs.fldType and
          (when A is void: true else: subnodesEq(lhs, rhs, branches))
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

func objAccs*(idx: int): ObjAccs =
  # TODO:DOC
  ObjAccs(isIdx: true, idx: idx)
func objAccs*(name: string): ObjAccs =
  # TODO:DOC
  ObjAccs(isIdx: false, name: name)

func objPath*(path: varargs[ObjAccs, `objAccs`]): ObjPath =
  # TODO:DOC
  toSeq(path)

func getAtPath*(obj: var ObjTree, path: ObjPath): var ObjTree =
  case obj.kind:
    of okComposed:
      if path.len < 1:
        return obj
      else:
        if path[0].isIdx:
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

      if not path[0].isIdx:
        argumentError:
          "Cannot access sequence elements by name, path {path}"
          "starts with non-index"

      elif path.len == 1:
        return obj.valItems[path[0].idx]

      else:
        return obj.valItems[path[0].idx].getAtPath(path[1..^1])

    else:
      raiseImplementError("")