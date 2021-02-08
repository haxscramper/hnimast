import hast_common, pragmas
export hast_common

import hmisc/helpers
import std/[macros, options, sugar, strformat, parseutils, sequtils]

type
  EnumFieldVal* = enum
    efvNone
    efvIdent
    efvOrdinal
    efvString
    efvOrdString

  RTimeOrdinalKind* = enum
    rtokInt
    rtokBool
    rtokChar

  RTimeOrdinal* = object
    case kind*: RTimeOrdinalKind
      of rtokInt:
        intVal*: BiggestInt
      of rtokBool:
        boolVal*: bool
      of rtokChar:
        charVal*: char

  EnumField*[NNode] = object
    docComment*: string
    codeComment*: string
    name*: string
    value*: Option[NNode]
    declNode*: Option[NNode]

    case kind*: EnumFieldVal
      of efvNone:
        discard

      of efvIdent:
        ident*: NNode

      of efvOrdinal:
        ordVal*: RtimeOrdinal

      of efvString:
        strval*: string

      of efvOrdString:
        ordStr*: tuple[ordVal: RtimeOrdinal, strval: string]


  EnumDecl*[NNode] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string
    declNode*: Option[NNode]

    # ## Enum declaration wrapper
    # meta*: DeclMetainfo

    name*: string
    values*: seq[EnumField[NNode]]
    exported*: bool
    pragma*: Pragma[NNode]

  NEnumDecl* = EnumDecl[NimNode]
  PEnumDecl* = EnumDecl[PNode]

#=============================  Predicates  ==============================#
func isEnum*(en: NimNode): bool =
  ## Check if `typeImpl` for `en` is `enum`
  en.getTypeImpl().kind == nnkEnumTy

#===============================  parsers  ===============================#

func makeEnumField*[NNode](
  name: string,
  value: Option[NNode] = none(NNode),
  comment: string = ""): EnumField[NNode] =
  EnumField[NNode](name: name, value: value, docComment: comment)

func newPEnumDecl*(
    name:        string,
    docComment:  string        = "",
    codeComment: string        = "",
    exported:    bool          = true,
    pragma:      Pragma[PNode] = Pragma[PNode](),
    iinfo:       LineInfo      = defaultIInfo
  ): EnumDecl[PNode] =

  result.name = name
  result.docComment = docComment
  result.codeComment = codeComment
  result.exported = exported
  result.pragma = pragma
  result.iinfo = iinfo

func addField*[N](
    en: var EnumDecl[N],
    name: string,
    value: Option[N] = none(N),
    docComment: string = ""
  ) =

  en.values.add makeEnumField(name, value, docComment)



func parseEnumField*[NNode](fld: NNode): EnumField[NNode] =
  case fld.kind.toNNK():
    of nnkEnumFieldDef:
      let val = fld[1]
      case val.kind.toNNK():
        of nnkCharLit..nnkUInt64Lit:
          result = EnumField[NNode](
            kind: efvOrdinal,
            ordVal: val.parseRTimeOrdinal()
          )

        of nnkPar, nnkTupleConstr:
          val[1].expectKind nnkStrLit
          result = EnumField[NNode](
            kind: efvOrdString,
            ordStr: (
              ordVal: val[0].parseRTimeOrdinal(),
              strval: val[1].getStrVal()))

        of nnkStrLit:
          result = EnumField[NNode](kind: efvString, strval: val.strVal)

        of nnkIdent, nnkSym:
          result = EnumField[NNode](kind: efvIdent, ident: val)

        else:
          raiseArgumentError(
            &"Unexpected node kind for enum field: {val.kind}")

      result.name = fld[0].getStrVal

    of nnkSym:
      result = makeEnumField(name = fld.getStrVal, value = none(NNode))

    else:
      raiseImplementError(&"#[ IMPLEMENT {fld.kind} ]#")


  result.declNode = some(fld)



#============================  Constructors  =============================#
func parseRTimeOrdinal*[NNode](nnode: NNode): RTimeOrdinal =
  let kind = nnode.kind.toNNK()
  case kind:
    of nnkIntLit .. nnkUInt64Lit:
      RTimeOrdinal(kind: rtokInt, intval: nnode.intVal)

    of nnkCharLit:
      RTimeOrdinal(kind: rtokChar, charval: char(nnode.intVal))

    of nnkIdent:
      let val = case nnode.getStrVal():
        of "off", "false":
          false

        of "on", "true":
          true

        else:
          raiseArgumentError(
            "Unexpected identifier for parsing RTimeOrdinal " &
              nnode.getStrVal())


      RTimeOrdinal(kind: rtokBool, boolVal: val)

    else:
      raiseArgumentError(
        &"Unexpected node kind for parsing RTimeOrdinal: {kind}")


func makeRTOrdinal*(ival: int): RTimeOrdinal =
  RTimeOrdinal(kind: rtokInt, intval: BiggestInt(ival))

func makeRTOrdinal*(ival: BiggestInt): RTimeOrdinal =
  RTimeOrdinal(kind: rtokInt, intval: ival)

func makeRTOrdinal*(cval: char): RTimeOrdinal =
  RTimeOrdinal(kind: rtokChar, charVal: cval)

# func parseEnumField*[NNode](enval: NNode): EnumField[NNode] =
#   let kind = nnode.kind.toNNK()
#   case kind:
#     of nnkEmpty:

func toNNode*[NNode](ro: RTimeOrdinal): NNode =
  case ro.kind:
    of rtokInt:
      newNNLit[NNode](ro.intVal)

    of rtokChar:
      newNNLit[NNode](ro.charVal)

    of rtokBool:
      if ro.boolVal:
        newNident[NNode]("true")
      else:
        newNident[NNode]("false")


func toNNode*[NNode](fld: EnumField[NNode]): NNode =
  var fldVal: Option[NNode] = case fld.kind:
    of efvNone:
      none(NNode)

    of efvIdent:
      some fld.ident

    of efvString:
      some newNNLit[NNode](fld.strval)

    of efvOrdinal:
      some toNNode[NNode](fld.ordval)

    of efvOrdString:
      some newNTree[NNode](
        nnkPar,
        toNNode[NNode](fld.ordStr.ordVal),
        newNNLit[NNode](fld.ordStr.strVal)
      )

  if fldVal.isNone():
    fldVal = fld.value

  if fldVal.isSome():
    newNTree[NNode](
      nnkEnumFieldDef,
      newNIdent[NNode](fld.name),
      fldVal.get()).withIt do:
        when NNode is PNode:
          it.comment = fld.docComment

  else:
    when NNode is PNode:
      newPIdent(fld.name).withIt do:
        it.comment = fld.docComment

    else:
      # TODO generate documentation comments for NimNode
      ident(fld.name)


func toNNode*[NNode](en: EnumDecl[NNode], standalone: bool = false): NNode =
  ## Convert enum definition to `NNode`. If `standalone` is true wrap
  ## result in `nnkTypeSection`, otherwise generate `nnkTypeDef` only.
  let flds = collect(newSeq):
    for val in en.values:
      toNNode(val)

  var head =
    if en.exported:
      newNTree[NNode](nnkPostfix,
        newNIdent[NNode]("*"),
        newNIdent[NNode](en.name)
      )

    else:
      newNIdent[NNode](en.name)

  if en.pragma.len > 0:
    head = newNTree[NNode](
      nnkPragmaExpr,
      head,
      toNNode[NNode](en.pragma)
    )

  # echov en.pragma.len
  # echov toNNode[NNode](en.pragma)
  # echov head

  result = newNTree[NNode](
    nnkTypeDef,
    head,
    newEmptyNNode[NNode](),
    newNTree[NNode](nnkEnumTy, @[ newEmptyNNode[NNode]() ] & flds))

  when NNode is PNode:
    result.comment = en.docComment

  if standalone:
    result = newNTree[NNode](
      nnkTypeSection,
      result
    )


func parseEnumImpl*[NNode](en: NNode): EnumDecl[NNode] =
  case en.kind.toNNK():
    of nnkSym:
      when NNode is PNode:
        raiseImplementError(
          "Parsing of enum implementation from " &
          "Sym node is not yet support for PNode")

      else:
        let impl = en.getTypeImpl()
        # echov impl.kind
        case impl.kind:
          of nnkBracketExpr:
            # let impl = impl.getTypeInst()[1].getImpl()
            return parseEnumImpl(impl.getTypeInst()[1].getImpl())

          of nnkEnumTy:
            result = parseEnumImpl(impl)

          else:
            raiseImplementError(&"#[ IMPLEMENT {impl.kind} ]#")

    of nnkTypeDef:
      result = parseEnumImpl(en[2])
      result.declNode = some(en)
      case toNNK(en[0].kind):
        of nnkIdent, nnkSym:
          result.name = en[0].getStrVal

        of nnkPragmaExpr:
          result.name = en[0][0].getStrVal()
          result.pragma = parsePragma(en[0][1])

        else:
          raiseImplementError($en[0].kind & $treeRepr(en[0]))

    of nnkEnumTy:
      for fld in en[1..^1]:
        result.values.add parseEnumField(fld)

    of nnkTypeSection:
      result = parseEnumImpl(en[0])

    else:
      raiseImplementError(&"#[ IMPLEMENT {en.kind} ]#")

func parseEnum*[NNode](node: NNode): EnumDecl[NNode] =
  return parseEnumImpl(node)

#========================  Other implementation  =========================#
func getEnumPref*(en: NimNode): string =
  ## Get enum prefix. As per `Nep style guide<https://nim-lang.org/docs/nep1.html#introduction-naming-conventions>`_
  ## it is recommended for members of enums should have an identifying
  ## prefix, such as an abbreviation of the enum's name. This functions
  ## returns this prefix.
  let impl = en.parseEnumImpl()
  # echov impl
  let
    name = impl.values[0].name
    pref = name.parseUntil(result, {'A' .. 'Z', '0' .. '9'})

macro enumPref*(a: typed): string =
  ## Generate string literal with enum prefix
  newLit(getEnumPref(a))

func getEnumNames*(en: NimNode): seq[string] =
  ## Get list of enum identifier names
  en.parseEnumImpl().values.mapIt(it.name)

macro enumNames*(en: typed): seq[string] =
  ## Generate list of enum names
  newLit en.getEnumNames()
