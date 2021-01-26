import hast_common, proc_decl, idents_types, object_decl, enum_decl, pragmas
import std/[sequtils]
import hmisc/helpers

type
  NimDeclKind* = enum
    nekPasstroughCode
    nekProcDecl
    nekObjectDecl
    nekEnumDecl
    nekAliasDecl
    nekMultitype

  AliasDecl*[N] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    isDistinct*: bool
    isExported*: bool
    newType*: Ntype[N]
    oldType*: Ntype[N]

  NimTypeDeclKind = enum
    ntdkEnumDecl
    ntdkObjectDecl
    ntdkAliasDecl

  NimTypeDecl*[N] = object
    case kind*: NimTypeDeclKind:
      of ntdkEnumDecl:
        enumDecl*: EnumDecl[N]

      of ntdkObjectDecl:
        objectDecl*: ObjectDecl[N, Pragma[N]]

      of ntdkAliasDecl:
        aliasDecl*: AliasDecl[N]

  NimDecl*[N] = object
    case kind*: NimDeclKind
      of nekProcDecl:
        procdecl*: ProcDecl[N]

      of nekEnumDecl:
        enumdecl*: EnumDecl[N]

      of nekObjectDecl:
        objectdecl*: ObjectDecl[N, Pragma[N]]

      of nekAliasDecl:
        aliasDecl*: AliasDecl[N]

      of nekPasstroughCode:
        passthrough*: N

      of nekMultitype:
        typedecls*: seq[NimTypeDecl[N]]

  PNimTypeDecl* = NimTypeDecl[Pnode]

  PNimDecl* = NimDecl[Pnode]
  PAliasDecl* = NimDecl[PNode]
  NAliasDecl* = NimDecl[NimNode]

  AnyNimDecl[N] =
          ProcDecl[N] |
          AliasDecl[N] |
          ProcDecl[N] |
          ObjectDecl[N, Pragma[N]] |
          EnumDecl[N] |
          AliasDecl[N] |
          NimTypeDecl[N]

func `==`*[N, A](a, b: ObjectBranch[N, A]): bool =
  a.isElse == b.isElse and
  a.flds == b.flds and
  a.annotation == b.annotation and
  (
    case a.isElse:
      of true: a.notOfValue == b.notOfValue
      of false: a.ofValue == b.ofValue
  )

func `==`*[N](a, b: EnumField[N]): bool =
  a.kind        == b.kind        and
  a.docComment  == b.docComment  and
  a.codeComment == b.codeComment and
  a.name        == b.name        and
  a.value       == b.value       and
  (
    case a.kind:
      of efvNone: true
      of efvIdent: a.ident == b.ident
      of efvOrdinal: a.ordVal == b.ordVal
      of efvString: a.strval == b.strval
      of efvOrdString: a.ordStr == b.ordStr
  )

func `==`*(a, b: RTimeOrdinal): bool =
  a.kind == b.kind and
  (
    case a.kind:
      of rtokInt: a.intVal == b.intVal
      of rtokBool: a.boolVal == b.boolVal
      of rtokChar: a.charVal == b.charVal
  )


func `==`*[N](a, b: NimTypeDecl[N]): bool =
  a.kind == b.kind and (
    case a.kind:
      of ntdkEnumDecl: a.enumDecl == b.enumDecl
      of ntdkObjectDecl: a.objectDecl == b.objectDecl
      of ntdkAliasDecl: a.aliasDecl == b.aliasDecl
  )

func `==`*[N](a, b: NimDecl[N]): bool =
  a.kind == b.kind and (
    case a.kind:
      of nekProcDecl: a.procdecl == b.procdecl
      of nekEnumDecl: a.enumdecl == b.enumdecl
      of nekObjectDecl: a.objectdecl == b.objectdecl
      of nekAliasDecl: a.aliasdecl == b.aliasdecl
      of nekPasstroughCode: a.passthrough == b.passthrough
      of nekMultitype:
        a.typedecls.len == b.typedecls.len and
        zip(a.typedecls, b.typedecls).allOfIt(it[0] == it[1])
  )


func toNNode*[N](entry: NimDecl[N], standalone: bool = true): N =
  case entry.kind:
    of nekProcDecl:
      return toNNode[N](entry.procdecl)
    of nekEnumDecl:
      return toNNode[N](entry.enumdecl, standalone = standalone)
    of nekObjectDecl:
      return toNNode[N](entry.objectdecl, standalone = standalone)
    of nekAliasDecl:
      return toNNode[N](entry.aliasDecl)
    of nekPasstroughCode:
      return entry.passthrough
    of nekMultitype:
      result = newNTree[N](nnkTypeSection)
      for elem in entry.typedecls:
        case elem.kind:
          of ntdkEnumDecl:
            result.add toNNode[N](elem.enumDecl, standalone = false)
          of ntdkObjectDecl:
            result.add toNNode[N](elem.objectDecl, standalone = false)
          of ntdkAliasDecl:
            result.add toNNode[N](elem.aliasDecl, standalone = false)



func toNimTypeDecl*[N](odc: ObjectDecl[N, Pragma[N]]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkObjectDecl, objectdecl: odc)

func toNimTypeDecl*[N](adc: AliasDecl[N]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkAliasDecl, aliasDecl: adc)

func toNimTypeDecl*[N](edc: EnumDecl[N]): NimTypeDecl[N] =
  NimTypeDecl[N](kind: ntdkEnumDecl, enumdecl: edc)

func toNimTypeDecl*[N](entry: NimDecl[N]): NimTypeDecl[N] =
  case entry.kind:
    of nekEnumDecl:
      return toNimTypeDecl[N](entry.enumdecl)
    of nekObjectDecl:
      return toNimTypeDecl[N](entry.objectdecl)
    of nekAliasDecl:
      return toNimTypeDecl[N](entry.aliasDecl)
    else:
     raiseAssert(&"Cannot convert to NimTypeDecl for kind {entry.kind}")

func toNimDecl*[N](prd: ProcDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekProcDecl, procdecl: prd)

func toNimDecl*[N](odc: ObjectDecl[N, Pragma[N]]): NimDecl[N] =
  NimDecl[N](kind: nekObjectDecl, objectdecl: odc)

func toNimDecl*[N](adc: AliasDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekAliasDecl, aliasDecl: adc)

func toNimDecl*[N](edc: EnumDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekEnumDecl, enumdecl: edc)

func toNimDecl*[N](decl: N): NimDecl[N] =
  NimDecl[N](kind: nekPasstroughCode, passthrough: decl)

func toNimDecl*[N](decl: seq[NimTypeDecl[N]]): NimDecl[N] =
  NimDecl[N](kind: nekMultitype, typedecls: decl)

func add*[N](declSeq: var seq[NimDecl[N]], decl: AnyNimDecl[N]) =
  declSeq.add toNimDecl(decl)

# func add*[N](declSeq: var seq[NimDecl[N]], decl: N) =
#   declSeq.add NimDecl(kind: nekPasstroughCode, passthrough: decl)

func newAliasDecl*[N](
    t1, t2: NType[N],
    isDistinct: bool = true,
    isExported: bool = true,
    iinfo:     LineInfo                          = defaultIInfo,
    docComment: string = "",
    codeComment: string = "",
  ): AliasDecl[N] =

  AliasDecl[N](
    oldType: t2,
    newType: t1,
    isExported: isExported,
    isDistinct: isDistinct,
    iinfo: iinfo,
    docComment: docComment,
    codeComment: codeComment
  )


func `$`*[N](nd: NimDecl[N]): string =
  {.cast(noSideEffect).}:
    when N is NimNode:
      $toNNode(nd)
    else:
      hnimast.`$`(toNNode(nd))

func toNNode*[N](alias: AliasDecl[N], standalone: bool = true): N =
  let pr = (alias.isDistinct, alias.isExported)
  let
    aType = toNNode[N](alias.newType)
    bType = toNNode[N](alias.oldType)

  if pr == (false, false):
    result = newNTree[N](nnkTypeDef, aType, newEmptyNNode[N](), bType)
  elif pr == (true, false):
    result = newNTree[N](
      nnkTypeDef,
      aType,
      newEmptyNNode[N](),
      newNTree[N](nnkDistinctTy, bType)
    )
  elif pr == (false, true):
    result = newNTree[N](
      nnkTypeDef,
      newNTree[N](nnkPostfix, newNIdent[N]("*"), aType),
      newEmptyNNode[N](),
      bType
    )
  elif pr == (true, true):
    result = newNTree[N](
      nnkTypeDef,
      newNTree[N](nnkPostfix, newNIdent[N]("*"), aType),
      newEmptyNNode[N](),
      newNTree[N](nnkDistinctTy, bType)
    )

  if standalone:
    result = newNTree[N](nnkTypeSection, result)


func `$`*[N](nd: seq[NimDecl[N]]): string =
  mapIt(nd, $it).join("\n")

proc `iinfo=`*[N](nd: var NimDecl[N], iinfo: LineInfo) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.iinfo = iinfo
    of nekEnumDecl:       nd.enumdecl.iinfo = iinfo
    of nekObjectDecl:     nd.objectdecl.iinfo = iinfo
    of nekAliasDecl:      nd.aliasdecl.iinfo = iinfo
    of nekMultitype:      discard
    of nekPasstroughCode: discard


proc addCodeComment*[N](nd: var AnyNimDecl[N], comm: string) =
  nd.codeComment &= comm

proc addCodeComment*[N](nd: var NimDecl[N], comm: string) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.codeComment &= comm
    of nekEnumDecl:       nd.enumdecl.codeComment &= comm
    of nekObjectDecl:     nd.objectdecl.codeComment &= comm
    of nekAliasDecl:      nd.aliasdecl.codeComment &= comm
    of nekMultitype:      discard
    of nekPasstroughCode: discard
