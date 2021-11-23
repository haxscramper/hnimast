import
  ./hast_common,
  ./proc_decl,
  ./idents_types,
  ./object_decl,
  ./enum_decl,
  ./pragmas

import
  std/[sequtils, strutils],
  hmisc/core/all,
  compiler/[ast]

type
  NimDeclKind* = enum
    nekPassthroughCode
    nekProcDecl
    nekObjectDecl
    nekFieldDecl
    nekEnumDecl
    nekAliasDecl
    nekMultitype

const nekTypeKinds* = {nekObjectdecl, nekAliasDecl, nekEnumDecl}

type
  AliasDecl*[N] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    isDistinct*: bool
    isExported*: bool
    newType*: Ntype[N]
    oldType*: Ntype[N]

  NimTypeDeclKind* = enum
    ntdkEnumDecl
    ntdkObjectDecl
    ntdkAliasDecl

  NimTypeDecl*[N] = object
    case kind*: NimTypeDeclKind:
      of ntdkEnumDecl:
        enumDecl*: EnumDecl[N]

      of ntdkObjectDecl:
        objectDecl*: ObjectDecl[N]

      of ntdkAliasDecl:
        aliasDecl*: AliasDecl[N]

  NimDecl*[N] = object
    case kind*: NimDeclKind
      of nekProcDecl:
        procdecl*: ProcDecl[N]

      of nekEnumDecl:
        enumdecl*: EnumDecl[N]

      of nekObjectDecl:
        objectdecl*: ObjectDecl[N]

      of nekAliasDecl:
        aliasDecl*: AliasDecl[N]

      of nekPassthroughCode:
        passIInfo*: LineInfo
        passthrough*: N

      of nekMultitype:
        typedecls*: seq[NimTypeDecl[N]]

      of nekFieldDecl:
        fieldDecl*: ObjectField[N]

  PNimTypeDecl* = NimTypeDecl[Pnode]

  PNimDecl* = NimDecl[Pnode]
  PAliasDecl* = AliasDecl[PNode]
  NAliasDecl* = AliasDecl[NimNode]

  AnyNimDecl*[N] =
    ProcDecl[N]    |
    AliasDecl[N]   |
    ProcDecl[N]    |
    ObjectDecl[N]  |
    ObjectField[N] |
    EnumDecl[N]    |
    AliasDecl[N]   |
    NimTypeDecl[N] |
    NimDecl[N]

func `==`*[N](a, b: ObjectBranch[N]): bool =
  a.isElse == b.isElse and
  a.flds == b.flds and
  a.pragma == b.pragma and
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
      of nekPassthroughCode: a.passthrough == b.passthrough
      of nekMultitype:
        a.typedecls.len == b.typedecls.len and
        zip(a.typedecls, b.typedecls).allIt(it[0] == it[1])
  )


proc toNNode*[N](entry: NimDecl[N], standalone: bool = true): N =
  case entry.kind:
    of nekProcDecl:
      return toNNode[N](entry.procdecl)

    of nekEnumDecl:
      return toNNode[N](entry.enumdecl, standalone = standalone)

    of nekObjectDecl:
      return toNNode[N](entry.objectdecl, standalone = standalone)

    of nekAliasDecl:
      return toNNode[N](entry.aliasDecl)

    of nekPassthroughCode:
      return entry.passthrough

    of nekFieldDecl:
      return toNNode[N](entry.fieldDecl)

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

proc toNNode*[N](entries: seq[NimDecl[N]]): N =
  result = newNTree[N](nnkStmtList)
  for entry in items(entries):
    result.add toNNode[N](entry)


proc toNimTypeDecl*[N](odc: ObjectDecl[N]): NimTypeDecl[N] =
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
      raise newUnexpectedKindError(
        entry, "Cannot convert to NimTypeDecl for kind")


func toNimDecl*[N](edc: ObjectField[N]): NimDecl[N] =
  NimDecl[N](kind: nekFieldDecl, fieldDecl: edc)

func toNimDecl*[N](prd: ProcDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekProcDecl, procdecl: prd)

func toNimDecl*[N](odc: ObjectDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekObjectDecl, objectdecl: odc)

func toNimDecl*[N](adc: AliasDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekAliasDecl, aliasDecl: adc)

func toNimDecl*[N](edc: EnumDecl[N]): NimDecl[N] =
  NimDecl[N](kind: nekEnumDecl, enumdecl: edc)

func toNimDecl*[N: NimNode | PNode](decl: N): NimDecl[N] =
  NimDecl[N](kind: nekPassthroughCode, passthrough: decl)

func toNimDecl*[N](decl: seq[NimTypeDecl[N]]): NimDecl[N] =
  NimDecl[N](kind: nekMultitype, typedecls: decl)

func getProc*[N](decl: NimDecl[N]): ProcDecl[N] =
  assertKind(decl, {nekProcDecl})
  decl.procDecl

func getEnum*[N](decl: NimTypeDecl[N]): EnumDecl[N] =
  assertKind(decl, {ntdkEnumDecl})
  decl.enumDecl

func getEnum*[N](decl: NimDecl[N]): EnumDecl[N] =
  assertKind(decl, {nekEnumDecl, nekMultitype})
  if decl of nekEnumDecl:
    decl.aliasDecl

  else:
    assert decl.typedecls.len == 1
    decl.typedecls[0].getEnum()


func getObject*[N](decl: NimTypeDecl[N]): ObjectDecl[N] =
  assertKind(decl, {ntdkObjectDecl})
  decl.objectDecl

func getObject*[N](decl: NimDecl[N]): ObjectDecl[N] =
  assertKind(decl, {nekObjectDecl, nekMultitype})
  if decl of nekObjectDecl:
    decl.objectDecl

  else:
    assert decl.typedecls.len == 1
    decl.typedecls[0].getObject()

func getAlias*[N](decl: NimTypeDecl[N]): AliasDecl[N] =
  assertKind(decl, {ntdkAliasDecl})
  decl.aliasDecl

func getAlias*[N](decl: NimDecl[N]): AliasDecl[N] =
  assertKind(decl, {nekAliasDecl, nekMultitype})
  if decl of nekAliasDecl:
    decl.aliasDecl

  else:
    assert decl.typedecls.len == 1
    decl.typedecls[0].getAlias()

func getTypes*[N](decl: NimDecl[N]): seq[NimTypeDecl[N]] =
  assertKind(decl, {nekMultitype})
  decl.typeDecls

func getName*[N](decl: NimTypeDecl[N]): string =
  case decl.kind:
    of ntdkEnumDecl: decl.enumDecl.name
    of ntdkObjectDecl: decl.objectDecl.name.head
    of ntdkAliasDecl: decl.aliasDecl.newType.head

func getFirst*[N](
    decls: seq[NimTypeDecl[N]], name: string): NimTypeDecl[N] =

  for decl in decls:
    if decl.getName() == name:
      return decl

  raise newGetterError(
    "Could not find type named '" & name & "'")

func getFirst*[N](decls: seq[NimDecl[N]], kind: NimDeclKind): NimDecl[N] =
  for d in decls:
    if d of kind:
      return d

func add*[N](declSeq: var seq[NimDecl[N]], decl: AnyNimDecl[N]) =
  when decl is NimDecl:
    system.add(declSeq, decl)

  else:
    declSeq.add toNimDecl(decl)

# func add*[N](declSeq: var seq[NimDecl[N]], decl: N) =
#   declSeq.add NimDecl(kind: nekPassthroughCode, passthrough: decl)

func newPassCode*[N](code: N): NimDecl[N] =
  NimDecl[N](kind: nekPassthroughCode, passthrough: code)

func add*[N](decls: var seq[NimDecl[N]], code: N) =
  decls.add newPassCode[N](code)

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
      `$`(toNNode(nd))

func toNNode*[N](alias: AliasDecl[N], standalone: bool = true): N =
  let pr = (alias.isDistinct, alias.isExported)
  var
    newType = toNNode[N](alias.newType, alias.isExported)
    oldType = toNNode[N](alias.oldType)

  if alias.isDistinct:
    result = newNTree[N](
      nnkTypeDef,
      newType,
      newEmptyNNode[N](),
      newNTree[N](nnkDistinctTy, oldType)
    )

  else:
    result = newNTree[N](nnkTypeDef, newType, newEmptyNNode[N](), oldType)

  if standalone:
    result = newNTree[N](nnkTypeSection, result)


func `$`*[N](nd: seq[NimDecl[N]]): string =
  mapIt(nd, $it).join("\n\n")

proc `iinfo=`*[N](nd: var NimDecl[N], iinfo: LineInfo) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.iinfo = iinfo
    of nekEnumDecl:       nd.enumdecl.iinfo = iinfo
    of nekObjectDecl:     nd.objectdecl.iinfo = iinfo
    of nekAliasDecl:      nd.aliasdecl.iinfo = iinfo
    of nekFieldDecl:      nd.fieldDecl.iinfo = iinfo
    of nekMultitype:      discard
    of nekPassthroughCode: nd.passIInfo = iinfo


proc addCodeCommentImpl[N](nd: var NimDecl[N], comm: string) =
 case nd.kind:
    of nekProcDecl:       nd.procdecl.codeComment &= comm
    of nekEnumDecl:       nd.enumdecl.codeComment &= comm
    of nekObjectDecl:     nd.objectdecl.codeComment &= comm
    of nekAliasDecl:      nd.aliasdecl.codeComment &= comm
    of nekFieldDecl:      nd.fieldDecl.codeComment &= comm
    of nekMultitype:      raise newArgumentError(
      "Cannot add code comments to multitype nim declaration.",
      "Check for declaration `kind == nekMultitype` and",
      "place code annotation in",
      "one of the nested `.typedecls` elements"
    )

    of nekPassthroughCode: discard


proc addCodeComment*[N](nd: var AnyNimDecl[N], comm: string) =
  when nd is NimDecl:
    addCodeCommentImpl(nd, comm)

  else:
    nd.codeComment &= comm

proc addCodeComment*[N](nd: var NimDecl[N], comm: string) =
  addCodeCommentImpl(nd, comm)


proc addDocCommentImpl[N](nd: var NimDecl[N], comm: string) =
  case nd.kind:
    of nekProcDecl:       nd.procdecl.docComment &= comm
    of nekEnumDecl:       nd.enumdecl.docComment &= comm
    of nekObjectDecl:     nd.objectdecl.docComment &= comm
    of nekAliasDecl:      nd.aliasdecl.docComment &= comm
    of nekFieldDecl:      nd.fieldDecl.docComment &= comm
    of nekMultitype:      discard
    of nekPassthroughCode: discard


proc addDocComment*[N](nd: var AnyNimDecl[N], comm: string) =
  when nd is NimDecl:
    addDocCommentImpl(nd, comm)

  else:
    nd.docComment &= comm

proc addDocComment*[N](nd: var NimDecl[N], comm: string) =
  addDocCommentImpl(nd, comm)
