import
  ./hast_common, ./idents_types, ./pragmas

import
  hmisc/core/all

import
  std/[sequtils, strutils, macros, options, strformat, tables]

import
  compiler/[ast, lineinfos]

when defined(nimdoc):
  static: quit 0

type
  # TODO different keyword types: `method`, `iterator`, `proc`,
  # `func`, `template` etc.
  ProcKind* = enum
    ## Procedure kind
    pkRegular ## Regular proc: `hello()`
    pkOperator ## Operator: `*`
    pkHook ## Destructor/sink (etc.) hook: `=destroy`
    pkAssgn ## Assignment proc `field=`
    pkLambda ## Anonymous procedure

  ProcDeclType* = enum
    ptkProc
    ptkFunc
    ptkIterator
    ptkConverter
    ptkMethod
    ptkTemplate
    ptkMacro

  ProcDecl*[NNode] = object
    iinfo*: LineInfo
    docComment*: string
    codeComment*: string

    declType*: ProcDeclType
    exported*: bool
    name*: string
    kind*: ProcKind
    signature*: NType[NNode] ## Signature of the proc as `ntProc` NType
    genParams*: seq[NType[NNode]] ## Generic parameters for proc
    impl*: NNode ## Implementation body
    declNode*: Option[NNode]

  PProcDecl* = ProcDecl[PNode]
  NProcDecl* = ProcDecl[NimNode]



func `==`*[NNode](lhs, rhs: ProcDecl[NNode]): bool =
  lhs.name == rhs.name and
  lhs.exported == rhs.exported and
  lhs.signature == rhs.signature

proc getName*[N](decl: ProcDecl[N]): string = decl.name

proc `arguments=`*(
  procDecl: var PProcDecl, arguments: seq[NIdentDefs[PNode]]) =
  procDecl.signature.arguments = arguments

proc arguments*(procDecl: var PProcDecl): var seq[NIdentDefs[PNode]] =
  procDecl.signature.arguments

proc arguments*[N](procDecl: ProcDecl[N]): seq[NIdentDefs[N]] =
  procDecl.signature.arguments

proc genTable*[N](procDecl: ProcDecl[N]): Table[string, int] =
  for idx, param in procDecl.genParams:
    result[param.head] = idx

proc addArgument*[N](decl: var ProcDecl[N], arg: NidentDefs[N]) =
  decl.signature.arguments.add arg

proc addArgument*[N](
    procDecl: var ProcDecl[N],
    argName: string, argType: NType[N], kind: NVarDeclKind = nvdLet,
    value: Option[N] = none(N)
  ) =

  procDecl.signature.arguments.add newNIdentDefs(
    argName, argType, kind, value)

proc addArgument*[N](
  procDecl: var ProcDecl[N], args: openarray[(string, NType[N])]) =

  for (argName, argType) in args:
    procDecl.addArgument(argName, argType)

proc addPragma*[N](
    decl: var ProcDecl[N], key, value: N) =
  decl.signature.pragma.add newNTree[N](nnkExprColonExpr, key, value)

proc addPragma*[N](f: var ProcDecl[N], values: seq[N]) =
  for v in values:
    f.signature.pragma.add v

proc addPragma*[N](decl: var ProcDecl[N], name: string) =
  decl.signature.pragma.add newNIdent[N](name)

proc addPragma*[N](
    decl: var ProcDecl[N], key: string, value: N) =
  decl.signature.pragma.add newNTree[N](
    nnkExprColonExpr, newNIdent[N](key), value)

# proc addArgument*[N](
#   procDecl: var ProcDecl,
#   args: openarray[(string, NType[N], NVarDeclKind)]) =

#   for (argName, argType, argKind) in args:

iterator argumentIdents*[N](procDecl: ProcDecl[N]): N =
  for argument in procDecl.signature.arguments:
    for ident in argument.idents:
      yield ident


func argumentNames*[N](procDecl: ProcDecl[N]): seq[string] =
  for argument in procDecl.signature.arguments:
    for ident in argument.idents:
      result.add ident.getStrVal()

func argumentTypes*[N](procDecl: ProcDecl[N]): seq[NType[N]] =
  for argument in procDecl.signature.arguments:
    for ident in argument.idents:
      result.add argument.vtype

proc returnType*[N](procDecl: ProcDecl[N]): Option[NType[N]] =
  procDecl.signature.returnType()


proc argumentType*[N](procDecl: ProcDecl[N], idx: int): NType[N] =
  procDecl.signature.argumentType(idx)

proc `returnType=`*[N](procDecl: var ProcDecl[N], retType: NType[N]) =
  procDecl.signature.returnType = retType

proc `pragma=`*[N](procDecl: var ProcDecl[N], pragma: Pragma[N]) =
  procDecl.signature.pragma = pragma

func toNNode*[NNode](
  pr: ProcDecl[NNode], standalone: bool = true): NNode =
  if pr.signature.kind != ntkProc:
    raise newArgumentError(
      "Invalid proc declaration - signature type has kind of",
      &"{pr.signature.kind}. Proc declaration location: {pr.iinfo}")


  let headSym = case pr.kind:
    of pkRegular:
      newNIdent[NNode](pr.name)

    of pkHook: newNTree[NNode](
      nnkAccQuoted,
      newNIdent[NNode]("="),
      newNIdent[NNode](pr.name))

    of pkAssgn: newNTree[NNode](
      nnkAccQuoted,
      newNIdent[NNode](pr.name),
      newNIdent[NNode]("="))

    of pkOperator: newNTree[NNode](
      nnkAccQuoted, newNIdent[NNode](pr.name))

    of pkLambda:
      newEmptyNNode[NNode]()

  let head =
    if pr.exported and pr.kind != pkLambda:
      newNTree[NNode](
        nnkPostfix, newNIdent[NNode]("*"), headSym)

    else:
      headSym

  let genParams =
    if pr.genParams.len == 0:
      newEmptyNNode[NNode]()
    else:
      newNTree[NNode](nnkGenericParams, pr.genParams.mapIt(toNNode[NNode](it)))


  let rettype =
    if pr.signature.rType.isSome():
      toNNode[NNode](pr.signature.rtype.get().getIt())
    else:
      newEmptyNNode[NNode]()

  let impl =
    if pr.impl == nil:
      newEmptyNNode[NNode]()
    else:
      pr.impl

  # if

  let prdecl =
    case pr.declType:
      of ptkProc: nnkProcDef
      of ptkFunc: nnkFuncDef
      of ptkIterator: nnkIteratorDef
      of ptkConverter: nnkConverterDef
      of ptkMethod: nnkMethodDef
      of ptkTemplate: nnkTemplateDef
      of ptkMacro: nnkMacroDef

  result = newNTree[NNode](
    prdecl,
    head,
    newEmptyNNode[NNode](),
    genParams,
    newNTree[NNode](
      nnkFormalParams,
      @[ rettype ] & pr.signature.arguments.mapIt(it.toNFormalParam())
    ),
    toNNode[NNode](pr.signature.pragma),
    newEmptyNNode[NNode](),
    impl
  )

  when NNode is PNode:
    result.comment = pr.docComment
    # debugecho result.comment

func newProcDecl*[N](name: string): ProcDecl[N] =
  result.name = name
  result.signature = NType[N](kind: ntkProc)

func copyForward*[N](decl: ProcDecl[N]): ProcDecl[N] =
  result = decl
  result.impl = newEmptyNNode[N]()

func newPProcDecl*(
    name:        string,
    args:        openarray[(string, NType[PNode])] = @[],
    returnTYpe:  Option[NType[PNode]]              = none(NType[PNode]),
    impl:        PNode                             = nil,
    exported:    bool                              = true,
    pragma:      Pragma[PNode]                     = Pragma[PNode](),
    genParams:   seq[NType[PNode]]                 = @[],
    iinfo:       LineInfo                          = defaultIInfo,
    declType:    ProcDeclType                      = ptkProc,
    docComment:  string                            = "",
    codeComment: string                            = "",
    kind: ProcKind                                 = pkRegular,
  ): ProcDecl[PNode] =

  result.name = name
  result.exported = exported
  result.signature = NType[PNode](
    kind: ntkProc,
    arguments: toNIdentDefs(args))

  result.declType         = declType
  result.signature.pragma = pragma
  result.genParams        = genParams
  result.docComment       = docComment
  result.codeComment      = codeComment
  result.iinfo            = iinfo
  result.kind             = kind

  if returnType.isSome():
    result.signature.setRtype returnType.get()

  result.impl = impl

func newNProcDecl*(
    name:        string,
    args:        openarray[(string, NType[NimNode])] = @[],
    returnType:  Option[NType[NimNode]]              = none(NType[NimNode]),
    impl:        NimNode                             = nil,
    exported:    bool                                = true,
    pragma:      Pragma[NimNode]                     = Pragma[NimNode](),
    iinfo:       LineInfo                            = defaultIInfo,
    declType:    ProcDeclType                        = ptkProc,
    docComment:  string                              = "",
    codeComment: string                              = "",
  ): ProcDecl[NimNode] =

  result.declType    = declType
  result.name        = name
  result.exported    = exported
  result.docComment  = docComment
  result.codeComment = codeComment
  result.iinfo       = iinfo


  result.signature = NType[NimNode](
    kind: ntkProc,
    arguments: toNIdentDefs(args)
  )

  result.signature.pragma = pragma
  if returnType.isSome():
    result.signature.setRtype returnType.get()

  result.impl = impl


# func newProcDeclNNode*[NNode](
#   procHead: NNode,
#   rtype: Option[NType[NNode]],
#   args: seq[NIdentDefs[NNode]],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   ## Generate procedure declaration
#   ##
#   ## ## Parameters
#   ##
#   ## :procHead: head of the procedure
#   ## :rtype: Optional return type
#   ## :args: Proc arguments
#   ## :impl: Proc implementation body
#   ## :pragma: Pragma annotation for proc
#   ## :exported: Whether or not procedure is exported

#   let procHead =
#     if exported:
#       newNTree[NNode](nnkPostfix, newNIdent[NNode]("*"), procHead)
#     else:
#       procHead

#   let impl =
#     if comment.len > 0:
#       newNTree[NNode](
#         nnkStmtList,
#         newCommentStmtNNode[NNode](comment),
#         impl
#       )
#     else:
#       impl



#   result = newNTree[NNode](
#     nnkProcDef,
#     procHead,
#     newEmptyNNode[NNode](),
#     newEmptyNNode[NNode](),  # XXXX generic type parameters,
#     newNTree[NNode]( # arguments
#       nnkFormalParams,
#       @[
#         rtype.isSome().tern(
#           toNNode[NNode](rtype.get()),
#           newEmptyNNode[NNode]()
#         )
#       ] &
#       args.mapIt(toNFormalParam[NNode](it))
#     ),
#     toNNode[NNode](pragma),
#     newEmptyNNode[NNode](), # XXXX reserved slot,
#   )

#   # if impl.kind.toNNK() != nnkEmpty:
#   result.add impl



# func newProcDeclNode*(
#   head: NimNode, rtype: Option[NType[NimNode]], args: seq[NIdentDefs[NimNode]],
#   impl: NimNode, pragma: NPragma = NPragma(), exported: bool = true,
#   comment: string = ""): NimNode {.deprecated.} =

#   newProcDeclNNode[NimNode](
#     head, rtype, args, impl, pragma, exported, comment)


# func newProcDeclNode*(
#   head: PNode, rtype: Option[NType[PNode]], args: seq[PIdentDefs],
#   impl: PNode, pragma: Pragma[PNode] = Pragma[PNode](),
#   exported: bool = true, comment: string = ""): PNode {.deprecated.} =

#   newProcDeclNNode[PNode](
#     head, rtype, args, impl, pragma, exported, comment)

# func newProcDeclNode*[NNode](
#   head: NNode,
#   args: openarray[tuple[name: string, atype: NType[NNode]]],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   newProcDeclNNode(
#     head,
#     none(NType[NNode]),
#     toNIdentDefs[NNode](args),
#     impl,
#     pragma,
#     exported,
#     comment
#   )


# func newProcDeclNode*[NNode](
#   accq: openarray[NNode],
#   rtype: NType,
#   args: openarray[tuple[name: string, atype: NType[NNode]]],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   newProcDeclNNode(
#     newNTree[NNode](nnkAccQuoted, accq),
#     some(rtype),
#     toNIdentDefs[NNode](args),
#     impl,
#     pragma,
#     exported,
#     comment
#   )


# func newProcDeclNode*[NNode](
#   accq: openarray[NNode],
#   args: openarray[tuple[name: string, atype: NType[NNode]]],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   newProcDeclNNode(
#     newNTree[NNode](nnkAccQuoted, accq),
#     none(NType[NNode]),
#     toNIdentDefs[NNode](args),
#     impl,
#     pragma,
#     exported,
#     comment
#   )


# func newProcDeclNode*[NNode](
#   head: NNode,
#   rtype: NType[NNode],
#   args: openarray[tuple[name: string, atype: NType[NNode]]],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   newProcDeclNNode(
#     head,
#     some(rtype),
#     toNIdentDefs[NNode](args),
#     impl,
#     pragma,
#     exported,
#     comment
#   )

# func newProcDeclNode*[NNode](
#   head: NNode,
#   args: openarray[tuple[
#     name: string,
#     atype: NType[NNode],
#     nvd: NVarDeclKind]
#   ],
#   impl: NNode,
#   pragma: Pragma[NNode] = Pragma[NNode](),
#   exported: bool = true,
#   comment: string = ""): NNode {.deprecated.} =
#   newProcDeclNNode(
#     head,
#     none(NType[NNode]),
#     toNIdentDefs[NNode](args),
#     impl,
#     pragma,
#     exported,
#     comment
#   )


proc parseProc*[N](node: N): ProcDecl[N] =
  result = newProcDecl[N](":tmp")
  result.declNode = some(node)

  case toNNK(node.kind):
    of nnkProcDeclKinds:
      case toNNK(node[0].kind):
        of nnkSym, nnkIdent, nnkAccQuoted:
          result.name = node[0].getStrVal()

        of nnkPostfix:
          result.name = node[0][1].getStrVal()
          result.exported = true

        else:
          raise newImplementKindError(node[0])


      case toNNK(node[1].kind):
        of nnkEmpty:
          discard

        else:
          # IMPLEMENT term rewriting arguments
          discard

      case toNNK(node[2].kind):
        of nnkEmpty:
          discard

        else:
          discard

      for arg in node[3][1..^1]:
        result.arguments.add parseNidentDefs(arg)

      result.impl = node[6]
      result.docComment = node.getDocComment()

    else:
      raise newImplementKindError(node, $node.getInfo())
