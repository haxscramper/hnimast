import hast_common, idents_types, pragmas
import hmisc/helpers
import std/[sequtils, strutils, macros, options]
import compiler/[ast, lineinfos]

type
  # TODO different keyword types: `method`, `iterator`, `proc`,
  # `func`, `template` etc.
  ProcKind* = enum
    ## Procedure kind
    pkRegular ## Regular proc: `hello()`
    pkOperator ## Operator: `*`
    pkHook ## Destructor/sink (etc.) hook: `=destroy`
    pkAssgn ## Assignment proc `field=`

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

  PProcDecl* = ProcDecl[PNode]
  NProcDecl* = ProcDecl[NimNode]



func `==`*[NNode](lhs, rhs: ProcDecl[NNode]): bool =
  lhs.name == rhs.name and
  lhs.exported == rhs.exported and
  lhs.signature == rhs.signature

proc `arguments=`*(
  procDecl: var PProcDecl, arguments: seq[NIdentDefs[PNode]]) =
  procDecl.signature.arguments = arguments

proc arguments*(procDecl: var PProcDecl): var seq[NIdentDefs[PNode]] =
  procDecl.signature.arguments

proc arguments*[N](procDecl: ProcDecl[N]): seq[NIdentDefs[N]] =
  procDecl.signature.arguments


iterator argumentIdents*[N](procDecl: ProcDecl[N]): N =
  for argument in procDecl.signature.arguments:
    for ident in argument.idents:
      yield ident

iterator argumentTypes*[N](procDecl: ProcDecl[N]): NType[N] =
  for argument in procDecl.signature.arguments:
    yield argument.vtype

proc returnType*[N](procDecl: ProcDecl[N]): Option[NType[N]] =
  procDecl.signature.returnType()

func toNNode*[NNode](
  pr: ProcDecl[NNode], standalone: bool = true): NNode =
  if pr.signature.kind != ntkProc:
    argumentError:
      "Invalid proc declaration - signature type has kind of"
      "{pr.signature.kind}. Proc declaration location: {pr.iinfo}"


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

  let head =
    if pr.exported: newNTree[NNode](
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

func newPProcDecl*(
    name:        string,
    args:        openarray[(string, NType[PNode])] = @[],
    rtyp:        Option[NType[PNode]]              = none(NType[PNode]),
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
    arguments: toNIdentDefs(args)
  )

  result.declType         = declType
  result.signature.pragma = pragma
  result.genParams        = genParams
  result.docComment       = docComment
  result.codeComment      = codeComment
  result.iinfo            = iinfo
  result.kind             = kind

  if rtyp.isSome():
    result.signature.setRtype rtyp.get()

  result.impl = impl

func newNProcDecl*(
    name:     string,
    args:        openarray[(string, NType[NimNode])] = @[],
    rtyp:        Option[NType[NimNode]]              = none(NType[NimNode]),
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
  if rtyp.isSome():
    result.signature.setRtype rtyp.get()

  result.impl = impl


func newProcDeclNNode*[NNode](
  procHead: NNode,
  rtype: Option[NType[NNode]],
  args: seq[NIdentDefs[NNode]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  ## Generate procedure declaration
  ##
  ## ## Parameters
  ##
  ## :procHead: head of the procedure
  ## :rtype: Optional return type
  ## :args: Proc arguments
  ## :impl: Proc implementation body
  ## :pragma: Pragma annotation for proc
  ## :exported: Whether or not procedure is exported

  let procHead =
    if exported:
      newNTree[NNode](nnkPostfix, newNIdent[NNode]("*"), procHead)
    else:
      procHead

  let impl =
    if comment.len > 0:
      newNTree[NNode](
        nnkStmtList,
        newCommentStmtNNode[NNode](comment),
        impl
      )
    else:
      impl



  result = newNTree[NNode](
    nnkProcDef,
    procHead,
    newEmptyNNode[NNode](),
    newEmptyNNode[NNode](),  # XXXX generic type parameters,
    newNTree[NNode]( # arguments
      nnkFormalParams,
      @[
        rtype.isSome().tern(
          toNNode[NNode](rtype.get()),
          newEmptyNNode[NNode]()
        )
      ] &
      args.mapIt(toNFormalParam[NNode](it))
    ),
    toNNode[NNode](pragma),
    newEmptyNNode[NNode](), # XXXX reserved slot,
  )

  # if impl.kind.toNNK() != nnkEmpty:
  result.add impl



func newProcDeclNode*(
  head: NimNode, rtype: Option[NType[NimNode]], args: seq[NIdentDefs[NimNode]],
  impl: NimNode, pragma: NPragma = NPragma(), exported: bool = true,
  comment: string = ""): NimNode {.deprecated.} =

  newProcDeclNNode[NimNode](
    head, rtype, args, impl, pragma, exported, comment)


func newProcDeclNode*(
  head: PNode, rtype: Option[NType[PNode]], args: seq[PIdentDefs],
  impl: PNode, pragma: Pragma[PNode] = Pragma[PNode](),
  exported: bool = true, comment: string = ""): PNode {.deprecated.} =

  newProcDeclNNode[PNode](
    head, rtype, args, impl, pragma, exported, comment)

func newProcDeclNode*[NNode](
  head: NNode,
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  newProcDeclNNode(
    head,
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  accq: openarray[NNode],
  rtype: NType,
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  newProcDeclNNode(
    newNTree[NNode](nnkAccQuoted, accq),
    some(rtype),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  accq: openarray[NNode],
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  newProcDeclNNode(
    newNTree[NNode](nnkAccQuoted, accq),
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )


func newProcDeclNode*[NNode](
  head: NNode,
  rtype: NType[NNode],
  args: openarray[tuple[name: string, atype: NType[NNode]]],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  newProcDeclNNode(
    head,
    some(rtype),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )

func newProcDeclNode*[NNode](
  head: NNode,
  args: openarray[tuple[
    name: string,
    atype: NType[NNode],
    nvd: NVarDeclKind]
  ],
  impl: NNode,
  pragma: Pragma[NNode] = Pragma[NNode](),
  exported: bool = true,
  comment: string = ""): NNode {.deprecated.} =
  newProcDeclNNode(
    head,
    none(NType[NNode]),
    toNIdentDefs[NNode](args),
    impl,
    pragma,
    exported,
    comment
  )

proc parseProc*[N](node: N): ProcDecl[N] =
  result = newProcDecl[N](":tmp")

  case toNNK(node.kind):
    of nnkProcDeclKinds:
      case toNNK(node[0].kind):
        of nnkSym, nnkIdent:
          result.name = node[0].getStrVal()

        else:
          raiseImplementError("")


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

      if node[6].kind in {nnkStmtList} and
         node[6].len > 0 and
         node[6][0].kind == nkCommentStmt
        :
        result.docComment = node[6][0].comment

    else:
      echo node.treeRepr()
      raiseImplementError($node.kind & " " & $node.getInfo())
