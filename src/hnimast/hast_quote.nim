import hast_common
import std/[strutils]
import compiler/[lineinfos]

func quoteAux(body: NimNode, resCall: string): NimNode =
  if body.kind == nnkPrefix and
     body[0].eqIdent("@@@!"):
    return body[1]

  elif body.kind == nnkInfix and
       body[0].eqIdent(".@@@!"):
    return newCall(
      resCall, ident "nnkDotExpr",
      quoteAux(body[1], resCall),
      body[2].dropPar1()
    )


  result = newCall(resCall, ident $body.kind)

  case body.kind:
    of nnkAccQuoted:
      if body[0].kind == nnkIdent and
         not body[0].strVal().validIdentifier(): # Special case
         # operators `[]` - most of the time you would want to
         # declare `` proc `[]` `` rather than interpolate `[]`
         # (which is not valid variable name even)
        let bodyLit = newLit body[0].strVal()
        return quote do:
          newPTree(nnkAccQuoted, newPIdent(`bodyLit`))

      else:
        var res: string
        for node in body:
          res &= node.repr

        return parseExpr(res)

    of nnkStrKinds:
      result.add newLit body.strVal

    of nnkFloatKinds:
      result.add newLit body.floatVal

    of nnkIntKinds:
      result.add newLit body.intVal

    of nnkIdent, nnkSym:
      result = newCall("newPIdent", newLit(body.strVal))

    else:
      var hasSplices = false

      block findSplices:
        for subnode in body:
          if subnode.kind == nnkPrefix and
             subnode[0].eqIdent("@@@"):

             hasSplices = true
             break findSplices

          for node in subnode:
            if node.kind == nnkPrefix and
               node[0].eqIdent("@@@^"):

              # IdentDefs     <- subnode
              #   Ident "arg" <- node
              #   Prefix      <- necessary prefix
              #     Ident "@@@^"
              #     Ident "nArgList"
              #   Empty

              hasSplices = true
              break findSplices


      if hasSplices:
        let kind = ident $body.kind
        result = newStmtList()

        var tree = ident "tree"

        result.add quote do:
          var `tree` = newPTree(`kind`)

        for subnode in body:
          var splice = false

          for node in subnode:
            if node.kind == nnkPrefix and
               node[0].eqIdent("@@@^"):
              let impl = node[1]

              result.add quote do:
                for val in `impl`:
                  `tree`.add val

              splice = true
              break


          if not splice:
            if subnode.kind == nnkPrefix and
               subnode[0].eqIdent("@@@"):
              let impl = subnode[1]
              result.add quote do:
                for val in `impl`:
                  `tree`.add val
            else:
              let builder = quoteAux(subnode, resCall)
              result.add quote do:
                `tree`.add `builder`

        result.add quote do:
          `tree`

        result = quote do:
          ((
            block:
              `result`
          ))

      else:
        for subnode in body:
          result.add quoteAux(subnode, resCall)

type NodeAuxTypes = SomeInteger | SomeFloat | string

func toPNodeAux*(value: PNode | NodeAuxTypes): PNode =
  when value is PNode:
    return value

  else:
    return newPLit(value)

func isSameCategory(kind1, kind2: NimNodeKind): bool =
  (kind1 in nnkStrKinds and kind2 in nnkStrKinds) or
  (kind1 in nnkIntKinds and kind2 in nnkIntKinds) or
  (kind1 in nnkFloatKinds and kind2 in nnkFloatKinds) or
  (kind1 in {nnkIdent, nnkSym} and kind2 in {nnkIdent, nnkSym})

func newPQuoteTree*(
    kind: NimNodeKind, subnodes: varargs[PNode, toPnodeAux]): PNode =

  if kind in nnkTokenKinds:
    assert subnodes.len == 1 and isSameCategory(
      subnodes[0].kind.toNNK(), kind),
      $subnodes.len & " " & $subnodes[0].kind & " " & $kind
    return subnodes[0]

  else:
    newPTree(kind, subnodes)

func toNimNodeAux*(value: NimNode | NodeAuxTypes): NimNode =
  when value is NimNode:
    return value

  else:
    return newLit(value)

func newNQuoteTree*(
    kind: NimNodeKind, subnodes: varargs[NimNode, toNimNodeAux]): NimNode =


  if kind in nnkTokenKinds:
    assert subnodes.len == 1 and isSameCategory(
      subnodes[0].kind, kind),
      $subnodes.len & " " & $subnodes[0].kind & " " & $kind
    return subnodes[0]

  else:
    newTree(kind, subnodes)

macro pquote*(mainBody: untyped): untyped =
  ## `quote` macro to generate `PNode` builder. Similarly to `superquote`
  ## from `macroutils` allows to use any expressions for interpolation.
  ## Additionally, to circumvent some limitations of how AccQuoted is
  ## parsed, you can use `@@@`, `@@@!` and `@@@^` prefixes for
  ## interpolation of the arguments directly.
  ##
  ## - `@@@!` - interpolate arguments directly. This is what you should
  ##    use instead of backticks
  ## - `@@@` - *splice* arguments into list. Adding more than one subnode
  ##   to generated code - `[1, 2, 3, @@@(moreArgs)]` - will insert result
  ##   of evaluation for `moreArgs` into `nnkBracketExpr` subnodes.
  ## - `@@@^` - splice arguments into *parent* list. This should be used in
  ##   cases where arbitrary expressions are not allowed, namely function
  ##   parameter list, field declarations etc. You now can do
  ##   `proc(a: int, b: @@@^(moreArgs))` to append to argument list. `b` in
  ##   this case only used as dummy node, since `proc(a: int, @@@(args))`
  ##   is not a valid syntax.
  ##
  ## NOTE - recommended way of using intrinsic DSL prefixes is
  ## `@@@(argument)` and not `@@@argument`. It clearly distinguishes
  ## between prefix and what should be spliced. Also allows for things like
  ## `@@@([arg1, arg2])` if needed.


  result = quoteAux(mainBody, "newPQuoteTree")

macro nquote*(mainBody: untyped): untyped =
  ## DSL and set of features is identical to `pquote`, but generates
  ## `NimNode` instead of `PNode`.
  result = quoteAux(mainBody, "newNQuoteTree")
