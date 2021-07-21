import
  hnimast/[compiler_aux, hast_common]

import
  std/[sets]

type
  Context = object
    fakes: HashSet[PSym]
    fakeList: seq[(TLineInfo, string)]

proc hasHiddenEffects*(node: PNode, ctx: var Context): bool =
  case node.kind:
    of nkIdentKinds:
      discard

    of nkCallKinds:
      let sym = node.headSym()
      if not isNil(sym) and sym in ctx.fakes:
        ctx.fakeList.add((node.info, node.getStrVal()))
        return true

      else:
        # if notNil(sym.typ) and notNil(sym.typ.n):
        #   if

        for arg in node:
          if hasHiddenEffects(arg, ctx):
            return true

    else:
      for sub in node:
        if hasHiddenEffects(sub, ctx):
          return true

proc warnFake*(node: PNode, ctx: var Context) =
  case node.kind:
    of nkProcDeclKinds:
      let sym = node[0].headSym()
      echo sym
      echo sym.typ.n.treeRepr()

    else:
      for sub in node:
        warnFake(sub, ctx)
  # echo node.treeRepr()

when isMainModule:
  let compiled = compileString("""
func realNoSide() = discard

proc fakeSide() {.noSideEffect.} =
  {.cast(noSideEffect).}:
    echo 1231

proc main() =
  fakeSide()

main()
""")

  var ctx: Context
  warnFake(compiled, ctx)
