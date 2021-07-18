import
  hnimast/[compiler_aux, hast_common, nimble_aux],
  std/[tables, sets, os, unittest],
  hmisc/base_errors,
  compiler/sighashes


import fusion/matching

suite "Package parsing":
  let p = currentSourcePath.parentDir.parentDir / "hnimast.nimble"
  let c = readFile(p)
  let info = parsePackageInfo(c)

proc toLua(n: PNode): string =
  template push(s: string): untyped = result.add s

  case n.kind:
    of nkStmtList:
      for sub in n:
        push sub.toLua()
        push "\n"

    of nkTypeSection:
      discard

    of nkProcDeclKinds:
      push "function "
      push n[0].toLua()

      push "("
      for idx, param in n[3][1 ..^ 1]:
        if idx > 0: push ", "
        push param[0].toLua()

      push ")\n"

      push n[^1].toLua()


      push "end\n"

    of nkAsgn:
      push n[0].toLua()
      push " = "
      push n[1].toLua()
      push "\n"

    of nkDotExpr:
      push n[0].toLua()
      push "."
      push n[1].toLua()

    of nkSym:
      push $n.sym.sighash()

    of nkVarSection:
      for decl in n:
        push decl[0].toLua()
        push " = "
        push decl[2].toLua()
        push "\n"

    of nkHiddenDeref, nkHiddenAddr:
      push n[0].toLua()

    of nkInfix:
      push n[1].toLua()
      push " "
      push n[0].getStrVal()
      push " "
      push n[2].toLua()

    of nkIntKinds:
      push $n.intVal

    of nkCall:
      push n[0].toLua()
      push "("
      for idx, arg in n[1 ..^ 1]:
        if idx > 0: push ", "
        push arg.toLua()

      push ")"

    of nkObjConstr:
      push "{"
      for field in n[1 ..^ 1]:
        push field[0].toLua()
        push " = "
        push field[1].toLua()

      push "}"

    else:
      raise newImplementKindError(n, n.treeRepr())

suite "String compilation":
  let tree = compileString("""

type
  Account = object
    balance: int

proc withdraw(acc: var Account, amount: int) =
  acc.balance = acc.balance - amount

var acc = Account(balance: 12)

acc.withdraw(100)
""")

  echo tree.treeRepr()

  echo tree.toLua()
