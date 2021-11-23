import std/[strutils, sequtils, strformat, macros, options]
import
  hmisc/core/all,
  hmisc/preludes/unittest

import
  hmisc/algo/clformat

import
  hnimast,
  hnimast/[obj_field_macros, pprint, hast_common]

import compiler/ast

macro showTyped*(body: typed) =
  echo body.treeRepr1(positionIndexed = false)

suite "HNimAst":
  test "{enumPref} :macro:":
    type
      En = enum
        en1 = 2

    let val = en1
    check:
      enumPref(En) == "en"
      enumPref(val) == "en"
      enumPref(en1) == "en"

    proc gen[T](a: T, pr: string): void =
      doAssert enumPref(a) == pr

    gen(en1, "en")

    type Alias = En

    var alias: Alias
    gen(alias, "en")

  test "{enumNames} :macro:":
    type
      En = enum
        en1 = "hello"
        en2 = "world"

    let val = en1

    check:
      enumNames(En) == @["en1", "en2"]
      enumNames(en1) == @["en1", "en2"]
      enumNames(val) == @["en1", "en2"]

  test "{parseObject} parse nim pragma":
    macro parse(body: untyped): untyped =
      for stmt in body:
        for obj in stmt:
          if obj.kind == nnkTypeDef:
            let obj = parseObject(obj)
            if obj.pragma.isSome():
              for call in obj.pragma.get().elements:
                discard

            for field in obj.flds:
              if field.pragma.isSome():
                for call in field.pragma.get().elements:
                  discard

    parse:
      type
        Type {.zzz(Check).} = object
          f1 {.check(it < 10).}: float = 12.0

        Type*[A] {.ss.} = object
          f1: int

        Type* {.ss.} = object
          f23: int

        Type[A] {.ss.} = object
          f33: int

        Type[B] {.ss.} = object
          case a: bool
            of true:
              b: int
            of false:
              c: float

        Hhhhh = object
          f1: float
          f3: int
          case f5: bool
            of false:
              f2: char
            else:
              f4: float


  test "{parseObject} filter pragma pragmas":
    macro parse(body: untyped): untyped =
      var obj = body[0][0].parseObject()
      for call in obj.pragma.get().elements:
        discard

      obj.pragma = none(NPragma)

      obj.eachFieldMut do(fld: var ObjectField[NimNode]):
        fld.pragma = none(NPragma)

      result = nnkTypeSection.newTree obj.toNimNode()

    parse:
      type
        Type {.zz(C), ee: "333", ee.} = object
          f1 {.check(it < 2).}: float = 32.0

  test "{eachCase}":
    macro mcr(body: untyped): untyped =
      let obj = body[0][0].parseObject()
      let objid = ident "hjhh"
      let impl = objid.eachCase(obj) do(fld: NObjectField) -> NimNode:
        newCall("echo", newDot(ident "hjhh", ident(fld.name)))
        # quote do:
        #   echo `objid`.`fld`

      result = newStmtList(body)

      result.add quote do:
        let hjhh {.inject.} = Hello()

      result.add impl

    mcr:
      type
        Hello = object
          ewre: char
          case a: uint8:
            of 0:
              zee: float
            of 2:
              eee: string
            of 4:
              eee3: int
              eee24: int
              eee2343: int
              eee321344: int
            else:
              eee23: string


  # Fails compilation with `Error: cannot evaluate at compile time: lhs1`
  # if I put `lhs1` inside of the callback - I have no idea why, and I
  # don't want to spend another five hours trying to figure this out, only
  # to later realize this is simply a compiler bug. btw, this code worked
  # perfectly well earlier.

  # test "{eachParallelCase}":
  #   ## Automatically generate comparison proc for case objects.
  #   macro mcr(body: untyped): untyped =
  #     let
  #       obj = body[0][0].parseObject()
  #       rhs1: NimNode = macros.ident"rhs"
  #       lhs1: NimNode = macros.ident"lhs"

  #     let val = newNQuoteTree(nnkDotExpr, @[toNimNodeAux lhs1])

  #     let impl = eachParallelCase((lhs1, rhs1), obj, proc(fld: NObjectField): NImNode = lhs1)
  #       # result = lhs1
  #       # let fld = ident fld.name
  #       # result = nquote do:
  #       #   if `lhs1`.`fld` != `rhs1`.`fld`:
  #       #     return false

  #     # let eqcmp = [ident "=="].newProcDeclNode(
  #     #   newNType("bool"),
  #     #   { "lhs" : obj.name, "rhs" : obj.name },
  #     #   pragma = newNPragma(newIdent("noSideEffect")),
  #     #   impl = (
  #     #     nquote do:
  #     #       `impl`
  #     #       return true
  #     #   ),
  #     #   exported = false
  #     # )

  #     # result = nnkStmtList.newTree(body, eqcmp)

  #   mcr:
  #     type
  #       A = object
  #         fdl: seq[float]
  #         case b: char
  #           of '0':
  #             qw: char
  #             wer: float
  #           of '-':
  #             ee: float
  #           else:
  #             eeerw: char
  #             # nil # TODO

  #   echo A() == A()

  test "{eachPath}":
    macro mcr(body: untyped): untyped =
      let obj = body[0][0].parseObject()
      let self = ident "self"
      let impl = self.eachPath(obj) do(
        path: NObjectPath,
        flds: seq[NObjectField]
      ) -> NimNode:
        discard

    mcr:
      type
        A = object
          c: int
          f: int
          case a: char
            of 'e':
              e: int
            of 'q':
              q: char
            else:
              hello: seq[seq[int]]

suite "PQuote do":
  test "1":
    let hello = "hello"
    let code = pquote do:
      @@@!(newPIdent(hello & "World"))

    echo code

  test "2":
    let args = @[nnkExprColonExpr.newPTree(
      newPIdent("arg"),
      newPIdent("int")
    )]

    let code2 = pquote do:
      proc zzz(arg1: float, arg2: @@@^args) =
        discard

    echo code2

  test "3":
    let vals = @[newPLit("3"), newPLit("4")]

    let code3 = pquote do:
      let vals = @["1", "2", @@@vals]

    echo code3

  test "4":
    let code3 = pquote do:
      let vals = @[@@@!(newPLit("123"))]

    echo code3

  test "5":
    let subfields = @[
      nnkIdentDefs.newPTree(newPIdent "f2", newPIdent "int", newEmptyPNode()),
      nnkIdentDefs.newPTree(newPIdent "f3", newPIdent "int", newEmptyPNode()),
      nnkIdentDefs.newPTree(newPIdent "f4", newPIdent "int", newEmptyPNode()),
    ]

    let code = pquote do:
      type
        E = object
          f1: int
          _: @@@^(subfields)

    echo code

  test "6":
    let code = pquote do:
      a.@@@!(newPIdent("hello"))

    echo code

suite "working with PNode":
  test "Core":
    echo newPIdent("hello")
    echo newReturn(newPIdent("qqqq"))
    echo newPrefix("!", newPIdent("eee"))
    block:
      var decl = newPProcDecl("nice", {"arg1" : newPType("HHH")}).toNNode()
      var procdef: ProcDecl[PNode]
      procdef.name = "Hello"
      procdef.signature = newProcNType[PNode](@[])
      procdef.docComment = "werqwre"
      let pd = procdef.toNNode()
      echo pd

      let node = parsePNodeStr($pd)
      echo node.treeRepr()

      decl.comment = "hello world"
      echo decl

    block:
      var en = PEnumDecl(name: "Eee").withIt do:
        it.values.add makeEnumField(
          name = "Hello",
          value = some(newPIdent("EEE")),
          comment = "documentation comment"
        )

      en.docComment = """
Aliquam erat volutpat. Nunc eleifend leo vitae magna. In id erat non
orci commodo lobortis. Proin neque massa, cursus ut, gravida ut,
lobortis eget, lacus. Sed diam. Praesent fermentum tempor tellus.
Nullam tempus. Mauris ac felis vel velit tristique imperdiet."""

      echo en.toNNode()

  test "Parsing objects":
    let node = """
type Type = object
  hello: float
""".parsePNodeStr()

    var obj = parseObject(node)
    obj.exported = true
    echo obj.toNNode()

  test "Runtime ordinal parsing":
    echo parsePNodeStr("1").dropStmtList().parseRTimeOrdinal()
    echo parsePNodeStr("'1'").dropStmtList().parseRTimeOrdinal()
    echo "type E = enum\n  f1 = 12".
      parsePNodeStr().
      dropStmtList().
      parseEnumImpl().
      toNNode()

  test "NimDecl API":
    let pproc = newPProcDecl(name = "hello")
    let pdecl = pproc.toNimDecl()

    let pnode = pdecl.toNNode()
    write(stdout, pdecl)

    var decls: seq[NimTypeDecl[PNode]]

    decls.add toNimTypeDecl(newEnumDecl[PNode](
      "Test", iinfo = currLInfo()))

    write(stdout, decls.toNimDecl())

suite "Distinct API":
  let node = newPProcDecl(name = "hello").toNNode()
  let pr: ProcDeclNode[PNode] = node.asProcDecl()

  echo pr.name().treeRepr()
