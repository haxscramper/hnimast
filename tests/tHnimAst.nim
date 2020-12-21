import sugar, strutils, sequtils, strformat, macros, options
import ../src/hnimast
import hmisc/helpers
import ../src/hnimast/obj_field_macros

import compiler/ast
import hmisc/types/colorstring
# import ../src/hnimast/hnim_ast
# import hpprint


#===========================  implementation  ============================#

#================================  tests  ================================#

import unittest

suite "HNimAst":
  test "{enumPref} :macro:":
    type
      En = enum
        en1 = 2

    assertEq enumPref(En), "en"
    let val = en1
    assertEq enumPref(val), "en"
    assertEq enumPref(en1), "en"

    proc gen[T](a: T, pr: string): void = assertEq enumPref(a), pr

    gen(en1, "en")

    type Alias = En

    var alias: Alias
    gen(alias, "en")

  test "{enumNames} :macro:":
    type
      En = enum
        en1 = "hello"
        en2 = "world"

    assertEq enumNames(En), @["en1", "en2"]
    assertEq enumNames(en1), @["en1", "en2"]
    let val = en1
    assertEq enumNames(val), @["en1", "en2"]

  test "{parseObject} parse nim pragma":
    macro parse(body: untyped): untyped =
      for stmt in body:
        for obj in stmt:
          if obj.kind == nnkTypeDef:
            let obj = obj.parseObject(parseNimPragma)
            if obj.annotation.isSome():
              for call in obj.annotation.get().elements:
                discard

            for field in obj.flds:
              if field.annotation.isSome():
                for call in field.annotation.get().elements:
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


  test "{parseObject} filter pragma annotations":
    macro parse(body: untyped): untyped =
      var obj = body[0][0].parseObject(parseNimPragma)
      for call in obj.annotation.get().elements:
        discard

      obj.annotation = none(NPragma)

      obj.eachFieldMut do(fld: var ObjectField[NimNode, NPragma]):
        fld.annotation = none(NPragma)

      result = nnkTypeSection.newTree obj.toNimNode()

    parse:
      type
        Type {.zz(C), ee: "333", ee.} = object
          f1 {.check(it < 2).}: float = 32.0

  test "{newProcDeclNode}":
    macro mcr(): untyped =
      result = newStmtList()
      result.add newProcDeclNode(
        ident "hello",
        { "world" : newNType("int") },
        newCall(
          "echo", newLit("value is: "), ident "world"
        ),
        exported = false
      )

    mcr()

    hello(12)

  test "{eachCase}":
    macro mcr(body: untyped): untyped =
      let obj = body[0][0].parseObject(parseNimPragma)
      let objid = ident "hjhh"
      let impl = objid.eachCase(obj) do(
        fld: NObjectField[NPragma]
      ) -> NimNode:
        let fld = ident fld.name
        quote do:
          echo `objid`.`fld`

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


  test "{eachParallelCase}":
    ## Automatically generate comparison proc for case objects.
    macro mcr(body: untyped): untyped =
      let
        obj = body[0][0].parseObject(parseNimPragma)
        lhs = ident "lhs"
        rhs = ident "rhs"

      let impl = (lhs, rhs).eachParallelCase(obj) do(
        fld: NObjectField[NPragma]) -> NimNode:
        let fld = ident fld.name
        quote do:
          if `lhs`.`fld` != `rhs`.`fld`:
            return false


      let eqcmp = [ident "=="].newProcDeclNode(
        newNType("bool"),
        { "lhs" : obj.name, "rhs" : obj.name },
        pragma = newNPragma("noSideEffect"),
        impl = (
          quote do:
            `impl`
            return true
        ),
        exported = false
      )

      result = nnkStmtList.newTree(body, eqcmp)

    mcr:
      type
        A = object
          fdl: seq[float]
          case b: char
            of '0':
              qw: char
              wer: float
            of '-':
              ee: float
            else:
              eeerw: char
              # nil # TODO

    echo A() == A()

  test "{eachPath}":
    macro mcr(body: untyped): untyped =
      let obj = body[0][0].parseObject(parseNimPragma)
      let self = ident "self"
      let impl = self.eachPath(obj) do(
        path: NObjectPath[NPragma],
        flds: seq[NObjectField[NPragma]]
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
      `newPIdent(hello & $$$"World")`

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


suite "working with PNode":
  test "Core":
    echo newPIdent("hello")
    echo newReturn(newPIdent("qqqq"))
    echo newPrefix("!", newPIdent("eee"))
    echo newProcDeclNNode(
      newPIdent("hello"), none(NType[PNode]), @[], newPIdent("impl"))

    echo newProcDeclNode(newPIdent("nice"), {
      "arg1" : newPType("HHH")
    }, newPIdent("implementation"), comment = "some documentation")

    block:
      var decl = newProcDeclNode(newPIdent("nice"), [
        ("arg1", newPType("HHH"), nvdVar)
      ], newPIdent("implementation"))


      echo newProcDeclNode(
        newPIdent("noimpl"), {"arg1" : newPType("HHH")}, newEmptyPNode())

      var procdef: ProcDecl[PNode]
      procdef.name = "Hello"
      procdef.signature = newProcNType[PNode](@[])
      procdef.docComment = "werqwre"
      let pd = procdef.toNNode()
      echo pd

      let node = parsePNodeStr($pd)
      echo node.treeRepr()
      # echo node.treeRepr()

      decl.comment = "hello world"
      echo decl

    block:
      var en = PEnumDecl(name: "Eee").withIt do:
        it.values.add makeEnumField(
          name = "Hello",
          value = some(newPIdent("EEE")),
          comment = "documentation comment"
        )

        # values: @{
        #   "hello" : some(
        #     newPIdent("eee").withIt do:
        #       it.comment = "documentation for field"
        #   ),
        #   "world" : some(newPLit(12))
        # }
      # )

      en.meta.docComment = """
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

    var obj = parseObject(node, parsePPragma)
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
    hnimast.write(stdout, pdecl)

    var decls: seq[NimTypeDecl[PNode]]

    decls.add toNimTypeDecl(newPEnumDecl("Test", iinfo = currIInfo()))

    hnimast.write(stdout, decls.toNimDecl())

import hnimast/pprint

suite "Pretty printing":
  test "Proc declaration":
    let pr = newPProcDecl(
      name = "hello",
      args = {
        "similarityTreshold" : newPType("ScoreCmpProc"),
        "secondArgument" : newPType("StdCxx11BasicStringSizeType"),
      },
      genParams = @[newPType("CharT")],
      pragma = newPPragma(
        newPident("cdecl"),
        nnkExprColonExpr.newPTree(
          newPIdent("importcpp"),
          newRStrLit("std::__cxx11::basic_string<'0, '1, '2>::size_type")
        )
      ),
      impl = ((
        pquote do:
          for a in b:
            echo a

          if b == 12:
            echo 123
      ))
    )

    echo pr.toNNode()
    startHax()
    echo pr.toNNode().toPString()

    echo toPString((
      pquote do:
      const
        arrCxxSCmapping: array[CxxSC, tuple[name: string, cEnum: CxxSC_Impl,
                                            cName: string, value: int]] = [
          (name: "World", cEnum: cxxSC_World, cName: "cxx::S::C::World", value: 12),
          (name: "Nice", cEnum: cxxSC_Nice, cName: "cxx::S::C::Nice", value: 13),
          (name: "HHHZ", cEnum: cxxSC_HHHZ, cName: "cxx::S::C::HHHZ", value: 14),
          (name: "Hello", cEnum: cxxSC_Hello, cName: "cxx::S::C::Hello", value: 33)]
    ))
