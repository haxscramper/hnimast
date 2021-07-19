import ./object_decl, ./enum_decl

import hnimast
import hmisc/hexceptions
import hmisc/algo/halgorithm
import hmisc/hdebug_misc
import std/[macros, options, sequtils, strutils, tables]

var objectImplMap {.compiletime.}: Table[string, NObjectDecl]
var enumImplMap {.compiletime.}: Table[string, NEnumDecl]


proc hasObjectStructure*(obj: NimNode): bool =
  obj.signatureHash() in objectImplMap


proc getEnumStructure*(obj: NimNode): NEnumDecl =
  enumImplMap[obj.signatureHash()]



proc baseImplSym*(t: NimNode, passSym: bool = false): NimNode =
  case t.kind:
    of nnkTypeofExpr:
      # echov t[0].getType().treeRepr1()
      # echov t.treeRepr1()
      result = baseImplSym(t[0], passSym = passSym)

    of nnkBracketExpr:
      if t[0].eqIdent("typedesc"):
        result = baseImplSym(t[1], passSym = passSym)

      else:
        # BracketExpr
        #   Sym "Table"
        #   Sym "string"
        #   Sym "string"
        result = baseImplSym(t[0], passSym = passSym)

    of nnkDotExpr:
      # echov t.treeRepr1()
      result = baseImplSym(t[1], passSym = passSym)

    of nnkSym:
      case t.symKind:
        of nskField:
          # echov t.getTypeImpl.treeRepr1()
          # echov t.getTypeInst.treeRepr1()
          result = t.getTypeInst().baseImplSym(passSym = passSym)
          # echov result

        else:
          if passSym:
            return t

          let impl = t.getTypeImpl()
          case impl.kind:
            of nnkBracketExpr:
              result = impl[1].baseImplSym()

            of nnkObjectTy, nnkEnumTy:
              result = t

            of nnkRefTy:
              if ":ObjectType" in impl[0].getStrVal():
                result = t

              else:
                result = baseImplSym(impl[0], passSym = passSym)

            else:
              raiseImplementKindError(impl, impl.treeRepr1())

    else:
      raiseImplementKindError(t, t.treeRepr())

proc genericParams*(T: NimNode): seq[NimNode] =
  var impl = getTypeImpl(T)
  # echo treeRepr1(impl)
  expectKind(impl, nnkBracketExpr)
  impl = impl[1]
  while true:
    case impl.kind:
      of nnkSym:
        impl = impl.getImpl

      of nnkTypeDef:
        impl = impl[2]

      of nnkTypeOfExpr:
        impl = getTypeInst(impl[0])

      of nnkObjectTy, nnkRefTy:
        break # ??

      of nnkBracketExpr:
        for ai in impl[1 .. ^1]:
          var ret: NimNode = nil
          case ai.typeKind
            of ntyTypeDesc:
              ret = ai

            of ntyStatic:
              doAssert false

            else:
              if
                (ai.kind == nnkSym and ai.symKind == nskType) or
                (ai.kind == nnkBracketExpr and
                 ai[0].kind == nnkSym and
                 ai[0].symKind == nskType) or

                ai.kind in {nnkRefTy, nnkVarTy, nnkPtrTy, nnkProcTy}:

                ret = ai

              elif
                ai.kind == nnkInfix and
                ai[0].kind == nnkIdent and
                ai[0].strVal == "..":

                ret = newTree(nnkBracketExpr, @[newIdent("range"), ai])

              else:
                ret = ai

          result.add ret
        break

      else:
        raise newUnexpectedKindError(impl.kind, impl.treeRepr1())

proc setObjectStructure*(
    obj: NimNode, consts: seq[NimNode], passSym: bool = false) =

  let impl = getTypeImplBody(obj, false)
  # echov obj.treeRepr1()
  # echov obj.repr
  # echov impl.treeRepr1()
  let sym = obj.baseImplSym()
  let hash = sym.signatureHash()
  # echov sym.getType().getTypeInst()
  if impl.isObject():
    if hash notin objectImplMap:
      var parsed: NObjectDecl = parseObject(impl, false, consts)
      if impl.kind in {nnkObjectTy}:
        parsed.name = newNType(sym.strVal())

      # echov parsed.name
      if parsed.hasPragma("defaultImpl"):
        let pragma = parsed.getPragmaArgs("defaultImpl")
        for field in iterateFields(parsed):
          for arg in pragma[0]:
            if field.name == arg[0].strVal():
              field.value = some arg[1]

      objectImplMap[hash] = parsed


  else:
    var parsed = parseEnum(impl)
    enumImplMap[hash] = parsed


proc getObjectStructure*(obj: NimNode): NObjectDecl =
  let sym = obj.baseImplSym()
  # echov sym
  let hash = sym.signatureHash()
  if hash in objectImplMap:
    result = objectImplMap[hash]

  else:
    setObjectStructure(obj, @[], passSym = true)
    if hash in objectImplMap:
      result = objectImplMap[hash]

    else:
      raiseArgumentError(
        "Cannot get object structure for node " &
        obj.toStrLit().strVal() &
        " - not recorded in object impl map"
      )


macro storeTraitsImpl*(obj: typed, consts: varargs[typed]) =
  setObjectStructure(obj, toSeq(consts))

macro storeTraits*(obj: untyped, consts: varargs[untyped]) =
  # Generate call to store all constants in `(name, node)` plist
  result = newCall("storeTraitsImpl", obj)
  for c in consts:
    result.add nnkPar.newTree(newLit(c.strVal()), c)
