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



proc baseImplSym*(t: NimNode): NimNode =
  case t.kind:
    of nnkTypeofExpr:
      result = baseImplSym(t[0])

    of nnkSym:
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
            result = baseImplSym(impl[0])

        else:
          raiseImplementKindError(impl, impl.treeRepr1())

    else:
      raiseImplementKindError(t)


proc setObjectStructure*(obj: NimNode, consts: seq[NimNode]) =
  let impl = getTypeImplBody(obj, false)
  let hash = obj.baseImplSym().signatureHash()
  if impl.isObject():
    if hash notin objectImplMap:
      var parsed: NObjectDecl = parseObject(impl, false, consts)
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
  let hash = obj.baseImplSym().signatureHash()
  if hash in objectImplMap:
    result = objectImplMap[hash]

  else:
    setObjectStructure(obj, @[])
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
