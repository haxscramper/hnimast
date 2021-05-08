import ./object_decl, ./enum_decl

import hnimast
import hmisc/hexceptions
import hmisc/algo/halgorithm
import hmisc/hdebug_misc
import std/[macros, options, sequtils, strutils, tables]

var objectImplMap {.compiletime.}: Table[string, NObjectDecl]
var enumImplMap {.compiletime.}: Table[string, NEnumDecl]

proc getObjectStructure*(obj: NimNode): NObjectDecl =
  let hash = obj.signatureHash()
  if hash in objectImplMap:
    objectImplMap[hash]

  else:
    raiseArgumentError(
      "Cannot get object structure for node " &
      obj.toStrLit().strVal() &
      " - not recorded in object impl map"
    )

proc getEnumStructure*(obj: NimNode): NEnumDecl =
  enumImplMap[obj.signatureHash()]

proc setObjectStructure*(obj: NimNode, consts: seq[NimNode]) =
  let impl = getTypeImplBody(obj, false)
  if impl.isObject():
    for c in consts:
      echov c.treeRepr1()

    if obj.signatureHash() notin objectImplMap:
      var parsed: NObjectDecl = parseObject(impl, false, consts)
      if parsed.hasPragma("defaultImpl"):
        let pragma = parsed.getPragmaArgs("defaultImpl")
        for field in iterateFields(parsed):
          for arg in pragma[0]:
            if field.name == arg[0].strVal():
              field.value = some arg[1]

      objectImplMap[obj.signatureHash()] = parsed


  else:
    var parsed = parseEnum(impl)
    enumImplMap[obj.signatureHash()] = parsed

macro storeTraitsImpl*(obj: typed, consts: varargs[typed]) =
  setObjectStructure(obj, toSeq(consts))

macro storeTraits*(obj: untyped, consts: varargs[untyped]) =
  # Generate call to store all constants in `(name, node)` plist
  result = newCall("storeTraitsImpl", obj)
  for c in consts:
    result.add nnkPar.newTree(newLit(c.strVal()), c)
