# import std/tables

type
  IgnoredArgsSeq* = object
    args: seq[string]

  IgnoredArgsArray* = object
    args: array[2, string]

  VmPrivateImpl[T] = object
    test: string
    genr: T

  VmInt* = int
  VmString* = string
  VmTuple* = (int, string)
  VmKind* = enum
    vmkFirst
    vmkSecond

  VmObject* = object
    field1*: int
    field2*: float

  VmVariant* = ref object
    beforeKind: char
    privateField: float
    tableField*: VmPrivateImpl[string]
    case kind*: VmKind
      of vmkFirst:
        field1*: string
        privateFieldUnderSwitch: string

        procField: proc(a: int): float {.noSideEffect.}
        case nested*: bool
          of true:
            discard

          of false:
            pointerField: pointer

        # case ranged*: range[0 .. 3]:
        #   of 0:
        #     test: array[1 .. 3, char]

        #   of 1: discard
        #   of 2: discard
        #   of 3: discard



      of vmkSecond:
        field2*: string

    afterKind: char

proc initVmPrivateImpl*[T](arg: string = ""): VmPrivateImpl[T] =
  result.test = arg

type
  VmWithRefFields* = ref object
    subfields: seq[VmWithRefFields]

proc nr*(args: varargs[VmWithRefFields]): VmWithRefFields =
  result = VmWithRefFields()
  for arg in args:
    result.subfields.add arg
