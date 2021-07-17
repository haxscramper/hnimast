type
  VmInt* = int
  VmString* = string
  VmTuple* = (int, string)
  VmKind* = enum
    vmkFirst
    vmkSecond

  VmObject* = object
    field1*: int
    field2*: float

  VmVariant* = object
    case kind*: VmKind
      of vmkFirst:
        field1*: string

      of vmkSecond:
        field2*: char
