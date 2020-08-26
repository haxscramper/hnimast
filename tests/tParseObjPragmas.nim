import sugar, strutils, sequtils, strformat, macros

import ../src/hnimast
import ../src/hnimast/obj_field_macros

#===========================  implementation  ============================#

#================================  tests  ================================#

import unittest

type
  Annot = object
    name: string

func parseAnnot(body: NimNode, kind: ObjectAnnotKind): Annot =
  discard
  # debugecho kind
  # debugecho body.treeRepr()

macro makeAnnots(body: untyped): untyped =
  for section in body:
    for obj in section:
      # echo obj.treeRepr()
      let parsed = obj.parseObject(parseAnnot)

makeAnnots:
  type
    Hello*[T] {.derive(Hash), nice(EE).} = object
      f1: int = 22
      f2: int

suite "Parse object pragmas":
  test "test":
    echo 1
