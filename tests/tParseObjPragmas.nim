import std/[strutils, macros]

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

macro makeAnnots(body: untyped): untyped =
  for section in body:
    for obj in section:
      let parsed = obj.parseObject()

makeAnnots:
  type
    Hello*[T] {.derive(Hash), nice(EE).} = object
      f1: int = 22
      f2: int

suite "Parse object pragmas":
  test "test":
    echo 1
