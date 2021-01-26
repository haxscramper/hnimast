## Statically typed nim ast representation with large number of helper
## functions - skipping nil nodes, normalizing set literals,
## generating and working with pragma annotations, parsing object
## defintions etc.

import hmisc/[helpers, base_errors]
export base_errors

import hmisc/types/colorstring
import std/[
  sequtils, colors, macros, tables, strutils, streams,
  terminal, options, parseutils, sets, strformat, sugar
]

import compiler/[ast, idents, lineinfos, renderer]

import hnimast/[pnode_parse]
export pnode_parse, options, NimNodeKind

export ast
export PNode
