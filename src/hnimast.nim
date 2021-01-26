## Statically typed nim ast representation with large number of helper
## functions - skipping nil nodes, normalizing set literals,
## generating and working with pragma annotations, parsing object
## defintions etc.

import hmisc/[helpers, base_errors]
export base_errors

import std/[options, macros]
import compiler/[ast, idents, lineinfos, renderer]
import hnimast/[
  pnode_parse,
  hast_common,
  pragmas,
  proc_decl,
  object_decl,
  enum_decl,
  idents_types,
  hast_quote,
  nim_decl
]

export pnode_parse,
  hast_common,
  pragmas,
  proc_decl,
  object_decl,
  enum_decl,
  idents_types,
  hast_quote,
  nim_decl

export pnode_parse, options, NimNodeKind

export ast
export PNode
