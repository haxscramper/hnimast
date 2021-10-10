import hnimast/pprint
import hnimast

when false:
  import ./test
  proc git_annotated_commit_from_ref*(arg_out: ptr ptr git_annotated_commit;
                                      repo: ptr git_repository;
                                      arg_ref: ptr git_reference): cint {.
      dynlib: libgitDl, importc.}

  proc test(arg: int): float

  type
    ass = proc(a: float): int

    git_status_t* = enum
      GIT_STATUS_CURRENT = 0,
      GIT_STATUS_INDEX_NEW = 1,
      GIT_STATUS_INDEX_MODIFIED = 2,
      GIT_STATUS_INDEX_DELETED ## Enum field documentation

    git_status_options* {.bycopy, header: "<git2/status.h>", importc.} = object
      ## OBject
      ## documentation
      version*: cuint
      show*: git_status_show_t ## The version
                               ## Documentation comment
      flags*: cuint ## Flags


  let val =
    case a:
      of 1: 2
      of 2: echo 1

let a = parsePnodeStr(currentSourcePath().readFile())
let b = a.toPString()
echo b
let c = parsePnodeStr(b)
