import hnimast/pprint
import hnimast
import hmisc/core/all

startHax()

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
      GIT_STATUS_CURRENT = 0 ## Enum
                             ## Field
      GIT_STATUS_INDEX_NEW = 1,
      GIT_STATUS_INDEX_MODIFIED = 2,
      GIT_STATUS_INDEX_DELETED ## Enum field documentation

    git_indexer_options* {.bycopy, header: "<git2/indexer.h>", importc.} = object
      version*: cuint
      progress_cb*: git_indexer_progress_cb ## progress_cb function to call with progress information

    git_status_options* {.bycopy, header: "<git2/status.h>", importc.} = object
      ## OBject
      ## documentation
      version*: cuint
      show*: git_status_show_t ## The version
                               ## Documentation comment
      flags*: cuint ## Flags

      test* {.importc: "field_".}: int

      case kind*: bool
        of true, false:
          ## Documentation for enum branch
          discard

        of false:
          ## Documentation for enum branch
          sub1*: int
          sub2*: float

  converter to_c_name*(arg: c_name) =
    case arg.kind:
      of c_a:

        a
      of c_b:

        b
  proc to_name*(arg: c_name) =
    case arg.kind:
      of a:

        c_a
      of b:

        c_b

  let val =
    case a:
      of 1: 2
      of 2: echo 1

let a = parsePnodeStr(currentSourcePath().readFile())
let b = a.toPString()
echo b
let c = parsePnodeStr(b)
