import hnimast/compiler_aux, std/os
# import hpprint

import std/[tables, sets]

let p = currentSourcePath.parentDir.parentDir / "hnimast.nimble"
let c = readFile(p)
let info = parsePackageInfoNims(c)

# pprint info
