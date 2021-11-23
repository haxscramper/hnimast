import
  hmisc/other/[oswrap, hshell, hlogger]

import
  hnimast,
  hnimast/codegen/hts_wrapgen,
  hmisc/core/all

import
  hmisc/other/hjson

const dir = oswrap.currentSourceDir()
let gen = getAppTempDir()

startHax()

let wrapper = gen /. "wrapper.nim"

grammarFromFile(
  langPrefix  = "lang",
  grammarJs   = AbsFile(relToSource"assets/grammar1.js"),
  parserOut   = some(gen /. "generated.c"),
  wrapperOut  = some wrapper,
  l           = newTermLogger(),
  testLink    = false
)

var cmd = shellCmd(nim, check, errormax = 2)

for path in shellCmd(nim, dump, "dump.format" = "json", "-").
  evalShellStdout().
  parseJson()["lib_paths"]:

  cmd.opt "path", path.asStr()

cmd.arg $wrapper

execShell cmd, limitErr = 30
