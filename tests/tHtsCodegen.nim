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
  defaultHtsGenConf.withIt do:
    it.langPrefix  = "lang"
    it.grammarJs   = AbsFile(relToSource"assets/grammar1.js")
    it.parserOut   = some(gen /. "generated.c")
    it.wrapperOut  = some wrapper
    it.l           = newTermLogger()
    it.testLink    = false
    it.testCheck   = false
)

var cmd = shellCmd(nim, check, errormax = 2)

let j = shellCmd(nim, dump, "dump.format" = "json", $currentSourcePath()).
  evalShellStdout()

for path in j.parseJson()["lib_paths"]:
  cmd.opt "path", path.asStr()

cmd.arg $wrapper

execShell cmd, limitErr = 30
