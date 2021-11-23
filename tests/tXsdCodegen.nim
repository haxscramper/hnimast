import
  hmisc/other/[oswrap, hshell]

import
  hnimast,
  hnimast/codegen/xsd_to_nim,
  hmisc/core/all

import
  hmisc/other/hjson

const dir = oswrap.currentSourceDir()
let gen = getAppTempFile("generated.nim")

startHax()

echov gen
AbsFile(relToSource"assets/xunit.xsd").
  generateForXsd().
  writeXsdGenerator(gen)

var cmd = shellCmd(nim, check, errormax = 2)

for path in shellCmd(nim, dump, "dump.format" = "json", "-").
  evalShellStdout().
  parseJson()["lib_paths"]:

  cmd.opt "path", path.asStr()

cmd.arg $gen

execShell cmd, limitErr = 30
