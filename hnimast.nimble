# Package

version       = "0.3.2"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.2.6"
requires "hmisc >= 0.8.0"
requires "macroutils"
requires "compiler"

# Test configuration

let
  testDir = "/tmp/docker-hnimast"
  localDevel = @["hmisc"]

from os import `/`
template canImport(x: untyped): untyped =
  compiles:
    import x


when canImport(hmisc/other/nimbleutils):
  import hmisc/other/nimbleutils

  task dockertestDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      AbsDir thisDir(),
      AbsDir testDir,
      localDevel, "nimble test") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

    rmDir testDir


  task dockertestAllDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      AbsDir thisDir(),
      AbsDir testDir,
      localDevel, "nimble testallTask") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

  task dockertest, "Test in new docker container":
    ## Run unit tests in new docker conatiner; download all
    ## dependencies using nimble.
    runDockerTest(AbsDir thisDir(), AbsDir testDir, "nimble test") do:
      discard

  task installtest, "Test installation from cloned repo":
    runDockerTest(AbsDir thisDir(), AbsDir testDir, "nimble install")

  task testall, "Run full test suite in all variations":
    runDockerTest(
      AbsDir thisDir(),
      AbsDir testDir, "nimble install hmisc@#head && nimble testallTask")

  task testallTask, "~~~ testall implementation ~~~":
    testAllImpl()

  task docgen, "Generate documentation":
    var conf = initBuildConf()
    conf.testRun = false
    conf.configureCI()
    runDocgen(conf)

  task dockerDockGen, "Test documentation generation in docker":
    runDockerTest(
      AbsDir thisDir(),
      AbsDir testDir,
      "nimble install -y hmisc@#master && nimble docgen"
    )
