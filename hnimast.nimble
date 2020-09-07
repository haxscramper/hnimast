# Package

version       = "0.3.2"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.2.6"
requires "hmisc >= 0.4.3"
requires "compiler"

# Test configuration

let
  testDir = "/tmp/docker-hnimast"
  localDevel = @["hmisc"]

template canImport(x: untyped): untyped =
  compiles:
    import x


when canImport(hmisc/other/nimbleutils):
  import hmisc/other/nimbleutils

  task dockertestDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      thisDir(), testDir, localDevel, "nimble test") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

    rmDir testDir


  task dockertestAllDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      thisDir(), testDir, localDevel, "nimble testallTask") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

  task dockertest, "Test in new docker container":
    ## Run unit tests in new docker conatiner; download all
    ## dependencies using nimble.
    runDockerTest(thisDir(), testDir, "nimble test") do:
      discard

  task installtest, "Test installation from cloned repo":
    runDockerTest(thisDir(), testDir, "nimble install")

  task testall, "Run full test suite in all variations":
    runDockerTest(
      thisDir(), testDir, "nimble install hmisc@#head && nimble testallTask")

  task testallTask, "~~~ testall implementation ~~~":
    testAllImpl()
