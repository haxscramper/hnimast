# Package

version       = "0.3.0"
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
  let develCmd = makeLocalDevel(testDir, localDevel)

  task dockertestDevel, "Test in docker container with local packages":
    ## Run unit test in new docker container. Only download
    ## dependencies that are not listed in `localDevel` list.
    let cmd = develCmd && ("cd " & "/project/main") && "nimble test"

    runDockerTest(thisDir(), testDir, cmd) do:
      writeTestConfig("""
        --verbosity:0
        --hints:off
        --warnings:off
      """)

    rmDir testDir


  task dockertest, "Test in new docker container":
    ## Run unit tests in new docker conatiner; download all
    ## dependencies using nimble.
    runDockerTest(thisDir(), testDir, "nimble test") do:
      discard

  task installtest, "Test installation from cloned repo":
    runDockerTest(thisDir(), testDir, "nimble install")

  task testall, "Run full test suite in all variations":
    runDockerTest(thisDir(), testDir, "nimble testallTask")

  task testallTask, "~~~ testall implementation ~~~":
    try:
      exec("choosenim stable")
      exec("nimble test")
      info "Stable test passed"
    except:
      err "Stable test failed"

    try:
      exec("choosenim devel")
      exec("nimble test")
      info "Devel test passed"
    except:
      exec("choosenim devel")
      err "Devel test failed"

    try:
      exec("nimble install")
      info "Installation OK"
    except:
      err "Installation failed"
