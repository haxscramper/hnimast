# Package

version       = "0.3.38"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.4.8"
requires "hmisc >= 0.12.0"
requires "compiler >= 1.4.8"


import std/[os, strutils, strformat]

task testall, "Run all tests":
  exec "nim r tests/noauto_testall.nim"
  exec "nim r -d:haxTestall tests/cpp/tQWindow.nim"

task docgen, "Generate documentation":
  var args = @[
    "nim", "doc2", "--project", "--warnings:off", "--errormax:1", "--outdir:htmldocs"]

  let
    cwd = getCurrentDir()
    res = &"{cwd}/docs"

  args.add "--git.url:\"" & getEnv("GITHUB_REPOSITORY", &"file://{res}") & "\""
  args.add "src/hnimast/docgen_target.nim"

  let cmd = join(args, " ")
  echo cmd
  exec cmd
