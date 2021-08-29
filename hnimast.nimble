# Package

version       = "0.3.36"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.4.0"
requires "hmisc >= 0.11.19"
requires "compiler >= 1.4.0"


import std/[os, strutils, strformat]

task docgen, "Generate documentation":
  var args = @[
    "nim", "doc2", "--project", "--warnings:off", "--errormax:1", "--outdir:docs"]

  let
    cwd = getCurrentDir()
    res = &"{cwd}/docs"

  args.add "--git.url:\"" & getEnv("GITHUB_REPOSITORY", &"file://{res}") & "\""
  args.add "src/hnimast/docgen_target.nim"

  let cmd = join(args, " ")
  echo cmd
  exec cmd
