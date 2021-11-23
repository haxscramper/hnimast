# Package

version       = "0.4.0"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.6.0"
requires "hmisc >= 0.12.0"


import std/[os, strutils, strformat]

task test, "Run tests":
  exec "nim r tests/runall.nim test " & currentSourcePath()

task docgen, "Generate documentation":
  exec "nim c -r tests/runall.nim doc " & currentSourcePath()

task push, "Execute checks and push ":
  exec "nim r tests/runall.nim push " & currentSourcePath()

task newversion, "Tag new version and push it to git":
   exec "nim r tests/runall.nim newversion " & currentSourcePath()
