# Package

version       = "0.3.24"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.4.0"
requires "hmisc >= 0.10.1"
requires "macroutils"
requires "compiler >= 1.4.0"
requires "nimble <= 0.13.0"

task docgen, "Generate documentation":
  exec("hmisc-putils docgen")
