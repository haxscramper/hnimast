# Package

version       = "0.3.17"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.4.0"
requires "hmisc >= 0.10.1"
requires "macroutils"
requires "compiler"

task docgen, "Generate documentation":
  exec("hmisc-putils docgen")
