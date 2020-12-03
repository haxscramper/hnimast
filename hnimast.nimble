# Package

version       = "0.3.4"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.2.6"
requires "hmisc >= 0.8.5"
requires "macroutils"
requires "compiler"

task docgen, "Generate documentation":
  exec("hmisc-putils docgen")
