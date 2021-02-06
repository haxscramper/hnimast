# Package

version       = "0.3.16"
author        = "haxscramper"
description   = "User-friendly wrapper for nim ast"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 1.4.0"
requires "hmisc >= 0.9.16"
requires "macroutils"
requires "compiler"

task docgen, "Generate documentation":
  exec("hmisc-putils docgen")
