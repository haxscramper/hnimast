import
  hmisc/other/[oswrap, hshell]

import
  hnimast,
  hnimast/codegen/xsd_to_nim,
  hmisc/core/all

import std/[strformat]

import
  hmisc/other/hjson

const dir = oswrap.currentSourceDir()
let gen = getAppTempFile("generated.nim")

startHax()

echov gen

let text = "\"\"\"" & """
<?xml version="1.0" encoding="UTF-8"?>

<shiporder orderid="889923"
xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
xsi:noNamespaceSchemaLocation="shiporder.xsd">
  <orderperson>John Smith</orderperson>
  <shipto>
    <name>Ola Nordmann</name>
    <address>Langgt 23</address>
    <city>4000 Stavanger</city>
    <country>Norway</country>
  </shipto>
  <item>
    <title>Empire Burlesque</title>
    <note>Special Edition</note>
    <quantity>1</quantity>
    <price>10.90</price>
  </item>
  <item>
    <title>Hide your heart</title>
    <quantity>1</quantity>
    <price>9.90</price>
  </item>
</shiporder>
""" & "\"\"\""

AbsFile(relToSource"assets/xunit.xsd").
  generateForXsd().
  writeXsdGenerator(gen, &"""

var ser = newXmlDeserializer({text})
var target: Shipordertype
ser.loadXml(target, "shiporder")

import hmisc/other/hpprint

pprint target

""")

var cmd = shellCmd(nim, r, errormax = 2)

for path in shellCmd(nim, dump, "dump.format" = "json", "-").
  evalShellStdout().
  parseJson()["lib_paths"]:

  cmd.opt "path", path.asStr()

cmd.arg $gen

execShell cmd, limitErr = 30
