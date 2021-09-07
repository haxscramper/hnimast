import std/[parseutils, strutils]

type
  IcppPartKind* = enum
    ipkArgSplice
    ipkTextPart
    ipkNextArg
    ipkNextDotArg ## `#.`
    ipkNextCnewArg

    ipkResultType
    ipkArgType

  IcppPart* = object
    case kind*: IcppPartKind
      of ipkTextPart:
        text*: string

      of ipkResultType, ipkArgType:
        argIdx*: int
        baseGet*: int

      else:
        discard

  IcppPattern* = object
    parts*: seq[IcppPart]

proc parsePatternCall*(pat: string): IcppPattern =
  var i = 0
  var j = 1

  template pushText(str: string): untyped =
    if result.parts.len > 0 and
       result.parts[^1].kind == ipkTextPart:
      result.parts[^1].text.add str

    else:
      result.parts.add IcppPart(kind: ipkTextPart, text: str)

  while i < pat.len:
    case pat[i]:
      of '@':
        result.parts.add IcppPart(kind: ipkArgSplice)
        inc i

      of '#':
        if i + 1 < pat.len and pat[i + 1] in {'+', '@'}:
          assert pat[i + 1] != '+',
           "`+` is handled differently for importcpp, but " &
             "manual does not say what this combination means exactly " &
             "so it is not supported for now."

          result.parts.add IcppPart(kind: ipkNextCnewArg)

          inc i
        elif i + 1 < pat.len and pat[i + 1] == '.':
          result.parts.add IcppPart(kind: ipkNextDotArg)

          inc i

        # elif i + 1 < pat.len and pat[i + 1] == '[':
        #   discard

        else:
          result.parts.add IcppPart(kind: ipkNextArg)

        inc j
        inc i
      of '\'':
        let begin = i
        var
          stars: int
          argIdx: int
          isPattern = false

        inc i

        while pat[i] == '*':
          inc stars
          inc i

        if pat[i] in Digits:
          argIdx = pat[i].ord - '0'.ord
          inc i
          isPattern = true

        else:
          i = begin


        if isPattern:
          if argIdx == 0:
            result.parts.add IcppPart(
              kind: ipkResultType, argIdx: -1, baseGet: stars)

          else:
            result.parts.add IcppPart(
              kind: ipkResultType, argIdx: argIdx - 1, baseGet: stars)

        else:
          pushText("'")
          inc i

      else:
        let start = i
        while i < pat.len:
          if pat[i] notin {'@', '#', '\''}: inc(i)
          else:
            break

        if i - 1 >= start:
          pushText(pat[start .. i - 1])
