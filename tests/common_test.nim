import
  hmisc/other/oswrap

converter toSeqString*(paths: seq[AbsDir]): seq[string] =
  for path in paths:
    result.add path.getStr()
