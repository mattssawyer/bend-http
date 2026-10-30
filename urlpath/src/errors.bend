# Every reason parse can reject a path.

import Base


type PathError is Data:
  NotAByte{}
  NotAbsolute{}
  InvalidByte{}
  BadPercent{}
  EncodedSlash{}
  EncodedBackslash{}
  ControlByte{}
  EncodedDotSegment{}
  DotSemicolonSegment{}
  EmptySegment{}
  AboveRoot{}
