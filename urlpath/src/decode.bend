# Percent-decoding of one segment: "%41" -> "A", decoded exactly once.

import Base
import ./errors.bend as Error
import ./bytes.bend as Byte


# Where the decoder is: normal text, just after "%", or after "%X" (hi = X's value)
type DecState is Data:
  Plain{}
  Hex1{}
  Hex2{hi: U32}

# Put a byte in front of a decoded result, unless it already failed
def ok_cons(b: U32, r: Result<&2, &2, Error.PathError, List<&2, U32>>) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{v}:
        Done{Con{b, v}}

def decode.next.plain(pchar: Bool, pct: Bool) -> DecState:
  match pchar:
    case True{}:
        Plain{}
    case False{}:
        match pct:
          case True{}:
              Hex1{}
          case False{}:
              Plain{}

# The state after reading byte b
def decode.next(+b: U32, st: DecState) -> DecState:
  match st:
    case Plain{}:
        decode.next.plain(Byte.is_pchar(b), U32.is_eq(b, 37))
    case Hex1{}:
        Hex2{Byte.hex_val(b)}
    case Hex2{hi}:
        Plain{}

# Normal text: keep a pchar byte, drop a "%" (the escape follows), reject anything else
def decode.step.plain(b: U32, r: Result<&2, &2, Error.PathError, List<&2, U32>>, pchar: Bool, pct: Bool) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match pchar:
    case True{}:
        ok_cons(b, r)
    case False{}:
        match pct:
          case True{}:
              r
          case False{}:
              Fail{Error.InvalidByte{}}

# First digit after "%": must be hex
def decode.step.hex1(r: Result<&2, &2, Error.PathError, List<&2, U32>>, hex: Bool) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match hex:
    case True{}:
        r
    case False{}:
        Fail{Error.BadPercent{}}

# Second digit after "%": must be hex, then output the decoded byte
def decode.step.hex2(v: U32, r: Result<&2, &2, Error.PathError, List<&2, U32>>, hex: Bool) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match hex:
    case True{}:
        ok_cons(v, r)
    case False{}:
        Fail{Error.BadPercent{}}

# Handle byte b in state st, given r = the decoded rest of the segment
def decode.step(+b: U32, st: DecState, r: Result<&2, &2, Error.PathError, List<&2, U32>>) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match st:
    case Plain{}:
        decode.step.plain(b, r, Byte.is_pchar(b), U32.is_eq(b, 37))
    case Hex1{}:
        decode.step.hex1(r, Byte.is_hex(b))
    case Hex2{+hi}:
        decode.step.hex2(Byte.hex_pair(hi, Byte.hex_val(b)), r, Byte.is_hex(b))

# End of segment: fine in normal text, BadPercent in the middle of an escape
def decode.end(st: DecState) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match st:
    case Plain{}:
        Done{Nil{}}
    case Hex1{}:
        Fail{Error.BadPercent{}}
    case Hex2{hi}:
        Fail{Error.BadPercent{}}

def decode.go(seg: List<&2, U32>, +st: DecState) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match seg:
    case Nil{}:
        decode.end(st)
    case Con{+b, t}:
        decode.step(b, st, decode.go(t, decode.next(b, st)))

# Decode one raw segment exactly once: "%41" -> "A", "%2541" -> "%41"
# Rejects a byte that isn't allowed (InvalidByte) or a broken escape (BadPercent)
def decode(seg: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  decode.go(seg, Plain{})
