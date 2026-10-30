# A byte-based implementation of the URL path parser.
# Author: Matthew Sawyer
# Last Updated: 2026-10-29
# Version: 1.0.0

import Base

# Convert the string to a list of bytes
def bytes(s: String) -> List<&2, U32>: 
  match s: 
    case SNil{}:
        Nil{}
    case SCon{c, t}: 
        Con{Char.to_u32(c), bytes(t)}

# Check if the byte is a digit
def is_digit(+b: U32) -> Bool: 
  (b >= 48 : U32) && (b <= 57 : U32)

# Check if the byte is a letter
def is_alpha(+b: U32) -> Bool: 
  (b >= 65 : U32) && (b <= 90 : U32) || (b >= 97 : U32) && (b <= 122 : U32)

# Check if the byte is a hexadecimal digit
def is_hex(+b: U32) -> Bool: 
  is_digit(b) || (b >= 65 : U32) && (b <= 70 : U32) 
  || (b >= 97 : U32) && (b <= 102 : U32)

# Check if the byte is a unreserved character (letters, digits, -, ., _, ~)
def is_unreserved(+b: U32) -> Bool: 
  is_alpha(b) || is_digit(b)
  || U32.is_eq(b, 45) || U32.is_eq(b, 46)
  || U32.is_eq(b, 95) || U32.is_eq(b, 126)

# Check if the byte is a sub-delim character (! $ & ' ( ) * + , ; =)
def is_sub_delim(+b: U32) -> Bool: 
  U32.is_eq(b, 33) || U32.is_eq(b, 36) || U32.is_eq(b, 38) || U32.is_eq(b, 39)
  || U32.is_eq(b, 40) || U32.is_eq(b, 41) || U32.is_eq(b, 42) || U32.is_eq(b, 43)
  || U32.is_eq(b, 44) || U32.is_eq(b, 59) || U32.is_eq(b, 61)

# Check if the byte is a pchar character (unreserved, sub-delimiter, :, @)
def is_pchar(+b: U32) -> Bool: 
  is_unreserved(b) || is_sub_delim(b) || U32.is_eq(b, 58) || U32.is_eq(b, 64)

# Add head to the linked list 
def add_head(head: U32, segs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>: 
  match segs: 
    case Nil{}:
        [[head]]
    case Con{first, rest}:
        Con{Con{head, first}, rest}

# Helper for split: start a new segment on "/", otherwise grow the first one
def split.if(+h: U32, rest: List<&2, List<&2, U32>>, slash: Bool) -> List<&2, List<&2, U32>>:
  match slash:
    case True{}:
        Con{Nil{}, rest}
    case False{}:
        add_head(h, rest)

# Split bytes on "/" (47). Always returns at least one segment.
# "/a/b" gives [[], [97], [98]]
def split(b: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match b:
    case Nil{}:
        [Nil{}]
    case Con{+h, t}:
        split.if(h, split(t), U32.is_eq(h, 47))

# Glue segments back together with "/" between them (undoes split)
def join(segs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match segs:
    case Nil{}:
        Nil{}
    case Con{s, Nil{}}:
        s
    case Con{s, r}:
        List.append(&2, U32, s, Con{47, join(r)})


# ---- Percent-decoding (step 3) ----

# Every reason parse can reject a path (see the spec, section 3.3)
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

# Where the decoder is: normal text, just after "%", or after "%X" (hi = X's value)
type DecState is Data:
  Plain{}
  Hex1{}
  Hex2{hi: U32}

def hex_val.if(+b: U32, digit: Bool, upper: Bool) -> U32:
  match digit:
    case True{}:
        U32.sub(b, 48)
    case False{}:
        match upper:
          case True{}:
              U32.sub(b, 55)
          case False{}:
              U32.sub(b, 87)

# The value of one hex digit: "0"-"9" -> 0-9, "A"-"F" and "a"-"f" -> 10-15
def hex_val(+b: U32) -> U32:
  hex_val.if(b, is_digit(b), (b >= 65 : U32) && (b <= 70 : U32))

# Put a byte in front of a decoded result, unless it already failed
def ok_cons(b: U32, r: Result<&2, &2, PathError, List<&2, U32>>) -> Result<&2, &2, PathError, List<&2, U32>>:
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
        decode.next.plain(is_pchar(b), U32.is_eq(b, 37))
    case Hex1{}:
        Hex2{hex_val(b)}
    case Hex2{hi}:
        Plain{}

# Normal text: keep a pchar byte, drop a "%" (the escape follows), reject anything else
def decode.step.plain(b: U32, r: Result<&2, &2, PathError, List<&2, U32>>, pchar: Bool, pct: Bool) -> Result<&2, &2, PathError, List<&2, U32>>:
  match pchar:
    case True{}:
        ok_cons(b, r)
    case False{}:
        match pct:
          case True{}:
              r
          case False{}:
              Fail{InvalidByte{}}

# First digit after "%": must be hex
def decode.step.hex1(r: Result<&2, &2, PathError, List<&2, U32>>, hex: Bool) -> Result<&2, &2, PathError, List<&2, U32>>:
  match hex:
    case True{}:
        r
    case False{}:
        Fail{BadPercent{}}

# Second digit after "%": must be hex, then output the decoded byte
def decode.step.hex2(v: U32, r: Result<&2, &2, PathError, List<&2, U32>>, hex: Bool) -> Result<&2, &2, PathError, List<&2, U32>>:
  match hex:
    case True{}:
        ok_cons(v, r)
    case False{}:
        Fail{BadPercent{}}

# Handle byte b in state st, given r = the decoded rest of the segment
def decode.step(+b: U32, st: DecState, r: Result<&2, &2, PathError, List<&2, U32>>) -> Result<&2, &2, PathError, List<&2, U32>>:
  match st:
    case Plain{}:
        decode.step.plain(b, r, is_pchar(b), U32.is_eq(b, 37))
    case Hex1{}:
        decode.step.hex1(r, is_hex(b))
    case Hex2{+hi}:
        decode.step.hex2(U32.add(U32.mul(hi, 16), hex_val(b)), r, is_hex(b))

# End of segment: fine in normal text, BadPercent in the middle of an escape
def decode.end(st: DecState) -> Result<&2, &2, PathError, List<&2, U32>>:
  match st:
    case Plain{}:
        Done{Nil{}}
    case Hex1{}:
        Fail{BadPercent{}}
    case Hex2{hi}:
        Fail{BadPercent{}}

def decode.go(seg: List<&2, U32>, +st: DecState) -> Result<&2, &2, PathError, List<&2, U32>>:
  match seg:
    case Nil{}:
        decode.end(st)
    case Con{+b, t}:
        decode.step(b, st, decode.go(t, decode.next(b, st)))

# Decode one raw segment exactly once: "%41" -> "A", "%2541" -> "%41"
# Rejects a byte that isn't allowed (InvalidByte) or a broken escape (BadPercent)
def decode(seg: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, U32>>:
  decode.go(seg, Plain{})

# True when every byte is a pchar (so there's nothing to decode)
def all_pchar(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        is_pchar(h) && all_pchar(t)
