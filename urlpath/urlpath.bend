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


# ---- Dot-segment removal (step 4) ----

# What a decoded segment is: ".", "..", or anything else
type SegKind is Data:
  Other{}
  Dot{}
  DotDot{}

# Second byte was ".": it's ".." only if nothing follows
def seg_kind.two(dot: Bool, t: List<&2, U32>) -> SegKind:
  match dot:
    case True{}:
        match t:
          case Nil{}:
              DotDot{}
          case Con{c, r}:
              Other{}
    case False{}:
        Other{}

# First byte was ".": it's "." if nothing follows, maybe ".." if another "." follows
def seg_kind.one(dot: Bool, t: List<&2, U32>) -> SegKind:
  match dot:
    case True{}:
        match t:
          case Nil{}:
              Dot{}
          case Con{+c, r}:
              seg_kind.two(U32.is_eq(c, 46), r)
    case False{}:
        Other{}

def seg_kind(s: List<&2, U32>) -> SegKind:
  match s:
    case Nil{}:
        Other{}
    case Con{+c, t}:
        seg_kind.one(U32.is_eq(c, 46), t)

# Is this kind an ordinary segment?
def is_other(k: SegKind) -> Bool:
  match k:
    case Other{}:
        True{}
    case Dot{}:
        False{}
    case DotDot{}:
        False{}

# Dot removal works right to left. up counts the ".." segments still waiting
# to remove an ordinary segment to their left; kept is the result so far.
type Dots is Data:
  Dots{up: Nat, kept: List<&2, List<&2, U32>>}

# An ordinary segment: kept, unless a ".." to its right removes it
def rd.keep(s: List<&2, U32>, d: Dots) -> Dots:
  match d:
    case Dots{up, kept}:
        match up:
          case 0n:
              Dots{0n, Con{s, kept}}
          case 1n+n:
              Dots{n, kept}

# A "..": one more segment to remove
def rd.up(d: Dots) -> Dots:
  match d:
    case Dots{up, kept}:
        Dots{1n+up, kept}

# Handle segment s, given d = the result for the segments to its right.
# last is True for the final segment: a final "." or ".." leaves an empty
# final segment, so "/a/b/.." becomes "/a/".
def rd.step(kind: SegKind, s: List<&2, U32>, last: Bool, d: Dots) -> Dots:
  match kind:
    case Other{}:
        match last:
          case True{}:
              Dots{0n, [s]}
          case False{}:
              rd.keep(s, d)
    case Dot{}:
        match last:
          case True{}:
              Dots{0n, [[]]}
          case False{}:
              d
    case DotDot{}:
        match last:
          case True{}:
              Dots{1n, [[]]}
          case False{}:
              rd.up(d)

def rd(segs: List<&2, List<&2, U32>>) -> Dots:
  match segs:
    case Nil{}:
        Dots{0n, Nil{}}
    case Con{+s, +rest}:
        rd.step(seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rd(rest))

# A ".." still waiting at the far left would climb above the root
def rd.end(d: Dots) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match d:
    case Dots{up, kept}:
        match up:
          case 0n:
              Done{kept}
          case 1n+n:
              Fail{AboveRoot{}}

# Remove "." and ".." segments (RFC 3986 section 5.2.4).
# "." is dropped, ".." drops the segment before it. A ".." with nothing
# before it would climb above the root, so it's rejected with AboveRoot.
def remove_dots(segs: List<&2, List<&2, U32>>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  rd.end(rd(segs))


# ---- parse (step 5) ----

# Every element is a byte (0-255)
def all_bytes(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        (h <= 255 : U32) && all_bytes(t)

# Does the list contain byte x?
def has_byte(b: List<&2, U32>, +x: U32) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+h, t}:
        U32.is_eq(h, x) || has_byte(t, x)

# A byte that must never appear in a decoded segment: "/", "\", controls
def unsafe_byte(+c: U32) -> Bool:
  U32.is_eq(c, 47) || U32.is_eq(c, 92) || (c < 32 : U32) || U32.is_eq(c, 127)

# No unsafe byte in this segment
def safe_seg(s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
        True{}
    case Con{+h, t}:
        Bool.not(unsafe_byte(h)) && safe_seg(t)

# Is the segment "." or ".."?
def is_dot_seg(s: List<&2, U32>) -> Bool:
  Bool.not(is_other(seg_kind(s)))

# Third byte after "..": is it ";"?
def dot_semi.two(semi: Bool, dot: Bool, t: List<&2, U32>) -> Bool:
  match semi:
    case True{}:
        True{}
    case False{}:
        match dot:
          case True{}:
              match t:
                case Nil{}:
                    False{}
                case Con{+c, r}:
                    U32.is_eq(c, 59)
          case False{}:
              False{}

def dot_semi.one(dot: Bool, t: List<&2, U32>) -> Bool:
  match dot:
    case True{}:
        match t:
          case Nil{}:
              False{}
          case Con{+c, r}:
              dot_semi.two(U32.is_eq(c, 59), U32.is_eq(c, 46), r)
    case False{}:
        False{}

# Does the segment start with ".;" or "..;"?
def dot_semi(s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
        False{}
    case Con{+c, t}:
        dot_semi.one(U32.is_eq(c, 46), t)

# The checks that don't depend on position: no unsafe byte, not an
# encoded "." or "..", no ".;" or "..;" start
def seg_ok.dots(+raw: List<&2, U32>, +d: List<&2, U32>) -> Bool:
  Bool.not(is_dot_seg(d) && has_byte(raw, 37)) && Bool.not(dot_semi(d))

def seg_ok.shape(+raw: List<&2, U32>, +d: List<&2, U32>) -> Bool:
  safe_seg(d) && seg_ok.dots(raw, d)

# Only the final segment may be empty
def seg_ok.place(d: List<&2, U32>, last: Bool) -> Bool:
  last || Bool.not(List.is_empty(&2, U32, d))

# Is a decoded segment acceptable? raw is its undecoded form, last is True
# for the final segment.
def seg_ok(+raw: List<&2, U32>, +d: List<&2, U32>, last: Bool) -> Bool:
  seg_ok.shape(raw, d) && seg_ok.place(d, last)

def seg_error.empty(enc_dot: Bool, semi: Bool) -> PathError:
  match enc_dot:
    case True{}:
        EncodedDotSegment{}
    case False{}:
        match semi:
          case True{}:
              DotSemicolonSegment{}
          case False{}:
              EmptySegment{}

def seg_error.control(control: Bool, enc_dot: Bool, semi: Bool) -> PathError:
  match control:
    case True{}:
        ControlByte{}
    case False{}:
        seg_error.empty(enc_dot, semi)

def seg_error.back(back: Bool, control: Bool, enc_dot: Bool, semi: Bool) -> PathError:
  match back:
    case True{}:
        EncodedBackslash{}
    case False{}:
        seg_error.control(control, enc_dot, semi)

def seg_error.slash(slash: Bool, back: Bool, control: Bool, enc_dot: Bool, semi: Bool) -> PathError:
  match slash:
    case True{}:
        EncodedSlash{}
    case False{}:
        seg_error.back(back, control, enc_dot, semi)

# Why seg_ok said no, checked in the spec's order
def seg_error(+raw: List<&2, U32>, +d: List<&2, U32>) -> PathError:
  seg_error.slash(has_byte(d, 47), has_byte(d, 92), Bool.not(safe_seg(d)),
    is_dot_seg(d) && has_byte(raw, 37), dot_semi(d))

def check_decoded.if(ok: Bool, +raw: List<&2, U32>, +d: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, U32>>:
  match ok:
    case True{}:
        Done{d}
    case False{}:
        Fail{seg_error(raw, d)}

def check_seg.d(r: Result<&2, &2, PathError, List<&2, U32>>, +raw: List<&2, U32>, last: Bool) -> Result<&2, &2, PathError, List<&2, U32>>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{+d}:
        check_decoded.if(seg_ok(raw, d, last), raw, d)

# Decode one raw segment and check it
def check_seg(+raw: List<&2, U32>, last: Bool) -> Result<&2, &2, PathError, List<&2, U32>>:
  check_seg.d(decode(raw), raw, last)

def check_all.cons(a: Result<&2, &2, PathError, List<&2, U32>>, b: Result<&2, &2, PathError, List<&2, List<&2, U32>>>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match a:
    case Fail{e}:
        Fail{e}
    case Done{s}:
        match b:
          case Fail{e}:
              Fail{e}
          case Done{ss}:
              Done{Con{s, ss}}

# Decode and check every raw segment, left to right; the first error wins
def check_all(raws: List<&2, List<&2, U32>>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match raws:
    case Nil{}:
        Done{Nil{}}
    case Con{+r, +rest}:
        check_all.cons(check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), check_all(rest))

def parse.dots(r: Result<&2, &2, PathError, List<&2, List<&2, U32>>>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{ds}:
        remove_dots(ds)

def parse.slash(slash: Bool, t: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match slash:
    case True{}:
        parse.dots(check_all(split(t)))
    case False{}:
        Fail{NotAbsolute{}}

def parse.first(raw: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match raw:
    case Nil{}:
        Fail{NotAbsolute{}}
    case Con{+c, t}:
        parse.slash(U32.is_eq(c, 47), t)

def parse.bytes(ok: Bool, raw: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  match ok:
    case True{}:
        parse.first(raw)
    case False{}:
        Fail{NotAByte{}}

# Turn the raw path of a request ("/a/b%20c") into its decoded segments,
# or say why it's rejected. See the spec, section 3.3.
def parse(+raw: List<&2, U32>) -> Result<&2, &2, PathError, List<&2, List<&2, U32>>>:
  parse.bytes(all_bytes(raw), raw)


# ---- What the laws promise about parse ----

# Starts with "/"
def starts_with_slash(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+c, t}:
        U32.is_eq(c, 47)

# No segment is "." or ".."
def no_dot_segs(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
        True{}
    case Con{+s, t}:
        Bool.not(is_dot_seg(s)) && no_dot_segs(t)

# No segment contains "/", "\" or a control byte
def all_safe(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
        True{}
    case Con{s, t}:
        safe_seg(s) && all_safe(t)

def eol.step(last: Bool, s: List<&2, U32>, r: Bool) -> Bool:
  match last:
    case True{}:
        True{}
    case False{}:
        Bool.not(List.is_empty(&2, U32, s)) && r

# Every segment except the last is non-empty
def only_last_empty(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
        True{}
    case Con{s, +rest}:
        eol.step(List.is_empty(&2, List<&2, U32>, rest), s, only_last_empty(rest))

# At least one segment, and only the last may be empty
def empty_only_last(+p: List<&2, List<&2, U32>>) -> Bool:
  Bool.not(List.is_empty(&2, List<&2, U32>, p)) && only_last_empty(p)
