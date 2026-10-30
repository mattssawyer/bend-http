# Checks on each decoded segment: no encoded "/", "\" or control byte, no encoded
# dot segment, no ".;" start, and no empty segment except the last.

import Base
import ./errors.bend as Error
import ./bytes.bend as Byte
import ./decode.bend as Decode
import ./dots.bend as Dots


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
  Bool.not(Dots.is_dot_seg(d) && Byte.has_byte(raw, 37)) && Bool.not(dot_semi(d))

def seg_ok.shape(+raw: List<&2, U32>, +d: List<&2, U32>) -> Bool:
  safe_seg(d) && seg_ok.dots(raw, d)

# Only the final segment may be empty
def seg_ok.place(d: List<&2, U32>, last: Bool) -> Bool:
  last || Bool.not(List.is_empty(&2, U32, d))

# Is a decoded segment acceptable? raw is its undecoded form, last is True
# for the final segment.
def seg_ok(+raw: List<&2, U32>, +d: List<&2, U32>, last: Bool) -> Bool:
  seg_ok.shape(raw, d) && seg_ok.place(d, last)

def seg_error.empty(enc_dot: Bool, semi: Bool) -> Error.PathError:
  match enc_dot:
    case True{}:
        Error.EncodedDotSegment{}
    case False{}:
        match semi:
          case True{}:
              Error.DotSemicolonSegment{}
          case False{}:
              Error.EmptySegment{}

def seg_error.control(control: Bool, enc_dot: Bool, semi: Bool) -> Error.PathError:
  match control:
    case True{}:
        Error.ControlByte{}
    case False{}:
        seg_error.empty(enc_dot, semi)

def seg_error.back(back: Bool, control: Bool, enc_dot: Bool, semi: Bool) -> Error.PathError:
  match back:
    case True{}:
        Error.EncodedBackslash{}
    case False{}:
        seg_error.control(control, enc_dot, semi)

def seg_error.slash(slash: Bool, back: Bool, control: Bool, enc_dot: Bool, semi: Bool) -> Error.PathError:
  match slash:
    case True{}:
        Error.EncodedSlash{}
    case False{}:
        seg_error.back(back, control, enc_dot, semi)

# Why seg_ok said no. If several checks fail, the first one here wins.
def seg_error(+raw: List<&2, U32>, +d: List<&2, U32>) -> Error.PathError:
  seg_error.slash(Byte.has_byte(d, 47), Byte.has_byte(d, 92), Bool.not(safe_seg(d)),
    Dots.is_dot_seg(d) && Byte.has_byte(raw, 37), dot_semi(d))

def check_decoded.if(ok: Bool, +raw: List<&2, U32>, +d: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match ok:
    case True{}:
        Done{d}
    case False{}:
        Fail{seg_error(raw, d)}

def check_seg.d(r: Result<&2, &2, Error.PathError, List<&2, U32>>, +raw: List<&2, U32>, last: Bool) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{+d}:
        check_decoded.if(seg_ok(raw, d, last), raw, d)

# Decode one raw segment and check it
def check_seg(+raw: List<&2, U32>, last: Bool) -> Result<&2, &2, Error.PathError, List<&2, U32>>:
  check_seg.d(Decode.decode(raw), raw, last)

def check_all.cons(a: Result<&2, &2, Error.PathError, List<&2, U32>>, b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
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
def check_all(raws: List<&2, List<&2, U32>>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match raws:
    case Nil{}:
        Done{Nil{}}
    case Con{+r, +rest}:
        check_all.cons(check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), check_all(rest))
