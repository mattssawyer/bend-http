# Byte helpers for HTTP: tokens, ASCII lowercase, comparing and cutting.

import Base
import ../../urlpath/src/bytes.bend as UrlByte


# A token character (RFC 9110 tchar): letters, digits and !#$%&'*+-.^_`|~
def is_tchar(+b: U32) -> Bool:
  UrlByte.is_alpha(b) || UrlByte.is_digit(b)
  || U32.is_eq(b, 33) || U32.is_eq(b, 35) || U32.is_eq(b, 36) || U32.is_eq(b, 37)
  || U32.is_eq(b, 38) || U32.is_eq(b, 39) || U32.is_eq(b, 42) || U32.is_eq(b, 43)
  || U32.is_eq(b, 45) || U32.is_eq(b, 46) || U32.is_eq(b, 94) || U32.is_eq(b, 95)
  || U32.is_eq(b, 96) || U32.is_eq(b, 124) || U32.is_eq(b, 126)

def all_tchar(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        is_tchar(h) && all_tchar(t)

# A token: one or more token characters
def is_token(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+h, t}:
        is_tchar(h) && all_tchar(t)

def lower.if(+b: U32, upper: Bool) -> U32:
  match upper:
    case True{}:
        U32.add(b, 32)
    case False{}:
        b

# ASCII lowercase of one byte: "A" -> "a"; other bytes are unchanged
def lower(+b: U32) -> U32:
  lower.if(b, (b >= 65 : U32) && (b <= 90 : U32))

# Are two byte lists the same?
def eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a:
    case Nil{}:
        List.is_empty(&2, U32, b)
    case Con{+x, at}:
        match b:
          case Nil{}:
              False{}
          case Con{+y, bt}:
              U32.is_eq(x, y) && eq(at, bt)

def drop_prefix_ci.if(same: Bool, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match same:
    case True{}:
        r
    case False{}:
        None{}

# If b starts with p, ignoring ASCII case, the rest of b. p must be lowercase.
def drop_prefix_ci(p: List<&2, U32>, b: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match p:
    case Nil{}:
        Some{b}
    case Con{+c, pt}:
        match b:
          case Nil{}:
              None{}
          case Con{+h, bt}:
              drop_prefix_ci.if(U32.is_eq(lower(h), c), drop_prefix_ci(pt, bt))

# If b starts with exactly p, the rest of b
def drop_prefix(p: List<&2, U32>, b: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match p:
    case Nil{}:
        Some{b}
    case Con{+c, pt}:
        match b:
          case Nil{}:
              None{}
          case Con{+h, bt}:
              drop_prefix_ci.if(U32.is_eq(h, c), drop_prefix(pt, bt))

# The bytes before and after a cut point
type Cut is Data:
  NoCut{}
  Cut{before: List<&2, U32>, after: List<&2, U32>}

def cut.cons(+h: U32, r: Cut) -> Cut:
  match r:
    case NoCut{}:
        NoCut{}
    case Cut{bf, af}:
        Cut{Con{h, bf}, af}

def cut.if(found: Bool, +h: U32, t: List<&2, U32>, r: Cut) -> Cut:
  match found:
    case True{}:
        Cut{Nil{}, t}
    case False{}:
        cut.cons(h, r)

# Cut b at the first byte x: "a b c" at " " -> "a", "b c"
def cut(b: List<&2, U32>, +x: U32) -> Cut:
  match b:
    case Nil{}:
        NoCut{}
    case Con{+h, +t}:
        cut.if(U32.is_eq(h, x), h, t, cut(t, x))

def cut_last.if(r: Cut, found: Bool, +h: U32, t: List<&2, U32>) -> Cut:
  match r:
    case Cut{bf, af}:
        Cut{Con{h, bf}, af}
    case NoCut{}:
        match found:
          case True{}:
              Cut{Nil{}, t}
          case False{}:
              NoCut{}

# Cut b at the last byte x: "a b c" at " " -> "a b", "c"
def cut_last(b: List<&2, U32>, +x: U32) -> Cut:
  match b:
    case Nil{}:
        NoCut{}
    case Con{+h, +t}:
        cut_last.if(cut_last(t, x), U32.is_eq(h, x), h, t)

def ends_with.if(last: Bool, here: Bool, r: Bool) -> Bool:
  match last:
    case True{}:
        here
    case False{}:
        r

# Is the last byte of b equal to x?
def ends_with(b: List<&2, U32>, +x: U32) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+h, +t}:
        ends_with.if(List.is_empty(&2, U32, t), U32.is_eq(h, x), ends_with(t, x))

# Is the first byte of b equal to x?
def starts_with(b: List<&2, U32>, +x: U32) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+h, t}:
        U32.is_eq(h, x)
