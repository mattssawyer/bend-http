# The properties the laws promise about parse and render, as functions.

import Base
import ./bytes.bend as Byte
import ./dots.bend as Dots
import ./check.bend as Check


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
        Bool.not(Dots.is_dot_seg(s)) && no_dot_segs(t)

# No segment contains "/", "\" or a control byte
def all_safe(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
        True{}
    case Con{s, t}:
        Check.safe_seg(s) && all_safe(t)

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

# Does the path start with "//"?
def starts_with_double_slash.two(+x: U32, t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
        False{}
    case Con{+y, r}:
        U32.is_eq(x, 47) && U32.is_eq(y, 47)

def starts_with_double_slash(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+x, t}:
        starts_with_double_slash.two(x, t)

def canonical.next(pchar: Bool, pct: Bool) -> Nat:
  match pchar:
    case True{}:
        0n
    case False{}:
        match pct:
          case True{}:
              2n
          case False{}:
              0n

def canonical.plain(pchar: Bool, slash: Bool, pct: Bool, r: Bool) -> Bool:
  match pchar:
    case True{}:
        r
    case False{}:
        match slash:
          case True{}:
              r
          case False{}:
              match pct:
                case True{}:
                    r
                case False{}:
                    False{}

# k is how many hex digits must come next (2 right after "%")
def canonical.go(b: List<&2, U32>, k: Nat) -> Bool:
  match b:
    case Nil{}:
        match k:
          case 0n:
              True{}
          case 1n+n:
              False{}
    case Con{+c, t}:
        match k:
          case 0n:
              canonical.plain(Byte.is_pchar(c), U32.is_eq(c, 47), U32.is_eq(c, 37),
                canonical.go(t, canonical.next(Byte.is_pchar(c), U32.is_eq(c, 37))))
          case 1n+n:
              Byte.is_upper_hex(c) && canonical.go(t, n)

# Every byte is "/", a pchar, or part of a %XX with uppercase hex digits
def canonical(b: List<&2, U32>) -> Bool:
  canonical.go(b, 0n)
