# Removing "." and ".." segments (RFC 3986 section 5.2.4).

import Base
import ./errors.bend as Error


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
type DotState is Data:
  DotState{up: Nat, kept: List<&2, List<&2, U32>>}

# An ordinary segment: kept, unless a ".." to its right removes it
def rd.keep(s: List<&2, U32>, d: DotState) -> DotState:
  match d:
    case DotState{up, kept}:
        match up:
          case 0n:
              DotState{0n, Con{s, kept}}
          case 1n+n:
              DotState{n, kept}

# A "..": one more segment to remove
def rd.up(d: DotState) -> DotState:
  match d:
    case DotState{up, kept}:
        DotState{1n+up, kept}

# Handle segment s, given d = the result for the segments to its right.
# last is True for the final segment: a final "." or ".." leaves an empty
# final segment, so "/a/b/.." becomes "/a/".
def rd.step(kind: SegKind, s: List<&2, U32>, last: Bool, d: DotState) -> DotState:
  match kind:
    case Other{}:
        match last:
          case True{}:
              DotState{0n, [s]}
          case False{}:
              rd.keep(s, d)
    case Dot{}:
        match last:
          case True{}:
              DotState{0n, [[]]}
          case False{}:
              d
    case DotDot{}:
        match last:
          case True{}:
              DotState{1n, [[]]}
          case False{}:
              rd.up(d)

def rd(segs: List<&2, List<&2, U32>>) -> DotState:
  match segs:
    case Nil{}:
        DotState{0n, Nil{}}
    case Con{+s, +rest}:
        rd.step(seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rd(rest))

# A ".." still waiting at the far left would climb above the root
def rd.end(d: DotState) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match d:
    case DotState{up, kept}:
        match up:
          case 0n:
              Done{kept}
          case 1n+n:
              Fail{Error.AboveRoot{}}

# Remove "." and ".." segments (RFC 3986 section 5.2.4).
# "." is dropped, ".." drops the segment before it. A ".." with nothing
# before it would climb above the root, so it's rejected with AboveRoot.
def remove_dots(segs: List<&2, List<&2, U32>>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  rd.end(rd(segs))

# Is the segment "." or ".."?
def is_dot_seg(s: List<&2, U32>) -> Bool:
  Bool.not(is_other(seg_kind(s)))
