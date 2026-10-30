# Turning segments back into a path, percent-encoding what needs it.

import Base
import ./bytes.bend as Byte
import ./split.bend as Split


def enc_byte.if(pchar: Bool, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match pchar:
    case True{}:
        Con{c, rest}
    case False{}:
        Con{37, Con{Byte.hex_digit(Byte.hi_nibble(c)), Con{Byte.hex_digit(Byte.lo_nibble(c)), rest}}}

# Write byte c in front of rest: as itself if it's a pchar, else as %XX
def enc_byte(+c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  enc_byte.if(Byte.is_pchar(c), c, rest)

# Encode one segment
def enc_seg(s: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Nil{}:
        Nil{}
    case Con{+c, t}:
        enc_byte(c, enc_seg(t))

# Encode every segment
def enc_segs(p: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match p:
    case Nil{}:
        Nil{}
    case Con{s, r}:
        Con{enc_seg(s), enc_segs(r)}

# Turn segments back into a path: "/" + segments joined by "/", with every
# byte that isn't a pchar written as %XX (uppercase hex).
# [[97], [98, 32]] -> "/a/b%20"
def render(p: List<&2, List<&2, U32>>) -> List<&2, U32>:
  Con{47, Split.join(enc_segs(p))}
