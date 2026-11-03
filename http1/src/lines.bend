# Finding the next line. Every line must end with exactly CRLF.

import Base


# The result of looking for one line
type LineScan is Data:
  Partial{}                                          # no CRLF yet: need more input
  TooLong{}                                          # more bytes than allowed before the CRLF
  NotByte{}                                          # an element above 255
  LoneLF{}                                           # LF without CR before it
  LoneCR{}                                           # CR not followed by LF
  Line{line: List<&2, U32>, rest: List<&2, U32>}    # the line without its CRLF, and what follows

def line.cons(+h: U32, r: LineScan) -> LineScan:
  match r:
    case Line{l, rest}:
        Line{Con{h, l}, rest}
    case other:
        other

def line.crlf(lf: Bool, t: List<&2, U32>) -> LineScan:
  match lf:
    case True{}:
        Line{Nil{}, t}
    case False{}:
        LoneCR{}

# After a CR, the next byte must be LF
def line.cr(t: List<&2, U32>) -> LineScan:
  match t:
    case Nil{}:
        Partial{}
    case Con{+h, r}:
        line.crlf(U32.is_eq(h, 10), r)

def line.byte(big: Bool, cr: Bool, lf: Bool, +h: U32, t: List<&2, U32>, none_left: Bool, k: Unit -> LineScan) -> LineScan:
  match big:
    case True{}:
        NotByte{}
    case False{}:
        match cr:
          case True{}:
              line.cr(t)
          case False{}:
              match lf:
                case True{}:
                    LoneLF{}
                case False{}:
                    match none_left:
                      case True{}:
                          TooLong{}
                      case False{}:
                          line.cons(h, k(Unit{}))

# The next line of b, allowing at most budget bytes before its CRLF.
# Problems are reported as soon as the bytes so far show them.
def next_line(b: List<&2, U32>, +budget: U32) -> LineScan:
  match b:
    case Nil{}:
        Partial{}
    case Con{+h, +t}:
        line.byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), h, t, U32.is_zero(budget),
          u => next_line(t, U32.sub(budget, 1)))


# ---- What law H7 promises ----

def clean.next(cr_before: Bool, cr: Bool) -> Bool:
  match cr_before:
    case True{}:
        False{}
    case False{}:
        cr

def clean.step(cr_before: Bool, cr: Bool, lf: Bool, r: Bool) -> Bool:
  match cr_before:
    case True{}:
        lf && r
    case False{}:
        match cr:
          case True{}:
              r
          case False{}:
              match lf:
                case True{}:
                    False{}
                case False{}:
                    r

# cr_before says the byte before was a CR, so this one must be LF
def clean.go(b: List<&2, U32>, +cr_before: Bool) -> Bool:
  match b:
    case Nil{}:
        Bool.not(cr_before)
    case Con{+c, t}:
        clean.step(cr_before, U32.is_eq(c, 13), U32.is_eq(c, 10), clean.go(t, clean.next(cr_before, U32.is_eq(c, 13))))

# Every CR is followed by LF, and every LF has a CR before it
def crlf_clean(b: List<&2, U32>) -> Bool:
  clean.go(b, False{})
