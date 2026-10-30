# The head of a request: the request line and the header fields, up to the
# empty line that ends them.

import Base
import ./reason.bend as Reason
import ./request.bend as Req
import ./limits.bend as Limits
import ./lines.bend as Lines
import ./fields.bend as Fields
import ./request_line.bend as Line


# What reading the head gives
type HeadResult is Data:
  HeadNeedMore{}                                     # the head isn't complete yet
  HeadRejected{reason: Reason.Reason}                # close the connection
  HeadParsed{line: Req.RequestLine, fields: List<&2, Req.Field>, rest: List<&2, U32>}

def head.cons(f: Req.Field, r: HeadResult) -> HeadResult:
  match r:
    case HeadParsed{l, fs, rest}:
        HeadParsed{l, Con{f, fs}, rest}
    case other:
        other

# The number of bytes in a list
def size(l: List<&2, U32>) -> U32:
  match l:
    case Nil{}:
        0
    case Con{h, t}:
        U32.inc(size(t))

# The line length plus its CRLF
def line_size(l: List<&2, U32>) -> U32:
  U32.add(size(l), 2)

def minus.if(fits: Bool, +a: U32, +b: U32) -> U32:
  match fits:
    case True{}:
        U32.sub(a, b)
    case False{}:
        0

# a - b, or 0 if b is bigger
def minus(+a: U32, +b: U32) -> U32:
  minus.if(U32.is_le(b, a), a, b)

# After the allowed number of fields only the empty line may come
def head.last(scan: Lines.LineScan, rl: Req.RequestLine) -> HeadResult:
  match scan:
    case Lines.Partial{}:
        HeadNeedMore{}
    case Lines.TooLong{}:
        HeadRejected{Reason.TooManyFields{}}
    case Lines.NotByte{}:
        HeadRejected{Reason.NotAByte{}}
    case Lines.LoneLF{}:
        HeadRejected{Reason.BareLF{}}
    case Lines.LoneCR{}:
        HeadRejected{Reason.BareCR{}}
    case Lines.Line{l, rest}:
        match l:
          case Nil{}:
              HeadParsed{rl, Nil{}, rest}
          case Con{c, t}:
              HeadRejected{Reason.TooManyFields{}}

def head.field2(r: Result<&2, &2, Reason.Reason, Req.Field>, rest: List<&2, U32>, sec: U32, k: List<&2, U32> -> U32 -> HeadResult) -> HeadResult:
  match r:
    case Fail{e}:
        HeadRejected{e}
    case Done{f}:
        head.cons(f, k(rest)(sec))

# One field line, or the empty line that ends the head.
# k reads the fields after this one, given the rest and the bytes left.
def head.field(scan: Lines.LineScan, +sec: U32, first: Bool, rl: Req.RequestLine, k: List<&2, U32> -> U32 -> HeadResult) -> HeadResult:
  match scan:
    case Lines.Partial{}:
        HeadNeedMore{}
    case Lines.TooLong{}:
        HeadRejected{Reason.HeaderTooLarge{}}
    case Lines.NotByte{}:
        HeadRejected{Reason.NotAByte{}}
    case Lines.LoneLF{}:
        HeadRejected{Reason.BareLF{}}
    case Lines.LoneCR{}:
        HeadRejected{Reason.BareCR{}}
    case Lines.Line{l, rest}:
        match l:
          case Nil{}:
              HeadParsed{rl, Nil{}, rest}
          case Con{+c, +t}:
              head.field2(Fields.field_line(Con{c, t}, first), rest, minus(sec, line_size(Con{c, t})), k)

# Read field lines. fuel is how many more are allowed, sec how many bytes
# of the header section are left, fl the limit for one line.
def head.fields(fuel: Nat, input: List<&2, U32>, +sec: U32, +fl: U32, first: Bool, +rl: Req.RequestLine) -> HeadResult:
  match fuel:
    case 0n:
        head.last(Lines.next_line(input, 0), rl)
    case 1n+n:
        head.field(Lines.next_line(input, U32.min(fl, minus(sec, 2))), sec, first, rl,
          r => s => head.fields(n, r, s, fl, False{}, rl))

def head.section(fits: Bool, rl: Req.RequestLine, rest: List<&2, U32>, sec: U32, fl: U32, nf: Nat) -> HeadResult:
  match fits:
    case True{}:
        head.fields(nf, rest, sec, fl, True{}, rl)
    case False{}:
        HeadRejected{Reason.HeaderTooLarge{}}

def head.line(r: Result<&2, &2, Reason.Reason, Req.RequestLine>, +l: List<&2, U32>, rest: List<&2, U32>, +sec: U32, fl: U32, nf: Nat) -> HeadResult:
  match r:
    case Fail{e}:
        HeadRejected{e}
    case Done{rl}:
        head.section(U32.is_le(line_size(l), sec), rl, rest, minus(sec, line_size(l)), fl, nf)

# The request line. empty says what to do with an empty line instead.
def head.request(scan: Lines.LineScan, empty: HeadResult, sec: U32, fl: U32, nf: Nat) -> HeadResult:
  match scan:
    case Lines.Partial{}:
        HeadNeedMore{}
    case Lines.TooLong{}:
        HeadRejected{Reason.TargetTooLong{}}
    case Lines.NotByte{}:
        HeadRejected{Reason.NotAByte{}}
    case Lines.LoneLF{}:
        HeadRejected{Reason.BareLF{}}
    case Lines.LoneCR{}:
        HeadRejected{Reason.BareCR{}}
    case Lines.Line{l, rest}:
        match l:
          case Nil{}:
              empty
          case Con{+c, +t}:
              head.line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf)

# One empty line before the request line is skipped; a second is rejected
def head.first(scan: Lines.LineScan, +rlim: U32, +sec: U32, +fl: U32, +nf: Nat) -> HeadResult:
  match scan:
    case Lines.Line{l, rest}:
        match l:
          case Nil{}:
              head.request(Lines.next_line(rest, rlim), HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf)
          case Con{+c, +t}:
              head.request(Lines.Line{Con{c, t}, rest}, HeadNeedMore{}, sec, fl, nf)
    case other:
        head.request(other, HeadNeedMore{}, sec, fl, nf)

# Read the head of a request from the start of input
def head(limits: Limits.Limits, input: List<&2, U32>) -> HeadResult:
  match limits:
    case Limits.Limits{+rl, fl, hs, nf, b, ce}:
        head.first(Lines.next_line(input, rl), rl, hs, fl, U32.to_nat(nf))
