# Parsing one whole request from the bytes received so far.

import Base
import ./reason.bend as Reason
import ./request.bend as Req
import ./limits.bend as Limits
import ./head.bend as Head
import ./framing.bend as Framing


# What parse gives
type Outcome is Data:
  NeedMore{expect_continue: Bool}                          # feed more input
  Rejected{reason: Reason.Reason}                          # close the connection; never parse what follows
  Parsed{request: Req.Request, leftover: List<&2, U32>}    # leftover starts the next request

# The first n bytes of b, and what follows them
type Taken is Data:
  Taken{taken: List<&2, U32>, rest: List<&2, U32>}

def take.cons(+h: U32, m: Maybe<&2, Taken>) -> Maybe<&2, Taken>:
  match m:
    case None{}:
        None{}
    case Some{tk}:
        match tk:
          case Taken{a, b}:
              Some{Taken{Con{h, a}, b}}

# The first n bytes of b, or None if b is shorter
def take(n: Nat, b: List<&2, U32>) -> Maybe<&2, Taken>:
  match n:
    case 0n:
        Some{Taken{Nil{}, b}}
    case 1n+k:
        match b:
          case Nil{}:
              None{}
          case Con{+h, t}:
              take.cons(h, take(k, t))

def parse.body(m: Maybe<&2, Taken>, method: List<&2, U32>, t: Req.Target, v: Req.Version, fs: List<&2, Req.Field>) -> Outcome:
  match m:
    case None{}:
        NeedMore{False{}}
    case Some{tk}:
        match tk:
          case Taken{body, left}:
              Parsed{Req.Request{method, t, v, fs, body}, left}

def parse.frame(r: Result<&2, &2, Reason.Reason, Framing.Framing>, method: List<&2, U32>, t: Req.Target, v: Req.Version, fs: List<&2, Req.Field>, rest: List<&2, U32>) -> Outcome:
  match r:
    case Fail{e}:
        Rejected{e}
    case Done{fr}:
        match fr:
          case Framing.NoBody{}:
              Parsed{Req.Request{method, t, v, fs, Nil{}}, rest}
          case Framing.Length{n}:
              parse.body(take(U32.to_nat(n), rest), method, t, v, fs)
          case Framing.Chunked{}:
              Rejected{Reason.UnsupportedTransferCoding{}}

def parse.head(h: Head.HeadResult, +lim: U32) -> Outcome:
  match h:
    case Head.HeadNeedMore{}:
        NeedMore{False{}}
    case Head.HeadRejected{e}:
        Rejected{e}
    case Head.HeadParsed{rl, +fs, rest}:
        match rl:
          case Req.RequestLine{m, t, +v}:
              parse.frame(Framing.framing(v, fs, lim), m, t, v, fs, rest)

def body_limit(l: Limits.Limits) -> U32:
  match l:
    case Limits.Limits{a, b, c, d, e, f}:
        e

# Parse one request from the start of input: everything received on the
# connection that hasn't been used yet. After Parsed, call parse again on
# leftover for the next request.
def parse(+limits: Limits.Limits, input: List<&2, U32>) -> Outcome:
  parse.head(Head.head(limits, input), body_limit(limits))
