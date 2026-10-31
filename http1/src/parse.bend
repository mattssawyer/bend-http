# Parsing one whole request from the bytes received so far.

import Base
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req
import ./limits.bend as Limits
import ./head.bend as Head
import ./framing.bend as Framing
import ./chunked.bend as Chunked
import ./host.bend as Host


# What parse gives
type Outcome is Data:
  NeedMore{expect_continue: Bool}                          # feed more input
  Rejected{reason: Reason.Reason}                          # close the connection; never parse what follows
  Parsed{request: Req.Request, leftover: List<&2, U32>}    # leftover starts the next request

def parse.body(m: Maybe<&2, Byte.Taken>, method: List<&2, U32>, t: Req.Target, v: Req.Version, fs: List<&2, Req.Field>, cont: Bool) -> Outcome:
  match m:
    case None{}:
        NeedMore{cont}
    case Some{tk}:
        match tk:
          case Byte.Taken{body, left}:
              Parsed{Req.Request{method, t, v, fs, body}, left}

def parse.chunked(c: Chunked.ChunkResult, method: List<&2, U32>, t: Req.Target, v: Req.Version, fs: List<&2, Req.Field>, cont: Bool) -> Outcome:
  match c:
    case Chunked.ChunkNeedMore{}:
        NeedMore{cont}
    case Chunked.ChunkRejected{e}:
        Rejected{e}
    case Chunked.ChunkDone{body, left}:
        Parsed{Req.Request{method, t, v, fs, body}, left}

def parse.frame(r: Result<&2, &2, Reason.Reason, Framing.Framing>, method: List<&2, U32>, t: Req.Target, v: Req.Version, fs: List<&2, Req.Field>, rest: List<&2, U32>, limits: Limits.Limits, cont: Bool) -> Outcome:
  match r:
    case Fail{e}:
        Rejected{e}
    case Done{fr}:
        match fr:
          case Framing.NoBody{}:
              Parsed{Req.Request{method, t, v, fs, Nil{}}, rest}
          case Framing.Length{n}:
              parse.body(Byte.take(U32.to_nat(n), rest), method, t, v, fs, cont)
          case Framing.Chunked{}:
              parse.chunked(Chunked.read(limits, rest), method, t, v, fs, cont)

# After the Host and Expect checks, decide the framing. cont says the client
# is waiting for "100 Continue": while the body is missing, NeedMore says so.
def parse.checks(r: Result<&2, &2, Reason.Reason, Bool>, m: List<&2, U32>, t: Req.Target, +v: Req.Version, +fs: List<&2, Req.Field>, rest: List<&2, U32>, +limits: Limits.Limits) -> Outcome:
  match r:
    case Fail{e}:
        Rejected{e}
    case Done{cont}:
        parse.frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, cont)

def parse.head(h: Head.HeadResult, +limits: Limits.Limits) -> Outcome:
  match h:
    case Head.HeadNeedMore{}:
        NeedMore{False{}}
    case Head.HeadRejected{e}:
        Rejected{e}
    case Head.HeadParsed{rl, +fs, rest}:
        match rl:
          case Req.RequestLine{m, +t, +v}:
              parse.checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits)

# Parse one request from the start of input: everything received on the
# connection that hasn't been used yet. After Parsed, call parse again on
# leftover for the next request.
def parse(+limits: Limits.Limits, input: List<&2, U32>) -> Outcome:
  parse.head(Head.head(limits, input), limits)
