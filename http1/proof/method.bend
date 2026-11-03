# Proof of law H10: the method never changes where a request ends.

import Base
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/chunked.bend as Chunked
import ../src/host.bend as Host
import ../src/parse.bend as Parse


law mb_body:
  for mb: Maybe<&2, Byte.Taken>
  for +m1: List<&2, U32>
  for +m2: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +cont: Bool
  {Parse.parse.body(mb, m1, t, v, fs, cont) == Parse.with_method(Parse.parse.body(mb, m2, t, v, fs, cont), m1) : Parse.Outcome}

def mb_body(mb, m1, m2, t, v, fs, cont):
  match mb:
    case None{}:
      {==}
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          {==}

law mb_chunked:
  for c: Chunked.ChunkResult
  for +m1: List<&2, U32>
  for +m2: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +cont: Bool
  {Parse.parse.chunked(c, m1, t, v, fs, cont) == Parse.with_method(Parse.parse.chunked(c, m2, t, v, fs, cont), m1) : Parse.Outcome}

def mb_chunked(c, m1, m2, t, v, fs, cont):
  match c:
    case Chunked.ChunkNeedMore{}:
      {==}
    case Chunked.ChunkRejected{e}:
      {==}
    case Chunked.ChunkDone{b, left}:
      {==}

law mb_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for +m1: List<&2, U32>
  for +m2: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  {Parse.parse.frame(r, m1, t, v, fs, rest, limits, cont) == Parse.with_method(Parse.parse.frame(r, m2, t, v, fs, rest, limits, cont), m1) : Parse.Outcome}

def mb_frame(r, m1, m2, t, v, fs, rest, limits, cont):
  match r:
    case Fail{e}:
      {==}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          {==}
        case Framing.Length{n}:
          mb_body(Byte.take(U32.to_nat(n), rest), m1, m2, t, v, fs, cont)
        case Framing.Chunked{}:
          mb_chunked(Chunked.read(limits, rest), m1, m2, t, v, fs, cont)

law mb_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for +m1: List<&2, U32>
  for +m2: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  {Parse.parse.checks(r, m1, t, v, fs, rest, limits) == Parse.with_method(Parse.parse.checks(r, m2, t, v, fs, rest, limits), m1) : Parse.Outcome}

def mb_checks(r, m1, m2, t, v, fs, rest, limits):
  match r:
    case Fail{e}:
      {==}
    case Done{+cont}:
      mb_frame(Framing.framing(v, fs, Limits.body(limits)), m1, m2, t, v, fs, rest, limits, cont)
