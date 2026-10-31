# Proof of law H6: an HTTP/1.1 request that is Parsed has exactly one Host.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/chunked.bend as Chunked
import ../src/host.bend as Host
import ../src/parse.bend as Parse


# What H6 promises for a version and the Host values
def V6(v: Req.Version, hosts: List<&2, List<&2, U32>>) -> Type:
  match v:
    case Req.Http11{}:
      {Host.one_host.go(hosts) == True{} : Bool}
    case Req.Http10{}:
      Unit

# ... for one outcome
def P6(o: Parse.Outcome) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      match rq:
        case Req.Request{m, t, v, hs, b}:
          V6(v, Host.named(hs, Path.bytes("host")))
    case other:
      Unit

# ... for a check that may fail
def C6(r: Result<&2, &2, Reason.Reason, Bool>, v: Req.Version, hosts: List<&2, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      V6(v, hosts)

def C6u(r: Result<&2, &2, Reason.Reason, Unit>, v: Req.Version, hosts: List<&2, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      V6(v, hosts)

law c6_one:
  for r: Result<&2, &2, Reason.Reason, Unit>
  for v: Req.Version
  for h: List<&2, U32>
  C6u(r, v, [h])

def c6_one(r, v, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{x}:
      match v:
        case Req.Http11{}:
          {==}
        case Req.Http10{}:
          Unit{}

# The Host check only passes HTTP/1.1 with exactly one Host value
law c6_host:
  for +hosts: List<&2, List<&2, U32>>
  for v: Req.Version
  for t: Req.Target
  C6u(Host.host.check(hosts, v, t), v, hosts)

def c6_host(hosts, v, t):
  match hosts:
    case Nil{}:
      match v:
        case Req.Http11{}:
          Unit{}
        case Req.Http10{}:
          Unit{}
    case Con{+h, rest}:
      match rest:
        case Nil{}:
          c6_one(Host.host.one(UrlByte.has_byte(h, 44), Host.host_ok(h), h, t), v, h)
        case Con{x, r}:
          Unit{}

law c6_any:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for v: Req.Version
  for hosts: List<&2, List<&2, U32>>
  for hv: V6(v, hosts)
  C6(r, v, hosts)

def c6_any(r, v, hosts, hv):
  match r:
    case Fail{e}:
      Unit{}
    case Done{x}:
      hv

law c6_expect:
  for r: Result<&2, &2, Reason.Reason, Unit>
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for hr: C6u(r, v, Host.named(fs, Path.bytes("host")))
  C6(Host.checks.expect(r, v, fs), v, Host.named(fs, Path.bytes("host")))

def c6_expect(r, v, fs, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{u}:
      c6_any(Host.expect.check(v, Host.named(fs, Path.bytes("expect"))), v, Host.named(fs, Path.bytes("host")), hr)

law c6:
  for +v: Req.Version
  for +t: Req.Target
  for +fs: List<&2, Req.Field>
  C6(Host.checks(v, t, fs), v, Host.named(fs, Path.bytes("host")))

def c6(v, t, fs):
  c6_expect(Host.host.check(Host.named(fs, Path.bytes("host")), v, t), v, fs, c6_host(Host.named(fs, Path.bytes("host")), v, t))

law p6_body:
  for mb: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for hv: V6(v, Host.named(fs, Path.bytes("host")))
  P6(Parse.parse.body(mb, m, t, v, fs, cont))

def p6_body(mb, m, t, v, fs, cont, hv):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          hv

law p6_chunked:
  for c: Chunked.ChunkResult
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for hv: V6(v, Host.named(fs, Path.bytes("host")))
  P6(Parse.parse.chunked(c, m, t, v, fs, cont))

def p6_chunked(c, m, t, v, fs, cont, hv):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, left}:
      hv

law p6_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  for hv: V6(v, Host.named(fs, Path.bytes("host")))
  P6(Parse.parse.frame(r, m, t, v, fs, rest, limits, cont))

def p6_frame(r, m, t, v, fs, rest, limits, cont, hv):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          hv
        case Framing.Length{n}:
          p6_body(Byte.take(U32.to_nat(n), rest), m, t, v, fs, cont, hv)
        case Framing.Chunked{}:
          p6_chunked(Chunked.read(limits, rest), m, t, v, fs, cont, hv)

law p6_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for m: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for hc: C6(r, v, Host.named(fs, Path.bytes("host")))
  P6(Parse.parse.checks(r, m, t, v, fs, rest, limits))

def p6_checks(r, m, t, v, fs, rest, limits, hc):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      p6_frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, cont, hc)

law p6_head:
  for h: Head.HeadResult
  for +limits: Limits.Limits
  P6(Parse.parse.head(h, limits))

def p6_head(h, limits):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, rest}:
      match rl:
        case Req.RequestLine{m, +t, +v}:
          p6_checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits, c6(v, t, fs))
