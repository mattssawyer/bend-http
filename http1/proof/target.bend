# Proof of law H8: every path in a Parsed request came from urlpath's parse.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/errors.bend as PathError
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/lines.bend as Lines
import ../src/fields.bend as Fields
import ../src/request_line.bend as Line
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/chunked.bend as Chunked
import ../src/host.bend as Host
import ../src/parse.bend as Parse


# p is what urlpath's parse gives for some bytes
def FromUrlpath(p: List<&2, List<&2, U32>>) -> Type:
  &raw: List<&2, U32> -> {Path.parse(raw) == Done{p} : Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>}

# What H8 promises about a target
def TOk(t: Req.Target) -> Type:
  match t:
    case Req.Origin{p, q}:
      FromUrlpath(p)
    case Req.Absolute{s, a, p, q}:
      FromUrlpath(p)
    case Req.Asterisk{}:
      Unit


# ---- The request line ----

def PQok(r: Result<&2, &2, Reason.Reason, Line.PathQuery>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{pq}:
      match pq:
        case Line.PathQuery{p, q}:
          FromUrlpath(p)

law pq_with:
  for r: Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>
  for q: Maybe<&2, List<&2, U32>>
  for +raw: List<&2, U32>
  for e: {r == Path.parse(raw) : Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>}
  PQok(Line.pq.with(Line.path_of(r), q))

def pq_with(r, q, raw, e):
  match r:
    case Fail{x}:
      Unit{}
    case Done{+p}:
      (raw, Equal.sym(Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>, Done{p}, Path.parse(raw), e))

law pq_query:
  for ok: Bool
  for +p: List<&2, U32>
  for q: List<&2, U32>
  PQok(Line.pq.query(ok, p, q))

def pq_query(ok, p, q):
  match ok:
    case True{}:
      pq_with(Path.parse(p), Some{q}, p, {==})
    case False{}:
      Unit{}

law pq_cut:
  for c: Byte.Cut
  for +t: List<&2, U32>
  PQok(Line.pq.cut(c, t))

def pq_cut(c, t):
  match c:
    case Byte.NoCut{}:
      pq_with(Path.parse(t), None{}, t, {==})
    case Byte.Cut{+p, +q}:
      pq_query(Line.query_ok(q), p, q)

law path_query:
  for +t: List<&2, U32>
  PQok(Line.path_query(t))

def path_query(t):
  pq_cut(Byte.cut(t, 63), t)

def TRok(r: Result<&2, &2, Reason.Reason, Req.Target>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{t}:
      TOk(t)

law tr_origin:
  for r: Result<&2, &2, Reason.Reason, Line.PathQuery>
  for h: PQok(r)
  TRok(Line.origin(r))

def tr_origin(r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{pq}:
      match pq:
        case Line.PathQuery{p, q}:
          h

law tr_done:
  for s: Req.Scheme
  for a: List<&2, U32>
  for r: Result<&2, &2, Reason.Reason, Line.PathQuery>
  for h: PQok(r)
  TRok(Line.absolute.done(s, a, r))

def tr_done(s, a, r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{pq}:
      match pq:
        case Line.PathQuery{p, q}:
          h

law tr_auth:
  for bad: Bool
  for s: Req.Scheme
  for +a: List<&2, U32>
  for +rest: List<&2, U32>
  TRok(Line.absolute.auth(bad, s, a, rest))

def tr_auth(bad, s, a, rest):
  match bad:
    case True{}:
      Unit{}
    case False{}:
      tr_done(s, a, Line.path_query(Line.abs_path(rest)), path_query(Line.abs_path(rest)))

law tr_rest:
  for s: Req.Scheme
  for +r: List<&2, U32>
  TRok(Line.absolute.rest(s, r))

def tr_rest(s, r):
  tr_auth(List.is_empty(&2, U32, Line.authority(r)) || Bool.not(Host.host_ok(Line.authority(r))), s, Line.authority(r), Line.after_authority(r))

law tr_http:
  for m: Maybe<&2, List<&2, U32>>
  TRok(Line.absolute.http(m))

def tr_http(m):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      tr_rest(Req.Http{}, r)

law tr_absolute:
  for m: Maybe<&2, List<&2, U32>>
  for +t: List<&2, U32>
  TRok(Line.absolute(m, t))

def tr_absolute(m, t):
  match m:
    case Some{+r}:
      tr_rest(Req.Https{}, r)
    case None{}:
      tr_http(Byte.drop_prefix_ci(Path.bytes("http://"), t))

law tr_asterisk:
  for ok: Bool
  TRok(Line.asterisk(ok))

def tr_asterisk(ok):
  match ok:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

law tr_form:
  for star: Bool
  for slash: Bool
  for +method: List<&2, U32>
  for +t: List<&2, U32>
  TRok(Line.target.form(star, slash, method, t))

def tr_form(star, slash, method, t):
  match star:
    case True{}:
      tr_asterisk(Byte.eq(method, Path.bytes("OPTIONS")))
    case False{}:
      match slash:
        case True{}:
          tr_origin(Line.path_query(t), path_query(t))
        case False{}:
          tr_absolute(Byte.drop_prefix_ci(Path.bytes("https://"), t), t)

law tr_target:
  for +method: List<&2, U32>
  for t: List<&2, U32>
  TRok(Line.target(method, t))

def tr_target(method, t):
  match t:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      tr_form(U32.is_eq(c, 42) && List.is_empty(&2, U32, rest), U32.is_eq(c, 47), method, Con{c, rest})

def RL8(rl: Req.RequestLine) -> Type:
  match rl:
    case Req.RequestLine{m, t, v}:
      TOk(t)

def RLok(r: Result<&2, &2, Reason.Reason, Req.RequestLine>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{rl}:
      RL8(rl)

law rl_version:
  for r: Result<&2, &2, Reason.Reason, Req.Version>
  for m: List<&2, U32>
  for t: Req.Target
  for h: TOk(t)
  RLok(Line.request_line.version(r, m, t))

def rl_version(r, m, t, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{v}:
      h

law rl_target:
  for r: Result<&2, &2, Reason.Reason, Req.Target>
  for m: List<&2, U32>
  for +v: List<&2, U32>
  for h: TRok(r)
  RLok(Line.request_line.target(r, m, v))

def rl_target(r, m, v, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+t}:
      rl_version(Line.version(v), m, t, h)

law rl_method:
  for short: Bool
  for connect: Bool
  for +m: List<&2, U32>
  for +t: List<&2, U32>
  for +v: List<&2, U32>
  RLok(Line.request_line.method(short, connect, m, t, v))

def rl_method(short, connect, m, t, v):
  match short:
    case False{}:
      Unit{}
    case True{}:
      match connect:
        case True{}:
          Unit{}
        case False{}:
          rl_target(Line.target(m, t), m, v, tr_target(m, t))

law rl_shape:
  for ok: Bool
  for +m: List<&2, U32>
  for +t: List<&2, U32>
  for +v: List<&2, U32>
  RLok(Line.request_line.shape(ok, m, t, v))

def rl_shape(ok, m, t, v):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      rl_method(Nat.is_le(List.length(&2, U32, m), 32n), Byte.eq(m, Path.bytes("CONNECT")), m, t, v)

law rl_second:
  for +m: List<&2, U32>
  for c: Byte.Cut
  RLok(Line.request_line.second(m, c))

def rl_second(m, c):
  match c:
    case Byte.NoCut{}:
      Unit{}
    case Byte.Cut{+t, +v}:
      rl_shape(Line.shape_ok(m, t, v), m, t, v)

law rl_first:
  for c: Byte.Cut
  RLok(Line.request_line.first(c))

def rl_first(c):
  match c:
    case Byte.NoCut{}:
      Unit{}
    case Byte.Cut{+m, rest}:
      rl_second(m, Byte.cut_last(rest, 32))

law rl:
  for l: List<&2, U32>
  RLok(Line.request_line(l))

def rl(l):
  rl_first(Byte.cut(l, 32))


# ---- The head ----

# What the head promises: its request line's target satisfies H8
def H8(h: Head.HeadResult) -> Type:
  match h:
    case Head.HeadParsed{rl, fs, rest}:
      RL8(rl)
    case other:
      Unit

law h8_cons:
  for f: Req.Field
  for h: Head.HeadResult
  for hh: H8(h)
  H8(Head.head.cons(f, h))

def h8_cons(f, h, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{l, fs, r}:
      hh

law h8_field2:
  for r: Result<&2, &2, Reason.Reason, Req.Field>
  for rest: List<&2, U32>
  for sec: U32
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for hk: H8(k(rest)(sec))
  H8(Head.head.field2(r, rest, sec, k))

def h8_field2(r, rest, sec, k, hk):
  match r:
    case Fail{e}:
      Unit{}
    case Done{f}:
      h8_cons(f, k(rest)(sec), hk)

law h8_field:
  for scan: Lines.LineScan
  for +sec: U32
  for first: Bool
  for rl: Req.RequestLine
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for hr: RL8(rl)
  for ih: @r: List<&2, U32> -> @s: U32 -> RL8(rl) -> H8(k(r)(s))
  H8(Head.head.field(scan, sec, first, rl, k))

def h8_field(scan, sec, first, rl, k, hr, ih):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{l, +rest}:
      match l:
        case Nil{}:
          hr
        case Con{+c, +t}:
          h8_field2(Fields.field_line(Con{c, t}, first), rest, Head.minus(sec, Head.line_size(Con{c, t})), k,
            ih(rest)(Head.minus(sec, Head.line_size(Con{c, t})))(hr))

law h8_last:
  for scan: Lines.LineScan
  for rl: Req.RequestLine
  for hr: RL8(rl)
  H8(Head.head.last(scan, rl))

def h8_last(scan, rl, hr):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{l, rest}:
      match l:
        case Nil{}:
          hr
        case Con{c, t}:
          Unit{}

law h8_fields:
  for fuel: Nat
  for input: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for first: Bool
  for +rl: Req.RequestLine
  for hr: RL8(rl)
  H8(Head.head.fields(fuel, input, sec, fl, first, rl))

def h8_fields(fuel, input, sec, fl, first, rl, hr):
  match fuel:
    case 0n:
      h8_last(Lines.next_line(input, 0), rl, hr)
    case 1n+(+n):
      h8_field(Lines.next_line(input, U32.min(fl, Head.minus(sec, 2))), sec, first, rl,
        r => s => Head.head.fields(n, r, s, fl, False{}, rl), hr,
        r => s => z => h8_fields(n, r, s, fl, False{}, rl, z))

law h8_section:
  for k: Bool
  for +rl: Req.RequestLine
  for rest: List<&2, U32>
  for sec: U32
  for fl: U32
  for nf: Nat
  for hr: RL8(rl)
  H8(Head.head.section(k, rl, rest, sec, fl, nf))

def h8_section(k, rl, rest, sec, fl, nf, hr):
  match k:
    case True{}:
      h8_fields(nf, rest, sec, fl, True{}, rl, hr)
    case False{}:
      Unit{}

law h8_line:
  for r: Result<&2, &2, Reason.Reason, Req.RequestLine>
  for +l: List<&2, U32>
  for rest: List<&2, U32>
  for +sec: U32
  for fl: U32
  for nf: Nat
  for hr: RLok(r)
  H8(Head.head.line(r, l, rest, sec, fl, nf))

def h8_line(r, l, rest, sec, fl, nf, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+rl}:
      h8_section(U32.is_le(Head.line_size(l), sec), rl, rest, Head.minus(sec, Head.line_size(l)), fl, nf, hr)

law h8_request:
  for scan: Lines.LineScan
  for empty: Head.HeadResult
  for sec: U32
  for fl: U32
  for nf: Nat
  for he: H8(empty)
  H8(Head.head.request(scan, empty, sec, fl, nf))

def h8_request(scan, empty, sec, fl, nf, he):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{l, rest}:
      match l:
        case Nil{}:
          he
        case Con{+c, +t}:
          h8_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf, rl(Con{c, t}))

law h8_first:
  for scan: Lines.LineScan
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  H8(Head.head.first(scan, rlim, sec, fl, nf))

def h8_first(scan, rlim, sec, fl, nf):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{l, rest}:
      match l:
        case Nil{}:
          h8_request(Lines.next_line(rest, rlim), Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf, Unit{})
        case Con{+c, +t}:
          h8_request(Lines.Line{Con{c, t}, rest}, Head.HeadNeedMore{}, sec, fl, nf, Unit{})

law h8_head:
  for l: Limits.Limits
  for i: List<&2, U32>
  H8(Head.head(l, i))

def h8_head(l, i):
  match l:
    case Limits.Limits{+rl, fl, hs, nf, b, ce}:
      h8_first(Lines.next_line(i, rl), rl, hs, fl, U32.to_nat(nf))


# ---- Parse ----

def P8(o: Parse.Outcome) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      match rq:
        case Req.Request{m, t, v, hs, b}:
          TOk(t)
    case other:
      Unit

law p8_body:
  for mb: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for ht: TOk(t)
  P8(Parse.parse.body(mb, m, t, v, fs, cont))

def p8_body(mb, m, t, v, fs, cont, ht):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          ht

law p8_chunked:
  for c: Chunked.ChunkResult
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for ht: TOk(t)
  P8(Parse.parse.chunked(c, m, t, v, fs, cont))

def p8_chunked(c, m, t, v, fs, cont, ht):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, left}:
      ht

law p8_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  for ht: TOk(t)
  P8(Parse.parse.frame(r, m, t, v, fs, rest, limits, cont))

def p8_frame(r, m, t, v, fs, rest, limits, cont, ht):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          ht
        case Framing.Length{n}:
          p8_body(Byte.take(U32.to_nat(n), rest), m, t, v, fs, cont, ht)
        case Framing.Chunked{}:
          p8_chunked(Chunked.read(limits, rest), m, t, v, fs, cont, ht)

law p8_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for m: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for ht: TOk(t)
  P8(Parse.parse.checks(r, m, t, v, fs, rest, limits))

def p8_checks(r, m, t, v, fs, rest, limits, ht):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      p8_frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, cont, ht)

law p8_head:
  for h: Head.HeadResult
  for +limits: Limits.Limits
  for hh: H8(h)
  P8(Parse.parse.head(h, limits))

def p8_head(h, limits, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, rest}:
      match rl:
        case Req.RequestLine{m, +t, +v}:
          p8_checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits, hh)
