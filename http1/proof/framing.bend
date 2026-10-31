# Proofs about framing: laws H4 (never both CL and TE) and H5 (one CL, and
# it is the body's length).

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/proof/logic.bend as Logic
import ../../urlpath/src/bytes.bend as UrlByte
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/parse.bend as Parse
import ../src/host.bend as Host
import ../src/limits.bend as Limits
import ../src/chunked.bend as Chunked


# ---- H4 ----

# What H4 promises about one outcome
def P4(o: Parse.Outcome) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      match rq:
        case Req.Request{m, t, v, hs, b}:
          {Framing.both_framing(hs) == False{} : Bool}
    case other:
      Unit

# What framing promises: if it says yes, the fields don't have both
def F4(r: Result<&2, &2, Reason.Reason, Framing.Framing>, fs: List<&2, Req.Field>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      {Framing.both_framing(fs) == False{} : Bool}

law f4_any:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for fs: List<&2, Req.Field>
  for h: {Framing.both_framing(fs) == False{} : Bool}
  F4(r, fs)

def f4_any(r, fs, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{x}:
      h

law f4_go:
  for k: Bool
  for te: Bool
  for v: Req.Version
  for vs: List<&2, List<&2, U32>>
  for tes: List<&2, List<&2, U32>>
  for +lim: U32
  for +fs: List<&2, Req.Field>
  for ek: {k == Framing.both_framing(fs) : Bool}
  F4(Framing.framing.go(k, te, v, vs, tes, lim), fs)

def f4_go(k, te, v, vs, tes, lim, fs, ek):
  match k:
    case True{}:
      Unit{}
    case False{}:
      f4_any(Framing.framing.te(te, v, vs, tes, lim), fs, Equal.sym(Bool, False{}, Framing.both_framing(fs), ek))

law f4:
  for v: Req.Version
  for +fs: List<&2, Req.Field>
  for +lim: U32
  F4(Framing.framing(v, fs, lim), fs)

def f4(v, fs, lim):
  f4_go(Framing.both_framing(fs), Framing.has_field(fs, Path.bytes("transfer-encoding")), v,
    Framing.named(fs, Path.bytes("content-length")), Framing.named(fs, Path.bytes("transfer-encoding")), lim, fs, {==})

law p4_body:
  for mb: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +cont: Bool
  for h: {Framing.both_framing(fs) == False{} : Bool}
  P4(Parse.parse.body(mb, m, t, v, fs, cont))

def p4_body(mb, m, t, v, fs, cont, h):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          h

law p4_chunked:
  for c: Chunked.ChunkResult
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +cont: Bool
  for h: {Framing.both_framing(fs) == False{} : Bool}
  P4(Parse.parse.chunked(c, m, t, v, fs, cont))

def p4_chunked(c, m, t, v, fs, cont, h):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, left}:
      h

law p4_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  for hr: F4(r, fs)
  P4(Parse.parse.frame(r, m, t, v, fs, rest, limits, cont))

def p4_frame(r, m, t, v, fs, rest, limits, cont, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          hr
        case Framing.Length{n}:
          p4_body(Byte.take(U32.to_nat(n), rest), m, t, v, fs, cont, hr)
        case Framing.Chunked{}:
          p4_chunked(Chunked.read(limits, rest), m, t, v, fs, cont, hr)

law p4_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for m: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  P4(Parse.parse.checks(r, m, t, v, fs, rest, limits))

def p4_checks(r, m, t, v, fs, rest, limits):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      p4_frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, cont, f4(v, fs, Limits.body(limits)))

law p4_head:
  for h: Head.HeadResult
  for +limits: Limits.Limits
  P4(Parse.parse.head(h, limits))

def p4_head(h, limits):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, rest}:
      match rl:
        case Req.RequestLine{m, +t, +v}:
          p4_checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits)


# ---- H5 ----

def P5(o: Parse.Outcome) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      match rq:
        case Req.Request{m, t, v, hs, b}:
          {Framing.content_length_ok(hs, b) == True{} : Bool}
    case other:
      Unit

# What framing promises, given vs = the Content-Length values: no body means
# the check passes for an empty body; Length{n} means it passes for any body
# of n bytes
def G5(r: Result<&2, &2, Reason.Reason, Framing.Framing>, vs: List<&2, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          {Framing.cl_ok.go(vs, Nil{}) == True{} : Bool}
        case Framing.Length{n}:
          @b: List<&2, U32> -> {List.length(&2, U32, b) == U32.to_nat(n) : Nat} -> {Framing.cl_ok.go(vs, b) == True{} : Bool}
        case Framing.Chunked{}:
          @b: List<&2, U32> -> {Framing.cl_ok.go(vs, b) == True{} : Bool}

law nat_eq_refl:
  for x: Nat
  {Nat.is_eq(x, x) == True{} : Bool}

def nat_eq_refl(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

law g5_len:
  for +n: U32
  for +v: List<&2, U32>
  for em: {Some{n} == Framing.digits(v) : Maybe<&2, U32>}
  for b: List<&2, U32>
  for hb: {List.length(&2, U32, b) == U32.to_nat(n) : Nat}
  {Framing.cl_ok.go([v], b) == True{} : Bool}

def g5_len(n, v, em, b, hb):
  %em : {Framing.cl_ok.v(_, b) == True{} : Bool}
  e = Equal.sym(Nat, List.length(&2, U32, b), U32.to_nat(n), hb)
  %e : {Nat.is_eq(_, U32.to_nat(n)) == True{} : Bool}
  nat_eq_refl(U32.to_nat(n))

law g5_limit:
  for k: Bool
  for +n: U32
  for +v: List<&2, U32>
  for em: {Some{n} == Framing.digits(v) : Maybe<&2, U32>}
  G5(Framing.cl.limit(k, n), [v])

def g5_limit(k, n, v, em):
  match k:
    case True{}:
      b => hb => g5_len(n, v, em, b, hb)
    case False{}:
      Unit{}

law g5_parsed:
  for m: Maybe<&2, U32>
  for +lim: U32
  for +v: List<&2, U32>
  for em: {m == Framing.digits(v) : Maybe<&2, U32>}
  G5(Framing.cl.parsed(m, lim), [v])

def g5_parsed(m, lim, v, em):
  match m:
    case None{}:
      Unit{}
    case Some{+n}:
      g5_limit(U32.is_le(n, lim), n, v, em)

law g5_valid:
  for k: Bool
  for +v: List<&2, U32>
  for +lim: U32
  G5(Framing.cl.valid(k, v, lim), [v])

def g5_valid(k, v, lim):
  match k:
    case True{}:
      g5_parsed(Framing.digits(v), lim, v, {==})
    case False{}:
      Unit{}

law g5_list:
  for k: Bool
  for +v: List<&2, U32>
  for +lim: U32
  G5(Framing.cl.list(k, v, lim), [v])

def g5_list(k, v, lim):
  match k:
    case True{}:
      Unit{}
    case False{}:
      g5_valid(Framing.cl_valid(v), v, lim)

law g5_cl:
  for +vs: List<&2, List<&2, U32>>
  for +lim: U32
  G5(Framing.cl(vs, lim), vs)

def g5_cl(vs, lim):
  match vs:
    case Nil{}:
      {==}
    case Con{+v, rest}:
      match rest:
        case Nil{}:
          g5_list(UrlByte.has_byte(v, 44), v, lim)
        case Con{w, r}:
          Unit{}

# With Transfer-Encoding present and not both framing fields, there is no
# Content-Length, so the check passes for any body
law vs_nil:
  for +vs: List<&2, List<&2, U32>>
  for h: {False{} == Bool.and(Bool.not(List.is_empty(&2, List<&2, U32>, vs)), True{}) : Bool}
  for b: List<&2, U32>
  {Framing.cl_ok.go(vs, b) == True{} : Bool}

def vs_nil(vs, h, b):
  match vs:
    case Nil{}:
      {==}
    case Con{v, r}:
      Logic.absurd({Framing.cl_ok.go(Con{v, r}, b) == True{} : Bool}, Logic.true_ne_false(h))

law g5_nil:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for +vs: List<&2, List<&2, U32>>
  for +h: {False{} == Bool.and(Bool.not(List.is_empty(&2, List<&2, U32>, vs)), True{}) : Bool}
  G5(r, vs)

def g5_nil(r, vs, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          vs_nil(vs, h, Nil{})
        case Framing.Length{n}:
          b => hb => vs_nil(vs, h, b)
        case Framing.Chunked{}:
          b => vs_nil(vs, h, b)

law g5_go:
  for k: Bool
  for te: Bool
  for v: Req.Version
  for +vs: List<&2, List<&2, U32>>
  for tes: List<&2, List<&2, U32>>
  for +lim: U32
  for ek: {k == Bool.and(Bool.not(List.is_empty(&2, List<&2, U32>, vs)), te) : Bool}
  G5(Framing.framing.go(k, te, v, vs, tes, lim), vs)

def g5_go(k, te, v, vs, tes, lim, ek):
  match k:
    case True{}:
      Unit{}
    case False{}:
      match te:
        case True{}:
          match v:
            case Req.Http10{}:
              Unit{}
            case Req.Http11{}:
              g5_nil(Framing.te(tes), vs, ek)
        case False{}:
          g5_cl(vs, lim)

# take gives exactly n bytes
def TakeLen(mb: Maybe<&2, Byte.Taken>, k: Nat) -> Type:
  match mb:
    case None{}:
      Unit
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          {List.length(&2, U32, a) == k : Nat}

law take_len_cons:
  for +h: U32
  for mb: Maybe<&2, Byte.Taken>
  for k: Nat
  for ih: TakeLen(mb, k)
  TakeLen(Byte.take.cons(h, mb), 1n+k)

def take_len_cons(h, mb, k, ih):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, a), k, ih)

law take_len:
  for +k: Nat
  for b: List<&2, U32>
  TakeLen(Byte.take(k, b), k)

def take_len(k, b):
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      match b:
        case Nil{}:
          Unit{}
        case Con{+h, +t}:
          take_len_cons(h, Byte.take(j, t), j, take_len(j, t))

law p5_body:
  for mb: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for n: U32
  for +cont: Bool
  for hf: @b: List<&2, U32> -> {List.length(&2, U32, b) == U32.to_nat(n) : Nat} -> {Framing.content_length_ok(fs, b) == True{} : Bool}
  for hl: TakeLen(mb, U32.to_nat(n))
  P5(Parse.parse.body(mb, m, t, v, fs, cont))

def p5_body(mb, m, t, v, fs, n, cont, hf, hl):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+a, b}:
          hf(a, hl)

law p5_chunked:
  for c: Chunked.ChunkResult
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +cont: Bool
  for hf: @b: List<&2, U32> -> {Framing.content_length_ok(fs, b) == True{} : Bool}
  P5(Parse.parse.chunked(c, m, t, v, fs, cont))

def p5_chunked(c, m, t, v, fs, cont, hf):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{+b, left}:
      hf(b)

law p5_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  for hr: G5(r, Framing.named(fs, Path.bytes("content-length")))
  P5(Parse.parse.frame(r, m, t, v, fs, rest, limits, cont))

def p5_frame(r, m, t, v, fs, rest, limits, cont, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          hr
        case Framing.Length{+n}:
          p5_body(Byte.take(U32.to_nat(n), rest), m, t, v, fs, n, cont, hr, take_len(U32.to_nat(n), rest))
        case Framing.Chunked{}:
          p5_chunked(Chunked.read(limits, rest), m, t, v, fs, cont, hr)

law p5_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for m: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  P5(Parse.parse.checks(r, m, t, v, fs, rest, limits))

def p5_checks(r, m, t, v, fs, rest, limits):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      p5_frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, cont,
        g5_go(Framing.both_framing(fs), Framing.has_field(fs, Path.bytes("transfer-encoding")), v,
          Framing.named(fs, Path.bytes("content-length")), Framing.named(fs, Path.bytes("transfer-encoding")), Limits.body(limits), {==}))

law p5_head:
  for h: Head.HeadResult
  for +limits: Limits.Limits
  P5(Parse.parse.head(h, limits))

def p5_head(h, limits):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, rest}:
      match rl:
        case Req.RequestLine{m, +t, +v}:
          p5_checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits)
