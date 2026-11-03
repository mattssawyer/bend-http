# Proof of law H1: after Parsed, the leftover is the end of the input.

import Base
import ../../urlpath/proof/logic.bend as Logic
import bend-mathlib@0.7.4.0/string.bend as MStr
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/lines.bend as Lines
import ../src/fields.bend as Fields
import ../src/request_line.bend as Line
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/parse.bend as Parse
import ../src/host.bend as Host
import ../src/chunked.bend as Chunked


# r is the end of i: i is some bytes, then r
def Suf(i: List<&2, U32>, r: List<&2, U32>) -> Type:
  &used: List<&2, U32> -> {i == List.append(&2, U32, used, r) : List<&2, U32>}

law app_assoc:
  for a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, a, b), c) == List.append(&2, U32, a, List.append(&2, U32, b, c)) : List<&2, U32>}

def app_assoc(a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{x, y},
        List.append(&2, U32, List.append(&2, U32, t, b), c), List.append(&2, U32, t, List.append(&2, U32, b, c)), app_assoc(t, b, c))

law suf_join:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for +u1: List<&2, U32>
  for +u2: List<&2, U32>
  for e1: {i == List.append(&2, U32, u1, m) : List<&2, U32>}
  for e2: {m == List.append(&2, U32, u2, r) : List<&2, U32>}
  {i == List.append(&2, U32, List.append(&2, U32, u1, u2), r) : List<&2, U32>}

def suf_join(i, m, r, u1, u2, e1, e2):
  Equal.trans(List<&2, U32>, i, List.append(&2, U32, u1, List.append(&2, U32, u2, r)), List.append(&2, U32, List.append(&2, U32, u1, u2), r),
    Equal.trans(List<&2, U32>, i, List.append(&2, U32, u1, m), List.append(&2, U32, u1, List.append(&2, U32, u2, r)), e1,
      Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, u1, y), m, List.append(&2, U32, u2, r), e2)),
    Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u1, u2), r), List.append(&2, U32, u1, List.append(&2, U32, u2, r)), app_assoc(u1, u2, r)))

law suf_trans2:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for +u1: List<&2, U32>
  for e1: {i == List.append(&2, U32, u1, m) : List<&2, U32>}
  for s2: Suf(m, r)
  Suf(i, r)

def suf_trans2(i, m, r, u1, e1, s2):
  match s2:
    case (+u2, e2):
      (List.append(&2, U32, u1, u2), suf_join(i, m, r, u1, u2, e1, e2))

law suf_trans:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for s1: Suf(i, m)
  for s2: Suf(m, r)
  Suf(i, r)

def suf_trans(i, m, r, s1, s2):
  match s1:
    case (+u1, e1):
      suf_trans2(i, m, r, u1, e1, s2)


# ---- Lines ----

# What next_line promises: the line, its CRLF and the rest make up b
def LS(b: List<&2, U32>, scan: Lines.LineScan) -> Type:
  match scan:
    case Lines.Line{l, rest}:
      {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>}
    case other:
      Unit

law suf_line:
  for +b: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for e: {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>}
  Suf(b, rest)

def suf_line(b, l, rest, e):
  (List.append(&2, U32, l, [13, 10]),
    Equal.trans(List<&2, U32>, b, List.append(&2, U32, l, Con{13, Con{10, rest}}), List.append(&2, U32, List.append(&2, U32, l, [13, 10]), rest), e,
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, l, [13, 10]), rest), List.append(&2, U32, l, Con{13, Con{10, rest}}), app_assoc(l, [13, 10], rest))))

law nl_cons:
  for +h: U32
  for +t: List<&2, U32>
  for r: Lines.LineScan
  for ih: LS(t, r)
  LS(Con{h, t}, Lines.line.cons(h, r))

def nl_cons(h, t, r, ih):
  match r:
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
    case Lines.Line{+l, +rest}:
      e = Equal.sym(List<&2, U32>, t, List.append(&2, U32, l, Con{13, Con{10, rest}}), ih)
      %e : {Con{h, _} == Con{h, List.append(&2, U32, l, Con{13, Con{10, rest}})} : List<&2, U32>}
      {==}

law nl_crlf:
  for k: Bool
  for +h: U32
  for +h2: U32
  for +r: List<&2, U32>
  for ek: {k == U32.is_eq(h2, 10) : Bool}
  for eh: {U32.is_eq(h, 13) == True{} : Bool}
  LS(Con{h, Con{h2, r}}, Lines.line.crlf(k, r))

def nl_crlf(k, h, h2, r, ek, eh):
  match k:
    case True{}:
      e1 = Equal.sym(U32, h, 13, MStr.u32_eq_of_is_eq(h, 13, eh))
      e2 = Equal.sym(U32, h2, 10, MStr.u32_eq_of_is_eq(h2, 10, Equal.sym(Bool, True{}, U32.is_eq(h2, 10), ek)))
      %e1 : {Con{_, Con{h2, r}} == Con{13, Con{10, r}} : List<&2, U32>}
      %e2 : {Con{13, Con{_, r}} == Con{13, Con{10, r}} : List<&2, U32>}
      {==}
    case False{}:
      Unit{}

law nl_cr:
  for +h: U32
  for t: List<&2, U32>
  for eh: {U32.is_eq(h, 13) == True{} : Bool}
  LS(Con{h, t}, Lines.line.cr(t))

def nl_cr(h, t, eh):
  match t:
    case Nil{}:
      Unit{}
    case Con{+h2, +r}:
      nl_crlf(U32.is_eq(h2, 10), h, h2, r, {==}, eh)

law nl_byte:
  for big: Bool
  for cr: Bool
  for lf: Bool
  for +h: U32
  for +t: List<&2, U32>
  for z: Bool
  for k: Unit -> Lines.LineScan
  for ecr: {cr == U32.is_eq(h, 13) : Bool}
  for ih: LS(t, k(Unit{}))
  LS(Con{h, t}, Lines.line.byte(big, cr, lf, h, t, z, k))

def nl_byte(big, cr, lf, h, t, z, k, ecr, ih):
  match big:
    case True{}:
      Unit{}
    case False{}:
      match cr:
        case True{}:
          nl_cr(h, t, Equal.sym(Bool, True{}, U32.is_eq(h, 13), ecr))
        case False{}:
          match lf:
            case True{}:
              Unit{}
            case False{}:
              match z:
                case True{}:
                  Unit{}
                case False{}:
                  nl_cons(h, t, k(Unit{}), ih)

law nl:
  for b: List<&2, U32>
  for +budget: U32
  LS(b, Lines.next_line(b, budget))

def nl(b, budget):
  match b:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      nl_byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), h, t, U32.is_zero(budget),
        u => Lines.next_line(t, U32.sub(budget, 1)), {==}, nl(t, U32.sub(budget, 1)))


# ---- Head ----

# What head promises: the rest after the head is the end of the input
def HS(h: Head.HeadResult, i: List<&2, U32>) -> Type:
  match h:
    case Head.HeadParsed{rl, fs, rest}:
      Suf(i, rest)
    case other:
      Unit

law hs_trans:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for s: Suf(i, m)
  for hh: HS(h, m)
  HS(h, i)

def hs_trans(h, i, m, s, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +r}:
      suf_trans(i, m, r, s, hh)

law hs_cons2:
  for f: Req.Field
  for h: Head.HeadResult
  for +b: List<&2, U32>
  for +rest: List<&2, U32>
  for s: Suf(b, rest)
  for hk: HS(h, rest)
  HS(Head.head.cons(f, h), b)

def hs_cons2(f, h, b, rest, s, hk):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{l, fs, +r}:
      suf_trans(b, rest, r, s, hk)

law hs_field2:
  for r: Result<&2, &2, Reason.Reason, Req.Field>
  for +b: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for s: Suf(b, rest)
  for hk: HS(k(rest)(sec), rest)
  HS(Head.head.field2(r, rest, sec, k), b)

def hs_field2(r, b, rest, sec, k, s, hk):
  match r:
    case Fail{e}:
      Unit{}
    case Done{f}:
      hs_cons2(f, k(rest)(sec), b, rest, s, hk)

law hs_field:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for +sec: U32
  for first: Bool
  for rl: Req.RequestLine
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for hl: LS(b, scan)
  for ih: @r: List<&2, U32> -> @s: U32 -> HS(k(r)(s), r)
  HS(Head.head.field(scan, sec, first, rl, k), b)

def hs_field(scan, b, sec, first, rl, k, hl, ih):
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
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          suf_line(b, Nil{}, rest, hl)
        case Con{+c, +t}:
          hs_field2(Fields.field_line(Con{c, t}, first), b, rest, Head.minus(Head.minus(sec, 2), Head.size(Con{c, t})), k,
            suf_line(b, Con{c, t}, rest, hl), ih(rest)(Head.minus(Head.minus(sec, 2), Head.size(Con{c, t}))))

law hs_last:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for rl: Req.RequestLine
  for hl: LS(b, scan)
  HS(Head.head.last(scan, rl), b)

def hs_last(scan, b, rl, hl):
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
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          suf_line(b, Nil{}, rest, hl)
        case Con{c, t}:
          Unit{}

law hs_fields:
  for fuel: Nat
  for +input: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for first: Bool
  for +rl: Req.RequestLine
  HS(Head.head.fields(fuel, input, sec, fl, first, rl), input)

def hs_fields(fuel, input, sec, fl, first, rl):
  match fuel:
    case 0n:
      hs_last(Lines.next_line(input, 0), input, rl, nl(input, 0))
    case 1n+(+n):
      hs_field(Lines.next_line(input, U32.min(fl, Head.minus(sec, 2))), input, sec, first, rl,
        r => s => Head.head.fields(n, r, s, fl, False{}, rl),
        nl(input, U32.min(fl, Head.minus(sec, 2))),
        r => s => hs_fields(n, r, s, fl, False{}, rl))

law hs_section:
  for k: Bool
  for +rl: Req.RequestLine
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for nf: Nat
  HS(Head.head.section(k, rl, rest, sec, fl, nf), rest)

def hs_section(k, rl, rest, sec, fl, nf):
  match k:
    case True{}:
      hs_fields(nf, rest, sec, fl, True{}, rl)
    case False{}:
      Unit{}

law hs_line:
  for r: Result<&2, &2, Reason.Reason, Req.RequestLine>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  HS(Head.head.line(r, l, rest, sec, fl, nf), rest)

def hs_line(r, l, rest, sec, fl, nf):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+rl}:
      hs_section(Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))), rl, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, nf)

law hs_request:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for empty: Head.HeadResult
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for hl: LS(b, scan)
  for he: HS(empty, b)
  HS(Head.head.request(scan, empty, sec, fl, nf), b)

def hs_request(scan, b, empty, sec, fl, nf, hl, he):
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
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          he
        case Con{+c, +t}:
          hs_trans(Head.head.line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf), b, rest,
            suf_line(b, Con{c, t}, rest, hl),
            hs_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf))

law hs_first:
  for scan: Lines.LineScan
  for +i: List<&2, U32>
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for hl: LS(i, scan)
  HS(Head.head.first(scan, rlim, sec, fl, nf), i)

def hs_first(scan, i, rlim, sec, fl, nf, hl):
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
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          hs_trans(Head.head.request(Lines.next_line(rest, rlim), Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf), i, rest,
            suf_line(i, Nil{}, rest, hl),
            hs_request(Lines.next_line(rest, rlim), rest, Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf, nl(rest, rlim), Unit{}))
        case Con{+c, +t}:
          hs_request(Lines.Line{Con{c, t}, rest}, i, Head.HeadNeedMore{}, sec, fl, nf, hl, Unit{})

law hs_head:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  HS(Head.head(l, i), i)

def hs_head(l, i):
  match l:
    case Limits.Limits{+rl, fl, hs, nf, b, ce}:
      hs_first(Lines.next_line(i, rl), i, rl, hs, fl, U32.to_nat(nf), nl(i, rl))


# ---- Body ----

# What take promises: the taken bytes and the rest make up b
def TakeSuf(mb: Maybe<&2, Byte.Taken>, b: List<&2, U32>) -> Type:
  match mb:
    case None{}:
      Unit
    case Some{tk}:
      match tk:
        case Byte.Taken{a, left}:
          {b == List.append(&2, U32, a, left) : List<&2, U32>}

law take_suf_cons:
  for +h: U32
  for +t: List<&2, U32>
  for mb: Maybe<&2, Byte.Taken>
  for ih: TakeSuf(mb, t)
  TakeSuf(Byte.take.cons(h, mb), Con{h, t})

def take_suf_cons(h, t, mb, ih):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+a, +left}:
          e = Equal.sym(List<&2, U32>, t, List.append(&2, U32, a, left), ih)
          %e : {Con{h, _} == Con{h, List.append(&2, U32, a, left)} : List<&2, U32>}
          {==}

law take_suf:
  for +k: Nat
  for +b: List<&2, U32>
  TakeSuf(Byte.take(k, b), b)

def take_suf(k, b):
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      match b:
        case Nil{}:
          Unit{}
        case Con{+h, +t}:
          take_suf_cons(h, t, Byte.take(j, t), take_suf(j, t))


# ---- Chunked body ----

# What reading a chunked body promises: the rest is the end of the input
def CS(c: Chunked.ChunkResult, b: List<&2, U32>) -> Type:
  match c:
    case Chunked.ChunkDone{body, rest}:
      Suf(b, rest)
    case other:
      Unit

law cs_trans:
  for c: Chunked.ChunkResult
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for s: Suf(i, m)
  for h: CS(c, m)
  CS(c, i)

def cs_trans(c, i, m, s, h):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, +r}:
      suf_trans(i, m, r, s, h)

law cs_cons:
  for data: List<&2, U32>
  for c: Chunked.ChunkResult
  for +i: List<&2, U32>
  for +r: List<&2, U32>
  for s: Suf(i, r)
  for h: CS(c, r)
  CS(Chunked.chunk.cons(data, c), i)

def cs_cons(data, c, i, r, s, h):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{x}:
      Unit{}
    case Chunked.ChunkDone{b, +left}:
      suf_trans(i, r, left, s, h)

law cs_cons_cr:
  for x: Bool
  for data: List<&2, U32>
  for b: List<&2, U32>
  CS(Chunked.chunk.cons(data, Chunked.chunk.cr(x)), b)

def cs_cons_cr(x, data, b):
  match x:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

law cs_lf:
  for f: Bool
  for data: List<&2, U32>
  for +a: U32
  for +b2: U32
  for +t2: List<&2, U32>
  for +i: List<&2, U32>
  for kk: Unit -> Chunked.ChunkResult
  for s: Suf(i, Con{a, Con{b2, t2}})
  for h: CS(kk(Unit{}), t2)
  CS(Chunked.chunk.cons(data, Chunked.chunk.lf(f, kk)), i)

def cs_lf(f, data, a, b2, t2, i, kk, s, h):
  match f:
    case True{}:
      cs_cons(data, kk(Unit{}), i, t2, suf_trans(i, Con{a, Con{b2, t2}}, t2, s, ([a, b2], {==})), h)
    case False{}:
      Unit{}

# The data, then exactly CRLF, then the rest of the chunks
law cs_crlf:
  for data: List<&2, U32>
  for +r: List<&2, U32>
  for +i: List<&2, U32>
  for k: List<&2, U32> -> Chunked.ChunkResult
  for s: Suf(i, r)
  for ih: @x: List<&2, U32> -> CS(k(x), x)
  CS(Chunked.chunk.cons(data, Chunked.chunk.crlf(r, k)), i)

def cs_crlf(data, r, i, k, s, ih):
  match r:
    case Nil{}:
      Unit{}
    case Con{+a, t}:
      match t:
        case Nil{}:
          cs_cons_cr(U32.is_eq(a, 13), data, i)
        case Con{+b2, +t2}:
          cs_lf(U32.is_eq(a, 13) && U32.is_eq(b2, 10), data, a, b2, t2, i, u => k(t2), s, ih(t2))

law cs_data:
  for m: Maybe<&2, Byte.Taken>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for k: List<&2, U32> -> Chunked.ChunkResult
  for s: Suf(i, rest)
  for ht: TakeSuf(m, rest)
  for ih: @x: List<&2, U32> -> CS(k(x), x)
  CS(Chunked.chunk.data(m, k), i)

def cs_data(m, rest, i, k, s, ht, ih):
  match m:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+data, +r}:
          cs_crlf(data, r, i, k, suf_trans(i, rest, r, s, (data, ht)), ih)

law cs_fits:
  for f: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for k: List<&2, U32> -> Chunked.ChunkResult
  for s: Suf(i, rest)
  for ih: @x: List<&2, U32> -> CS(k(x), x)
  CS(Chunked.chunk.fits(f, n, rest, k), i)

def cs_fits(f, n, rest, i, k, s, ih):
  match f:
    case True{}:
      cs_data(Byte.take(U32.to_nat(n), rest), rest, i, k, s, take_suf(U32.to_nat(n), rest), ih)
    case False{}:
      Unit{}

law cs_trailers:
  for h: Head.HeadResult
  for +b: List<&2, U32>
  for +i: List<&2, U32>
  for s: Suf(i, b)
  for hh: HS(h, b)
  CS(Chunked.chunk.trailers(h), i)

def cs_trailers(h, b, i, s, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +rest}:
      suf_trans(i, b, rest, s, hh)

law hs_trailers:
  for +limits: Limits.Limits
  for +rest: List<&2, U32>
  HS(Head.trailers(limits, rest), rest)

def hs_trailers(limits, rest):
  match limits:
    case Limits.Limits{rl, +fl, +hs, nf, b, ce}:
      hs_fields(U32.to_nat(nf), rest, hs, fl, False{}, Req.RequestLine{Nil{}, Req.Asterisk{}, Req.Http11{}})

law cs_zero:
  for z: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for s: Suf(i, rest)
  for ih: @x: List<&2, U32> -> @t: U32 -> CS(k(x)(t), x)
  CS(Chunked.chunk.zero(z, n, rest, total, limits, k), i)

def cs_zero(z, n, rest, i, total, limits, k, s, ih):
  match z:
    case True{}:
      cs_trailers(Head.trailers(limits, rest), rest, i, s, hs_trailers(limits, rest))
    case False{}:
      cs_fits(U32.is_le(n, U32.sub(Limits.body(limits), total)), n, rest, i, r2 => k(r2)(U32.add(total, n)), s,
        x => ih(x)(U32.add(total, n)))

law cs_size:
  for r: Result<&2, &2, Reason.Reason, U32>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for s: Suf(i, rest)
  for ih: @x: List<&2, U32> -> @t: U32 -> CS(k(x)(t), x)
  CS(Chunked.chunk.size(r, rest, total, limits, k), i)

def cs_size(r, rest, i, total, limits, k, s, ih):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+n}:
      cs_zero(U32.is_zero(n), n, rest, i, total, limits, k, s, ih)

law cs_long:
  for x: Bool
  for b: List<&2, U32>
  CS(Chunked.chunk.long(x), b)

def cs_long(x, b):
  match x:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

law cs_line:
  for scan: Lines.LineScan
  for +input: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for hl: LS(input, scan)
  for ih: @x: List<&2, U32> -> @s: U32 -> CS(k(x)(s), x)
  CS(Chunked.chunk.line(scan, input, total, limits, k), input)

def cs_line(scan, input, total, limits, k, hl, ih):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      cs_long(Byte.prefix_has(input, Chunked.size_budget(limits), 59), input)
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      cs_size(Chunked.size_line(l, Limits.chunk_ext(limits)), rest, input, total, limits, k, suf_line(input, l, rest, hl), ih)

law cs_chunks:
  for fuel: Nat
  for +input: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  CS(Chunked.chunks(fuel, input, total, limits), input)

def cs_chunks(fuel, input, total, limits):
  match fuel:
    case 0n:
      Unit{}
    case 1n+(+n):
      cs_line(Lines.next_line(input, Chunked.size_budget(limits)), input, total, limits,
        r => s => Chunked.chunks(n, r, s, limits),
        nl(input, Chunked.size_budget(limits)),
        r => s => cs_chunks(n, r, s, limits))


# ---- Parse ----

# What H1 promises about one outcome
def PS(o: Parse.Outcome, i: List<&2, U32>) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      Suf(i, left)
    case other:
      Unit

law ps_body:
  for mb: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for +cont: Bool
  for ht: TakeSuf(mb, rest)
  for hh: Suf(i, rest)
  PS(Parse.parse.body(mb, m, t, v, fs, cont), i)

def ps_body(mb, m, t, v, fs, rest, i, cont, ht, hh):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+a, +left}:
          suf_trans(i, rest, left, hh, (a, ht))

law ps_chunked:
  for c: Chunked.ChunkResult
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for +cont: Bool
  for hh: Suf(i, rest)
  for hc: CS(c, rest)
  PS(Parse.parse.chunked(c, m, t, v, fs, cont), i)

def ps_chunked(c, m, t, v, fs, rest, i, cont, hh, hc):
  match c:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, +left}:
      suf_trans(i, rest, left, hh, hc)

law ps_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +i: List<&2, U32>
  for +cont: Bool
  for hh: Suf(i, rest)
  PS(Parse.parse.frame(r, m, t, v, fs, rest, limits, cont), i)

def ps_frame(r, m, t, v, fs, rest, limits, i, cont, hh):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          hh
        case Framing.Length{+n}:
          ps_body(Byte.take(U32.to_nat(n), rest), m, t, v, fs, rest, i, cont, take_suf(U32.to_nat(n), rest), hh)
        case Framing.Chunked{}:
          ps_chunked(Chunked.read(limits, rest), m, t, v, fs, rest, i, cont, hh,
            cs_chunks(1n+List.length(&2, U32, rest), rest, 0, limits))

law ps_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for m: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +i: List<&2, U32>
  for hh: Suf(i, rest)
  PS(Parse.parse.checks(r, m, t, v, fs, rest, limits), i)

def ps_checks(r, m, t, v, fs, rest, limits, i, hh):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      ps_frame(Framing.framing(v, fs, Limits.body(limits)), m, t, v, fs, rest, limits, i, cont, hh)

law ps_head:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +limits: Limits.Limits
  for hh: HS(h, i)
  PS(Parse.parse.head(h, limits), i)

def ps_head(h, i, limits, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, +rest}:
      match rl:
        case Req.RequestLine{m, +t, +v}:
          ps_checks(Host.checks(v, t, fs), m, t, v, fs, rest, limits, i, hh)
