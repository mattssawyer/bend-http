# Proof of law H1: after Parsed, the leftover is the end of the input.

import Base
import ../../urlpath/proof/logic.bend as Logic
import bend-mathlib@0.7.4.0/string.bend as MStr
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/lines.bend as Lines
import ../src/fields.bend as Fields
import ../src/request_line.bend as Line
import ../src/head.bend as Head
import ../src/framing.bend as Framing
import ../src/parse.bend as Parse


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
          hs_field2(Fields.field_line(Con{c, t}, first), b, rest, Head.minus(sec, Head.line_size(Con{c, t})), k,
            suf_line(b, Con{c, t}, rest, hl), ih(rest)(Head.minus(sec, Head.line_size(Con{c, t}))))

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
      hs_section(U32.is_le(Head.line_size(l), sec), rl, rest, Head.minus(sec, Head.line_size(l)), fl, nf)

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
def TakeSuf(mb: Maybe<&2, Parse.Taken>, b: List<&2, U32>) -> Type:
  match mb:
    case None{}:
      Unit
    case Some{tk}:
      match tk:
        case Parse.Taken{a, left}:
          {b == List.append(&2, U32, a, left) : List<&2, U32>}

law take_suf_cons:
  for +h: U32
  for +t: List<&2, U32>
  for mb: Maybe<&2, Parse.Taken>
  for ih: TakeSuf(mb, t)
  TakeSuf(Parse.take.cons(h, mb), Con{h, t})

def take_suf_cons(h, t, mb, ih):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Parse.Taken{+a, +left}:
          e = Equal.sym(List<&2, U32>, t, List.append(&2, U32, a, left), ih)
          %e : {Con{h, _} == Con{h, List.append(&2, U32, a, left)} : List<&2, U32>}
          {==}

law take_suf:
  for +k: Nat
  for +b: List<&2, U32>
  TakeSuf(Parse.take(k, b), b)

def take_suf(k, b):
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      match b:
        case Nil{}:
          Unit{}
        case Con{+h, +t}:
          take_suf_cons(h, t, Parse.take(j, t), take_suf(j, t))


# ---- Parse ----

# What H1 promises about one outcome
def PS(o: Parse.Outcome, i: List<&2, U32>) -> Type:
  match o:
    case Parse.Parsed{rq, left}:
      Suf(i, left)
    case other:
      Unit

law ps_body:
  for mb: Maybe<&2, Parse.Taken>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for ht: TakeSuf(mb, rest)
  for hh: Suf(i, rest)
  PS(Parse.parse.body(mb, m, t, v, fs), i)

def ps_body(mb, m, t, v, fs, rest, i, ht, hh):
  match mb:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Parse.Taken{+a, +left}:
          suf_trans(i, rest, left, hh, (a, ht))

law ps_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for m: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +i: List<&2, U32>
  for hh: Suf(i, rest)
  PS(Parse.parse.frame(r, m, t, v, fs, rest), i)

def ps_frame(r, m, t, v, fs, rest, i, hh):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          hh
        case Framing.Length{+n}:
          ps_body(Parse.take(U32.to_nat(n), rest), m, t, v, fs, rest, i, take_suf(U32.to_nat(n), rest), hh)
        case Framing.Chunked{}:
          Unit{}

law ps_head:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +lim: U32
  for hh: HS(h, i)
  PS(Parse.parse.head(h, lim), i)

def ps_head(h, i, lim, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, +fs, +rest}:
      match rl:
        case Req.RequestLine{m, t, +v}:
          ps_frame(Framing.framing(v, fs, lim), m, t, v, fs, rest, i, hh)
