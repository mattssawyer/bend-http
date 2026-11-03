# Proofs of laws H2 and H3: more input never changes a final answer. A
# rejection stays the same rejection, and a parsed request stays the same,
# with the new bytes added to the leftover.

import Base
import ../../urlpath/proof/logic.bend as Logic
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


# ---- Lines ----

# s2 (from the input plus m) agrees with s1 whenever s1 is final
def LSt(s1: Lines.LineScan, s2: Lines.LineScan, m: List<&2, U32>) -> Type:
  match s1:
    case Lines.Partial{}:
      Unit
    case Lines.TooLong{}:
      {s2 == Lines.TooLong{} : Lines.LineScan}
    case Lines.NotByte{}:
      {s2 == Lines.NotByte{} : Lines.LineScan}
    case Lines.LoneLF{}:
      {s2 == Lines.LoneLF{} : Lines.LineScan}
    case Lines.LoneCR{}:
      {s2 == Lines.LoneCR{} : Lines.LineScan}
    case Lines.Line{l, rest}:
      {s2 == Lines.Line{l, List.append(&2, U32, rest, m)} : Lines.LineScan}

law st_lcons:
  for +h: U32
  for r1: Lines.LineScan
  for -r2: Lines.LineScan
  for m: List<&2, U32>
  for hr: LSt(r1, r2, m)
  LSt(Lines.line.cons(h, r1), Lines.line.cons(h, r2), m)

def st_lcons(h, r1, r2, m, hr):
  match r1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, r2, Lines.TooLong{}, hr)
      %e : {Lines.line.cons(h, _) == Lines.TooLong{} : Lines.LineScan}
      {==}
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, r2, Lines.NotByte{}, hr)
      %e : {Lines.line.cons(h, _) == Lines.NotByte{} : Lines.LineScan}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, r2, Lines.LoneLF{}, hr)
      %e : {Lines.line.cons(h, _) == Lines.LoneLF{} : Lines.LineScan}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, r2, Lines.LoneCR{}, hr)
      %e : {Lines.line.cons(h, _) == Lines.LoneCR{} : Lines.LineScan}
      {==}
    case Lines.Line{+l, +rest}:
      e = Equal.sym(Lines.LineScan, r2, Lines.Line{l, List.append(&2, U32, rest, m)}, hr)
      %e : {Lines.line.cons(h, _) == Lines.Line{Con{h, l}, List.append(&2, U32, rest, m)} : Lines.LineScan}
      {==}

law st_crlf:
  for k: Bool
  for r: List<&2, U32>
  for m: List<&2, U32>
  LSt(Lines.line.crlf(k, r), Lines.line.crlf(k, List.append(&2, U32, r, m)), m)

def st_crlf(k, r, m):
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

law st_cr:
  for t: List<&2, U32>
  for m: List<&2, U32>
  LSt(Lines.line.cr(t), Lines.line.cr(List.append(&2, U32, t, m)), m)

def st_cr(t, m):
  match t:
    case Nil{}:
      Unit{}
    case Con{+h2, +r}:
      st_crlf(U32.is_eq(h2, 10), r, m)

law st_byte:
  for big: Bool
  for cr: Bool
  for lf: Bool
  for +h: U32
  for +t: List<&2, U32>
  for z: Bool
  for k1: Unit -> Lines.LineScan
  for -k2: Unit -> Lines.LineScan
  for +m: List<&2, U32>
  for ih: LSt(k1(Unit{}), k2(Unit{}), m)
  LSt(Lines.line.byte(big, cr, lf, h, t, z, k1), Lines.line.byte(big, cr, lf, h, List.append(&2, U32, t, m), z, k2), m)

def st_byte(big, cr, lf, h, t, z, k1, k2, m, ih):
  match big:
    case True{}:
      {==}
    case False{}:
      match cr:
        case True{}:
          st_cr(t, m)
        case False{}:
          match lf:
            case True{}:
              {==}
            case False{}:
              match z:
                case True{}:
                  {==}
                case False{}:
                  st_lcons(h, k1(Unit{}), k2(Unit{}), m, ih)

law st_nl:
  for +b: List<&2, U32>
  for +budget: U32
  for +m: List<&2, U32>
  LSt(Lines.next_line(b, budget), Lines.next_line(List.append(&2, U32, b, m), budget), m)

def st_nl(b, budget, m):
  match b:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      st_byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), h, t, U32.is_zero(budget),
        u => Lines.next_line(t, U32.sub(budget, 1)), u => Lines.next_line(List.append(&2, U32, t, m), U32.sub(budget, 1)), m,
        st_nl(t, U32.sub(budget, 1), m))


# ---- Head ----

def HSt(h1: Head.HeadResult, h2: Head.HeadResult, m: List<&2, U32>) -> Type:
  match h1:
    case Head.HeadNeedMore{}:
      Unit
    case Head.HeadRejected{e}:
      {h2 == Head.HeadRejected{e} : Head.HeadResult}
    case Head.HeadParsed{rl, fs, rest}:
      {h2 == Head.HeadParsed{rl, fs, List.append(&2, U32, rest, m)} : Head.HeadResult}

law st_hcons:
  for +f: Req.Field
  for h1: Head.HeadResult
  for -h2: Head.HeadResult
  for m: List<&2, U32>
  for hh: HSt(h1, h2, m)
  HSt(Head.head.cons(f, h1), Head.head.cons(f, h2), m)

def st_hcons(f, h1, h2, m, hh):
  match h1:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{+x}:
      e = Equal.sym(Head.HeadResult, h2, Head.HeadRejected{x}, hh)
      %e : {Head.head.cons(f, _) == Head.HeadRejected{x} : Head.HeadResult}
      {==}
    case Head.HeadParsed{+rl, +fs, +rest}:
      e = Equal.sym(Head.HeadResult, h2, Head.HeadParsed{rl, fs, List.append(&2, U32, rest, m)}, hh)
      %e : {Head.head.cons(f, _) == Head.HeadParsed{rl, Con{f, fs}, List.append(&2, U32, rest, m)} : Head.HeadResult}
      {==}

law st_field2:
  for r: Result<&2, &2, Reason.Reason, Req.Field>
  for +rest: List<&2, U32>
  for +sec: U32
  for k1: List<&2, U32> -> U32 -> Head.HeadResult
  for -k2: List<&2, U32> -> U32 -> Head.HeadResult
  for +m: List<&2, U32>
  for ih: HSt(k1(rest)(sec), k2(List.append(&2, U32, rest, m))(sec), m)
  HSt(Head.head.field2(r, rest, sec, k1), Head.head.field2(r, List.append(&2, U32, rest, m), sec, k2), m)

def st_field2(r, rest, sec, k1, k2, m, ih):
  match r:
    case Fail{e}:
      {==}
    case Done{+f}:
      st_hcons(f, k1(rest)(sec), k2(List.append(&2, U32, rest, m))(sec), m, ih)

law st_field:
  for s1: Lines.LineScan
  for -s2: Lines.LineScan
  for +sec: U32
  for +first: Bool
  for +rl: Req.RequestLine
  for k1: List<&2, U32> -> U32 -> Head.HeadResult
  for -k2: List<&2, U32> -> U32 -> Head.HeadResult
  for +m: List<&2, U32>
  for hl: LSt(s1, s2, m)
  for ih: @r: List<&2, U32> -> @s: U32 -> HSt(k1(r)(s), k2(List.append(&2, U32, r, m))(s), m)
  HSt(Head.head.field(s1, sec, first, rl, k1), Head.head.field(s2, sec, first, rl, k2), m)

def st_field(s1, s2, sec, first, rl, k1, k2, m, hl, ih):
  match s1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.TooLong{}, hl)
      %e : {Head.head.field(_, sec, first, rl, k2) == Head.HeadRejected{Reason.HeaderTooLarge{}} : Head.HeadResult}
      {==}
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.NotByte{}, hl)
      %e : {Head.head.field(_, sec, first, rl, k2) == Head.HeadRejected{Reason.NotAByte{}} : Head.HeadResult}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneLF{}, hl)
      %e : {Head.head.field(_, sec, first, rl, k2) == Head.HeadRejected{Reason.BareLF{}} : Head.HeadResult}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneCR{}, hl)
      %e : {Head.head.field(_, sec, first, rl, k2) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}
      {==}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Nil{}, List.append(&2, U32, rest, m)}, hl)
          %e : {Head.head.field(_, sec, first, rl, k2) == Head.HeadParsed{rl, Nil{}, List.append(&2, U32, rest, m)} : Head.HeadResult}
          {==}
        case Con{+c, +t}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Con{c, t}, List.append(&2, U32, rest, m)}, hl)
          %e : HSt(Head.head.field2(Fields.field_line(Con{c, t}, first), rest, Head.minus(Head.minus(sec, 2), Head.size(Con{c, t})), k1), Head.head.field(_, sec, first, rl, k2), m)
          st_field2(Fields.field_line(Con{c, t}, first), rest, Head.minus(Head.minus(sec, 2), Head.size(Con{c, t})), k1, k2, m,
            ih(rest)(Head.minus(Head.minus(sec, 2), Head.size(Con{c, t}))))

law st_last:
  for s1: Lines.LineScan
  for -s2: Lines.LineScan
  for +rl: Req.RequestLine
  for +m: List<&2, U32>
  for hl: LSt(s1, s2, m)
  HSt(Head.head.last(s1, rl), Head.head.last(s2, rl), m)

def st_last(s1, s2, rl, m, hl):
  match s1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.TooLong{}, hl)
      %e : {Head.head.last(_, rl) == Head.HeadRejected{Reason.TooManyFields{}} : Head.HeadResult}
      {==}
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.NotByte{}, hl)
      %e : {Head.head.last(_, rl) == Head.HeadRejected{Reason.NotAByte{}} : Head.HeadResult}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneLF{}, hl)
      %e : {Head.head.last(_, rl) == Head.HeadRejected{Reason.BareLF{}} : Head.HeadResult}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneCR{}, hl)
      %e : {Head.head.last(_, rl) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}
      {==}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Nil{}, List.append(&2, U32, rest, m)}, hl)
          %e : {Head.head.last(_, rl) == Head.HeadParsed{rl, Nil{}, List.append(&2, U32, rest, m)} : Head.HeadResult}
          {==}
        case Con{+c, +t}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Con{c, t}, List.append(&2, U32, rest, m)}, hl)
          %e : {Head.head.last(_, rl) == Head.HeadRejected{Reason.TooManyFields{}} : Head.HeadResult}
          {==}

law st_fields:
  for fuel: Nat
  for +b: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +first: Bool
  for +rl: Req.RequestLine
  for +m: List<&2, U32>
  HSt(Head.head.fields(fuel, b, sec, fl, first, rl), Head.head.fields(fuel, List.append(&2, U32, b, m), sec, fl, first, rl), m)

def st_fields(fuel, b, sec, fl, first, rl, m):
  match fuel:
    case 0n:
      st_last(Lines.next_line(b, 0), Lines.next_line(List.append(&2, U32, b, m), 0), rl, m, st_nl(b, 0, m))
    case 1n+(+n):
      st_field(Lines.next_line(b, U32.min(fl, Head.minus(sec, 2))), Lines.next_line(List.append(&2, U32, b, m), U32.min(fl, Head.minus(sec, 2))),
        sec, first, rl,
        r => s => Head.head.fields(n, r, s, fl, False{}, rl), r => s => Head.head.fields(n, r, s, fl, False{}, rl), m,
        st_nl(b, U32.min(fl, Head.minus(sec, 2)), m),
        r => s => st_fields(n, r, s, fl, False{}, rl, m))

law st_section:
  for k: Bool
  for +rl: Req.RequestLine
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +m: List<&2, U32>
  HSt(Head.head.section(k, rl, rest, sec, fl, nf), Head.head.section(k, rl, List.append(&2, U32, rest, m), sec, fl, nf), m)

def st_section(k, rl, rest, sec, fl, nf, m):
  match k:
    case True{}:
      st_fields(nf, rest, sec, fl, True{}, rl, m)
    case False{}:
      {==}

law st_line:
  for r: Result<&2, &2, Reason.Reason, Req.RequestLine>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +m: List<&2, U32>
  HSt(Head.head.line(r, l, rest, sec, fl, nf), Head.head.line(r, l, List.append(&2, U32, rest, m), sec, fl, nf), m)

def st_line(r, l, rest, sec, fl, nf, m):
  match r:
    case Fail{e}:
      {==}
    case Done{+rl}:
      st_section(Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))), rl, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, nf, m)

law st_request:
  for s1: Lines.LineScan
  for -s2: Lines.LineScan
  for +empty: Head.HeadResult
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +m: List<&2, U32>
  for hl: LSt(s1, s2, m)
  for he: HSt(empty, empty, m)
  HSt(Head.head.request(s1, empty, sec, fl, nf), Head.head.request(s2, empty, sec, fl, nf), m)

def st_request(s1, s2, empty, sec, fl, nf, m, hl, he):
  match s1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.TooLong{}, hl)
      %e : {Head.head.request(_, empty, sec, fl, nf) == Head.HeadRejected{Reason.TargetTooLong{}} : Head.HeadResult}
      {==}
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.NotByte{}, hl)
      %e : {Head.head.request(_, empty, sec, fl, nf) == Head.HeadRejected{Reason.NotAByte{}} : Head.HeadResult}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneLF{}, hl)
      %e : {Head.head.request(_, empty, sec, fl, nf) == Head.HeadRejected{Reason.BareLF{}} : Head.HeadResult}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneCR{}, hl)
      %e : {Head.head.request(_, empty, sec, fl, nf) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}
      {==}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Nil{}, List.append(&2, U32, rest, m)}, hl)
          %e : HSt(empty, Head.head.request(_, empty, sec, fl, nf), m)
          he
        case Con{+c, +t}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Con{c, t}, List.append(&2, U32, rest, m)}, hl)
          %e : HSt(Head.head.line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf), Head.head.request(_, empty, sec, fl, nf), m)
          st_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf, m)

law st_first:
  for s1: Lines.LineScan
  for -s2: Lines.LineScan
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +m: List<&2, U32>
  for hl: LSt(s1, s2, m)
  HSt(Head.head.first(s1, rlim, sec, fl, nf), Head.head.first(s2, rlim, sec, fl, nf), m)

def st_first(s1, s2, rlim, sec, fl, nf, m, hl):
  match s1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.TooLong{}, hl)
      %e : {Head.head.first(_, rlim, sec, fl, nf) == Head.HeadRejected{Reason.TargetTooLong{}} : Head.HeadResult}
      {==}
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.NotByte{}, hl)
      %e : {Head.head.first(_, rlim, sec, fl, nf) == Head.HeadRejected{Reason.NotAByte{}} : Head.HeadResult}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneLF{}, hl)
      %e : {Head.head.first(_, rlim, sec, fl, nf) == Head.HeadRejected{Reason.BareLF{}} : Head.HeadResult}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneCR{}, hl)
      %e : {Head.head.first(_, rlim, sec, fl, nf) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}
      {==}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Nil{}, List.append(&2, U32, rest, m)}, hl)
          %e : HSt(Head.head.request(Lines.next_line(rest, rlim), Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf), Head.head.first(_, rlim, sec, fl, nf), m)
          st_request(Lines.next_line(rest, rlim), Lines.next_line(List.append(&2, U32, rest, m), rlim), Head.HeadRejected{Reason.InvalidRequestLine{}},
            sec, fl, nf, m, st_nl(rest, rlim, m), {==})
        case Con{+c, +t}:
          e = Equal.sym(Lines.LineScan, s2, Lines.Line{Con{c, t}, List.append(&2, U32, rest, m)}, hl)
          %e : HSt(Head.head.request(Lines.Line{Con{c, t}, rest}, Head.HeadNeedMore{}, sec, fl, nf), Head.head.first(_, rlim, sec, fl, nf), m)
          st_request(Lines.Line{Con{c, t}, rest}, Lines.Line{Con{c, t}, List.append(&2, U32, rest, m)}, Head.HeadNeedMore{},
            sec, fl, nf, m, {==}, Unit{})

law st_head:
  for +l: Limits.Limits
  for +b: List<&2, U32>
  for +m: List<&2, U32>
  HSt(Head.head(l, b), Head.head(l, List.append(&2, U32, b, m)), m)

def st_head(l, b, m):
  match l:
    case Limits.Limits{+rl, fl, hs, nf, bl, ce}:
      st_first(Lines.next_line(b, rl), Lines.next_line(List.append(&2, U32, b, m), rl), rl, hs, fl, U32.to_nat(nf), m, st_nl(b, rl, m))


# ---- take ----

def TSt(t1: Maybe<&2, Byte.Taken>, t2: Maybe<&2, Byte.Taken>, m: List<&2, U32>) -> Type:
  match t1:
    case None{}:
      Unit
    case Some{tk}:
      match tk:
        case Byte.Taken{a, r}:
          {t2 == Some{Byte.Taken{a, List.append(&2, U32, r, m)}} : Maybe<&2, Byte.Taken>}

law st_take_cons:
  for +h: U32
  for t1: Maybe<&2, Byte.Taken>
  for -t2: Maybe<&2, Byte.Taken>
  for m: List<&2, U32>
  for ih: TSt(t1, t2, m)
  TSt(Byte.take.cons(h, t1), Byte.take.cons(h, t2), m)

def st_take_cons(h, t1, t2, m, ih):
  match t1:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+a, +r}:
          e = Equal.sym(Maybe<&2, Byte.Taken>, t2, Some{Byte.Taken{a, List.append(&2, U32, r, m)}}, ih)
          %e : {Byte.take.cons(h, _) == Some{Byte.Taken{Con{h, a}, List.append(&2, U32, r, m)}} : Maybe<&2, Byte.Taken>}
          {==}

law st_take:
  for +k: Nat
  for +b: List<&2, U32>
  for +m: List<&2, U32>
  TSt(Byte.take(k, b), Byte.take(k, List.append(&2, U32, b, m)), m)

def st_take(k, b, m):
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      match b:
        case Nil{}:
          Unit{}
        case Con{+h, +t}:
          st_take_cons(h, Byte.take(j, t), Byte.take(j, List.append(&2, U32, t, m)), m, st_take(j, t, m))


# ---- "Too long" only depends on the bytes so far ----

def NotTL(s: Lines.LineScan) -> Type:
  match s:
    case Lines.TooLong{}:
      Empty
    case other:
      Unit

law tl_absurd:
  for -s: Lines.LineScan
  for e: {s == Lines.TooLong{} : Lines.LineScan}
  for h: NotTL(s)
  Empty

def tl_absurd(s, e, h):
  %e : NotTL(_)
  h

law cons_tl:
  for +h: U32
  for r: Lines.LineScan
  for e: {Lines.line.cons(h, r) == Lines.TooLong{} : Lines.LineScan}
  {r == Lines.TooLong{} : Lines.LineScan}

def cons_tl(h, r, e):
  match r:
    case Lines.Partial{}:
      Logic.absurd({Lines.Partial{} == Lines.TooLong{} : Lines.LineScan}, tl_absurd(Lines.Partial{}, e, Unit{}))
    case Lines.TooLong{}:
      {==}
    case Lines.NotByte{}:
      Logic.absurd({Lines.NotByte{} == Lines.TooLong{} : Lines.LineScan}, tl_absurd(Lines.NotByte{}, e, Unit{}))
    case Lines.LoneLF{}:
      Logic.absurd({Lines.LoneLF{} == Lines.TooLong{} : Lines.LineScan}, tl_absurd(Lines.LoneLF{}, e, Unit{}))
    case Lines.LoneCR{}:
      Logic.absurd({Lines.LoneCR{} == Lines.TooLong{} : Lines.LineScan}, tl_absurd(Lines.LoneCR{}, e, Unit{}))
    case Lines.Line{l, rest}:
      Logic.absurd({Lines.Line{l, rest} == Lines.TooLong{} : Lines.LineScan}, tl_absurd(Lines.Line{Con{h, l}, rest}, e, Unit{}))

law crlf_not_tl:
  for k: Bool
  for r: List<&2, U32>
  for e: {Lines.line.crlf(k, r) == Lines.TooLong{} : Lines.LineScan}
  Empty

def crlf_not_tl(k, r, e):
  match k:
    case True{}:
      tl_absurd(Lines.Line{Nil{}, r}, e, Unit{})
    case False{}:
      tl_absurd(Lines.LoneCR{}, e, Unit{})

law cr_not_tl:
  for t: List<&2, U32>
  for e: {Lines.line.cr(t) == Lines.TooLong{} : Lines.LineScan}
  Empty

def cr_not_tl(t, e):
  match t:
    case Nil{}:
      tl_absurd(Lines.Partial{}, e, Unit{})
    case Con{+h2, +r}:
      crlf_not_tl(U32.is_eq(h2, 10), r, e)

law ph_if:
  for y: Bool
  for -ka: Unit -> Bool
  for -kb: Unit -> Bool
  for hk: {ka(Unit{}) == kb(Unit{}) : Bool}
  {Byte.prefix_has.if(False{}, y, ka) == Byte.prefix_has.if(False{}, y, kb) : Bool}

def ph_if(y, ka, kb, hk):
  match y:
    case True{}:
      {==}
    case False{}:
      hk

law ph_byte:
  for big: Bool
  for cr: Bool
  for lf: Bool
  for z: Bool
  for +h: U32
  for +t: List<&2, U32>
  for +n: U32
  for +x: U32
  for +m: List<&2, U32>
  for e: {Lines.line.byte(big, cr, lf, h, t, z, u => Lines.next_line(t, U32.sub(n, 1))) == Lines.TooLong{} : Lines.LineScan}
  for ih: {Lines.next_line(t, U32.sub(n, 1)) == Lines.TooLong{} : Lines.LineScan} -> {Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x) == Byte.prefix_has(t, U32.sub(n, 1), x) : Bool}
  {Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x)) == Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(t, U32.sub(n, 1), x)) : Bool}

def ph_byte(big, cr, lf, z, h, t, n, x, m, e, ih):
  match big:
    case True{}:
      Logic.absurd({Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x)) == Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(t, U32.sub(n, 1), x)) : Bool},
        tl_absurd(Lines.NotByte{}, e, Unit{}))
    case False{}:
      match cr:
        case True{}:
          Logic.absurd({Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x)) == Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(t, U32.sub(n, 1), x)) : Bool},
            cr_not_tl(t, e))
        case False{}:
          match lf:
            case True{}:
              Logic.absurd({Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x)) == Byte.prefix_has.if(z, U32.is_eq(h, x), u => Byte.prefix_has(t, U32.sub(n, 1), x)) : Bool},
                tl_absurd(Lines.LoneLF{}, e, Unit{}))
            case False{}:
              match z:
                case True{}:
                  {==}
                case False{}:
                  ph_if(U32.is_eq(h, x), u => Byte.prefix_has(List.append(&2, U32, t, m), U32.sub(n, 1), x), u => Byte.prefix_has(t, U32.sub(n, 1), x),
                    ih(cons_tl(h, Lines.next_line(t, U32.sub(n, 1)), e)))

# If the line is too long, the first n bytes are all here, so looking in
# them gives the same answer with more input
law ph:
  for +b: List<&2, U32>
  for +n: U32
  for +x: U32
  for +m: List<&2, U32>
  for e: {Lines.next_line(b, n) == Lines.TooLong{} : Lines.LineScan}
  {Byte.prefix_has(List.append(&2, U32, b, m), n, x) == Byte.prefix_has(b, n, x) : Bool}

def ph(b, n, x, m, e):
  match b:
    case Nil{}:
      Logic.absurd({Byte.prefix_has(m, n, x) == False{} : Bool}, tl_absurd(Lines.Partial{}, e, Unit{}))
    case Con{+h, +t}:
      ph_byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), U32.is_zero(n), h, t, n, x, m, e,
        z => ph(t, U32.sub(n, 1), x, m, z))


# ---- Chunked body ----

def CSt(c1: Chunked.ChunkResult, c2: Chunked.ChunkResult, m: List<&2, U32>) -> Type:
  match c1:
    case Chunked.ChunkNeedMore{}:
      Unit
    case Chunked.ChunkRejected{e}:
      {c2 == Chunked.ChunkRejected{e} : Chunked.ChunkResult}
    case Chunked.ChunkDone{b, rest}:
      {c2 == Chunked.ChunkDone{b, List.append(&2, U32, rest, m)} : Chunked.ChunkResult}

law st_ccons:
  for +data: List<&2, U32>
  for c1: Chunked.ChunkResult
  for -c2: Chunked.ChunkResult
  for m: List<&2, U32>
  for hc: CSt(c1, c2, m)
  CSt(Chunked.chunk.cons(data, c1), Chunked.chunk.cons(data, c2), m)

def st_ccons(data, c1, c2, m, hc):
  match c1:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{+x}:
      e = Equal.sym(Chunked.ChunkResult, c2, Chunked.ChunkRejected{x}, hc)
      %e : {Chunked.chunk.cons(data, _) == Chunked.ChunkRejected{x} : Chunked.ChunkResult}
      {==}
    case Chunked.ChunkDone{+b, +rest}:
      e = Equal.sym(Chunked.ChunkResult, c2, Chunked.ChunkDone{b, List.append(&2, U32, rest, m)}, hc)
      %e : {Chunked.chunk.cons(data, _) == Chunked.ChunkDone{List.append(&2, U32, data, b), List.append(&2, U32, rest, m)} : Chunked.ChunkResult}
      {==}

# A lone byte after the data that isn't CR stays a rejection with more input
law st_one:
  for x: Bool
  for +a: U32
  for data: List<&2, U32>
  for m: List<&2, U32>
  for -k2: List<&2, U32> -> Chunked.ChunkResult
  for ex: {x == U32.is_eq(a, 13) : Bool}
  CSt(Chunked.chunk.cons(data, Chunked.chunk.cr(x)), Chunked.chunk.cons(data, Chunked.chunk.crlf(Con{a, m}, k2)), m)

def st_one(x, a, data, m, k2, ex):
  match x:
    case True{}:
      Unit{}
    case False{}:
      match m:
        case Nil{}:
          %ex : {Chunked.chunk.cons(data, Chunked.chunk.cr(_)) == Chunked.ChunkRejected{Reason.MissingChunkDataCRLF{}} : Chunked.ChunkResult}
          {==}
        case Con{+b, +t}:
          %ex : {Chunked.chunk.cons(data, Chunked.chunk.lf(Bool.and(_, U32.is_eq(b, 10)), u => k2(t))) == Chunked.ChunkRejected{Reason.MissingChunkDataCRLF{}} : Chunked.ChunkResult}
          {==}

law st_lf:
  for f: Bool
  for +data: List<&2, U32>
  for kk1: Unit -> Chunked.ChunkResult
  for -kk2: Unit -> Chunked.ChunkResult
  for m: List<&2, U32>
  for h: CSt(kk1(Unit{}), kk2(Unit{}), m)
  CSt(Chunked.chunk.cons(data, Chunked.chunk.lf(f, kk1)), Chunked.chunk.cons(data, Chunked.chunk.lf(f, kk2)), m)

def st_lf(f, data, kk1, kk2, m, h):
  match f:
    case True{}:
      st_ccons(data, kk1(Unit{}), kk2(Unit{}), m, h)
    case False{}:
      {==}

# The data, then exactly CRLF, then the rest of the chunks
law st_ccrlf:
  for +data: List<&2, U32>
  for r: List<&2, U32>
  for k1: List<&2, U32> -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for ih: @x: List<&2, U32> -> CSt(k1(x), k2(List.append(&2, U32, x, m)), m)
  CSt(Chunked.chunk.cons(data, Chunked.chunk.crlf(r, k1)), Chunked.chunk.cons(data, Chunked.chunk.crlf(List.append(&2, U32, r, m), k2)), m)

def st_ccrlf(data, r, k1, k2, m, ih):
  match r:
    case Nil{}:
      Unit{}
    case Con{+a, t}:
      match t:
        case Nil{}:
          st_one(U32.is_eq(a, 13), a, data, m, k2, {==})
        case Con{+b, +t2}:
          st_lf(U32.is_eq(a, 13) && U32.is_eq(b, 10), data, u => k1(t2), u => k2(List.append(&2, U32, t2, m)), m, ih(t2))

law st_data:
  for t1: Maybe<&2, Byte.Taken>
  for -t2: Maybe<&2, Byte.Taken>
  for k1: List<&2, U32> -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for ht: TSt(t1, t2, m)
  for ih: @x: List<&2, U32> -> CSt(k1(x), k2(List.append(&2, U32, x, m)), m)
  CSt(Chunked.chunk.data(t1, k1), Chunked.chunk.data(t2, k2), m)

def st_data(t1, t2, k1, k2, m, ht, ih):
  match t1:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+data, +r}:
          e = Equal.sym(Maybe<&2, Byte.Taken>, t2, Some{Byte.Taken{data, List.append(&2, U32, r, m)}}, ht)
          %e : CSt(Chunked.chunk.cons(data, Chunked.chunk.crlf(r, k1)), Chunked.chunk.data(_, k2), m)
          st_ccrlf(data, r, k1, k2, m, ih)

law st_fits:
  for f: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for k1: List<&2, U32> -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for ih: @x: List<&2, U32> -> CSt(k1(x), k2(List.append(&2, U32, x, m)), m)
  CSt(Chunked.chunk.fits(f, n, rest, k1), Chunked.chunk.fits(f, n, List.append(&2, U32, rest, m), k2), m)

def st_fits(f, n, rest, k1, k2, m, ih):
  match f:
    case True{}:
      st_data(Byte.take(U32.to_nat(n), rest), Byte.take(U32.to_nat(n), List.append(&2, U32, rest, m)), k1, k2, m,
        st_take(U32.to_nat(n), rest, m), ih)
    case False{}:
      {==}

law st_trailers:
  for h1: Head.HeadResult
  for -h2: Head.HeadResult
  for m: List<&2, U32>
  for hh: HSt(h1, h2, m)
  CSt(Chunked.chunk.trailers(h1), Chunked.chunk.trailers(h2), m)

def st_trailers(h1, h2, m, hh):
  match h1:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{+x}:
      e = Equal.sym(Head.HeadResult, h2, Head.HeadRejected{x}, hh)
      %e : {Chunked.chunk.trailers(_) == Chunked.ChunkRejected{x} : Chunked.ChunkResult}
      {==}
    case Head.HeadParsed{+rl, +fs, +rest}:
      e = Equal.sym(Head.HeadResult, h2, Head.HeadParsed{rl, fs, List.append(&2, U32, rest, m)}, hh)
      %e : {Chunked.chunk.trailers(_) == Chunked.ChunkDone{Nil{}, List.append(&2, U32, rest, m)} : Chunked.ChunkResult}
      {==}

law st_trailers_head:
  for +l: Limits.Limits
  for +rest: List<&2, U32>
  for +m: List<&2, U32>
  HSt(Head.trailers(l, rest), Head.trailers(l, List.append(&2, U32, rest, m)), m)

def st_trailers_head(l, rest, m):
  match l:
    case Limits.Limits{rl, +fl, +hs, nf, b, ce}:
      st_fields(U32.to_nat(nf), rest, hs, fl, False{}, Req.RequestLine{Nil{}, Req.Asterisk{}, Req.Http11{}}, m)

law st_zero:
  for z: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k1: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for ih: @x: List<&2, U32> -> @s: U32 -> CSt(k1(x)(s), k2(List.append(&2, U32, x, m))(s), m)
  CSt(Chunked.chunk.zero(z, n, rest, total, limits, k1), Chunked.chunk.zero(z, n, List.append(&2, U32, rest, m), total, limits, k2), m)

def st_zero(z, n, rest, total, limits, k1, k2, m, ih):
  match z:
    case True{}:
      st_trailers(Head.trailers(limits, rest), Head.trailers(limits, List.append(&2, U32, rest, m)), m, st_trailers_head(limits, rest, m))
    case False{}:
      st_fits(U32.is_le(n, U32.sub(Limits.body(limits), total)), n, rest,
        r2 => k1(r2)(U32.add(total, n)), r2 => k2(r2)(U32.add(total, n)), m,
        x => ih(x)(U32.add(total, n)))

law st_size:
  for r: Result<&2, &2, Reason.Reason, U32>
  for +rest: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k1: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for ih: @x: List<&2, U32> -> @s: U32 -> CSt(k1(x)(s), k2(List.append(&2, U32, x, m))(s), m)
  CSt(Chunked.chunk.size(r, rest, total, limits, k1), Chunked.chunk.size(r, List.append(&2, U32, rest, m), total, limits, k2), m)

def st_size(r, rest, total, limits, k1, k2, m, ih):
  match r:
    case Fail{e}:
      {==}
    case Done{+n}:
      st_zero(U32.is_zero(n), n, rest, total, limits, k1, k2, m, ih)

law st_long:
  for y: Bool
  for -y2: Bool
  for m: List<&2, U32>
  for ey: {y2 == y : Bool}
  CSt(Chunked.chunk.long(y), Chunked.chunk.long(y2), m)

def st_long(y, y2, m, ey):
  match y:
    case True{}:
      e = Equal.sym(Bool, y2, True{}, ey)
      %e : {Chunked.chunk.long(_) == Chunked.ChunkRejected{Reason.ChunkExtensionTooLong{}} : Chunked.ChunkResult}
      {==}
    case False{}:
      e = Equal.sym(Bool, y2, False{}, ey)
      %e : {Chunked.chunk.long(_) == Chunked.ChunkRejected{Reason.InvalidChunkSize{}} : Chunked.ChunkResult}
      {==}

law st_cline:
  for s1: Lines.LineScan
  for -s2: Lines.LineScan
  for +input: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for k1: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for -k2: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for +m: List<&2, U32>
  for es: {Lines.next_line(input, Chunked.size_budget(limits)) == s1 : Lines.LineScan}
  for hl: LSt(s1, s2, m)
  for ih: @x: List<&2, U32> -> @s: U32 -> CSt(k1(x)(s), k2(List.append(&2, U32, x, m))(s), m)
  CSt(Chunked.chunk.line(s1, input, total, limits, k1), Chunked.chunk.line(s2, List.append(&2, U32, input, m), total, limits, k2), m)

def st_cline(s1, s2, input, total, limits, k1, k2, m, es, hl, ih):
  match s1:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.TooLong{}, hl)
      %e : CSt(Chunked.chunk.long(Byte.prefix_has(input, Chunked.size_budget(limits), 59)), Chunked.chunk.line(_, List.append(&2, U32, input, m), total, limits, k2), m)
      st_long(Byte.prefix_has(input, Chunked.size_budget(limits), 59), Byte.prefix_has(List.append(&2, U32, input, m), Chunked.size_budget(limits), 59), m,
        ph(input, Chunked.size_budget(limits), 59, m, es))
    case Lines.NotByte{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.NotByte{}, hl)
      %e : {Chunked.chunk.line(_, List.append(&2, U32, input, m), total, limits, k2) == Chunked.ChunkRejected{Reason.NotAByte{}} : Chunked.ChunkResult}
      {==}
    case Lines.LoneLF{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneLF{}, hl)
      %e : {Chunked.chunk.line(_, List.append(&2, U32, input, m), total, limits, k2) == Chunked.ChunkRejected{Reason.BareLF{}} : Chunked.ChunkResult}
      {==}
    case Lines.LoneCR{}:
      e = Equal.sym(Lines.LineScan, s2, Lines.LoneCR{}, hl)
      %e : {Chunked.chunk.line(_, List.append(&2, U32, input, m), total, limits, k2) == Chunked.ChunkRejected{Reason.BareCR{}} : Chunked.ChunkResult}
      {==}
    case Lines.Line{+l, +rest}:
      e = Equal.sym(Lines.LineScan, s2, Lines.Line{l, List.append(&2, U32, rest, m)}, hl)
      %e : CSt(Chunked.chunk.size(Chunked.size_line(l, Limits.chunk_ext(limits)), rest, total, limits, k1), Chunked.chunk.line(_, List.append(&2, U32, input, m), total, limits, k2), m)
      st_size(Chunked.size_line(l, Limits.chunk_ext(limits)), rest, total, limits, k1, k2, m, ih)

law st_chunks:
  for f1: Nat
  for f2: Nat
  for +input: List<&2, U32>
  for +total: U32
  for +limits: Limits.Limits
  for +m: List<&2, U32>
  for hf: {Nat.is_le(f1, f2) == True{} : Bool}
  CSt(Chunked.chunks(f1, input, total, limits), Chunked.chunks(f2, List.append(&2, U32, input, m), total, limits), m)

def st_chunks(f1, f2, input, total, limits, m, hf):
  match f1:
    case 0n:
      Unit{}
    case 1n+(+n1):
      match f2:
        case 0n:
          Logic.absurd(CSt(Chunked.chunks(1n+n1, input, total, limits), Chunked.ChunkNeedMore{}, m), Logic.true_ne_false(hf))
        case 1n+(+n2):
          st_cline(Lines.next_line(input, Chunked.size_budget(limits)), Lines.next_line(List.append(&2, U32, input, m), Chunked.size_budget(limits)),
            input, total, limits,
            r => s => Chunked.chunks(n1, r, s, limits), r => s => Chunked.chunks(n2, r, s, limits), m,
            {==}, st_nl(input, Chunked.size_budget(limits), m),
            r => s => st_chunks(n1, n2, r, s, limits, m, hf))

law le_zero:
  for x: Nat
  {Nat.is_le(0n, x) == True{} : Bool}

def le_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

law len_le:
  for b: List<&2, U32>
  for m: List<&2, U32>
  {Nat.is_le(List.length(&2, U32, b), List.length(&2, U32, List.append(&2, U32, b, m))) == True{} : Bool}

def len_le(b, m):
  match b:
    case Nil{}:
      le_zero(List.length(&2, U32, m))
    case Con{h, t}:
      len_le(t, m)

law st_read:
  for +limits: Limits.Limits
  for +b: List<&2, U32>
  for +m: List<&2, U32>
  CSt(Chunked.read(limits, b), Chunked.read(limits, List.append(&2, U32, b, m)), m)

def st_read(limits, b, m):
  st_chunks(1n+List.length(&2, U32, b), 1n+List.length(&2, U32, List.append(&2, U32, b, m)), b, 0, limits, m, len_le(b, m))


# ---- Parse ----

# What H2 and H3 promise together
def OSt(o1: Parse.Outcome, o2: Parse.Outcome, m: List<&2, U32>) -> Type:
  match o1:
    case Parse.NeedMore{c}:
      Unit
    case Parse.Rejected{x}:
      {o2 == Parse.Rejected{x} : Parse.Outcome}
    case Parse.Parsed{r, rest}:
      {o2 == Parse.Parsed{r, List.append(&2, U32, rest, m)} : Parse.Outcome}

law st_pbody:
  for t1: Maybe<&2, Byte.Taken>
  for -t2: Maybe<&2, Byte.Taken>
  for +mt: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +cont: Bool
  for m: List<&2, U32>
  for ht: TSt(t1, t2, m)
  OSt(Parse.parse.body(t1, mt, t, v, fs, cont), Parse.parse.body(t2, mt, t, v, fs, cont), m)

def st_pbody(t1, t2, mt, t, v, fs, cont, m, ht):
  match t1:
    case None{}:
      Unit{}
    case Some{tk}:
      match tk:
        case Byte.Taken{+a, +r}:
          e = Equal.sym(Maybe<&2, Byte.Taken>, t2, Some{Byte.Taken{a, List.append(&2, U32, r, m)}}, ht)
          %e : {Parse.parse.body(_, mt, t, v, fs, cont) == Parse.Parsed{Req.Request{mt, t, v, fs, a}, List.append(&2, U32, r, m)} : Parse.Outcome}
          {==}

law st_pchunked:
  for c1: Chunked.ChunkResult
  for -c2: Chunked.ChunkResult
  for +mt: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +cont: Bool
  for m: List<&2, U32>
  for hc: CSt(c1, c2, m)
  OSt(Parse.parse.chunked(c1, mt, t, v, fs, cont), Parse.parse.chunked(c2, mt, t, v, fs, cont), m)

def st_pchunked(c1, c2, mt, t, v, fs, cont, m, hc):
  match c1:
    case Chunked.ChunkNeedMore{}:
      Unit{}
    case Chunked.ChunkRejected{+x}:
      e = Equal.sym(Chunked.ChunkResult, c2, Chunked.ChunkRejected{x}, hc)
      %e : {Parse.parse.chunked(_, mt, t, v, fs, cont) == Parse.Rejected{x} : Parse.Outcome}
      {==}
    case Chunked.ChunkDone{+b, +rest}:
      e = Equal.sym(Chunked.ChunkResult, c2, Chunked.ChunkDone{b, List.append(&2, U32, rest, m)}, hc)
      %e : {Parse.parse.chunked(_, mt, t, v, fs, cont) == Parse.Parsed{Req.Request{mt, t, v, fs, b}, List.append(&2, U32, rest, m)} : Parse.Outcome}
      {==}

law st_pframe:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for +mt: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +cont: Bool
  for +m: List<&2, U32>
  OSt(Parse.parse.frame(r, mt, t, v, fs, rest, limits, cont), Parse.parse.frame(r, mt, t, v, fs, List.append(&2, U32, rest, m), limits, cont), m)

def st_pframe(r, mt, t, v, fs, rest, limits, cont, m):
  match r:
    case Fail{e}:
      {==}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          {==}
        case Framing.Length{+n}:
          st_pbody(Byte.take(U32.to_nat(n), rest), Byte.take(U32.to_nat(n), List.append(&2, U32, rest, m)), mt, t, v, fs, cont, m,
            st_take(U32.to_nat(n), rest, m))
        case Framing.Chunked{}:
          st_pchunked(Chunked.read(limits, rest), Chunked.read(limits, List.append(&2, U32, rest, m)), mt, t, v, fs, cont, m,
            st_read(limits, rest, m))

law st_pchecks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for +mt: List<&2, U32>
  for +t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +limits: Limits.Limits
  for +m: List<&2, U32>
  OSt(Parse.parse.checks(r, mt, t, v, fs, rest, limits), Parse.parse.checks(r, mt, t, v, fs, List.append(&2, U32, rest, m), limits), m)

def st_pchecks(r, mt, t, v, fs, rest, limits, m):
  match r:
    case Fail{e}:
      {==}
    case Done{+cont}:
      st_pframe(Framing.framing(v, fs, Limits.body(limits)), mt, t, v, fs, rest, limits, cont, m)

law st_phead:
  for h1: Head.HeadResult
  for -h2: Head.HeadResult
  for +limits: Limits.Limits
  for +m: List<&2, U32>
  for hh: HSt(h1, h2, m)
  OSt(Parse.parse.head(h1, limits), Parse.parse.head(h2, limits), m)

def st_phead(h1, h2, limits, m, hh):
  match h1:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{+x}:
      e = Equal.sym(Head.HeadResult, h2, Head.HeadRejected{x}, hh)
      %e : {Parse.parse.head(_, limits) == Parse.Rejected{x} : Parse.Outcome}
      {==}
    case Head.HeadParsed{rl, +fs, +rest}:
      match rl:
        case Req.RequestLine{+mt, +t, +v}:
          e = Equal.sym(Head.HeadResult, h2, Head.HeadParsed{Req.RequestLine{mt, t, v}, fs, List.append(&2, U32, rest, m)}, hh)
          %e : OSt(Parse.parse.checks(Host.checks(v, t, fs), mt, t, v, fs, rest, limits), Parse.parse.head(_, limits), m)
          st_pchecks(Host.checks(v, t, fs), mt, t, v, fs, rest, limits, m)

# More input never changes a final answer
law st_parse:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  OSt(Parse.parse(l, i), Parse.parse(l, List.append(&2, U32, i, m)), m)

def st_parse(l, i, m):
  st_phead(Head.head(l, i), Head.head(l, List.append(&2, U32, i, m)), l, m, st_head(l, i, m))
