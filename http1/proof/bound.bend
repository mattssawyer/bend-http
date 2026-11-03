# Proof of law H9: if the input is longer than the largest request the
# limits allow, parse never says "need more".

import Base
import ../../urlpath/proof/logic.bend as Logic
import bend-mathlib@0.7.4.0/nat.bend as MNat
import bend-mathlib@0.7.4.0/list.bend as MList
import bend-kit-lemmas@0.1.1.0/lemmas.bend as Kit
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
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ./arith.bend as A
import ./suffix.bend as Suffix
import ./framing.bend as FrameProof


# ---- Lines ----

# A line still waiting for its CRLF has at most budget + 1 bytes (the last
# may be a CR); a whole line has at most budget bytes
def LP(b: List<&2, U32>, budget: U32, s: Lines.LineScan) -> Data:
  match s:
    case Lines.Partial{}:
      MNat.le(List.length(&2, U32, b), 1n+U32.to_nat(budget))
    case Lines.Line{l, rest}:
      MNat.le(List.length(&2, U32, l), U32.to_nat(budget))
    case other:
      Unit

law lp_cons:
  for +h: U32
  for +t: List<&2, U32>
  for r: Lines.LineScan
  for +budget: U32
  for eb: {U32.to_nat(budget) == 1n+U32.to_nat(U32.sub(budget, 1)) : Nat}
  for ih: LP(t, U32.sub(budget, 1), r)
  LP(Con{h, t}, budget, Lines.line.cons(h, r))

def lp_cons(h, t, r, budget, eb, ih):
  match r:
    case Lines.Partial{}:
      A.le_eq(1n+List.length(&2, U32, t), 1n+1n+U32.to_nat(U32.sub(budget, 1)), 1n+U32.to_nat(budget),
        MNat.succ_le_succ(List.length(&2, U32, t), 1n+U32.to_nat(U32.sub(budget, 1)), ih),
        Equal.cong(Nat, Nat, x => 1n+x, 1n+U32.to_nat(U32.sub(budget, 1)), U32.to_nat(budget), Equal.sym(Nat, U32.to_nat(budget), 1n+U32.to_nat(U32.sub(budget, 1)), eb)))
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, rest}:
      A.le_eq(1n+List.length(&2, U32, l), 1n+U32.to_nat(U32.sub(budget, 1)), U32.to_nat(budget),
        MNat.succ_le_succ(List.length(&2, U32, l), U32.to_nat(U32.sub(budget, 1)), ih),
        Equal.sym(Nat, U32.to_nat(budget), 1n+U32.to_nat(U32.sub(budget, 1)), eb))

law lp_crlf:
  for k: Bool
  for +h: U32
  for +h2: U32
  for r: List<&2, U32>
  for +budget: U32
  LP(Con{h, Con{h2, r}}, budget, Lines.line.crlf(k, r))

def lp_crlf(k, h, h2, r, budget):
  match k:
    case True{}:
      MNat.zero_le(U32.to_nat(budget))
    case False{}:
      Unit{}

law lp_cr:
  for +h: U32
  for t: List<&2, U32>
  for +budget: U32
  LP(Con{h, t}, budget, Lines.line.cr(t))

def lp_cr(h, t, budget):
  match t:
    case Nil{}:
      MNat.zero_le(U32.to_nat(budget))
    case Con{+h2, +r}:
      lp_crlf(U32.is_eq(h2, 10), h, h2, r, budget)

law lp_byte:
  for big: Bool
  for cr: Bool
  for lf: Bool
  for +h: U32
  for +t: List<&2, U32>
  for z: Bool
  for k: Unit -> Lines.LineScan
  for +budget: U32
  for ez: {z == U32.is_zero(budget) : Bool}
  for ih: LP(t, U32.sub(budget, 1), k(Unit{}))
  LP(Con{h, t}, budget, Lines.line.byte(big, cr, lf, h, t, z, k))

def lp_byte(big, cr, lf, h, t, z, k, budget, ez, ih):
  match big:
    case True{}:
      Unit{}
    case False{}:
      match cr:
        case True{}:
          lp_cr(h, t, budget)
        case False{}:
          match lf:
            case True{}:
              Unit{}
            case False{}:
              match z:
                case True{}:
                  Unit{}
                case False{}:
                  lp_cons(h, t, k(Unit{}), budget, A.u32_pred(budget, Equal.sym(Bool, False{}, U32.is_zero(budget), ez)), ih)

law lp:
  for b: List<&2, U32>
  for +budget: U32
  LP(b, budget, Lines.next_line(b, budget))

def lp(b, budget):
  match b:
    case Nil{}:
      MNat.zero_le(1n+U32.to_nat(budget))
    case Con{+h, +t}:
      lp_byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), h, t, U32.is_zero(budget),
        u => Lines.next_line(t, U32.sub(budget, 1)), budget, {==}, lp(t, U32.sub(budget, 1)))


# ---- Rearranging ----

# b = x + 2 + y and s = x + 2 + z with y <= z + 1 give b <= s + 1
law alg_need:
  for -lb: Nat
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for -sn: Nat
  for eb: {lb == Nat.add(x, 1n+1n+y) : Nat}
  for es: {sn == Nat.add(x, 1n+1n+z) : Nat}
  for hy: MNat.le(y, 1n+z)
  MNat.le(lb, 1n+sn)

def alg_need(lb, x, y, z, sn, eb, es, hy):
  A.eq_le(lb, Nat.add(x, 1n+1n+y), 1n+sn, eb,
    A.le_eq(Nat.add(x, 1n+1n+y), Nat.add(x, 1n+1n+1n+z), 1n+sn,
      MNat.add_le_add_left(1n+1n+y, 1n+1n+1n+z, x, MNat.succ_le_succ(1n+y, 1n+1n+z, MNat.succ_le_succ(y, 1n+z, hy))),
      Equal.trans(Nat, Nat.add(x, 1n+1n+1n+z), 1n+Nat.add(x, 1n+1n+z), 1n+sn, MNat.add_succ(x, 1n+1n+z),
        Equal.cong(Nat, Nat, u => 1n+u, Nat.add(x, 1n+1n+z), sn, Equal.sym(Nat, sn, Nat.add(x, 1n+1n+z), es)))))

# b = x + 2 + y and s = x + 2 + z with y <= z + 2 + w give b <= s + 2 + w
law alg_parsed:
  for -lb: Nat
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +w: Nat
  for -sn: Nat
  for eb: {lb == Nat.add(x, 1n+1n+y) : Nat}
  for es: {sn == Nat.add(x, 1n+1n+z) : Nat}
  for hy: MNat.le(y, Nat.add(z, 1n+1n+w))
  MNat.le(lb, Nat.add(sn, 1n+1n+w))

def alg_parsed(lb, x, y, z, w, sn, eb, es, hy):
  A.eq_le(lb, Nat.add(x, 1n+1n+y), Nat.add(sn, 1n+1n+w), eb,
    A.le_eq(Nat.add(x, 1n+1n+y), Nat.add(x, 1n+1n+Nat.add(z, 1n+1n+w)), Nat.add(sn, 1n+1n+w),
      MNat.add_le_add_left(1n+1n+y, 1n+1n+Nat.add(z, 1n+1n+w), x,
        MNat.succ_le_succ(1n+y, 1n+Nat.add(z, 1n+1n+w), MNat.succ_le_succ(y, Nat.add(z, 1n+1n+w), hy))),
      Equal.trans(Nat, Nat.add(x, 1n+1n+Nat.add(z, 1n+1n+w)), Nat.add(Nat.add(x, 1n+1n+z), 1n+1n+w), Nat.add(sn, 1n+1n+w),
        Equal.sym(Nat, Nat.add(Nat.add(x, 1n+1n+z), 1n+1n+w), Nat.add(x, 1n+1n+Nat.add(z, 1n+1n+w)), MNat.add_assoc(x, 1n+1n+z, 1n+1n+w)),
        Equal.cong(Nat, Nat, u => Nat.add(u, 1n+1n+w), Nat.add(x, 1n+1n+z), sn, Equal.sym(Nat, sn, Nat.add(x, 1n+1n+z), es)))))

# (a + b) + 2 = b + 2 + a
law alg_rearr:
  for +a: Nat
  for +b: Nat
  {Nat.add(Nat.add(a, b), 2n) == Nat.add(b, 1n+1n+a) : Nat}

def alg_rearr(a, b):
  Equal.trans(Nat, Nat.add(Nat.add(a, b), 2n), 1n+1n+Nat.add(b, a), Nat.add(b, 1n+1n+a),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), 2n), Nat.add(2n, Nat.add(a, b)), 1n+1n+Nat.add(b, a),
      MNat.add_comm(Nat.add(a, b), 2n),
      Equal.cong(Nat, Nat, u => 1n+1n+u, Nat.add(a, b), Nat.add(b, a), MNat.add_comm(a, b))),
    Equal.sym(Nat, Nat.add(b, 1n+1n+a), 1n+1n+Nat.add(b, a),
      Equal.trans(Nat, Nat.add(b, 1n+1n+a), 1n+Nat.add(b, 1n+a), 1n+1n+Nat.add(b, a), MNat.add_succ(b, 1n+a),
        Equal.cong(Nat, Nat, u => 1n+u, Nat.add(b, 1n+a), 1n+Nat.add(b, a), MNat.add_succ(b, a)))))

# After a line l that fits, sec = l + 2 + what's left
law es_of:
  for +sec: U32
  for +l: List<&2, U32>
  for f1: {U32.is_le(2, sec) == True{} : Bool}
  for f2: {U32.is_le(Head.size(l), Head.minus(sec, 2)) == True{} : Bool}
  for sz: {U32.to_nat(Head.size(l)) == List.length(&2, U32, l) : Nat}
  {U32.to_nat(sec) == Nat.add(List.length(&2, U32, l), 1n+1n+U32.to_nat(Head.minus(Head.minus(sec, 2), Head.size(l)))) : Nat}

def es_of(sec, l, f1, f2, sz):
  +m2 = U32.to_nat(Head.minus(sec, 2))
  +r = U32.to_nat(Head.minus(Head.minus(sec, 2), Head.size(l)))
  Equal.trans(Nat, U32.to_nat(sec), Nat.add(m2, 2n), Nat.add(List.length(&2, U32, l), 1n+1n+r),
    Equal.sym(Nat, Nat.add(m2, 2n), U32.to_nat(sec), A.minus_eq(sec, 2, f1)),
    Equal.trans(Nat, Nat.add(m2, 2n), Nat.add(Nat.add(r, List.length(&2, U32, l)), 2n), Nat.add(List.length(&2, U32, l), 1n+1n+r),
      Equal.cong(Nat, Nat, u => Nat.add(u, 2n), m2, Nat.add(r, List.length(&2, U32, l)),
        Equal.sym(Nat, Nat.add(r, List.length(&2, U32, l)), m2,
          Equal.trans(Nat, Nat.add(r, List.length(&2, U32, l)), Nat.add(r, U32.to_nat(Head.size(l))), m2,
            Equal.cong(Nat, Nat, u => Nat.add(r, u), List.length(&2, U32, l), U32.to_nat(Head.size(l)), Equal.sym(Nat, U32.to_nat(Head.size(l)), List.length(&2, U32, l), sz)),
            A.minus_eq(Head.minus(sec, 2), Head.size(l), f2)))),
      alg_rearr(r, List.length(&2, U32, l))))

# A non-empty field line within the budget fits
law es_field:
  for +sec: U32
  for +l: List<&2, U32>
  for +hlen: MNat.le(List.length(&2, U32, l), U32.to_nat(Head.minus(sec, 2)))
  for hne: MNat.le(1n, List.length(&2, U32, l))
  for +hlt: MNat.lt(List.length(&2, U32, l), Kit.pow2(32n))
  {U32.to_nat(sec) == Nat.add(List.length(&2, U32, l), 1n+1n+U32.to_nat(Head.minus(Head.minus(sec, 2), Head.size(l)))) : Nat}

def es_field(sec, l, hlen, hne, hlt):
  +sz = A.size_nat(l, hlt)
  es_of(sec, l,
    A.minus_pos(sec, 2, MNat.le_trans(1n, List.length(&2, U32, l), U32.to_nat(Head.minus(sec, 2)), hne, hlen)),
    A.le_u32(Head.size(l), Head.minus(sec, 2), A.eq_le(U32.to_nat(Head.size(l)), List.length(&2, U32, l), U32.to_nat(Head.minus(sec, 2)), sz, hlen)),
    sz)


# ---- Fields ----

# Waiting means at most sec + 1 bytes; done means at most sec + 2 before rest
def FB(h: Head.HeadResult, b: List<&2, U32>, sec: U32) -> Data:
  match h:
    case Head.HeadNeedMore{}:
      MNat.le(List.length(&2, U32, b), 1n+U32.to_nat(sec))
    case Head.HeadRejected{e}:
      Unit
    case Head.HeadParsed{rl, fs, rest}:
      MNat.le(List.length(&2, U32, b), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, rest)))

law fb_shift:
  for h: Head.HeadResult
  for -b: List<&2, U32>
  for -sec: U32
  for +rest: List<&2, U32>
  for +sec2: U32
  for +l: List<&2, U32>
  for eb: {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  for es: {U32.to_nat(sec) == Nat.add(List.length(&2, U32, l), 1n+1n+U32.to_nat(sec2)) : Nat}
  for hh: FB(h, rest, sec2)
  FB(h, b, sec)

def fb_shift(h, b, sec, rest, sec2, l, eb, es, hh):
  match h:
    case Head.HeadNeedMore{}:
      alg_need(List.length(&2, U32, b), List.length(&2, U32, l), List.length(&2, U32, rest), U32.to_nat(sec2), U32.to_nat(sec), eb, es, hh)
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +r}:
      alg_parsed(List.length(&2, U32, b), List.length(&2, U32, l), List.length(&2, U32, rest), U32.to_nat(sec2), List.length(&2, U32, r), U32.to_nat(sec), eb, es, hh)

law fb_cons:
  for f: Req.Field
  for h: Head.HeadResult
  for -b: List<&2, U32>
  for -sec: U32
  for +rest: List<&2, U32>
  for +sec2: U32
  for +l: List<&2, U32>
  for eb: {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  for es: {U32.to_nat(sec) == Nat.add(List.length(&2, U32, l), 1n+1n+U32.to_nat(sec2)) : Nat}
  for hh: FB(h, rest, sec2)
  FB(Head.head.cons(f, h), b, sec)

def fb_cons(f, h, b, sec, rest, sec2, l, eb, es, hh):
  match h:
    case Head.HeadNeedMore{}:
      fb_shift(Head.HeadNeedMore{}, b, sec, rest, sec2, l, eb, es, hh)
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, r}:
      fb_shift(Head.HeadParsed{rl, Con{f, fs}, r}, b, sec, rest, sec2, l, eb, es, hh)

law fb_field2:
  for r: Result<&2, &2, Reason.Reason, Req.Field>
  for -b: List<&2, U32>
  for -sec: U32
  for +rest: List<&2, U32>
  for +sec2: U32
  for +l: List<&2, U32>
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for eb: {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  for es: {U32.to_nat(sec) == Nat.add(List.length(&2, U32, l), 1n+1n+U32.to_nat(sec2)) : Nat}
  for hk: FB(k(rest)(sec2), rest, sec2)
  FB(Head.head.field2(r, rest, sec2, k), b, sec)

def fb_field2(r, b, sec, rest, sec2, l, k, eb, es, hk):
  match r:
    case Fail{e}:
      Unit{}
    case Done{f}:
      fb_cons(f, k(rest)(sec2), b, sec, rest, sec2, l, eb, es, hk)

# An empty line ends the head: 2 bytes, then rest
law fb_end:
  for -b: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for e: {b == List.append(&2, U32, Nil{}, Con{13, Con{10, rest}}) : List<&2, U32>}
  MNat.le(List.length(&2, U32, b), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, rest)))

def fb_end(b, rest, sec, e):
  A.eq_le(List.length(&2, U32, b), 1n+1n+List.length(&2, U32, rest), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, rest)),
    A.len_line(b, Nil{}, rest, e), A.le_addl(1n+1n+List.length(&2, U32, rest), U32.to_nat(sec)))

law fb_field:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for +sec: U32
  for first: Bool
  for rl: Req.RequestLine
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for +bud: U32
  for +hl: LP(b, bud, scan)
  for hs: Suffix.LS(b, scan)
  for +hb: MNat.le(U32.to_nat(bud), U32.to_nat(Head.minus(sec, 2)))
  for ih: @r: List<&2, U32> -> @s: U32 -> FB(k(r)(s), r, s)
  FB(Head.head.field(scan, sec, first, rl, k), b, sec)

def fb_field(scan, b, sec, first, rl, k, bud, hl, hs, hb, ih):
  match scan:
    case Lines.Partial{}:
      MNat.le_trans(List.length(&2, U32, b), 1n+U32.to_nat(bud), 1n+U32.to_nat(sec), hl,
        MNat.succ_le_succ(U32.to_nat(bud), U32.to_nat(sec), MNat.le_trans(U32.to_nat(bud), U32.to_nat(Head.minus(sec, 2)), U32.to_nat(sec), hb, A.minus_le(sec, 2))))
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
          fb_end(b, rest, sec, hs)
        case Con{+c, +t}:
          fb_field2(Fields.field_line(Con{c, t}, first), b, sec, rest, Head.minus(Head.minus(sec, 2), Head.size(Con{c, t})), Con{c, t}, k,
            A.len_line(b, Con{c, t}, rest, hs),
            es_field(sec, Con{c, t}, MNat.le_trans(List.length(&2, U32, Con{c, t}), U32.to_nat(bud), U32.to_nat(Head.minus(sec, 2)), hl, hb),
              MNat.zero_le(List.length(&2, U32, t)),
              MNat.lt_of_le_of_lt(List.length(&2, U32, Con{c, t}), U32.to_nat(bud), Kit.pow2(32n), hl, Kit.u32_to_nat_lt(bud))),
            ih(rest)(Head.minus(Head.minus(sec, 2), Head.size(Con{c, t}))))

law fb_last:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for rl: Req.RequestLine
  for +sec: U32
  for hl: LP(b, 0, scan)
  for hs: Suffix.LS(b, scan)
  FB(Head.head.last(scan, rl), b, sec)

def fb_last(scan, b, rl, sec, hl, hs):
  match scan:
    case Lines.Partial{}:
      MNat.le_trans(List.length(&2, U32, b), 1n, 1n+U32.to_nat(sec), hl, MNat.zero_le(U32.to_nat(sec)))
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
          fb_end(b, rest, sec, hs)
        case Con{c, t}:
          Unit{}

law fb_fields:
  for fuel: Nat
  for +b: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for first: Bool
  for +rl: Req.RequestLine
  FB(Head.head.fields(fuel, b, sec, fl, first, rl), b, sec)

def fb_fields(fuel, b, sec, fl, first, rl):
  match fuel:
    case 0n:
      fb_last(Lines.next_line(b, 0), b, rl, sec, lp(b, 0), Suffix.nl(b, 0))
    case 1n+(+n):
      fb_field(Lines.next_line(b, U32.min(fl, Head.minus(sec, 2))), b, sec, first, rl,
        r => s => Head.head.fields(n, r, s, fl, False{}, rl), U32.min(fl, Head.minus(sec, 2)),
        lp(b, U32.min(fl, Head.minus(sec, 2))), Suffix.nl(b, U32.min(fl, Head.minus(sec, 2))),
        A.min_le(fl, Head.minus(sec, 2)),
        r => s => fb_fields(n, r, s, fl, False{}, rl))


# ---- Request line and head ----

# After the request line: waiting means at most rlim + sec + 1 bytes
def RB(h: Head.HeadResult, b: List<&2, U32>, rlim: U32, sec: U32) -> Data:
  match h:
    case Head.HeadNeedMore{}:
      MNat.le(List.length(&2, U32, b), 1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)))
    case Head.HeadRejected{e}:
      Unit
    case Head.HeadParsed{rl, fs, rest}:
      MNat.le(List.length(&2, U32, b), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, rest)))

law fb_rb:
  for h: Head.HeadResult
  for +b: List<&2, U32>
  for +sec: U32
  for +rlim: U32
  for hf: FB(h, b, sec)
  RB(h, b, rlim, sec)

def fb_rb(h, b, sec, rlim, hf):
  match h:
    case Head.HeadNeedMore{}:
      MNat.le_trans(List.length(&2, U32, b), 1n+U32.to_nat(sec), 1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), hf,
        MNat.succ_le_succ(U32.to_nat(sec), Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), A.le_addl(U32.to_nat(sec), U32.to_nat(rlim))))
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, rest}:
      hf

law rb_section:
  for k: Bool
  for +rl: Req.RequestLine
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +b: List<&2, U32>
  for +l: List<&2, U32>
  for +rlim: U32
  for eb: {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  for ek: {k == Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))) : Bool}
  for +hlt: MNat.lt(List.length(&2, U32, l), Kit.pow2(32n))
  RB(Head.head.section(k, rl, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, nf), b, rlim, sec)

def rb_section(k, rl, rest, sec, fl, nf, b, l, rlim, eb, ek, hlt):
  match k:
    case True{}:
      +f = Equal.sym(Bool, True{}, Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))), ek)
      +h = Head.head.fields(nf, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, True{}, rl)
      fb_rb(h, b, sec, rlim,
        fb_shift(h, b, sec, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), l, eb,
          es_of(sec, l, Logic.and_left(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2)), f),
            Logic.and_right(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2)), f), A.size_nat(l, hlt)),
          fb_fields(nf, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, True{}, rl)))
    case False{}:
      Unit{}

law rb_line:
  for r: Result<&2, &2, Reason.Reason, Req.RequestLine>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +b: List<&2, U32>
  for +rlim: U32
  for eb: {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  for hlt: MNat.lt(List.length(&2, U32, l), Kit.pow2(32n))
  RB(Head.head.line(r, l, rest, sec, fl, nf), b, rlim, sec)

def rb_line(r, l, rest, sec, fl, nf, b, rlim, eb, hlt):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+rl}:
      rb_section(Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))), rl, rest, sec, fl, nf, b, l, rlim, eb, {==}, hlt)

law rb_request:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for empty: Head.HeadResult
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +hl: LP(b, rlim, scan)
  for hs: Suffix.LS(b, scan)
  for he: RB(empty, b, rlim, sec)
  RB(Head.head.request(scan, empty, sec, fl, nf), b, rlim, sec)

def rb_request(scan, b, empty, rlim, sec, fl, nf, hl, hs, he):
  match scan:
    case Lines.Partial{}:
      MNat.le_trans(List.length(&2, U32, b), 1n+U32.to_nat(rlim), 1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), hl,
        MNat.succ_le_succ(U32.to_nat(rlim), Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), MNat.le_add_right(U32.to_nat(rlim), U32.to_nat(sec))))
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
          rb_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf, b, rlim, A.len_line(b, Con{c, t}, rest, hs),
            MNat.lt_of_le_of_lt(List.length(&2, U32, Con{c, t}), U32.to_nat(rlim), Kit.pow2(32n), hl, Kit.u32_to_nat_lt(rlim)))

# The head: waiting means at most rlim + sec + 3 bytes; done means at most
# sec + 4 bytes before rest
def HB(h: Head.HeadResult, i: List<&2, U32>, rlim: U32, sec: U32) -> Data:
  match h:
    case Head.HeadNeedMore{}:
      MNat.le(List.length(&2, U32, i), 1n+1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)))
    case Head.HeadRejected{e}:
      Unit
    case Head.HeadParsed{rl, fs, rest}:
      MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, rest)))

# After a skipped empty line: two more bytes
law rb_hb2:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +rest: List<&2, U32>
  for +rlim: U32
  for +sec: U32
  for eb: {List.length(&2, U32, i) == 1n+1n+List.length(&2, U32, rest) : Nat}
  for hr: RB(h, rest, rlim, sec)
  HB(h, i, rlim, sec)

def rb_hb2(h, i, rest, rlim, sec, eb, hr):
  match h:
    case Head.HeadNeedMore{}:
      A.eq_le(List.length(&2, U32, i), 1n+1n+List.length(&2, U32, rest), 1n+1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), eb,
        MNat.succ_le_succ(1n+List.length(&2, U32, rest), 1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)),
          MNat.succ_le_succ(List.length(&2, U32, rest), 1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), hr)))
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +r}:
      A.eq_le(List.length(&2, U32, i), 1n+1n+List.length(&2, U32, rest), 1n+1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), eb,
        MNat.succ_le_succ(1n+List.length(&2, U32, rest), 1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)),
          MNat.succ_le_succ(List.length(&2, U32, rest), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), hr)))

law le_plus2:
  for +x: Nat
  for +y: Nat
  for +n: Nat
  for h: MNat.le(n, y)
  MNat.le(n, 1n+1n+y)

def le_plus2(x, y, n, h):
  MNat.le_trans(n, y, 1n+1n+y, h, MNat.le_trans(y, 1n+y, 1n+1n+y, MNat.le_succ(y), MNat.le_succ(1n+y)))

law rb_hb0:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +rlim: U32
  for +sec: U32
  for hr: RB(h, i, rlim, sec)
  HB(h, i, rlim, sec)

def rb_hb0(h, i, rlim, sec, hr):
  match h:
    case Head.HeadNeedMore{}:
      MNat.le_trans(List.length(&2, U32, i), 1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), 1n+1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), hr,
        MNat.le_trans(1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), 1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), 1n+1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)),
          MNat.le_succ(1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec))), MNat.le_succ(1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)))))
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +r}:
      MNat.le_trans(List.length(&2, U32, i), Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), 1n+1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), hr,
        MNat.le_trans(Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), 1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)), 1n+1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)),
          MNat.le_succ(Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r))), MNat.le_succ(1n+Nat.add(U32.to_nat(sec), 1n+1n+List.length(&2, U32, r)))))

law hb_first:
  for scan: Lines.LineScan
  for +i: List<&2, U32>
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for +hl: LP(i, rlim, scan)
  for hs: Suffix.LS(i, scan)
  HB(Head.head.first(scan, rlim, sec, fl, nf), i, rlim, sec)

def hb_first(scan, i, rlim, sec, fl, nf, hl, hs):
  match scan:
    case Lines.Partial{}:
      MNat.le_trans(List.length(&2, U32, i), 1n+U32.to_nat(rlim), 1n+1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), hl,
        MNat.succ_le_succ(U32.to_nat(rlim), 1n+1n+Nat.add(U32.to_nat(rlim), U32.to_nat(sec)),
          le_plus2(Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), Nat.add(U32.to_nat(rlim), U32.to_nat(sec)), U32.to_nat(rlim),
            MNat.le_add_right(U32.to_nat(rlim), U32.to_nat(sec)))))
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
          +h = Head.head.request(Lines.next_line(rest, rlim), Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf)
          rb_hb2(h, i, rest, rlim, sec, A.len_line(i, Nil{}, rest, hs),
            rb_request(Lines.next_line(rest, rlim), rest, Head.HeadRejected{Reason.InvalidRequestLine{}}, rlim, sec, fl, nf,
              lp(rest, rlim), Suffix.nl(rest, rlim), Unit{}))
        case Con{+c, +t}:
          +h = Head.head.line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf)
          rb_hb0(h, i, rlim, sec,
            rb_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf, i, rlim, A.len_line(i, Con{c, t}, rest, hs),
              MNat.lt_of_le_of_lt(List.length(&2, U32, Con{c, t}), U32.to_nat(rlim), Kit.pow2(32n), hl, Kit.u32_to_nat_lt(rlim))))

def HBL(h: Head.HeadResult, i: List<&2, U32>, l: Limits.Limits) -> Data:
  match l:
    case Limits.Limits{rl, fl, hs, nf, b, ce}:
      HB(h, i, rl, hs)

law hb_head:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  HBL(Head.head(l, i), i, l)

def hb_head(l, i):
  match l:
    case Limits.Limits{+rl, +fl, +hs, +nf, b, ce}:
      hb_first(Lines.next_line(i, rl), i, rl, hs, fl, U32.to_nat(nf), lp(i, rl), Suffix.nl(i, rl))


# ---- More rearranging ----

law add_s2:
  for +x: Nat
  for +y: Nat
  {Nat.add(x, 1n+1n+y) == 1n+1n+Nat.add(x, y) : Nat}

def add_s2(x, y):
  Equal.trans(Nat, Nat.add(x, 1n+1n+y), 1n+Nat.add(x, 1n+y), 1n+1n+Nat.add(x, y), MNat.add_succ(x, 1n+y),
    Equal.cong(Nat, Nat, u => 1n+u, Nat.add(x, 1n+y), 1n+Nat.add(x, y), MNat.add_succ(x, y)))

law add_s5:
  for +x: Nat
  for +y: Nat
  {Nat.add(x, 1n+1n+1n+1n+1n+y) == 1n+1n+1n+1n+1n+Nat.add(x, y) : Nat}

def add_s5(x, y):
  Equal.trans(Nat, Nat.add(x, 1n+1n+1n+1n+1n+y), 1n+1n+Nat.add(x, 1n+1n+1n+y), 1n+1n+1n+1n+1n+Nat.add(x, y),
    add_s2(x, 1n+1n+1n+y),
    Equal.cong(Nat, Nat, u => 1n+1n+u, Nat.add(x, 1n+1n+1n+y), 1n+1n+1n+Nat.add(x, y),
      Equal.trans(Nat, Nat.add(x, 1n+1n+1n+y), 1n+1n+Nat.add(x, 1n+y), 1n+1n+1n+Nat.add(x, y), add_s2(x, 1n+y),
        Equal.cong(Nat, Nat, u => 1n+1n+u, Nat.add(x, 1n+y), 1n+Nat.add(x, y), MNat.add_succ(x, y)))))


# ---- The chunk bound ----

def SB(l: Limits.Limits) -> Nat:
  U32.to_nat(Chunked.size_budget(l))

def HSn(l: Limits.Limits) -> Nat:
  U32.to_nat(Limits.header_section(l))

def Bn(l: Limits.Limits) -> Nat:
  U32.to_nat(Limits.body(l))

# What a bytes of data can bring with them: a * (size_budget + 5)
def rep(+l: Limits.Limits, a: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      Nat.add(1n+1n+1n+1n+1n+SB(l), rep(l, p))

law rep_ge:
  for +l: Limits.Limits
  for p: Nat
  MNat.le(p, rep(l, p))

def rep_ge(l, p):
  match p:
    case 0n:
      {==}
    case 1n+(+q):
      MNat.succ_le_succ(q, 1n+1n+1n+1n+Nat.add(SB(l), rep(l, q)),
        MNat.le_trans(q, rep(l, q), 1n+1n+1n+1n+Nat.add(SB(l), rep(l, q)), rep_ge(l, q),
          A.le_addl(rep(l, q), 1n+1n+1n+1n+SB(l))))

# One byte of data (and so one chunk) is worth at least size_budget + 5 + p
law rep_big:
  for +l: Limits.Limits
  for +p: Nat
  MNat.le(1n+1n+1n+1n+1n+Nat.add(SB(l), p), rep(l, 1n+p))

def rep_big(l, p):
  MNat.succ_le_succ(1n+1n+1n+1n+Nat.add(SB(l), p), 1n+1n+1n+1n+Nat.add(SB(l), rep(l, p)),
    MNat.succ_le_succ(1n+1n+1n+Nat.add(SB(l), p), 1n+1n+1n+Nat.add(SB(l), rep(l, p)),
      MNat.succ_le_succ(1n+1n+Nat.add(SB(l), p), 1n+1n+Nat.add(SB(l), rep(l, p)),
        MNat.succ_le_succ(1n+Nat.add(SB(l), p), 1n+Nat.add(SB(l), rep(l, p)),
          MNat.succ_le_succ(Nat.add(SB(l), p), Nat.add(SB(l), rep(l, p)),
            MNat.add_le_add_left(p, rep(l, p), SB(l), rep_ge(l, p)))))))

law psi_add:
  for +l: Limits.Limits
  for a: Nat
  for +b: Nat
  {Parse.chunk_bound(l, Nat.add(a, b)) == Nat.add(rep(l, a), Parse.chunk_bound(l, b)) : Nat}

def psi_add(l, a, b):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, Nat.add(1n+1n+1n+1n+1n+SB(l), Parse.chunk_bound(l, Nat.add(p, b))),
        Nat.add(1n+1n+1n+1n+1n+SB(l), Nat.add(rep(l, p), Parse.chunk_bound(l, b))),
        Nat.add(Nat.add(1n+1n+1n+1n+1n+SB(l), rep(l, p)), Parse.chunk_bound(l, b)),
        Equal.cong(Nat, Nat, u => Nat.add(1n+1n+1n+1n+1n+SB(l), u), Parse.chunk_bound(l, Nat.add(p, b)), Nat.add(rep(l, p), Parse.chunk_bound(l, b)), psi_add(l, p, b)),
        Equal.sym(Nat, Nat.add(Nat.add(1n+1n+1n+1n+1n+SB(l), rep(l, p)), Parse.chunk_bound(l, b)), Nat.add(1n+1n+1n+1n+1n+SB(l), Nat.add(rep(l, p), Parse.chunk_bound(l, b))),
          MNat.add_assoc(1n+1n+1n+1n+1n+SB(l), rep(l, p), Parse.chunk_bound(l, b))))

# The bound never drops below what the last chunk and trailers need
law psi_ge_k:
  for +l: Limits.Limits
  for d: Nat
  MNat.le(Parse.chunk_bound(l, 0n), Parse.chunk_bound(l, d))

def psi_ge_k(l, d):
  match d:
    case 0n:
      MNat.le_refl(Parse.chunk_bound(l, 0n))
    case 1n+(+p):
      MNat.le_trans(Parse.chunk_bound(l, 0n), Parse.chunk_bound(l, p), Nat.add(1n+1n+1n+1n+1n+SB(l), Parse.chunk_bound(l, p)), psi_ge_k(l, p),
        A.le_addl(Parse.chunk_bound(l, p), 1n+1n+1n+1n+1n+SB(l)))

# A size line still waiting for its CRLF fits in the bound
law sb_k:
  for +l: Limits.Limits
  MNat.le(1n+SB(l), Parse.chunk_bound(l, 0n))

def sb_k(l):
  A.le_eq(1n+SB(l), 1n+Nat.add(SB(l), 1n+1n+HSn(l)), Parse.chunk_bound(l, 0n),
    MNat.succ_le_succ(SB(l), Nat.add(SB(l), 1n+1n+HSn(l)), MNat.le_add_right(SB(l), 1n+1n+HSn(l))),
    Equal.sym(Nat, Nat.add(SB(l), 1n+1n+1n+HSn(l)), 1n+Nat.add(SB(l), 1n+1n+HSn(l)), MNat.add_succ(SB(l), 1n+1n+HSn(l))))

# Partway through a chunk's data (rest has at most x + 1 bytes)
law arith_partial:
  for +l: Limits.Limits
  for -lin: Nat
  for +ll: Nat
  for +lr: Nat
  for x: Nat
  for +d: Nat
  for +d2: Nat
  for eb: {lin == Nat.add(ll, 1n+1n+lr) : Nat}
  for hll: MNat.le(ll, SB(l))
  for hlr: MNat.le(lr, 1n+x)
  for hx: MNat.le(1n, x)
  for ed: {d == Nat.add(x, d2) : Nat}
  MNat.le(lin, Parse.chunk_bound(l, d))

def arith_partial(l, lin, ll, lr, x, d, d2, eb, hll, hlr, hx, ed):
  match x:
    case 0n:
      Logic.absurd(MNat.le(lin, Parse.chunk_bound(l, d)), Logic.true_ne_false(hx))
    case 1n+(+p):
      +s = SB(l)
      A.eq_le(lin, Nat.add(ll, 1n+1n+lr), Parse.chunk_bound(l, d), eb,
        MNat.le_trans(Nat.add(ll, 1n+1n+lr), Nat.add(s, 1n+1n+1n+1n+p), Parse.chunk_bound(l, d),
          A.le_add2(ll, s, 1n+1n+lr, 1n+1n+1n+1n+p, hll, MNat.succ_le_succ(1n+lr, 1n+1n+1n+p, MNat.succ_le_succ(lr, 1n+1n+p, hlr))),
          A.eq_le(Nat.add(s, 1n+1n+1n+1n+p), 1n+1n+1n+1n+Nat.add(s, p), Parse.chunk_bound(l, d),
            Equal.trans(Nat, Nat.add(s, 1n+1n+1n+1n+p), 1n+1n+Nat.add(s, 1n+1n+p), 1n+1n+1n+1n+Nat.add(s, p), add_s2(s, 1n+1n+p),
              Equal.cong(Nat, Nat, u => 1n+1n+u, Nat.add(s, 1n+1n+p), 1n+1n+Nat.add(s, p), add_s2(s, p))),
            MNat.le_trans(1n+1n+1n+1n+Nat.add(s, p), rep(l, 1n+p), Parse.chunk_bound(l, d),
              MNat.le_trans(1n+1n+1n+1n+Nat.add(s, p), 1n+1n+1n+1n+1n+Nat.add(s, p), rep(l, 1n+p), MNat.le_succ(1n+1n+1n+1n+Nat.add(s, p)), rep_big(l, p)),
              A.le_eq(rep(l, 1n+p), Nat.add(rep(l, 1n+p), Parse.chunk_bound(l, d2)), Parse.chunk_bound(l, d),
                MNat.le_add_right(rep(l, 1n+p), Parse.chunk_bound(l, d2)),
                Equal.trans(Nat, Nat.add(rep(l, 1n+p), Parse.chunk_bound(l, d2)), Parse.chunk_bound(l, Nat.add(1n+p, d2)), Parse.chunk_bound(l, d),
                  Equal.sym(Nat, Parse.chunk_bound(l, Nat.add(1n+p, d2)), Nat.add(rep(l, 1n+p), Parse.chunk_bound(l, d2)), psi_add(l, 1n+p, d2)),
                  Equal.cong(Nat, Nat, u => Parse.chunk_bound(l, u), Nat.add(1n+p, d2), d, Equal.sym(Nat, d, Nat.add(1n+p, d2), ed))))))))

# A whole chunk, then more chunks within the smaller bound
law arith_step:
  for +l: Limits.Limits
  for -lin: Nat
  for +ll: Nat
  for -lr: Nat
  for +lt2: Nat
  for x: Nat
  for +d: Nat
  for +d2: Nat
  for eb: {lin == Nat.add(ll, 1n+1n+lr) : Nat}
  for hll: MNat.le(ll, SB(l))
  for elr: {lr == Nat.add(x, 1n+1n+lt2) : Nat}
  for ih: MNat.le(lt2, Parse.chunk_bound(l, d2))
  for hx: MNat.le(1n, x)
  for ed: {d == Nat.add(x, d2) : Nat}
  MNat.le(lin, Parse.chunk_bound(l, d))

def arith_step(l, lin, ll, lr, lt2, x, d, d2, eb, hll, elr, ih, hx, ed):
  match x:
    case 0n:
      Logic.absurd(MNat.le(lin, Parse.chunk_bound(l, d)), Logic.true_ne_false(hx))
    case 1n+(+p):
      +s = SB(l)
      +c = Parse.chunk_bound(l, d2)
      eb2 = Equal.trans(Nat, lin, Nat.add(ll, 1n+1n+lr), Nat.add(ll, 1n+1n+Nat.add(1n+p, 1n+1n+lt2)), eb,
        Equal.cong(Nat, Nat, u => Nat.add(ll, 1n+1n+u), lr, Nat.add(1n+p, 1n+1n+lt2), elr))
      A.eq_le(lin, Nat.add(ll, 1n+1n+Nat.add(1n+p, 1n+1n+lt2)), Parse.chunk_bound(l, d), eb2,
        MNat.le_trans(Nat.add(ll, 1n+1n+Nat.add(1n+p, 1n+1n+lt2)), Nat.add(s, 1n+1n+Nat.add(1n+p, 1n+1n+c)), Parse.chunk_bound(l, d),
          A.le_add2(ll, s, 1n+1n+Nat.add(1n+p, 1n+1n+lt2), 1n+1n+Nat.add(1n+p, 1n+1n+c), hll,
            MNat.succ_le_succ(1n+Nat.add(1n+p, 1n+1n+lt2), 1n+Nat.add(1n+p, 1n+1n+c),
              MNat.succ_le_succ(Nat.add(1n+p, 1n+1n+lt2), Nat.add(1n+p, 1n+1n+c),
                MNat.add_le_add_left(1n+1n+lt2, 1n+1n+c, 1n+p,
                  MNat.succ_le_succ(1n+lt2, 1n+c, MNat.succ_le_succ(lt2, c, ih)))))),
          A.eq_le(Nat.add(s, 1n+1n+Nat.add(1n+p, 1n+1n+c)), Nat.add(1n+1n+1n+1n+1n+Nat.add(s, p), c), Parse.chunk_bound(l, d),
            Equal.trans(Nat, Nat.add(s, 1n+1n+1n+Nat.add(p, 1n+1n+c)), Nat.add(s, 1n+1n+1n+1n+1n+Nat.add(p, c)), Nat.add(1n+1n+1n+1n+1n+Nat.add(s, p), c),
              Equal.cong(Nat, Nat, u => Nat.add(s, 1n+1n+1n+u), Nat.add(p, 1n+1n+c), 1n+1n+Nat.add(p, c), add_s2(p, c)),
              Equal.trans(Nat, Nat.add(s, 1n+1n+1n+1n+1n+Nat.add(p, c)), 1n+1n+1n+1n+1n+Nat.add(s, Nat.add(p, c)), Nat.add(1n+1n+1n+1n+1n+Nat.add(s, p), c),
                add_s5(s, Nat.add(p, c)),
                Equal.cong(Nat, Nat, u => 1n+1n+1n+1n+1n+u, Nat.add(s, Nat.add(p, c)), Nat.add(Nat.add(s, p), c),
                  Equal.sym(Nat, Nat.add(Nat.add(s, p), c), Nat.add(s, Nat.add(p, c)), MNat.add_assoc(s, p, c))))),
            MNat.le_trans(Nat.add(1n+1n+1n+1n+1n+Nat.add(s, p), c), Nat.add(rep(l, 1n+p), c), Parse.chunk_bound(l, d),
              MNat.add_le_add_right(1n+1n+1n+1n+1n+Nat.add(s, p), rep(l, 1n+p), c, rep_big(l, p)),
              A.le_eq(Nat.add(rep(l, 1n+p), c), Parse.chunk_bound(l, Nat.add(1n+p, d2)), Parse.chunk_bound(l, d),
                A.eq_le(Nat.add(rep(l, 1n+p), c), Parse.chunk_bound(l, Nat.add(1n+p, d2)), Parse.chunk_bound(l, Nat.add(1n+p, d2)),
                  Equal.sym(Nat, Parse.chunk_bound(l, Nat.add(1n+p, d2)), Nat.add(rep(l, 1n+p), c), psi_add(l, 1n+p, d2)),
                  MNat.le_refl(Parse.chunk_bound(l, Nat.add(1n+p, d2)))),
                Equal.cong(Nat, Nat, u => Parse.chunk_bound(l, u), Nat.add(1n+p, d2), d, Equal.sym(Nat, d, Nat.add(1n+p, d2), ed)))))))


# ---- take ----

# If take finds too few bytes, there were fewer than k
def TS(m: Maybe<&2, Byte.Taken>, b: List<&2, U32>, k: Nat) -> Data:
  match m:
    case None{}:
      MNat.lt(List.length(&2, U32, b), k)
    case Some{tk}:
      Unit

law ts_cons:
  for +h: U32
  for t: List<&2, U32>
  for m: Maybe<&2, Byte.Taken>
  for j: Nat
  for ih: TS(m, t, j)
  TS(Byte.take.cons(h, m), Con{h, t}, 1n+j)

def ts_cons(h, t, m, j, ih):
  match m:
    case None{}:
      ih
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          Unit{}

law take_short:
  for +k: Nat
  for b: List<&2, U32>
  TS(Byte.take(k, b), b, k)

def take_short(k, b):
  match k:
    case 0n:
      Unit{}
    case 1n+(+j):
      match b:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          ts_cons(h, t, Byte.take(j, t), j, take_short(j, t))


# ---- Chunks ----

def CB(c: Chunked.ChunkResult, input: List<&2, U32>, +l: Limits.Limits, t: U32) -> Data:
  match c:
    case Chunked.ChunkNeedMore{}:
      MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
    case other:
      Unit

law cb_cons:
  for data: List<&2, U32>
  for c: Chunked.ChunkResult
  for -input: List<&2, U32>
  for -l: Limits.Limits
  for -t: U32
  for h: CB(c, input, l, t)
  CB(Chunked.chunk.cons(data, c), input, l, t)

def cb_cons(data, c, input, l, t, h):
  match c:
    case Chunked.ChunkNeedMore{}:
      h
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, r}:
      Unit{}

# Moving a bound from the rest of the input to the whole of it
law cb_lift:
  for c: Chunked.ChunkResult
  for -t2: List<&2, U32>
  for -input: List<&2, U32>
  for -l: Limits.Limits
  for -t: U32
  for -t3: U32
  for step: MNat.le(List.length(&2, U32, t2), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t3)))) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hc: CB(c, t2, l, t3)
  CB(c, input, l, t)

def cb_lift(c, t2, input, l, t, t3, step, hc):
  match c:
    case Chunked.ChunkNeedMore{}:
      step(hc)
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, r}:
      Unit{}

law cb_ccr:
  for x: Bool
  for data: List<&2, U32>
  for -input: List<&2, U32>
  for -l: Limits.Limits
  for -t: U32
  for hp: MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  CB(Chunked.chunk.cons(data, Chunked.chunk.cr(x)), input, l, t)

def cb_ccr(x, data, input, l, t, hp):
  match x:
    case True{}:
      hp
    case False{}:
      Unit{}

law cb_clf:
  for f: Bool
  for data: List<&2, U32>
  for kk: Unit -> Chunked.ChunkResult
  for -t2: List<&2, U32>
  for -input: List<&2, U32>
  for -l: Limits.Limits
  for -t: U32
  for -t3: U32
  for step: MNat.le(List.length(&2, U32, t2), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t3)))) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hc: CB(kk(Unit{}), t2, l, t3)
  CB(Chunked.chunk.cons(data, Chunked.chunk.lf(f, kk)), input, l, t)

def cb_clf(f, data, kk, t2, input, l, t, t3, step, hc):
  match f:
    case True{}:
      +c = kk(Unit{})
      cb_cons(data, c, input, l, t, cb_lift(c, t2, input, l, t, t3, step, hc))
    case False{}:
      Unit{}

# After the data: wait for CRLF, or go on to the next chunk
law cb_crlf:
  for data: List<&2, U32>
  for r: List<&2, U32>
  for k: List<&2, U32> -> Chunked.ChunkResult
  for -input: List<&2, U32>
  for -rest: List<&2, U32>
  for +l: Limits.Limits
  for -t: U32
  for -t3: U32
  for +x: Nat
  for +elen: {List.length(&2, U32, rest) == Nat.add(x, List.length(&2, U32, r)) : Nat}
  for hp: MNat.le(List.length(&2, U32, rest), 1n+x) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hs: @t2: List<&2, U32> -> {List.length(&2, U32, rest) == Nat.add(x, 1n+1n+List.length(&2, U32, t2)) : Nat} -> MNat.le(List.length(&2, U32, t2), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t3)))) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hf: @t2: List<&2, U32> -> {List.length(&2, U32, rest) == Nat.add(x, 1n+1n+List.length(&2, U32, t2)) : Nat} -> CB(k(t2), t2, l, t3)
  CB(Chunked.chunk.cons(data, Chunked.chunk.crlf(r, k)), input, l, t)

def cb_crlf(data, r, k, input, rest, l, t, t3, x, elen, hp, hs, hf):
  match r:
    case Nil{}:
      hp(A.eq_le(List.length(&2, U32, rest), x, 1n+x,
        Equal.trans(Nat, List.length(&2, U32, rest), Nat.add(x, 0n), x, elen, MNat.add_zero(x)), MNat.le_succ(x)))
    case Con{+a, t1}:
      match t1:
        case Nil{}:
          cb_ccr(U32.is_eq(a, 13), data, input, l, t,
            hp(A.eq_le(List.length(&2, U32, rest), 1n+x, 1n+x,
              Equal.trans(Nat, List.length(&2, U32, rest), Nat.add(x, 1n), 1n+x, elen, A.add_one(x)), MNat.le_refl(1n+x))))
        case Con{+b, +t2}:
          cb_clf(U32.is_eq(a, 13) && U32.is_eq(b, 10), data, u => k(t2), t2, input, l, t, t3, hs(t2)(elen), hf(t2)(elen))

law cb_data:
  for m: Maybe<&2, Byte.Taken>
  for k: List<&2, U32> -> Chunked.ChunkResult
  for -input: List<&2, U32>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for -t: U32
  for -t3: U32
  for +x: Nat
  for ht: Suffix.TakeSuf(m, rest)
  for hl: FrameProof.TakeLen(m, x)
  for hsh: TS(m, rest, x)
  for hp: MNat.le(List.length(&2, U32, rest), 1n+x) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hs: @t2: List<&2, U32> -> {List.length(&2, U32, rest) == Nat.add(x, 1n+1n+List.length(&2, U32, t2)) : Nat} -> MNat.le(List.length(&2, U32, t2), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t3)))) -> MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))))
  for hf: @t2: List<&2, U32> -> {List.length(&2, U32, rest) == Nat.add(x, 1n+1n+List.length(&2, U32, t2)) : Nat} -> CB(k(t2), t2, l, t3)
  CB(Chunked.chunk.data(m, k), input, l, t)

def cb_data(m, k, input, rest, l, t, t3, x, ht, hl, hsh, hp, hs, hf):
  match m:
    case None{}:
      hp(MNat.le_trans(List.length(&2, U32, rest), x, 1n+x, MNat.le_of_lt(List.length(&2, U32, rest), x, hsh), MNat.le_succ(x)))
    case Some{tk}:
      match tk:
        case Byte.Taken{+data, +r}:
          cb_crlf(data, r, k, input, rest, l, t, t3, x,
              Equal.trans(Nat, List.length(&2, U32, rest), Nat.add(List.length(&2, U32, data), List.length(&2, U32, r)), Nat.add(x, List.length(&2, U32, r)),
                Equal.trans(Nat, List.length(&2, U32, rest), List.length(&2, U32, List.append(&2, U32, data, r)), Nat.add(List.length(&2, U32, data), List.length(&2, U32, r)),
                  Equal.cong(List<&2, U32>, Nat, y => List.length(&2, U32, y), rest, List.append(&2, U32, data, r), ht),
                  MList.length_append(&2, U32, data, r)),
                Equal.cong(Nat, Nat, u => Nat.add(u, List.length(&2, U32, r)), List.length(&2, U32, data), x, hl)),
              hp, hs, hf)

# There is always fuel for the next chunk: it is shorter than this input
law fuel_step:
  for -lin: Nat
  for +ll: Nat
  for -lr: Nat
  for +lt2: Nat
  for +x: Nat
  for +nf: Nat
  for eb: {lin == Nat.add(ll, 1n+1n+lr) : Nat}
  for elr: {lr == Nat.add(x, 1n+1n+lt2) : Nat}
  for hf: MNat.le(lin, nf)
  MNat.le(1n+lt2, nf)

def fuel_step(lin, ll, lr, lt2, x, nf, eb, elr, hf):
  +a = Nat.add(x, 1n+1n+lt2)
  MNat.le_trans(1n+lt2, Nat.add(ll, 1n+1n+a), nf,
    MNat.le_trans(1n+lt2, a, Nat.add(ll, 1n+1n+a),
      MNat.le_trans(1n+lt2, 1n+1n+lt2, a, MNat.le_succ(1n+lt2), A.le_addl(1n+1n+lt2, x)),
      MNat.le_trans(a, 1n+1n+a, Nat.add(ll, 1n+1n+a), MNat.le_trans(a, 1n+a, 1n+1n+a, MNat.le_succ(a), MNat.le_succ(1n+a)), A.le_addl(1n+1n+a, ll))),
    A.eq_le(Nat.add(ll, 1n+1n+a), lin, nf,
      Equal.sym(Nat, lin, Nat.add(ll, 1n+1n+a), Equal.trans(Nat, lin, Nat.add(ll, 1n+1n+lr), Nat.add(ll, 1n+1n+a), eb,
        Equal.cong(Nat, Nat, u => Nat.add(ll, 1n+1n+u), lr, a, elr))),
      hf))

# The running total plus this chunk still fits the body limit
law hsum:
  for +l: Limits.Limits
  for +t: U32
  for +n: U32
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +hn: MNat.le(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)))
  MNat.le(Nat.add(U32.to_nat(t), U32.to_nat(n)), Bn(l))

def hsum(l, t, n, ht, hn):
  +db = Kit.u32_sub_nat(Limits.body(l), t, ht)
  +sb = Nat.sub(Bn(l), U32.to_nat(t))
  A.le_eq(Nat.add(U32.to_nat(t), U32.to_nat(n)), Nat.add(U32.to_nat(t), sb), Bn(l),
    MNat.add_le_add_left(U32.to_nat(n), sb, U32.to_nat(t), A.le_eq(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)), sb, hn, db)),
    Equal.trans(Nat, Nat.add(U32.to_nat(t), sb), Nat.add(sb, U32.to_nat(t)), Bn(l), MNat.add_comm(U32.to_nat(t), sb), MNat.sub_add_cancel(Bn(l), U32.to_nat(t), ht)))

law et3:
  for +l: Limits.Limits
  for +t: U32
  for +n: U32
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +hn: MNat.le(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)))
  {U32.to_nat(U32.add(t, n)) == Nat.add(U32.to_nat(t), U32.to_nat(n)) : Nat}

def et3(l, t, n, ht, hn):
  Kit.u32_add_nat(t, n, MNat.lt_of_le_of_lt(Nat.add(U32.to_nat(t), U32.to_nat(n)), U32.to_nat(Limits.body(l)), Kit.pow2(32n), hsum(l, t, n, ht, hn), Kit.u32_to_nat_lt(Limits.body(l))))

law ht3:
  for +l: Limits.Limits
  for +t: U32
  for +n: U32
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +hn: MNat.le(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)))
  MNat.le(U32.to_nat(U32.add(t, n)), Bn(l))

def ht3(l, t, n, ht, hn):
  A.eq_le(U32.to_nat(U32.add(t, n)), Nat.add(U32.to_nat(t), U32.to_nat(n)), Bn(l), et3(l, t, n, ht, hn), hsum(l, t, n, ht, hn))

# What's left of the body before this chunk = the chunk + what's left after it
law d_split:
  for +l: Limits.Limits
  for +t: U32
  for +n: U32
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +hn: MNat.le(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)))
  {U32.to_nat(U32.sub(Limits.body(l), t)) == Nat.add(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n)))) : Nat}

def d_split(l, t, n, ht, hn):
  +sb = Nat.sub(Bn(l), U32.to_nat(t))
  +db = Kit.u32_sub_nat(Limits.body(l), t, ht)
  +hn2 = A.le_eq(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), t)), sb, hn, db)
  +d2 = Equal.trans(Nat, U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n))), Nat.sub(Bn(l), U32.to_nat(U32.add(t, n))), Nat.sub(sb, U32.to_nat(n)),
    Kit.u32_sub_nat(Limits.body(l), U32.add(t, n), ht3(l, t, n, ht, hn)),
    Equal.trans(Nat, Nat.sub(Bn(l), U32.to_nat(U32.add(t, n))), Nat.sub(Bn(l), Nat.add(U32.to_nat(t), U32.to_nat(n))), Nat.sub(sb, U32.to_nat(n)),
      Equal.cong(Nat, Nat, u => Nat.sub(Bn(l), u), U32.to_nat(U32.add(t, n)), Nat.add(U32.to_nat(t), U32.to_nat(n)), et3(l, t, n, ht, hn)),
      Equal.sym(Nat, Nat.sub(sb, U32.to_nat(n)), Nat.sub(Bn(l), Nat.add(U32.to_nat(t), U32.to_nat(n))), MNat.sub_sub(Bn(l), U32.to_nat(t), U32.to_nat(n)))))
  Equal.trans(Nat, U32.to_nat(U32.sub(Limits.body(l), t)), sb, Nat.add(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n)))), db,
    Equal.trans(Nat, sb, Nat.add(Nat.sub(sb, U32.to_nat(n)), U32.to_nat(n)), Nat.add(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n)))),
      Equal.sym(Nat, Nat.add(Nat.sub(sb, U32.to_nat(n)), U32.to_nat(n)), sb, MNat.sub_add_cancel(sb, U32.to_nat(n), hn2)),
      Equal.trans(Nat, Nat.add(Nat.sub(sb, U32.to_nat(n)), U32.to_nat(n)), Nat.add(U32.to_nat(n), Nat.sub(sb, U32.to_nat(n))), Nat.add(U32.to_nat(n), U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n)))),
        MNat.add_comm(Nat.sub(sb, U32.to_nat(n)), U32.to_nat(n)),
        Equal.cong(Nat, Nat, u => Nat.add(U32.to_nat(n), u), Nat.sub(sb, U32.to_nat(n)), U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n))),
          Equal.sym(Nat, U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n))), Nat.sub(sb, U32.to_nat(n)), d2)))))

law cb_fits:
  for f: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for +input: List<&2, U32>
  for +l: Limits.Limits
  for +t: U32
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for ef: {f == U32.is_le(n, U32.sub(Limits.body(l), t)) : Bool}
  for hz: {U32.is_zero(n) == False{} : Bool}
  for +ll: Nat
  for +eb: {List.length(&2, U32, input) == Nat.add(ll, 1n+1n+List.length(&2, U32, rest)) : Nat}
  for +hll: MNat.le(ll, SB(l))
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +nf: Nat
  for +hfu: MNat.le(List.length(&2, U32, input), nf)
  for ih: @x: List<&2, U32> -> @s: U32 -> MNat.le(U32.to_nat(s), Bn(l)) -> MNat.le(1n+List.length(&2, U32, x), nf) -> CB(k(x)(s), x, l, s)
  CB(Chunked.chunk.fits(f, n, rest, r2 => k(r2)(U32.add(t, n))), input, l, t)

def cb_fits(f, n, rest, input, l, t, k, ef, hz, ll, eb, hll, ht, nf, hfu, ih):
  match f:
    case True{}:
      +hn = A.u32_le(n, U32.sub(Limits.body(l), t), Equal.sym(Bool, True{}, U32.is_le(n, U32.sub(Limits.body(l), t)), ef))
      +hx = A.u32_pos(n, hz)
      +ed = d_split(l, t, n, ht, hn)
      +h3 = ht3(l, t, n, ht, hn)
      +d = U32.to_nat(U32.sub(Limits.body(l), t))
      +d2 = U32.to_nat(U32.sub(Limits.body(l), U32.add(t, n)))
      cb_data(Byte.take(U32.to_nat(n), rest), r2 => k(r2)(U32.add(t, n)), input, rest, l, t, U32.add(t, n), U32.to_nat(n),
        Suffix.take_suf(U32.to_nat(n), rest), FrameProof.take_len(U32.to_nat(n), rest), take_short(U32.to_nat(n), rest),
        h => arith_partial(l, List.length(&2, U32, input), ll, List.length(&2, U32, rest), U32.to_nat(n), d, d2, eb, hll, h, hx, ed),
        t2 => e => z => arith_step(l, List.length(&2, U32, input), ll, List.length(&2, U32, rest), List.length(&2, U32, t2), U32.to_nat(n), d, d2, eb, hll, e, z, hx, ed),
        +t2 => e => ih(t2)(U32.add(t, n))(h3)(fuel_step(List.length(&2, U32, input), ll, List.length(&2, U32, rest), List.length(&2, U32, t2), U32.to_nat(n), nf, eb, e, hfu)))
    case False{}:
      Unit{}

law cb_trailers:
  for h: Head.HeadResult
  for -input: List<&2, U32>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for +t: U32
  for +ll: Nat
  for eb: {List.length(&2, U32, input) == Nat.add(ll, 1n+1n+List.length(&2, U32, rest)) : Nat}
  for hll: MNat.le(ll, SB(l))
  for hh: FB(h, rest, Limits.header_section(l))
  CB(Chunked.chunk.trailers(h), input, l, t)

def cb_trailers(h, input, rest, l, t, ll, eb, hll, hh):
  match h:
    case Head.HeadNeedMore{}:
      A.eq_le(List.length(&2, U32, input), Nat.add(ll, 1n+1n+List.length(&2, U32, rest)), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))), eb,
        MNat.le_trans(Nat.add(ll, 1n+1n+List.length(&2, U32, rest)), Parse.chunk_bound(l, 0n), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))),
          A.le_add2(ll, SB(l), 1n+1n+List.length(&2, U32, rest), 1n+1n+1n+HSn(l), hll,
            MNat.succ_le_succ(1n+List.length(&2, U32, rest), 1n+1n+HSn(l), MNat.succ_le_succ(List.length(&2, U32, rest), 1n+HSn(l), hh))),
          psi_ge_k(l, U32.to_nat(U32.sub(Limits.body(l), t)))))
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, r}:
      Unit{}

law tb:
  for +l: Limits.Limits
  for +rest: List<&2, U32>
  FB(Head.trailers(l, rest), rest, Limits.header_section(l))

def tb(l, rest):
  match l:
    case Limits.Limits{rl, +fl, +hs, nf, b, ce}:
      fb_fields(U32.to_nat(nf), rest, hs, fl, False{}, Req.RequestLine{Nil{}, Req.Asterisk{}, Req.Http11{}})

law cb_zero:
  for z: Bool
  for +n: U32
  for +rest: List<&2, U32>
  for +input: List<&2, U32>
  for +l: Limits.Limits
  for +t: U32
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for ez: {z == U32.is_zero(n) : Bool}
  for +ll: Nat
  for +eb: {List.length(&2, U32, input) == Nat.add(ll, 1n+1n+List.length(&2, U32, rest)) : Nat}
  for +hll: MNat.le(ll, SB(l))
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +nf: Nat
  for +hfu: MNat.le(List.length(&2, U32, input), nf)
  for ih: @x: List<&2, U32> -> @s: U32 -> MNat.le(U32.to_nat(s), Bn(l)) -> MNat.le(1n+List.length(&2, U32, x), nf) -> CB(k(x)(s), x, l, s)
  CB(Chunked.chunk.zero(z, n, rest, t, l, k), input, l, t)

def cb_zero(z, n, rest, input, l, t, k, ez, ll, eb, hll, ht, nf, hfu, ih):
  match z:
    case True{}:
      cb_trailers(Head.trailers(l, rest), input, rest, l, t, ll, eb, hll, tb(l, rest))
    case False{}:
      cb_fits(U32.is_le(n, U32.sub(Limits.body(l), t)), n, rest, input, l, t, k, {==}, Equal.sym(Bool, False{}, U32.is_zero(n), ez),
        ll, eb, hll, ht, nf, hfu, ih)

law cb_size:
  for r: Result<&2, &2, Reason.Reason, U32>
  for +rest: List<&2, U32>
  for +input: List<&2, U32>
  for +l: Limits.Limits
  for +t: U32
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for +ll: Nat
  for +eb: {List.length(&2, U32, input) == Nat.add(ll, 1n+1n+List.length(&2, U32, rest)) : Nat}
  for +hll: MNat.le(ll, SB(l))
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +nf: Nat
  for +hfu: MNat.le(List.length(&2, U32, input), nf)
  for ih: @x: List<&2, U32> -> @s: U32 -> MNat.le(U32.to_nat(s), Bn(l)) -> MNat.le(1n+List.length(&2, U32, x), nf) -> CB(k(x)(s), x, l, s)
  CB(Chunked.chunk.size(r, rest, t, l, k), input, l, t)

def cb_size(r, rest, input, l, t, k, ll, eb, hll, ht, nf, hfu, ih):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+n}:
      cb_zero(U32.is_zero(n), n, rest, input, l, t, k, {==}, ll, eb, hll, ht, nf, hfu, ih)

law cb_long:
  for x: Bool
  for -input: List<&2, U32>
  for -l: Limits.Limits
  for -t: U32
  CB(Chunked.chunk.long(x), input, l, t)

def cb_long(x, input, l, t):
  match x:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

law cb_line:
  for scan: Lines.LineScan
  for +input: List<&2, U32>
  for +t: U32
  for +l: Limits.Limits
  for k: List<&2, U32> -> U32 -> Chunked.ChunkResult
  for +hl: LP(input, Chunked.size_budget(l), scan)
  for hs: Suffix.LS(input, scan)
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for +nf: Nat
  for +hfu: MNat.le(List.length(&2, U32, input), nf)
  for ih: @x: List<&2, U32> -> @s: U32 -> MNat.le(U32.to_nat(s), Bn(l)) -> MNat.le(1n+List.length(&2, U32, x), nf) -> CB(k(x)(s), x, l, s)
  CB(Chunked.chunk.line(scan, input, t, l, k), input, l, t)

def cb_line(scan, input, t, l, k, hl, hs, ht, nf, hfu, ih):
  match scan:
    case Lines.Partial{}:
      MNat.le_trans(List.length(&2, U32, input), 1n+SB(l), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))), hl,
        MNat.le_trans(1n+SB(l), Parse.chunk_bound(l, 0n), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t))), sb_k(l),
          psi_ge_k(l, U32.to_nat(U32.sub(Limits.body(l), t)))))
    case Lines.TooLong{}:
      cb_long(Byte.prefix_has(input, Chunked.size_budget(l), 59), input, l, t)
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+ln, +rest}:
      cb_size(Chunked.size_line(ln, Limits.chunk_ext(l)), rest, input, l, t, k, List.length(&2, U32, ln),
        A.len_line(input, ln, rest, hs), hl, ht, nf, hfu, ih)

law cb_chunks:
  for fuel: Nat
  for +input: List<&2, U32>
  for +t: U32
  for +l: Limits.Limits
  for +ht: MNat.le(U32.to_nat(t), Bn(l))
  for hf: MNat.le(1n+List.length(&2, U32, input), fuel)
  CB(Chunked.chunks(fuel, input, t, l), input, l, t)

def cb_chunks(fuel, input, t, l, ht, hf):
  match fuel:
    case 0n:
      Logic.absurd(MNat.le(List.length(&2, U32, input), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), t)))), Logic.true_ne_false(hf))
    case 1n+(+nf):
      cb_line(Lines.next_line(input, Chunked.size_budget(l)), input, t, l, r => s => Chunked.chunks(nf, r, s, l),
        lp(input, Chunked.size_budget(l)), Suffix.nl(input, Chunked.size_budget(l)), ht, nf, hf,
        r => s => hs => hfu => cb_chunks(nf, r, s, l, hs, hfu))


# ---- An accepted Content-Length is within the body limit ----

def FLn(r: Result<&2, &2, Reason.Reason, Framing.Framing>, lim: U32) -> Data:
  match r:
    case Fail{e}:
      Unit
    case Done{fr}:
      match fr:
        case Framing.Length{n}:
          MNat.le(U32.to_nat(n), U32.to_nat(lim))
        case other:
          Unit

law fl_limit:
  for k: Bool
  for +n: U32
  for +lim: U32
  for ek: {k == U32.is_le(n, lim) : Bool}
  FLn(Framing.cl.limit(k, n), lim)

def fl_limit(k, n, lim, ek):
  match k:
    case True{}:
      A.u32_le(n, lim, Equal.sym(Bool, True{}, U32.is_le(n, lim), ek))
    case False{}:
      Unit{}

law fl_parsed:
  for m: Maybe<&2, U32>
  for +lim: U32
  FLn(Framing.cl.parsed(m, lim), lim)

def fl_parsed(m, lim):
  match m:
    case None{}:
      Unit{}
    case Some{+n}:
      fl_limit(U32.is_le(n, lim), n, lim, {==})

law fl_valid:
  for k: Bool
  for v: List<&2, U32>
  for +lim: U32
  FLn(Framing.cl.valid(k, v, lim), lim)

def fl_valid(k, v, lim):
  match k:
    case True{}:
      fl_parsed(Framing.digits(v), lim)
    case False{}:
      Unit{}

law fl_list:
  for k: Bool
  for +v: List<&2, U32>
  for +lim: U32
  FLn(Framing.cl.list(k, v, lim), lim)

def fl_list(k, v, lim):
  match k:
    case True{}:
      Unit{}
    case False{}:
      fl_valid(Framing.cl_valid(v), v, lim)

law fl_cl:
  for vs: List<&2, List<&2, U32>>
  for +lim: U32
  FLn(Framing.cl(vs, lim), lim)

def fl_cl(vs, lim):
  match vs:
    case Nil{}:
      Unit{}
    case Con{+v, rest}:
      match rest:
        case Nil{}:
          fl_list(UrlByte.has_byte(v, 44), v, lim)
        case Con{w, r}:
          Unit{}

law fl_final:
  for last: Bool
  for one: Bool
  for any: Bool
  for idn: Bool
  for lim: U32
  FLn(Framing.te.final(last, one, any, idn), lim)

def fl_final(last, one, any, idn, lim):
  match last:
    case True{}:
      match one:
        case True{}:
          Unit{}
        case False{}:
          Unit{}
    case False{}:
      match any:
        case True{}:
          Unit{}
        case False{}:
          match idn:
            case True{}:
              Unit{}
            case False{}:
              Unit{}

law fl_members:
  for bad: Bool
  for twice: Bool
  for +ms: List<&2, List<&2, U32>>
  for lim: U32
  FLn(Framing.te.members(bad, twice, ms), lim)

def fl_members(bad, twice, ms, lim):
  match bad:
    case True{}:
      Unit{}
    case False{}:
      match twice:
        case True{}:
          Unit{}
        case False{}:
          fl_final(Framing.last_is_chunked(ms), Nat.is_eq(List.length(&2, List<&2, U32>, ms), 1n), Nat.is_eq(Framing.count_chunked(ms), 1n),
            Byte.eq(Byte.lower_all(List.concat(&2, U32, ms)), Path.bytes("identity")) && Nat.is_eq(List.length(&2, List<&2, U32>, ms), 1n), lim)

law fl_te:
  for vs: List<&2, List<&2, U32>>
  for lim: U32
  FLn(Framing.te(vs), lim)

def fl_te(vs, lim):
  match vs:
    case Nil{}:
      Unit{}
    case Con{+v, rest}:
      match rest:
        case Nil{}:
          fl_members(Framing.te.bad(Framing.trim_all(Byte.split_on(v, 44))), Nat.is_le(2n, Framing.count_chunked(Framing.trim_all(Byte.split_on(v, 44)))),
            Framing.trim_all(Byte.split_on(v, 44)), lim)
        case Con{w, r}:
          Unit{}

law fl_go:
  for k: Bool
  for te: Bool
  for v: Req.Version
  for vs: List<&2, List<&2, U32>>
  for tes: List<&2, List<&2, U32>>
  for +lim: U32
  FLn(Framing.framing.go(k, te, v, vs, tes, lim), lim)

def fl_go(k, te, v, vs, tes, lim):
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
              fl_te(tes, lim)
        case False{}:
          fl_cl(vs, lim)

law fl:
  for v: Req.Version
  for +fs: List<&2, Req.Field>
  for +lim: U32
  FLn(Framing.framing(v, fs, lim), lim)

def fl(v, fs, lim):
  fl_go(Framing.both_framing(fs), Framing.has_field(fs, Path.bytes("transfer-encoding")), v,
    Framing.named(fs, Path.bytes("content-length")), Framing.named(fs, Path.bytes("transfer-encoding")), lim)


# ---- Parse ----

def PB(o: Parse.Outcome, i: List<&2, U32>, +l: Limits.Limits) -> Data:
  match o:
    case Parse.NeedMore{c}:
      MNat.le(List.length(&2, U32, i), Parse.max_request(l))
    case other:
      Unit

law final_bound:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  for +rest: List<&2, U32>
  for +y: Nat
  for hh: MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)))
  for hr: MNat.le(List.length(&2, U32, rest), y)
  for hy: MNat.le(y, Nat.add(Bn(l), Parse.chunk_bound(l, Bn(l))))
  MNat.le(List.length(&2, U32, i), Parse.max_request(l))

def final_bound(l, i, rest, y, hh, hr, hy):
  +z = {Nat.add(Bn(l), Parse.chunk_bound(l, Bn(l))) : Nat}
  +top = {1n+1n+Nat.add(HSn(l), 1n+1n+z) : Nat}
  MNat.le_trans(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)), Parse.max_request(l), hh,
    MNat.le_trans(1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)), top, Parse.max_request(l),
      MNat.succ_le_succ(1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)), 1n+Nat.add(HSn(l), 1n+1n+z),
        MNat.succ_le_succ(Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)), Nat.add(HSn(l), 1n+1n+z),
          MNat.add_le_add_left(1n+1n+List.length(&2, U32, rest), 1n+1n+z, HSn(l),
            MNat.succ_le_succ(1n+List.length(&2, U32, rest), 1n+z,
              MNat.succ_le_succ(List.length(&2, U32, rest), z, MNat.le_trans(List.length(&2, U32, rest), y, z, hr, hy)))))),
      A.le_addl(top, 1n+1n+1n+Nat.add(U32.to_nat(Limits.request_line(l)), HSn(l)))))

law pb_body:
  for m: Maybe<&2, Byte.Taken>
  for mt: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for +i: List<&2, U32>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for +n: U32
  for hh: MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)))
  for hs: TS(m, rest, U32.to_nat(n))
  for hn: MNat.le(U32.to_nat(n), Bn(l))
  PB(Parse.parse.body(m, mt, t, v, fs, cont), i, l)

def pb_body(m, mt, t, v, fs, cont, i, rest, l, n, hh, hs, hn):
  match m:
    case None{}:
      final_bound(l, i, rest, Bn(l), hh,
        MNat.le_trans(List.length(&2, U32, rest), U32.to_nat(n), Bn(l), MNat.le_of_lt(List.length(&2, U32, rest), U32.to_nat(n), hs), hn),
        MNat.le_add_right(Bn(l), Parse.chunk_bound(l, Bn(l))))
    case Some{tk}:
      match tk:
        case Byte.Taken{a, b}:
          Unit{}

law sub0:
  for +l: Limits.Limits
  {U32.to_nat(U32.sub(Limits.body(l), 0)) == Bn(l) : Nat}

def sub0(l):
  Equal.trans(Nat, U32.to_nat(U32.sub(Limits.body(l), 0)), Nat.sub(Bn(l), 0n), Bn(l),
    Kit.u32_sub_nat(Limits.body(l), 0, MNat.zero_le(Bn(l))), MNat.sub_zero(Bn(l)))

law pb_chunked:
  for c: Chunked.ChunkResult
  for mt: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for cont: Bool
  for +i: List<&2, U32>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for hh: MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)))
  for hc: CB(c, rest, l, 0)
  PB(Parse.parse.chunked(c, mt, t, v, fs, cont), i, l)

def pb_chunked(c, mt, t, v, fs, cont, i, rest, l, hh, hc):
  match c:
    case Chunked.ChunkNeedMore{}:
      final_bound(l, i, rest, Parse.chunk_bound(l, Bn(l)), hh,
        A.le_eq(List.length(&2, U32, rest), Parse.chunk_bound(l, U32.to_nat(U32.sub(Limits.body(l), 0))), Parse.chunk_bound(l, Bn(l)), hc,
          Equal.cong(Nat, Nat, u => Parse.chunk_bound(l, u), U32.to_nat(U32.sub(Limits.body(l), 0)), Bn(l), sub0(l))),
        A.le_addl(Parse.chunk_bound(l, Bn(l)), Bn(l)))
    case Chunked.ChunkRejected{e}:
      Unit{}
    case Chunked.ChunkDone{b, r}:
      Unit{}

law pb_frame:
  for r: Result<&2, &2, Reason.Reason, Framing.Framing>
  for mt: List<&2, U32>
  for t: Req.Target
  for v: Req.Version
  for fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for cont: Bool
  for +i: List<&2, U32>
  for hh: MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)))
  for hfl: FLn(r, Limits.body(l))
  PB(Parse.parse.frame(r, mt, t, v, fs, rest, l, cont), i, l)

def pb_frame(r, mt, t, v, fs, rest, l, cont, i, hh, hfl):
  match r:
    case Fail{e}:
      Unit{}
    case Done{fr}:
      match fr:
        case Framing.NoBody{}:
          Unit{}
        case Framing.Length{+n}:
          pb_body(Byte.take(U32.to_nat(n), rest), mt, t, v, fs, cont, i, rest, l, n, hh, take_short(U32.to_nat(n), rest), hfl)
        case Framing.Chunked{}:
          pb_chunked(Chunked.read(l, rest), mt, t, v, fs, cont, i, rest, l, hh,
            cb_chunks(1n+List.length(&2, U32, rest), rest, 0, l, MNat.zero_le(Bn(l)), MNat.le_refl(1n+List.length(&2, U32, rest))))

law pb_checks:
  for r: Result<&2, &2, Reason.Reason, Bool>
  for mt: List<&2, U32>
  for t: Req.Target
  for +v: Req.Version
  for +fs: List<&2, Req.Field>
  for +rest: List<&2, U32>
  for +l: Limits.Limits
  for +i: List<&2, U32>
  for hh: MNat.le(List.length(&2, U32, i), 1n+1n+Nat.add(HSn(l), 1n+1n+List.length(&2, U32, rest)))
  PB(Parse.parse.checks(r, mt, t, v, fs, rest, l), i, l)

def pb_checks(r, mt, t, v, fs, rest, l, i, hh):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+cont}:
      pb_frame(Framing.framing(v, fs, Limits.body(l)), mt, t, v, fs, rest, l, cont, i, hh, fl(v, fs, Limits.body(l)))

law pb_head:
  for l: Limits.Limits
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for hh: HBL(h, i, l)
  PB(Parse.parse.head(h, l), i, l)

def pb_head(l, h, i, hh):
  match l:
    case Limits.Limits{+rl, +fl, +hs, +nf, +b, +ce}:
      match h:
        case Head.HeadNeedMore{}:
          MNat.le_trans(List.length(&2, U32, i), 1n+1n+1n+Nat.add(U32.to_nat(rl), U32.to_nat(hs)), Parse.max_request(Limits.Limits{rl, fl, hs, nf, b, ce}), hh,
            MNat.le_add_right(1n+1n+1n+Nat.add(U32.to_nat(rl), U32.to_nat(hs)),
              1n+1n+Nat.add(U32.to_nat(hs), 1n+1n+Nat.add(U32.to_nat(b), Parse.chunk_bound(Limits.Limits{rl, fl, hs, nf, b, ce}, U32.to_nat(b))))))
        case Head.HeadRejected{e}:
          Unit{}
        case Head.HeadParsed{rq, +fs, +rest}:
          match rq:
            case Req.RequestLine{mt, +t, +v}:
              pb_checks(Host.checks(v, t, fs), mt, t, v, fs, rest, Limits.Limits{rl, fl, hs, nf, b, ce}, i, hh)

# parse never says "need more" for more input than max_request
law pb_parse:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  PB(Parse.parse(l, i), i, l)

def pb_parse(l, i):
  pb_head(l, Head.head(l, i), i, hb_head(l, i))

law nm_false:
  for o: Parse.Outcome
  for +i: List<&2, U32>
  for +l: Limits.Limits
  for hb: PB(o, i, l)
  for hl: MNat.lt(Parse.max_request(l), List.length(&2, U32, i))
  {Parse.is_need_more(o) == False{} : Bool}

def nm_false(o, i, l, hb, hl):
  match o:
    case Parse.NeedMore{c}:
      Logic.absurd({True{} == False{} : Bool}, A.lt_le_absurd(Parse.max_request(l), List.length(&2, U32, i), hl, hb))
    case Parse.Rejected{x}:
      {==}
    case Parse.Parsed{r, rest}:
      {==}
