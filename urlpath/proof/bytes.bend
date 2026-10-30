# Facts about single bytes and hex digits. A U32 that is at most 255 is one of
# 256 values, so some facts are checked by computing them for every value.

import Base
import ../src/bytes.bend as Byte
import bend-mathlib@0.7.4.0/string.bend as MStr
import bend-kit-lemmas@0.1.1.0/lemmas.bend as Kit
import ./logic.bend as Logic


# What we need from a digit render writes: uppercase hex, not "/", a byte
def dig_ok(+d: U32) -> Bool:
  Bool.and(Byte.is_upper_hex(d), Bool.and(Bool.not(U32.is_eq(d, 47)), U32.is_le(d, 255)))

def all_dig(tbl: List<&2, U32>) -> Bool:
  match tbl:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(dig_ok(d), all_dig(rest))

law hdg_at:
  for k: Bool
  for d: U32
  for o: U32
  for hd: {dig_ok(d) == True{} : Bool}
  for ho: {dig_ok(o) == True{} : Bool}
  {dig_ok(Byte.hex_digit.if(k, d, o)) == True{} : Bool}

def hdg_at(k, d, o, hd, ho):
  match k:
    case True{}:
      hd
    case False{}:
      ho

law hdg:
  for tbl: List<&2, U32>
  for +n: U32
  for +i: U32
  for +h: {all_dig(tbl) == True{} : Bool}
  {dig_ok(Byte.hex_digit.go(tbl, n, i)) == True{} : Bool}

def hdg(tbl, n, i, h):
  match tbl:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      hdg_at(U32.is_eq(n, i), d, Byte.hex_digit.go(rest, n, U32.inc(i)),
        Logic.and_left(dig_ok(d), all_dig(rest), h),
        hdg(rest, n, U32.inc(i), Logic.and_right(dig_ok(d), all_dig(rest), h)))

# Every digit render writes is fine, whatever n is
law hd_ok:
  for +n: U32
  {dig_ok(Byte.hex_digit(n)) == True{} : Bool}

def hd_ok(n):
  hdg(Byte.hex_digits(), n, 0, {==})

law hd_upper:
  for +n: U32
  {Byte.is_upper_hex(Byte.hex_digit(n)) == True{} : Bool}

def hd_upper(n):
  Logic.and_left(Byte.is_upper_hex(Byte.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Byte.hex_digit(n), 47)), U32.is_le(Byte.hex_digit(n), 255)), hd_ok(n))

law hd_not_slash:
  for +n: U32
  {Bool.not(U32.is_eq(Byte.hex_digit(n), 47)) == True{} : Bool}

def hd_not_slash(n):
  Logic.and_left(Bool.not(U32.is_eq(Byte.hex_digit(n), 47)), U32.is_le(Byte.hex_digit(n), 255),
    Logic.and_right(Byte.is_upper_hex(Byte.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Byte.hex_digit(n), 47)), U32.is_le(Byte.hex_digit(n), 255)), hd_ok(n)))

law hd_byte:
  for +n: U32
  {U32.is_le(Byte.hex_digit(n), 255) == True{} : Bool}

def hd_byte(n):
  Logic.and_right(Bool.not(U32.is_eq(Byte.hex_digit(n), 47)), U32.is_le(Byte.hex_digit(n), 255),
    Logic.and_right(Byte.is_upper_hex(Byte.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Byte.hex_digit(n), 47)), U32.is_le(Byte.hex_digit(n), 255)), hd_ok(n)))

# A pchar byte is never "/"
law pns_at:
  for k: Bool
  for +c: U32
  for ek: {k == U32.is_eq(c, 47) : Bool}
  for h: {Byte.is_pchar(c) == True{} : Bool}
  {k == False{} : Bool}

def pns_at(k, c, ek, h):
  match k:
    case True{}:
      e = MStr.u32_eq_of_is_eq(c, 47, Equal.sym(Bool, True{}, U32.is_eq(c, 47), ek))
      hp = Equal.trans(Bool, Byte.is_pchar(47), Byte.is_pchar(c), True{},
        Equal.cong(U32, Bool, +x => Byte.is_pchar(x), 47, c, Equal.sym(U32, c, 47, e)), h)
      Logic.absurd({True{} == False{} : Bool}, Logic.true_ne_false(hp))
    case False{}:
      {==}

law pns:
  for +c: U32
  for h: {Byte.is_pchar(c) == True{} : Bool}
  {U32.is_eq(c, 47) == False{} : Bool}

def pns(c, h):
  pns_at(U32.is_eq(c, 47), c, {==}, h)

# The %XX round trip for byte c: both digits are hex and decode back to c
def rt(+c: U32) -> Bool:
  Bool.and(Byte.is_hex(Byte.hex_digit(Byte.hi_nibble(c))),
    Bool.and(Byte.is_hex(Byte.hex_digit(Byte.lo_nibble(c))),
      U32.is_eq(Byte.hex_pair(Byte.hex_val(Byte.hex_digit(Byte.hi_nibble(c))), Byte.hex_val(Byte.hex_digit(Byte.lo_nibble(c)))), c)))

# Which fact to check
type Chk is Data:
  RoundTrip{}
  HexSmall{}
  PairByte{hi: U32}

def chk(c: Chk, +x: U32) -> Bool:
  match c:
    case RoundTrip{}:
      rt(x)
    case HexSmall{}:
      Bool.or(Bool.not(Byte.is_hex(x)), U32.is_le(Byte.hex_val(x), 15))
    case PairByte{+hi}:
      U32.is_le(Byte.hex_pair(hi, x), 255)

# Check values k, k+1, ..., k+d
def chk_all(+c: Chk, d: Nat, +k: Nat) -> Bool:
  match d:
    case 0n:
      chk(c, U32.from_nat(k))
    case 1n+p:
      Bool.and(chk(c, U32.from_nat(k)), chk_all(c, p, 1n+k))

# j + k, counted so that it matches chk_all's steps
def addr(j: Nat, k: Nat) -> Nat:
  match j:
    case 0n:
      k
    case 1n+p:
      addr(p, 1n+k)

law addr_succ:
  for j: Nat
  for k: Nat
  {addr(j, 1n+k) == 1n+addr(j, k) : Nat}

def addr_succ(j, k):
  match j:
    case 0n:
      {==}
    case 1n+p:
      addr_succ(p, 1n+k)

law addr_zero:
  for +m: Nat
  {addr(m, 0n) == m : Nat}

def addr_zero(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, addr(p, 1n), 1n+addr(p, 0n), 1n+p, addr_succ(p, 0n),
        Equal.cong(Nat, Nat, x => 1n+x, addr(p, 0n), p, addr_zero(p)))

law chk_ext:
  for +c: Chk
  for +d: Nat
  for +k: Nat
  for j: Nat
  for +h: {chk_all(c, d, k) == True{} : Bool}
  for hj: {Nat.is_le(j, d) == True{} : Bool}
  {chk(c, U32.from_nat(addr(j, k))) == True{} : Bool}

def chk_ext(c, d, k, j, h, hj):
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+q:
          Logic.absurd({chk(c, U32.from_nat(addr(1n+q, k))) == True{} : Bool}, Logic.true_ne_false(hj))
    case 1n+(+p):
      match j:
        case 0n:
          Logic.and_left(chk(c, U32.from_nat(k)), chk_all(c, p, 1n+k), h)
        case 1n+q:
          chk_ext(c, p, 1n+k, q, Logic.and_right(chk(c, U32.from_nat(k)), chk_all(c, p, 1n+k), h), hj)

# From "checked for 0..d" to the fact for one U32 x with value <= d
law chk_u32:
  for +c: Chk
  for +x: U32
  for d: Nat
  for hx: {Nat.is_le(U32.to_nat(x), d) == True{} : Bool}
  for h: {chk_all(c, d, 0n) == True{} : Bool}
  {chk(c, x) == True{} : Bool}

def chk_u32(c, x, d, hx, h):
  ft = Kit.u32_from_to_nat(x)
  %ft : {chk(c, _) == True{} : Bool}
  az = addr_zero(U32.to_nat(x))
  %az : {chk(c, U32.from_nat(_)) == True{} : Bool}
  chk_ext(c, d, 0n, U32.to_nat(x), h, hx)

law le255:
  for +x: U32
  for hx: {U32.is_le(x, 255) == True{} : Bool}
  {Nat.is_le(U32.to_nat(x), 255n) == True{} : Bool}

def le255(x, hx):
  Equal.trans(Bool, Nat.is_le(U32.to_nat(x), 255n), U32.is_le(x, 255), True{},
    Equal.sym(Bool, U32.is_le(x, 255), Nat.is_le(U32.to_nat(x), 255n), Kit.u32_is_le_nat(x, 255)), hx)

law le15:
  for +x: U32
  for hx: {U32.is_le(x, 15) == True{} : Bool}
  {Nat.is_le(U32.to_nat(x), 15n) == True{} : Bool}

def le15(x, hx):
  Equal.trans(Bool, Nat.is_le(U32.to_nat(x), 15n), U32.is_le(x, 15), True{},
    Equal.sym(Bool, U32.is_le(x, 15), Nat.is_le(U32.to_nat(x), 15n), Kit.u32_is_le_nat(x, 15)), hx)

law all_rt:
  {chk_all(RoundTrip{}, 255n, 0n) == True{} : Bool}

def all_rt():
  {==}

law all_hex_small:
  {chk_all(HexSmall{}, 255n, 0n) == True{} : Bool}

def all_hex_small():
  {==}

# Every byte survives %XX
law byte_rt:
  for +x: U32
  for hx: {U32.is_le(x, 255) == True{} : Bool}
  {rt(x) == True{} : Bool}

def byte_rt(x, hx):
  chk_u32(RoundTrip{}, x, 255n, le255(x, hx), all_rt())

# A hex digit's value is at most 15
law hex_small:
  for +x: U32
  for hx: {U32.is_le(x, 255) == True{} : Bool}
  for hh: {Byte.is_hex(x) == True{} : Bool}
  {U32.is_le(Byte.hex_val(x), 15) == True{} : Bool}

def hex_small(x, hx, hh):
  Logic.implies(Byte.is_hex(x), U32.is_le(Byte.hex_val(x), 15),
    chk_u32(HexSmall{}, x, 255n, le255(x, hx), all_hex_small()), hh)

# Two hex digit values make a byte: checked for all 16 x 16 pairs
def pair_all(d: Nat, +k: Nat) -> Bool:
  match d:
    case 0n:
      chk_all(PairByte{U32.from_nat(k)}, 15n, 0n)
    case 1n+p:
      Bool.and(chk_all(PairByte{U32.from_nat(k)}, 15n, 0n), pair_all(p, 1n+k))

law pair_ext:
  for +d: Nat
  for +k: Nat
  for j: Nat
  for +h: {pair_all(d, k) == True{} : Bool}
  for hj: {Nat.is_le(j, d) == True{} : Bool}
  {chk_all(PairByte{U32.from_nat(addr(j, k))}, 15n, 0n) == True{} : Bool}

def pair_ext(d, k, j, h, hj):
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+q:
          Logic.absurd({chk_all(PairByte{U32.from_nat(addr(1n+q, k))}, 15n, 0n) == True{} : Bool}, Logic.true_ne_false(hj))
    case 1n+(+p):
      match j:
        case 0n:
          Logic.and_left(chk_all(PairByte{U32.from_nat(k)}, 15n, 0n), pair_all(p, 1n+k), h)
        case 1n+q:
          pair_ext(p, 1n+k, q, Logic.and_right(chk_all(PairByte{U32.from_nat(k)}, 15n, 0n), pair_all(p, 1n+k), h), hj)

law all_pairs:
  {pair_all(15n, 0n) == True{} : Bool}

def all_pairs():
  {==}

law pair_byte:
  for +hi: U32
  for +lo: U32
  for hh: {U32.is_le(hi, 15) == True{} : Bool}
  for hl: {U32.is_le(lo, 15) == True{} : Bool}
  {U32.is_le(Byte.hex_pair(hi, lo), 255) == True{} : Bool}

def pair_byte(hi, lo, hh, hl):
  ft = Kit.u32_from_to_nat(hi)
  %ft : {U32.is_le(Byte.hex_pair(_, lo), 255) == True{} : Bool}
  az = addr_zero(U32.to_nat(hi))
  %az : {U32.is_le(Byte.hex_pair(U32.from_nat(_), lo), 255) == True{} : Bool}
  chk_u32(PairByte{U32.from_nat(addr(U32.to_nat(hi), 0n))}, lo, 15n, le15(lo, hl),
    pair_ext(15n, 0n, U32.to_nat(hi), all_pairs(), le15(hi, hh)))
