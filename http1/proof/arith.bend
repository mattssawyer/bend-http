# Arithmetic used by the proof of law H9: Nat inequalities, and how the
# parser's U32 counters relate to Nat.

import Base
import ../../urlpath/proof/logic.bend as Logic
import bend-mathlib@0.7.4.0/nat.bend as MNat
import bend-mathlib@0.7.4.0/list.bend as MList
import bend-kit-lemmas@0.1.1.0/lemmas.bend as Kit
import ../src/head.bend as Head


# ---- Nat ----

law le_add2:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for h1: MNat.le(a, b)
  for h2: MNat.le(c, d)
  MNat.le(Nat.add(a, c), Nat.add(b, d))

def le_add2(a, b, c, d, h1, h2):
  MNat.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), MNat.add_le_add_right(a, b, c, h1), MNat.add_le_add_left(c, d, b, h2))

# x <= k + x
law le_addl:
  for +x: Nat
  for +k: Nat
  MNat.le(x, Nat.add(k, x))

def le_addl(x, k):
  MNat.add_le_add_right(0n, k, x, MNat.zero_le(k))

law not_succ_le:
  for b: Nat
  for h: MNat.le(1n+b, b)
  Empty

def not_succ_le(b, h):
  match b:
    case 0n:
      Logic.true_ne_false(h)
    case 1n+p:
      not_succ_le(p, h)

law lt_le_absurd:
  for +a: Nat
  for +b: Nat
  for hl: MNat.lt(a, b)
  for hb: MNat.le(b, a)
  Empty

def lt_le_absurd(a, b, hl, hb):
  not_succ_le(a, MNat.le_trans(1n+a, b, a,
    Equal.trans(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), True{}, Equal.sym(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), MNat.is_lt_eq_succ_le(a, b)), hl),
    hb))

law add_one:
  for +x: Nat
  {Nat.add(x, 1n) == 1n+x : Nat}

def add_one(x):
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, MNat.add_succ(x, 0n),
    Equal.cong(Nat, Nat, y => 1n+y, Nat.add(x, 0n), x, MNat.add_zero(x)))

# Rewrite the bound of an inequality
law le_eq:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for h: MNat.le(a, b)
  for e: {b == c : Nat}
  MNat.le(a, c)

def le_eq(a, b, c, h, e):
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

law eq_le:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for e: {a == b : Nat}
  for h: MNat.le(b, c)
  MNat.le(a, c)

def eq_le(a, b, c, e, h):
  e2 = Equal.sym(Nat, a, b, e)
  %e2 : {Nat.is_le(_, c) == True{} : Bool}
  h


# ---- U32 and Nat ----

law u32_le:
  for +a: U32
  for +b: U32
  for h: {U32.is_le(a, b) == True{} : Bool}
  MNat.le(U32.to_nat(a), U32.to_nat(b))

def u32_le(a, b, h):
  Equal.trans(Bool, Nat.is_le(U32.to_nat(a), U32.to_nat(b)), U32.is_le(a, b), True{},
    Equal.sym(Bool, U32.is_le(a, b), Nat.is_le(U32.to_nat(a), U32.to_nat(b)), Kit.u32_is_le_nat(a, b)), h)

law le_u32:
  for +a: U32
  for +b: U32
  for h: MNat.le(U32.to_nat(a), U32.to_nat(b))
  {U32.is_le(a, b) == True{} : Bool}

def le_u32(a, b, h):
  Equal.trans(Bool, U32.is_le(a, b), Nat.is_le(U32.to_nat(a), U32.to_nat(b)), True{}, Kit.u32_is_le_nat(a, b), h)

law minus_eq_at:
  for k: Bool
  for +a: U32
  for +b: U32
  for ek: {k == U32.is_le(b, a) : Bool}
  for +h: {U32.is_le(b, a) == True{} : Bool}
  {Nat.add(U32.to_nat(Head.minus.if(k, a, b)), U32.to_nat(b)) == U32.to_nat(a) : Nat}

def minus_eq_at(k, a, b, ek, h):
  match k:
    case True{}:
      es = Equal.sym(Nat, U32.to_nat(U32.sub(a, b)), Nat.sub(U32.to_nat(a), U32.to_nat(b)), Kit.u32_sub_nat(a, b, u32_le(b, a, h)))
      %es : {Nat.add(_, U32.to_nat(b)) == U32.to_nat(a) : Nat}
      MNat.sub_add_cancel(U32.to_nat(a), U32.to_nat(b), u32_le(b, a, h))
    case False{}:
      Logic.absurd({Nat.add(U32.to_nat(Head.minus.if(False{}, a, b)), U32.to_nat(b)) == U32.to_nat(a) : Nat},
        Logic.true_ne_false(Equal.trans(Bool, False{}, U32.is_le(b, a), True{}, ek, h)))

# When b fits in a, minus(a, b) + b is a
law minus_eq:
  for +a: U32
  for +b: U32
  for h: {U32.is_le(b, a) == True{} : Bool}
  {Nat.add(U32.to_nat(Head.minus(a, b)), U32.to_nat(b)) == U32.to_nat(a) : Nat}

def minus_eq(a, b, h):
  minus_eq_at(U32.is_le(b, a), a, b, {==}, h)

law minus_le_at:
  for k: Bool
  for +a: U32
  for +b: U32
  for ek: {k == U32.is_le(b, a) : Bool}
  MNat.le(U32.to_nat(Head.minus.if(k, a, b)), U32.to_nat(a))

def minus_le_at(k, a, b, ek):
  match k:
    case True{}:
      es = Equal.sym(Nat, U32.to_nat(U32.sub(a, b)), Nat.sub(U32.to_nat(a), U32.to_nat(b)),
        Kit.u32_sub_nat(a, b, u32_le(b, a, Equal.sym(Bool, True{}, U32.is_le(b, a), ek))))
      %es : {Nat.is_le(_, U32.to_nat(a)) == True{} : Bool}
      MNat.sub_le(U32.to_nat(a), U32.to_nat(b))
    case False{}:
      MNat.zero_le(U32.to_nat(a))

law minus_le:
  for +a: U32
  for +b: U32
  MNat.le(U32.to_nat(Head.minus(a, b)), U32.to_nat(a))

def minus_le(a, b):
  minus_le_at(U32.is_le(b, a), a, b, {==})

law minus_pos_at:
  for k: Bool
  for +a: U32
  for +b: U32
  for ek: {k == U32.is_le(b, a) : Bool}
  for h: MNat.le(1n, U32.to_nat(Head.minus.if(k, a, b)))
  {U32.is_le(b, a) == True{} : Bool}

def minus_pos_at(k, a, b, ek, h):
  match k:
    case True{}:
      Equal.sym(Bool, True{}, U32.is_le(b, a), ek)
    case False{}:
      Logic.absurd({U32.is_le(b, a) == True{} : Bool}, Logic.true_ne_false(h))

# If minus(a, b) is at least 1, then b fit in a
law minus_pos:
  for +a: U32
  for +b: U32
  for h: MNat.le(1n, U32.to_nat(Head.minus(a, b)))
  {U32.is_le(b, a) == True{} : Bool}

def minus_pos(a, b, h):
  minus_pos_at(U32.is_le(b, a), a, b, {==}, h)

law min_at:
  for c: Bool
  for +x: Word(32n)
  for +y: Word(32n)
  for ec: {c == U32.is_lt(U32{x}, U32{y}) : Bool}
  MNat.le(U32.to_nat(Bool.pick(U32, c, U32{x}, U32{y})), U32.to_nat(U32{y}))

def min_at(c, x, y, ec):
  match c:
    case True{}:
      MNat.le_of_lt(U32.to_nat(U32{x}), U32.to_nat(U32{y}),
        Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32{x}), U32.to_nat(U32{y})), U32.is_lt(U32{x}, U32{y}), True{},
          Equal.sym(Bool, U32.is_lt(U32{x}, U32{y}), Nat.is_lt(U32.to_nat(U32{x}), U32.to_nat(U32{y})), Kit.u32_is_lt_nat(U32{x}, U32{y})),
          Equal.sym(Bool, True{}, U32.is_lt(U32{x}, U32{y}), ec)))
    case False{}:
      MNat.le_refl(U32.to_nat(U32{y}))

law min_le:
  for a: U32
  for b: U32
  MNat.le(U32.to_nat(U32.min(a, b)), U32.to_nat(b))

def min_le(a, b):
  match a:
    case U32{+x}:
      match b:
        case U32{+y}:
          min_at(U32.is_lt(U32{x}, U32{y}), x, y, {==})

# The tail of a short list is short (built so no conversion touches 2^32)
law lt_tail:
  for +c: U32
  for +t: List<&2, U32>
  for h: MNat.lt(List.length(&2, U32, Con{c, t}), Kit.pow2(32n))
  MNat.lt(List.length(&2, U32, t), Kit.pow2(32n))

def lt_tail(c, t, h):
  MNat.lt_of_le_of_lt(List.length(&2, U32, t), List.length(&2, U32, Con{c, t}), Kit.pow2(32n), MNat.le_succ(List.length(&2, U32, t)), h)

law le_one_more:
  for +c: U32
  for +t: List<&2, U32>
  for +x: Nat
  for e: {x == List.length(&2, U32, t) : Nat}
  MNat.le(1n+x, List.length(&2, U32, Con{c, t}))

def le_one_more(c, t, x, e):
  e2 = Equal.sym(Nat, x, List.length(&2, U32, t), e)
  %e2 : {Nat.is_le(1n+_, 1n+List.length(&2, U32, t)) == True{} : Bool}
  MNat.le_refl(1n+List.length(&2, U32, t))

law inc_ok:
  for +c: U32
  for +t: List<&2, U32>
  for +ih: {U32.to_nat(Head.size(t)) == List.length(&2, U32, t) : Nat}
  for h: MNat.lt(List.length(&2, U32, Con{c, t}), Kit.pow2(32n))
  {U32.to_nat(U32.inc(Head.size(t))) == 1n+List.length(&2, U32, t) : Nat}

def inc_ok(c, t, ih, h):
  Equal.trans(Nat, U32.to_nat(U32.inc(Head.size(t))), 1n+U32.to_nat(Head.size(t)), 1n+List.length(&2, U32, t),
    Kit.u32_inc_nat(Head.size(t), MNat.lt_of_le_of_lt(1n+U32.to_nat(Head.size(t)), List.length(&2, U32, Con{c, t}), Kit.pow2(32n),
      le_one_more(c, t, U32.to_nat(Head.size(t)), ih), h)),
    Equal.cong(Nat, Nat, x => 1n+x, U32.to_nat(Head.size(t)), List.length(&2, U32, t), ih))

# Head.size counts a list (which is always short enough for a U32 here)
law size_nat:
  for l: List<&2, U32>
  for +h: MNat.lt(List.length(&2, U32, l), Kit.pow2(32n))
  {U32.to_nat(Head.size(l)) == List.length(&2, U32, l) : Nat}

def size_nat(l, h):
  match l:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      inc_ok(c, t, size_nat(t, lt_tail(c, t, h)), h)

law pos_of_ne:
  for x: Nat
  for h: {Nat.is_eq(x, 0n) == False{} : Bool}
  MNat.le(1n, x)

def pos_of_ne(x, h):
  match x:
    case 0n:
      Logic.absurd(MNat.le(1n, 0n), Logic.true_ne_false(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p:
      MNat.zero_le(p)

law u32_pos:
  for +n: U32
  for hz: {U32.is_zero(n) == False{} : Bool}
  MNat.le(1n, U32.to_nat(n))

def u32_pos(n, hz):
  pos_of_ne(U32.to_nat(n), Equal.trans(Bool, Nat.is_eq(U32.to_nat(n), 0n), U32.is_eq(n, 0), False{},
    Equal.sym(Bool, U32.is_eq(n, 0), Nat.is_eq(U32.to_nat(n), 0n), Kit.u32_is_eq_nat(n, 0)), hz))

# A U32 that isn't zero is one more than itself minus 1
law u32_pred:
  for +n: U32
  for hz: {U32.is_zero(n) == False{} : Bool}
  {U32.to_nat(n) == 1n+U32.to_nat(U32.sub(n, 1)) : Nat}

def u32_pred(n, hz):
  +pos = u32_pos(n, hz)
  es = Equal.sym(Nat, U32.to_nat(U32.sub(n, 1)), Nat.sub(U32.to_nat(n), 1n), Kit.u32_sub_nat(n, 1, pos))
  %es : {U32.to_nat(n) == 1n+_ : Nat}
  Equal.sym(Nat, 1n+Nat.sub(U32.to_nat(n), 1n), U32.to_nat(n),
    Equal.trans(Nat, 1n+Nat.sub(U32.to_nat(n), 1n), Nat.add(Nat.sub(U32.to_nat(n), 1n), 1n), U32.to_nat(n),
      Equal.sym(Nat, Nat.add(Nat.sub(U32.to_nat(n), 1n), 1n), 1n+Nat.sub(U32.to_nat(n), 1n), add_one(Nat.sub(U32.to_nat(n), 1n))),
      MNat.sub_add_cancel(U32.to_nat(n), 1n, pos)))

# The length of a line, its CRLF and the rest
law len_line:
  for -b: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for e: {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>}
  {List.length(&2, U32, b) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}

def len_line(b, l, rest, e):
  e2 = Equal.sym(List<&2, U32>, b, List.append(&2, U32, l, Con{13, Con{10, rest}}), e)
  %e2 : {List.length(&2, U32, _) == Nat.add(List.length(&2, U32, l), 1n+1n+List.length(&2, U32, rest)) : Nat}
  MList.length_append(&2, U32, l, Con{13, Con{10, rest}})
