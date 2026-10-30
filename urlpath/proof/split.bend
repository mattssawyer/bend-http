# Proofs about split and join.

import Base
import ../src/bytes.bend as Byte
import ../src/split.bend as Split
import bend-mathlib@0.7.4.0/string.bend as MStr
import ./logic.bend as Logic


# split never returns an empty list
law add_head_ne:
  for -h: U32
  for segs: List<&2, List<&2, U32>>
  Logic.NonEmpty(Split.add_head(h, segs))

def add_head_ne(h, segs):
  match segs:
    case Nil{}:
      Unit{}
    case Con{s, r}:
      Unit{}

law split_if_ne:
  for -h: U32
  for rest: List<&2, List<&2, U32>>
  for slash: Bool
  Logic.NonEmpty(Split.split.if(h, rest, slash))

def split_if_ne(h, rest, slash):
  match slash:
    case True{}:
      Unit{}
    case False{}:
      add_head_ne(h, rest)

law split_ne:
  for b: List<&2, U32>
  Logic.NonEmpty(Split.split(b))

def split_ne(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+h, t}:
      split_if_ne(h, Split.split(t), U32.is_eq(h, 47))

# Joining with an empty first segment puts a "/" in front
law join_nil_head:
  for r: List<&2, List<&2, U32>>
  for ne: Logic.NonEmpty(r)
  {Split.join(Con{Nil{}, r}) == Con{47, Split.join(r)} : List<&2, U32>}

def join_nil_head(r, ne):
  match r:
    case Nil{}:
      Logic.absurd({Split.join(Con{Nil{}, Nil{}}) == Con{47, Split.join(Nil{})} : List<&2, U32>}, ne)
    case Con{s, t}:
      {==}

# Joining after add_head puts the byte in front
law join_add_head:
  for -h: U32
  for segs: List<&2, List<&2, U32>>
  {Split.join(Split.add_head(h, segs)) == Con{h, Split.join(segs)} : List<&2, U32>}

def join_add_head(h, segs):
  match segs:
    case Nil{}:
      {==}
    case Con{s, r}:
      match r:
        case Nil{}:
          {==}
        case Con{s2, r2}:
          {==}

# One step of the round trip, split on whether the byte is "/"
law join_split.at:
  for k: Bool
  for +h: U32
  for +t: List<&2, U32>
  for ek: {k == U32.is_eq(h, 47) : Bool}
  for ih: {Split.join(Split.split(t)) == t : List<&2, U32>}
  for ne: Logic.NonEmpty(Split.split(t))
  {Split.join(Split.split.if(h, Split.split(t), k)) == Con{h, t} : List<&2, U32>}

def join_split.at(k, h, t, ek, ih, ne):
  match k:
    case True{}:
      eh = Equal.sym(U32, h, 47, MStr.u32_eq_of_is_eq(h, 47, Equal.sym(Bool, True{}, U32.is_eq(h, 47), ek)))
      %eh : {Split.join(Con{Nil{}, Split.split(t)}) == Con{_, t} : List<&2, U32>}
      %ih : {Split.join(Con{Nil{}, Split.split(t)}) == Con{47, _} : List<&2, U32>}
      join_nil_head(Split.split(t), ne)
    case False{}:
      %ih : {Split.join(Split.add_head(h, Split.split(t))) == Con{h, _} : List<&2, U32>}
      join_add_head(h, Split.split(t))

# Splitting bytes with no "/" gives one segment
law sj0:
  for s: List<&2, U32>
  for +h: {Byte.has_byte(s, 47) == False{} : Bool}
  {Split.split(s) == [s] : List<&2, List<&2, U32>>}

def sj0(s, h):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      hc = Equal.sym(Bool, U32.is_eq(c, 47), False{}, Logic.or_l(U32.is_eq(c, 47), Byte.has_byte(t, 47), h))
      ih = Equal.sym(List<&2, List<&2, U32>>, Split.split(t), [t], sj0(t, Logic.or_r(U32.is_eq(c, 47), Byte.has_byte(t, 47), h)))
      %hc : {Split.split.if(c, Split.split(t), _) == [Con{c, t}] : List<&2, List<&2, U32>>}
      %ih : {Split.add_head(c, _) == [Con{c, t}] : List<&2, List<&2, U32>>}
      {==}

# Splitting "s/rest" with no "/" in s gives s, then the split of rest
law sj1:
  for s: List<&2, U32>
  for +j: List<&2, U32>
  for +h: {Byte.has_byte(s, 47) == False{} : Bool}
  {Split.split(List.append(&2, U32, s, Con{47, j})) == Con{s, Split.split(j)} : List<&2, List<&2, U32>>}

def sj1(s, j, h):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      hc = Equal.sym(Bool, U32.is_eq(c, 47), False{}, Logic.or_l(U32.is_eq(c, 47), Byte.has_byte(t, 47), h))
      ih = Equal.sym(List<&2, List<&2, U32>>, Split.split(List.append(&2, U32, t, Con{47, j})), Con{t, Split.split(j)},
        sj1(t, j, Logic.or_r(U32.is_eq(c, 47), Byte.has_byte(t, 47), h)))
      %hc : {Split.split.if(c, Split.split(List.append(&2, U32, t, Con{47, j})), _) == Con{Con{c, t}, Split.split(j)} : List<&2, List<&2, U32>>}
      %ih : {Split.add_head(c, _) == Con{Con{c, t}, Split.split(j)} : List<&2, List<&2, U32>>}
      {==}

law join_split:
  for b: List<&2, U32>
  {Split.join(Split.split(b)) == b : List<&2, U32>}

def join_split(b):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      join_split.at(U32.is_eq(h, 47), h, t, {==}, join_split(t), split_ne(t))
