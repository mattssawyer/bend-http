# is_prefix is sound (law U8).

import Base
import ../src/prefix.bend as Prefix
import bend-mathlib@0.7.4.0/string.bend as MStr
import ./logic.bend as Logic


# bytes_eq really means equal
law bytes_eq_ok:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {Prefix.bytes_eq(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

def bytes_eq_ok(a, b, h):
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{y, bt}:
          Logic.absurd({Nil{} == Con{y, bt} : List<&2, U32>}, Logic.true_ne_false(h))
    case Con{+x, +at}:
      match b:
        case Nil{}:
          Logic.absurd({Con{x, at} == Nil{} : List<&2, U32>}, Logic.true_ne_false(h))
        case Con{+y, +bt}:
          hx = MStr.u32_eq_of_is_eq(x, y, Logic.and_left(U32.is_eq(x, y), Prefix.bytes_eq(at, bt), h))
          ht = bytes_eq_ok(at, bt, Logic.and_right(U32.is_eq(x, y), Prefix.bytes_eq(at, bt), h))
          %hx : {Con{x, at} == Con{_, bt} : List<&2, U32>}
          %ht : {Con{x, at} == Con{x, _} : List<&2, U32>}
          {==}

law prefix_cons:
  for x: List<&2, U32>
  for y: List<&2, U32>
  for ar: List<&2, List<&2, U32>>
  for br: List<&2, List<&2, U32>>
  for rest: List<&2, List<&2, U32>>
  for hx: {x == y : List<&2, U32>}
  for e: {br == List.append(&2, List<&2, U32>, ar, rest) : List<&2, List<&2, U32>>}
  {Con{y, br} == List.append(&2, List<&2, U32>, Con{x, ar}, rest) : List<&2, List<&2, U32>>}

def prefix_cons(x, y, ar, br, rest, hx, e):
  %e : {Con{y, br} == Con{x, _} : List<&2, List<&2, U32>>}
  %hx : {Con{_, br} == Con{x, br} : List<&2, List<&2, U32>>}
  {==}

# Add one matching segment to a prefix witness
law prefix_step:
  for x: List<&2, U32>
  for y: List<&2, U32>
  for ar: List<&2, List<&2, U32>>
  for br: List<&2, List<&2, U32>>
  for hx: {x == y : List<&2, U32>}
  for pr: &rest: List<&2, List<&2, U32>> -> {br == List.append(&2, List<&2, U32>, ar, rest) : List<&2, List<&2, U32>>}
  exs rest: List<&2, List<&2, U32>>
  {Con{y, br} == List.append(&2, List<&2, U32>, Con{x, ar}, rest) : List<&2, List<&2, U32>>}

def prefix_step(x, y, ar, br, hx, pr):
  match pr:
    case (+rest, e):
      (rest, prefix_cons(x, y, ar, br, rest, hx, e))

law is_prefix_sound:
  for a: List<&2, List<&2, U32>>
  for +b: List<&2, List<&2, U32>>
  for +h: {Prefix.is_prefix(a, b) == True{} : Bool}
  exs rest: List<&2, List<&2, U32>>
  {b == List.append(&2, List<&2, U32>, a, rest) : List<&2, List<&2, U32>>}

def is_prefix_sound(a, b, h):
  match a:
    case Nil{}:
      (b, {==})
    case Con{+x, +ar}:
      match b:
        case Nil{}:
          Logic.absurd(&rest: List<&2, List<&2, U32>> -> {Nil{} == List.append(&2, List<&2, U32>, Con{x, ar}, rest) : List<&2, List<&2, U32>>}, Logic.true_ne_false(h))
        case Con{+y, +br}:
          prefix_step(x, y, ar, br, bytes_eq_ok(x, y, Logic.and_left(Prefix.bytes_eq(x, y), Prefix.is_prefix(ar, br), h)),
            is_prefix_sound(ar, br, Logic.and_right(Prefix.bytes_eq(x, y), Prefix.is_prefix(ar, br), h)))
