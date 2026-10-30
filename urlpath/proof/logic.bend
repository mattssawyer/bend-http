# Small facts about Bool, Empty and lists used by the other proofs.

import Base


# Anything follows from an impossible case
law absurd:
  for -P: Type
  for x: Empty
  P

def absurd(P, x):
  match x:

# "This list has at least one item", as a type
def NonEmpty(xs: List<&2, List<&2, U32>>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

# True can't equal False
law true_ne_false:
  for e: {False{} == True{} : Bool}
  Empty

def true_ne_false(e):
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Facts about "and" being True
law and_left:
  for x: Bool
  for y: Bool
  for h: {Bool.and(x, y) == True{} : Bool}
  {x == True{} : Bool}

def and_left(x, y, h):
  match x:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, true_ne_false(h))

law and_right:
  for x: Bool
  for y: Bool
  for h: {Bool.and(x, y) == True{} : Bool}
  {y == True{} : Bool}

def and_right(x, y, h):
  match x:
    case True{}:
      h
    case False{}:
      absurd({y == True{} : Bool}, true_ne_false(h))

law and_intro:
  for x: Bool
  for y: Bool
  for hx: {x == True{} : Bool}
  for hy: {y == True{} : Bool}
  {Bool.and(x, y) == True{} : Bool}

def and_intro(x, y, hx, hy):
  match x:
    case True{}:
      hy
    case False{}:
      absurd({Bool.and(False{}, y) == True{} : Bool}, true_ne_false(hx))

# not x is True means x is False
law not_true:
  for x: Bool
  for h: {Bool.not(x) == True{} : Bool}
  {x == False{} : Bool}

def not_true(x, h):
  match x:
    case True{}:
      absurd({True{} == False{} : Bool}, true_ne_false(h))
    case False{}:
      {==}

law app_nil:
  for xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def app_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %app_nil(t) : {Con{x, List.append(&2, U32, t, Nil{})} == Con{x, _} : List<&2, U32>}
      {==}

# "not x or y" with x True gives y
law implies:
  for x: Bool
  for y: Bool
  for h: {Bool.or(Bool.not(x), y) == True{} : Bool}
  for hx: {x == True{} : Bool}
  {y == True{} : Bool}

def implies(x, y, h, hx):
  match x:
    case True{}:
      h
    case False{}:
      absurd({y == True{} : Bool}, true_ne_false(hx))

# "or" being False
law or_l:
  for x: Bool
  for y: Bool
  for h: {Bool.or(x, y) == False{} : Bool}
  {x == False{} : Bool}

def or_l(x, y, h):
  match x:
    case True{}:
      absurd({True{} == False{} : Bool}, true_ne_false(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      {==}

law or_r:
  for x: Bool
  for y: Bool
  for h: {Bool.or(x, y) == False{} : Bool}
  {y == False{} : Bool}

def or_r(x, y, h):
  match x:
    case True{}:
      absurd({y == False{} : Bool}, true_ne_false(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      h
