import Base
import ./LAWS.bend as Laws
import ./urlpath.bend as Path
import bend-mathlib@0.7.4.0/string.bend as MStr

def Laws.bytes_get(): 
  {==}

def Laws.bytes_post(): 
  {==}

def Laws.bytes_put(): 
  {==}

def Laws.bytes_delete(): 
  {==}

def Laws.digit_7(): 
  {==}

def Laws.digit_A(): 
  {==}

def Laws.alpha_7(): 
  {==}

def Laws.alpha_A(): 
  {==}

def Laws.hex_A(): 
  {==}

def Laws.hex_N(): 
  {==}

def Laws.unreserved_A(): 
  {==}

def Laws.unreserved_7(): 
  {==}

def Laws.unreserved_bang(): 
  {==}

def Laws.sub_delim_bang(): 
  {==}

def Laws.sub_delim_qmark(): 
  {==}

def Laws.pchar_A(): 
  {==}

def Laws.pchar_7(): 
  {==}

def Laws.pchar_qmark(): 
  {==}

def Laws.pchar_slash(): 
  {==}

def Laws.pchar_mod(): 
  {==}

def Laws.split_empty():
  {==}

def Laws.split_root():
  {==}

def Laws.split_ab():
  {==}

def Laws.split_trailing():
  {==}

def Laws.join_ab():
  {==}


# ---- Helpers for the round-trip proof ----

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

# split never returns an empty list
law add_head_ne:
  for -h: U32
  for segs: List<&2, List<&2, U32>>
  NonEmpty(Path.add_head(h, segs))

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
  NonEmpty(Path.split.if(h, rest, slash))

def split_if_ne(h, rest, slash):
  match slash:
    case True{}:
      Unit{}
    case False{}:
      add_head_ne(h, rest)

law split_ne:
  for b: List<&2, U32>
  NonEmpty(Path.split(b))

def split_ne(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+h, t}:
      split_if_ne(h, Path.split(t), U32.is_eq(h, 47))

# Joining with an empty first segment puts a "/" in front
law join_nil_head:
  for r: List<&2, List<&2, U32>>
  for ne: NonEmpty(r)
  {Path.join(Con{Nil{}, r}) == Con{47, Path.join(r)} : List<&2, U32>}

def join_nil_head(r, ne):
  match r:
    case Nil{}:
      absurd({Path.join(Con{Nil{}, Nil{}}) == Con{47, Path.join(Nil{})} : List<&2, U32>}, ne)
    case Con{s, t}:
      {==}

# Joining after add_head puts the byte in front
law join_add_head:
  for -h: U32
  for segs: List<&2, List<&2, U32>>
  {Path.join(Path.add_head(h, segs)) == Con{h, Path.join(segs)} : List<&2, U32>}

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
  for ih: {Path.join(Path.split(t)) == t : List<&2, U32>}
  for ne: NonEmpty(Path.split(t))
  {Path.join(Path.split.if(h, Path.split(t), k)) == Con{h, t} : List<&2, U32>}

def join_split.at(k, h, t, ek, ih, ne):
  match k:
    case True{}:
      eh = Equal.sym(U32, h, 47, MStr.u32_eq_of_is_eq(h, 47, Equal.sym(Bool, True{}, U32.is_eq(h, 47), ek)))
      %eh : {Path.join(Con{Nil{}, Path.split(t)}) == Con{_, t} : List<&2, U32>}
      %ih : {Path.join(Con{Nil{}, Path.split(t)}) == Con{47, _} : List<&2, U32>}
      join_nil_head(Path.split(t), ne)
    case False{}:
      %ih : {Path.join(Path.add_head(h, Path.split(t))) == Con{h, _} : List<&2, U32>}
      join_add_head(h, Path.split(t))


# ---- Round trip ----

def Laws.join_split(b):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      join_split.at(U32.is_eq(h, 47), h, t, {==}, Laws.join_split(t), split_ne(t))


# ---- Percent-decoding ----

def Laws.decode_plain_abc():
  {==}

def Laws.decode_empty():
  {==}

def Laws.decode_upper():
  {==}

def Laws.decode_lower():
  {==}

def Laws.decode_once():
  {==}

def Laws.decode_utf8():
  {==}

def Laws.decode_bad_hex():
  {==}

def Laws.decode_short():
  {==}

def Laws.decode_lone_pct():
  {==}

def Laws.decode_space():
  {==}

def Laws.decode_high_byte():
  {==}

def Laws.decode_first_error():
  {==}

# True can't equal False
law true_ne_false:
  for e: {False{} == True{} : Bool}
  Empty

def true_ne_false(e):
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# One step of decode_plain, split on whether the first byte is a pchar
law decode_plain.at:
  for k: Bool
  for +h: U32
  for +t: List<&2, U32>
  for e: {Bool.and(k, Path.all_pchar(t)) == True{} : Bool}
  for ih: {Path.all_pchar(t) == True{} : Bool} -> {Path.decode.go(t, Path.Plain{}) == Done{t} : Result<&2, &2, Path.PathError, List<&2, U32>>}
  {Path.decode.step.plain(h, Path.decode.go(t, Path.decode.next.plain(k, U32.is_eq(h, 37))), k, U32.is_eq(h, 37)) == Done{Con{h, t}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

def decode_plain.at(k, h, t, e, ih):
  match k:
    case True{}:
      %ih(e) : {Path.ok_cons(h, Path.decode.go(t, Path.Plain{})) == Path.ok_cons(h, _) : Result<&2, &2, Path.PathError, List<&2, U32>>}
      {==}
    case False{}:
      absurd({Path.decode.step.plain(h, Path.decode.go(t, Path.decode.next.plain(False{}, U32.is_eq(h, 37))), False{}, U32.is_eq(h, 37)) == Done{Con{h, t}} : Result<&2, &2, Path.PathError, List<&2, U32>>}, true_ne_false(e))

def Laws.decode_plain(b, e):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      decode_plain.at(Path.is_pchar(h), h, t, e, e2 => Laws.decode_plain(t, e2))


# ---- Dot-segment removal ----

def Laws.dots_single():
  {==}

def Laws.dots_parent():
  {==}

def Laws.dots_end_parent():
  {==}

def Laws.dots_end_single():
  {==}

def Laws.dots_root_single():
  {==}

def Laws.dots_to_root():
  {==}

def Laws.dots_none():
  {==}

def Laws.dots_lookalikes():
  {==}

def Laws.dots_above_root():
  {==}

def Laws.dots_above_root_late():
  {==}

def Laws.dots_above_root_mid():
  {==}
