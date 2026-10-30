import Base
import ./LAWS.bend as Laws
import ./urlpath.bend as Path
import bend-mathlib@0.7.4.0/string.bend as MStr
import bend-kit-lemmas@0.1.1.0/lemmas.bend as Kit

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


# ---- parse examples ----

def Laws.parse_root():
  {==}

def Laws.parse_not_absolute():
  {==}

def Laws.parse_empty():
  {==}

def Laws.parse_space():
  {==}

def Laws.parse_fragment():
  {==}

def Laws.parse_bad_percent():
  {==}

def Laws.parse_hex_case():
  {==}

def Laws.parse_dots():
  {==}

def Laws.parse_above_root():
  {==}

def Laws.parse_encoded_dotdot():
  {==}

def Laws.parse_mixed_dotdot():
  {==}

def Laws.parse_encoded_slash():
  {==}

def Laws.parse_raw_backslash():
  {==}

def Laws.parse_encoded_backslash():
  {==}

def Laws.parse_nul():
  {==}

def Laws.parse_del():
  {==}

def Laws.parse_double_encoding():
  {==}

def Laws.parse_overlong():
  {==}

def Laws.parse_double_slash():
  {==}

def Laws.parse_inner_empty():
  {==}

def Laws.parse_dotdot_semi():
  {==}

def Laws.parse_semi_param():
  {==}

def Laws.parse_trailing():
  {==}

def Laws.parse_trailing_dotdot():
  {==}

def Laws.parse_encoded_query():
  {==}

def Laws.parse_case_kept():
  {==}

def Laws.parse_not_a_byte():
  {==}

def Laws.parse_high_byte():
  {==}


# ---- Helpers for the parse laws (U1-U4) ----

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

# The segments kept by dot removal
def kept_of(d: Path.Dots) -> List<&2, List<&2, U32>>:
  match d:
    case Path.Dots{up, kept}:
      kept


# ---- U1: an accepted path started with "/" ----

# What U1 promises about one parse result
def U1ok(b: List<&2, U32>, r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Path.starts_with_slash(b) == True{} : Bool}

law u1_any:
  for b: List<&2, U32>
  for r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for h: {Path.starts_with_slash(b) == True{} : Bool}
  U1ok(b, r)

def u1_any(b, r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{p}:
      h

law u1_slash:
  for k: Bool
  for +c: U32
  for +t: List<&2, U32>
  for ek: {k == U32.is_eq(c, 47) : Bool}
  U1ok(Con{c, t}, Path.parse.slash(k, t))

def u1_slash(k, c, t, ek):
  match k:
    case True{}:
      u1_any(Con{c, t}, Path.parse.dots(Path.check_all(Path.split(t))), Equal.sym(Bool, True{}, U32.is_eq(c, 47), ek))
    case False{}:
      Unit{}

law u1_first:
  for +b: List<&2, U32>
  U1ok(b, Path.parse.first(b))

def u1_first(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, +t}:
      u1_slash(U32.is_eq(c, 47), c, t, {==})

law u1_bytes:
  for k: Bool
  for +b: List<&2, U32>
  U1ok(b, Path.parse.bytes(k, b))

def u1_bytes(k, b):
  match k:
    case True{}:
      u1_first(b)
    case False{}:
      Unit{}

def Laws.accepts_only_absolute(b, p, e):
  %e : U1ok(b, _)
  u1_bytes(Path.all_bytes(b), b)


# ---- U2: no "." or ".." segment survives ----

def U2ok(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Path.no_dot_segs(p) == True{} : Bool}

# One step of dot removal keeps the invariant
law u2_step:
  for k: Path.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Path.Dots
  for ek: {k == Path.seg_kind(s) : Path.SegKind}
  for ih: {Path.no_dot_segs(kept_of(d)) == True{} : Bool}
  {Path.no_dot_segs(kept_of(Path.rd.step(k, s, l, d))) == True{} : Bool}

def u2_step(k, s, l, d, ek, ih):
  match k:
    case Path.Other{}:
      match l:
        case True{}:
          %ek : {Bool.and(Bool.not(Bool.not(Path.is_other(_))), True{}) == True{} : Bool}
          {==}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              match up:
                case 0n:
                  %ek : {Bool.and(Bool.not(Bool.not(Path.is_other(_))), Path.no_dot_segs(kept)) == True{} : Bool}
                  ih
                case 1n+n:
                  ih
    case Path.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Path.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              ih

law u2_kept:
  for segs: List<&2, List<&2, U32>>
  {Path.no_dot_segs(kept_of(Path.rd(segs))) == True{} : Bool}

def u2_kept(segs):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u2_step(Path.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Path.rd(rest), {==}, u2_kept(rest))

law u2_end:
  for d: Path.Dots
  for h: {Path.no_dot_segs(kept_of(d)) == True{} : Bool}
  U2ok(Path.rd.end(d))

def u2_end(d, h):
  match d:
    case Path.Dots{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law u2_dots:
  for r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  U2ok(Path.parse.dots(r))

def u2_dots(r):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u2_end(Path.rd(ds), u2_kept(ds))

law u2_slash:
  for k: Bool
  for +t: List<&2, U32>
  U2ok(Path.parse.slash(k, t))

def u2_slash(k, t):
  match k:
    case True{}:
      u2_dots(Path.check_all(Path.split(t)))
    case False{}:
      Unit{}

law u2_first:
  for b: List<&2, U32>
  U2ok(Path.parse.first(b))

def u2_first(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, t}:
      u2_slash(U32.is_eq(c, 47), t)

law u2_bytes:
  for k: Bool
  for b: List<&2, U32>
  U2ok(Path.parse.bytes(k, b))

def u2_bytes(k, b):
  match k:
    case True{}:
      u2_first(b)
    case False{}:
      Unit{}

def Laws.no_dot_segments(b, p, e):
  %e : U2ok(_)
  u2_bytes(Path.all_bytes(b), b)


# ---- U3: no "/", "\" or control byte in any segment ----

def U3ok(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Path.all_safe(p) == True{} : Bool}

# What U3 needs from one checked segment
def SegOk3(r: Result<&2, &2, Path.PathError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      {Path.safe_seg(s) == True{} : Bool}

law u3_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for l: Bool
  for ek: {k == Path.seg_ok(raw, d, l) : Bool}
  SegOk3(Path.check_decoded.if(k, raw, d))

def u3_seg_if(k, raw, d, l, ek):
  match k:
    case True{}:
      and_left(Path.safe_seg(d), Path.seg_ok.dots(raw, d),
        and_left(Path.seg_ok.shape(raw, d), Path.seg_ok.place(d, l),
          Equal.sym(Bool, True{}, Path.seg_ok(raw, d, l), ek)))
    case False{}:
      Unit{}

law u3_seg_d:
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  SegOk3(Path.check_seg.d(r, raw, l))

def u3_seg_d(r, raw, l):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      u3_seg_if(Path.seg_ok(raw, d, l), raw, d, l, {==})

law u3_cons:
  for a: Result<&2, &2, Path.PathError, List<&2, U32>>
  for b: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for ha: SegOk3(a)
  for hb: U3ok(b)
  U3ok(Path.check_all.cons(a, b))

def u3_cons(a, b, ha, hb):
  match a:
    case Fail{e}:
      Unit{}
    case Done{+s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{+ss}:
          and_intro(Path.safe_seg(s), Path.all_safe(ss), ha, hb)

law u3_check_all:
  for raws: List<&2, List<&2, U32>>
  U3ok(Path.check_all(raws))

def u3_check_all(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u3_cons(Path.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Path.check_all(rest),
        u3_seg_d(Path.decode(r), r, List.is_empty(&2, List<&2, U32>, rest)), u3_check_all(rest))

# One step of dot removal keeps every segment safe
law u3_step:
  for k: Path.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Path.Dots
  for hs: {Path.safe_seg(s) == True{} : Bool}
  for ih: {Path.all_safe(kept_of(d)) == True{} : Bool}
  {Path.all_safe(kept_of(Path.rd.step(k, s, l, d))) == True{} : Bool}

def u3_step(k, s, l, d, hs, ih):
  match k:
    case Path.Other{}:
      match l:
        case True{}:
          and_intro(Path.safe_seg(s), True{}, hs, {==})
        case False{}:
          match d:
            case Path.Dots{up, +kept}:
              match up:
                case 0n:
                  and_intro(Path.safe_seg(s), Path.all_safe(kept), hs, ih)
                case 1n+n:
                  ih
    case Path.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Path.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              ih

law u3_kept:
  for segs: List<&2, List<&2, U32>>
  for +h: {Path.all_safe(segs) == True{} : Bool}
  {Path.all_safe(kept_of(Path.rd(segs))) == True{} : Bool}

def u3_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u3_step(Path.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Path.rd(rest),
        and_left(Path.safe_seg(s), Path.all_safe(rest), h),
        u3_kept(rest, and_right(Path.safe_seg(s), Path.all_safe(rest), h)))

law u3_end:
  for d: Path.Dots
  for h: {Path.all_safe(kept_of(d)) == True{} : Bool}
  U3ok(Path.rd.end(d))

def u3_end(d, h):
  match d:
    case Path.Dots{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law u3_dots:
  for r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for h: U3ok(r)
  U3ok(Path.parse.dots(r))

def u3_dots(r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u3_end(Path.rd(ds), u3_kept(ds, h))

law u3_slash:
  for k: Bool
  for +t: List<&2, U32>
  U3ok(Path.parse.slash(k, t))

def u3_slash(k, t):
  match k:
    case True{}:
      u3_dots(Path.check_all(Path.split(t)), u3_check_all(Path.split(t)))
    case False{}:
      Unit{}

law u3_first:
  for b: List<&2, U32>
  U3ok(Path.parse.first(b))

def u3_first(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, t}:
      u3_slash(U32.is_eq(c, 47), t)

law u3_bytes:
  for k: Bool
  for b: List<&2, U32>
  U3ok(Path.parse.bytes(k, b))

def u3_bytes(k, b):
  match k:
    case True{}:
      u3_first(b)
    case False{}:
      Unit{}

def Laws.no_unsafe_bytes(b, p, e):
  %e : U3ok(_)
  u3_bytes(Path.all_bytes(b), b)


# ---- U4: at least one segment, and only the last may be empty ----

def U4ok(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Path.empty_only_last(p) == True{} : Bool}

# Facts about check_all's result: only the last segment is empty,
# it's non-empty, and it's empty exactly when the input was (l)
def OLEok(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      {Path.only_last_empty(ss) == True{} : Bool}

def NEok(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      NonEmpty(ss)

def LenOk(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>, l: Bool) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      {List.is_empty(&2, List<&2, U32>, ss) == l : Bool}

# What U4 needs from one checked segment: it's non-empty unless last
def SegOk4(r: Result<&2, &2, Path.PathError, List<&2, U32>>, l: Bool) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      {Path.seg_ok.place(s, l) == True{} : Bool}

law u4_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for +l: Bool
  for ek: {k == Path.seg_ok(raw, d, l) : Bool}
  SegOk4(Path.check_decoded.if(k, raw, d), l)

def u4_seg_if(k, raw, d, l, ek):
  match k:
    case True{}:
      and_right(Path.seg_ok.shape(raw, d), Path.seg_ok.place(d, l),
        Equal.sym(Bool, True{}, Path.seg_ok(raw, d, l), ek))
    case False{}:
      Unit{}

law u4_seg_d:
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  SegOk4(Path.check_seg.d(r, raw, l), l)

def u4_seg_d(r, raw, l):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      u4_seg_if(Path.seg_ok(raw, d, l), raw, d, l, {==})

law u4_cons:
  for l: Bool
  for a: Result<&2, &2, Path.PathError, List<&2, U32>>
  for b: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for ha: SegOk4(a, l)
  for hb: OLEok(b)
  for hlen: LenOk(b, l)
  OLEok(Path.check_all.cons(a, b))

def u4_cons(l, a, b, ha, hb, hlen):
  match l:
    case True{}:
      match a:
        case Fail{e}:
          Unit{}
        case Done{+s}:
          match b:
            case Fail{e}:
              Unit{}
            case Done{+ss}:
              eh = Equal.sym(Bool, List.is_empty(&2, List<&2, U32>, ss), True{}, hlen)
              %eh : {Path.eol.step(_, s, Path.only_last_empty(ss)) == True{} : Bool}
              {==}
    case False{}:
      match a:
        case Fail{e}:
          Unit{}
        case Done{+s}:
          match b:
            case Fail{e}:
              Unit{}
            case Done{+ss}:
              eh = Equal.sym(Bool, List.is_empty(&2, List<&2, U32>, ss), False{}, hlen)
              %eh : {Path.eol.step(_, s, Path.only_last_empty(ss)) == True{} : Bool}
              and_intro(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(ss), ha, hb)

law u4_len_cons:
  for a: Result<&2, &2, Path.PathError, List<&2, U32>>
  for b: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  LenOk(Path.check_all.cons(a, b), False{})

def u4_len_cons(a, b):
  match a:
    case Fail{e}:
      Unit{}
    case Done{s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{ss}:
          {==}

law u4_len:
  for +raws: List<&2, List<&2, U32>>
  LenOk(Path.check_all(raws), List.is_empty(&2, List<&2, U32>, raws))

def u4_len(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u4_len_cons(Path.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Path.check_all(rest))

law u4_ole_ca:
  for raws: List<&2, List<&2, U32>>
  OLEok(Path.check_all(raws))

def u4_ole_ca(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u4_cons(List.is_empty(&2, List<&2, U32>, rest),
        Path.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Path.check_all(rest),
        u4_seg_d(Path.decode(r), r, List.is_empty(&2, List<&2, U32>, rest)),
        u4_ole_ca(rest), u4_len(rest))

law u4_ne_cons:
  for a: Result<&2, &2, Path.PathError, List<&2, U32>>
  for b: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  NEok(Path.check_all.cons(a, b))

def u4_ne_cons(a, b):
  match a:
    case Fail{e}:
      Unit{}
    case Done{s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{ss}:
          Unit{}

law u4_ne_ca:
  for raws: List<&2, List<&2, U32>>
  for ne: NonEmpty(raws)
  NEok(Path.check_all(raws))

def u4_ne_ca(raws, ne):
  match raws:
    case Nil{}:
      ne
    case Con{+r, +rest}:
      u4_ne_cons(Path.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Path.check_all(rest))

# Putting a non-empty segment in front keeps "only the last is empty"
law u4_ole_cons:
  for +s: List<&2, U32>
  for kept: List<&2, List<&2, U32>>
  for hs: {Bool.not(List.is_empty(&2, U32, s)) == True{} : Bool}
  for hk: {Path.only_last_empty(kept) == True{} : Bool}
  {Path.only_last_empty(Con{s, kept}) == True{} : Bool}

def u4_ole_cons(s, kept, hs, hk):
  match kept:
    case Nil{}:
      {==}
    case Con{+k1, +kr}:
      and_intro(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(Con{k1, kr}), hs, hk)

# One step of dot removal keeps "only the last is empty"
law u4_step:
  for k: Path.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for +rest: List<&2, List<&2, U32>>
  for d: Path.Dots
  for +h: {Path.eol.step(l, s, Path.only_last_empty(rest)) == True{} : Bool}
  for ih: {Path.only_last_empty(rest) == True{} : Bool} -> {Path.only_last_empty(kept_of(d)) == True{} : Bool}
  {Path.only_last_empty(kept_of(Path.rd.step(k, s, l, d))) == True{} : Bool}

def u4_step(k, s, l, rest, d, h, ih):
  match k:
    case Path.Other{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Path.Dots{up, +kept}:
              match up:
                case 0n:
                  u4_ole_cons(s, kept,
                    and_left(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(rest), h),
                    ih(and_right(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(rest), h)))
                case 1n+n:
                  ih(and_right(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(rest), h))
    case Path.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih(and_right(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(rest), h))
    case Path.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              ih(and_right(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(rest), h))

law u4_kept:
  for segs: List<&2, List<&2, U32>>
  for h: {Path.only_last_empty(segs) == True{} : Bool}
  {Path.only_last_empty(kept_of(Path.rd(segs))) == True{} : Bool}

def u4_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u4_step(Path.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rest, Path.rd(rest), h,
        e2 => u4_kept(rest, e2))

# A list that isn't empty is NonEmpty
law u4_ne_of:
  for rest: List<&2, List<&2, U32>>
  for e: {False{} == List.is_empty(&2, List<&2, U32>, rest) : Bool}
  NonEmpty(rest)

def u4_ne_of(rest, e):
  match rest:
    case Nil{}:
      true_ne_false(e)
    case Con{s, r}:
      Unit{}

# Dot removal of a non-empty list keeps at least one segment
law u4_kne_step:
  for k: Path.SegKind
  for s: List<&2, U32>
  for l: Bool
  for +rest: List<&2, List<&2, U32>>
  for d: Path.Dots
  for el: {l == List.is_empty(&2, List<&2, U32>, rest) : Bool}
  for ih: NonEmpty(rest) -> NonEmpty(kept_of(d))
  NonEmpty(kept_of(Path.rd.step(k, s, l, d)))

def u4_kne_step(k, s, l, rest, d, el, ih):
  match k:
    case Path.Other{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              match up:
                case 0n:
                  Unit{}
                case 1n+n:
                  ih(u4_ne_of(rest, el))
    case Path.Dot{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          ih(u4_ne_of(rest, el))
    case Path.DotDot{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              ih(u4_ne_of(rest, el))

law u4_kne:
  for segs: List<&2, List<&2, U32>>
  for ne: NonEmpty(segs)
  NonEmpty(kept_of(Path.rd(segs)))

def u4_kne(segs, ne):
  match segs:
    case Nil{}:
      ne
    case Con{+s, +rest}:
      u4_kne_step(Path.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rest, Path.rd(rest), {==},
        x => u4_kne(rest, x))

law ne_bool:
  for xs: List<&2, List<&2, U32>>
  for ne: NonEmpty(xs)
  {Bool.not(List.is_empty(&2, List<&2, U32>, xs)) == True{} : Bool}

def ne_bool(xs, ne):
  match xs:
    case Nil{}:
      absurd({Bool.not(List.is_empty(&2, List<&2, U32>, Nil{})) == True{} : Bool}, ne)
    case Con{s, r}:
      {==}

law u4_end:
  for d: Path.Dots
  for ho: {Path.only_last_empty(kept_of(d)) == True{} : Bool}
  for hn: NonEmpty(kept_of(d))
  U4ok(Path.rd.end(d))

def u4_end(d, ho, hn):
  match d:
    case Path.Dots{up, +kept}:
      match up:
        case 0n:
          and_intro(Bool.not(List.is_empty(&2, List<&2, U32>, kept)), Path.only_last_empty(kept), ne_bool(kept, hn), ho)
        case 1n+n:
          Unit{}

law u4_dots:
  for r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for h1: OLEok(r)
  for h2: NEok(r)
  U4ok(Path.parse.dots(r))

def u4_dots(r, h1, h2):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u4_end(Path.rd(ds), u4_kept(ds, h1), u4_kne(ds, h2))

law u4_slash:
  for k: Bool
  for +t: List<&2, U32>
  U4ok(Path.parse.slash(k, t))

def u4_slash(k, t):
  match k:
    case True{}:
      u4_dots(Path.check_all(Path.split(t)), u4_ole_ca(Path.split(t)), u4_ne_ca(Path.split(t), split_ne(t)))
    case False{}:
      Unit{}

law u4_first:
  for b: List<&2, U32>
  U4ok(Path.parse.first(b))

def u4_first(b):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, t}:
      u4_slash(U32.is_eq(c, 47), t)

law u4_bytes:
  for k: Bool
  for b: List<&2, U32>
  U4ok(Path.parse.bytes(k, b))

def u4_bytes(k, b):
  match k:
    case True{}:
      u4_first(b)
    case False{}:
      Unit{}

def Laws.empty_only_last(b, p, e):
  %e : U4ok(_)
  u4_bytes(Path.all_bytes(b), b)


# ---- render and is_prefix examples ----

def Laws.render_ab():
  {==}

def Laws.render_root():
  {==}

def Laws.render_trailing():
  {==}

def Laws.render_utf8():
  {==}

def Laws.render_percent():
  {==}

def Laws.render_slash():
  {==}

def Laws.render_keeps_pchar():
  {==}

def Laws.prefix_yes():
  {==}

def Laws.prefix_empty():
  {==}

def Laws.prefix_same():
  {==}

def Laws.prefix_segmentwise():
  {==}

def Laws.prefix_longer():
  {==}


# ---- U8: is_prefix is sound ----

# bytes_eq really means equal
law bytes_eq_ok:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {Path.bytes_eq(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

def bytes_eq_ok(a, b, h):
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{y, bt}:
          absurd({Nil{} == Con{y, bt} : List<&2, U32>}, true_ne_false(h))
    case Con{+x, +at}:
      match b:
        case Nil{}:
          absurd({Con{x, at} == Nil{} : List<&2, U32>}, true_ne_false(h))
        case Con{+y, +bt}:
          hx = MStr.u32_eq_of_is_eq(x, y, and_left(U32.is_eq(x, y), Path.bytes_eq(at, bt), h))
          ht = bytes_eq_ok(at, bt, and_right(U32.is_eq(x, y), Path.bytes_eq(at, bt), h))
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

def Laws.is_prefix_sound(a, b, h):
  match a:
    case Nil{}:
      (b, {==})
    case Con{+x, +ar}:
      match b:
        case Nil{}:
          absurd(&rest: List<&2, List<&2, U32>> -> {Nil{} == List.append(&2, List<&2, U32>, Con{x, ar}, rest) : List<&2, List<&2, U32>>}, true_ne_false(h))
        case Con{+y, +br}:
          prefix_step(x, y, ar, br, bytes_eq_ok(x, y, and_left(Path.bytes_eq(x, y), Path.is_prefix(ar, br), h)),
            Laws.is_prefix_sound(ar, br, and_right(Path.bytes_eq(x, y), Path.is_prefix(ar, br), h)))


# ---- Facts about the hex digits render writes ----

# What we need from a digit render writes: uppercase hex, not "/", a byte
def dig_ok(+d: U32) -> Bool:
  Bool.and(Path.is_upper_hex(d), Bool.and(Bool.not(U32.is_eq(d, 47)), U32.is_le(d, 255)))

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
  {dig_ok(Path.hex_digit.if(k, d, o)) == True{} : Bool}

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
  {dig_ok(Path.hex_digit.go(tbl, n, i)) == True{} : Bool}

def hdg(tbl, n, i, h):
  match tbl:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      hdg_at(U32.is_eq(n, i), d, Path.hex_digit.go(rest, n, U32.inc(i)),
        and_left(dig_ok(d), all_dig(rest), h),
        hdg(rest, n, U32.inc(i), and_right(dig_ok(d), all_dig(rest), h)))

# Every digit render writes is fine, whatever n is
law hd_ok:
  for +n: U32
  {dig_ok(Path.hex_digit(n)) == True{} : Bool}

def hd_ok(n):
  hdg(Path.hex_digits(), n, 0, {==})

law hd_upper:
  for +n: U32
  {Path.is_upper_hex(Path.hex_digit(n)) == True{} : Bool}

def hd_upper(n):
  and_left(Path.is_upper_hex(Path.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Path.hex_digit(n), 47)), U32.is_le(Path.hex_digit(n), 255)), hd_ok(n))

law hd_not_slash:
  for +n: U32
  {Bool.not(U32.is_eq(Path.hex_digit(n), 47)) == True{} : Bool}

def hd_not_slash(n):
  and_left(Bool.not(U32.is_eq(Path.hex_digit(n), 47)), U32.is_le(Path.hex_digit(n), 255),
    and_right(Path.is_upper_hex(Path.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Path.hex_digit(n), 47)), U32.is_le(Path.hex_digit(n), 255)), hd_ok(n)))

law hd_byte:
  for +n: U32
  {U32.is_le(Path.hex_digit(n), 255) == True{} : Bool}

def hd_byte(n):
  and_right(Bool.not(U32.is_eq(Path.hex_digit(n), 47)), U32.is_le(Path.hex_digit(n), 255),
    and_right(Path.is_upper_hex(Path.hex_digit(n)), Bool.and(Bool.not(U32.is_eq(Path.hex_digit(n), 47)), U32.is_le(Path.hex_digit(n), 255)), hd_ok(n)))

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

# Appending after an encoded byte is the same as encoding in front of the append
law ae_at:
  for k: Bool
  for +c: U32
  for e: List<&2, U32>
  for rest: List<&2, U32>
  {List.append(&2, U32, Path.enc_byte.if(k, c, e), rest) == Path.enc_byte.if(k, c, List.append(&2, U32, e, rest)) : List<&2, U32>}

def ae_at(k, c, e, rest):
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

law ae:
  for +c: U32
  for e: List<&2, U32>
  for rest: List<&2, U32>
  {List.append(&2, U32, Path.enc_byte(c, e), rest) == Path.enc_byte(c, List.append(&2, U32, e, rest)) : List<&2, U32>}

def ae(c, e, rest):
  ae_at(Path.is_pchar(c), c, e, rest)

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


# ---- U7: render writes canonical bytes ----

# The canonical check passes straight over one encoded byte
law cb_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Path.is_pchar(c) : Bool}
  {Path.canonical.go(Path.enc_byte.if(k, c, r), 0n) == Path.canonical.go(r, 0n) : Bool}

def cb_at(k, c, r, ek):
  match k:
    case True{}:
      %ek : {Path.canonical.plain(_, U32.is_eq(c, 47), U32.is_eq(c, 37), Path.canonical.go(r, Path.canonical.next(_, U32.is_eq(c, 37)))) == Path.canonical.go(r, 0n) : Bool}
      {==}
    case False{}:
      ux = Equal.sym(Bool, Path.is_upper_hex(Path.hex_digit(Path.hi_nibble(c))), True{}, hd_upper(Path.hi_nibble(c)))
      uy = Equal.sym(Bool, Path.is_upper_hex(Path.hex_digit(Path.lo_nibble(c))), True{}, hd_upper(Path.lo_nibble(c)))
      %ux : {Bool.and(_, Bool.and(Path.is_upper_hex(Path.hex_digit(Path.lo_nibble(c))), Path.canonical.go(r, 0n))) == Path.canonical.go(r, 0n) : Bool}
      %uy : {Bool.and(_, Path.canonical.go(r, 0n)) == Path.canonical.go(r, 0n) : Bool}
      {==}

law cb:
  for +c: U32
  for +r: List<&2, U32>
  {Path.canonical.go(Path.enc_byte(c, r), 0n) == Path.canonical.go(r, 0n) : Bool}

def cb(c, r):
  cb_at(Path.is_pchar(c), c, r, {==})

# ... and over a whole encoded segment
law ce:
  for s: List<&2, U32>
  for +rest: List<&2, U32>
  {Path.canonical.go(List.append(&2, U32, Path.enc_seg(s), rest), 0n) == Path.canonical.go(rest, 0n) : Bool}

def ce(s, rest):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      a = Equal.sym(List<&2, U32>, List.append(&2, U32, Path.enc_byte(c, Path.enc_seg(t)), rest), Path.enc_byte(c, List.append(&2, U32, Path.enc_seg(t), rest)), ae(c, Path.enc_seg(t), rest))
      %a : {Path.canonical.go(_, 0n) == Path.canonical.go(rest, 0n) : Bool}
      Equal.trans(Bool, Path.canonical.go(Path.enc_byte(c, List.append(&2, U32, Path.enc_seg(t), rest)), 0n),
        Path.canonical.go(List.append(&2, U32, Path.enc_seg(t), rest), 0n), Path.canonical.go(rest, 0n),
        cb(c, List.append(&2, U32, Path.enc_seg(t), rest)), ce(t, rest))

# The joined encoded segments are canonical (r first, so it can shrink)
law cj:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  {Path.canonical.go(Path.join(Con{Path.enc_seg(s), Path.enc_segs(r)}), 0n) == True{} : Bool}

def cj(r, s):
  match r:
    case Nil{}:
      a = app_nil(Path.enc_seg(s))
      %a : {Path.canonical.go(_, 0n) == True{} : Bool}
      ce(s, Nil{})
    case Con{+r1, +rr}:
      +j = {Con{47, Path.join(Con{Path.enc_seg(r1), Path.enc_segs(rr)})} : List<&2, U32>}
      a = Equal.sym(Bool, Path.canonical.go(List.append(&2, U32, Path.enc_seg(s), j), 0n), Path.canonical.go(j, 0n), ce(s, j))
      %a : {_ == True{} : Bool}
      cj(rr, r1)

def Laws.render_canonical(p):
  match p:
    case Nil{}:
      {==}
    case Con{+s, r}:
      cj(r, s)


# ---- U6: render never starts with "//" ----

# A pchar byte is never "/"
law pns_at:
  for k: Bool
  for +c: U32
  for ek: {k == U32.is_eq(c, 47) : Bool}
  for h: {Path.is_pchar(c) == True{} : Bool}
  {k == False{} : Bool}

def pns_at(k, c, ek, h):
  match k:
    case True{}:
      e = MStr.u32_eq_of_is_eq(c, 47, Equal.sym(Bool, True{}, U32.is_eq(c, 47), ek))
      hp = Equal.trans(Bool, Path.is_pchar(47), Path.is_pchar(c), True{},
        Equal.cong(U32, Bool, +x => Path.is_pchar(x), 47, c, Equal.sym(U32, c, 47, e)), h)
      absurd({True{} == False{} : Bool}, true_ne_false(hp))
    case False{}:
      {==}

law pns:
  for +c: U32
  for h: {Path.is_pchar(c) == True{} : Bool}
  {U32.is_eq(c, 47) == False{} : Bool}

def pns(c, h):
  pns_at(U32.is_eq(c, 47), c, {==}, h)

# An encoded byte never starts with "/"
law fb_at:
  for k: Bool
  for +c: U32
  for r: List<&2, U32>
  for ek: {k == Path.is_pchar(c) : Bool}
  {Path.starts_with_double_slash.two(47, Path.enc_byte.if(k, c, r)) == False{} : Bool}

def fb_at(k, c, r, ek):
  match k:
    case True{}:
      pns(c, Equal.sym(Bool, True{}, Path.is_pchar(c), ek))
    case False{}:
      {==}

law fb:
  for +c: U32
  for r: List<&2, U32>
  {Path.starts_with_double_slash.two(47, Path.enc_byte(c, r)) == False{} : Bool}

def fb(c, r):
  fb_at(Path.is_pchar(c), c, r, {==})

law ds:
  for p: List<&2, List<&2, U32>>
  for h: {Path.empty_only_last(p) == True{} : Bool}
  {Path.starts_with_double_slash(Path.render(p)) == False{} : Bool}

def ds(p, h):
  match p:
    case Nil{}:
      absurd({Path.starts_with_double_slash(Path.render(Nil{})) == False{} : Bool}, true_ne_false(h))
    case Con{s, r}:
      match s:
        case Nil{}:
          match r:
            case Nil{}:
              {==}
            case Con{r1, rr}:
              absurd({Path.starts_with_double_slash(Path.render(Con{Nil{}, Con{r1, rr}})) == False{} : Bool}, true_ne_false(h))
        case Con{+c, +t}:
          match r:
            case Nil{}:
              fb(c, Path.enc_seg(t))
            case Con{+r1, +rr}:
              +j = {Con{47, Path.join(Con{Path.enc_seg(r1), Path.enc_segs(rr)})} : List<&2, U32>}
              a = Equal.sym(List<&2, U32>, List.append(&2, U32, Path.enc_byte(c, Path.enc_seg(t)), j), Path.enc_byte(c, List.append(&2, U32, Path.enc_seg(t), j)), ae(c, Path.enc_seg(t), j))
              %a : {Path.starts_with_double_slash.two(47, _) == False{} : Bool}
              fb(c, List.append(&2, U32, Path.enc_seg(t), j))

def Laws.render_no_double_slash(b, p, e):
  ds(p, Laws.empty_only_last(b, p, e))


# ---- Byte facts checked for every value (used by U5) ----
# A U32 that is at most 255 is one of 256 values, so a fact about it can be
# checked by computing it for each value, then applied to any such U32.

# The %XX round trip for byte c: both digits are hex and decode back to c
def rt(+c: U32) -> Bool:
  Bool.and(Path.is_hex(Path.hex_digit(Path.hi_nibble(c))),
    Bool.and(Path.is_hex(Path.hex_digit(Path.lo_nibble(c))),
      U32.is_eq(Path.hex_pair(Path.hex_val(Path.hex_digit(Path.hi_nibble(c))), Path.hex_val(Path.hex_digit(Path.lo_nibble(c)))), c)))

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
      Bool.or(Bool.not(Path.is_hex(x)), U32.is_le(Path.hex_val(x), 15))
    case PairByte{+hi}:
      U32.is_le(Path.hex_pair(hi, x), 255)

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
          absurd({chk(c, U32.from_nat(addr(1n+q, k))) == True{} : Bool}, true_ne_false(hj))
    case 1n+(+p):
      match j:
        case 0n:
          and_left(chk(c, U32.from_nat(k)), chk_all(c, p, 1n+k), h)
        case 1n+q:
          chk_ext(c, p, 1n+k, q, and_right(chk(c, U32.from_nat(k)), chk_all(c, p, 1n+k), h), hj)

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

# A hex digit's value is at most 15
law hex_small:
  for +x: U32
  for hx: {U32.is_le(x, 255) == True{} : Bool}
  for hh: {Path.is_hex(x) == True{} : Bool}
  {U32.is_le(Path.hex_val(x), 15) == True{} : Bool}

def hex_small(x, hx, hh):
  implies(Path.is_hex(x), U32.is_le(Path.hex_val(x), 15),
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
          absurd({chk_all(PairByte{U32.from_nat(addr(1n+q, k))}, 15n, 0n) == True{} : Bool}, true_ne_false(hj))
    case 1n+(+p):
      match j:
        case 0n:
          and_left(chk_all(PairByte{U32.from_nat(k)}, 15n, 0n), pair_all(p, 1n+k), h)
        case 1n+q:
          pair_ext(p, 1n+k, q, and_right(chk_all(PairByte{U32.from_nat(k)}, 15n, 0n), pair_all(p, 1n+k), h), hj)

law all_pairs:
  {pair_all(15n, 0n) == True{} : Bool}

def all_pairs():
  {==}

law pair_byte:
  for +hi: U32
  for +lo: U32
  for hh: {U32.is_le(hi, 15) == True{} : Bool}
  for hl: {U32.is_le(lo, 15) == True{} : Bool}
  {U32.is_le(Path.hex_pair(hi, lo), 255) == True{} : Bool}

def pair_byte(hi, lo, hh, hl):
  ft = Kit.u32_from_to_nat(hi)
  %ft : {U32.is_le(Path.hex_pair(_, lo), 255) == True{} : Bool}
  az = addr_zero(U32.to_nat(hi))
  %az : {U32.is_le(Path.hex_pair(U32.from_nat(_), lo), 255) == True{} : Bool}
  chk_u32(PairByte{U32.from_nat(addr(U32.to_nat(hi), 0n))}, lo, 15n, le15(lo, hl),
    pair_ext(15n, 0n, U32.to_nat(hi), all_pairs(), le15(hi, hh)))


# ---- Decoding only produces bytes ----

def DecOk(r: Result<&2, &2, Path.PathError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{d}:
      {Path.all_bytes(d) == True{} : Bool}

# In the middle of an escape, the first digit's value is at most 15
def StOk(st: Path.DecState) -> Type:
  match st:
    case Path.Plain{}:
      Unit
    case Path.Hex1{}:
      Unit
    case Path.Hex2{hi}:
      {U32.is_le(hi, 15) == True{} : Bool}

law dec_okcons:
  for +b: U32
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hr: DecOk(r)
  DecOk(Path.ok_cons(b, r))

def dec_okcons(b, r, hb, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      and_intro(U32.is_le(b, 255), Path.all_bytes(d), hb, hr)

law dec_plain:
  for p: Bool
  for q: Bool
  for +b: U32
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for ih: StOk(Path.decode.next.plain(p, q)) -> DecOk(r)
  DecOk(Path.decode.step.plain(b, r, p, q))

def dec_plain(p, q, b, r, hb, ih):
  match p:
    case True{}:
      dec_okcons(b, r, hb, ih(Unit{}))
    case False{}:
      match q:
        case True{}:
          ih(Unit{})
        case False{}:
          Unit{}

law dec_hex1:
  for k: Bool
  for +b: U32
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for ek: {k == Path.is_hex(b) : Bool}
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for ih: StOk(Path.Hex2{Path.hex_val(b)}) -> DecOk(r)
  DecOk(Path.decode.step.hex1(r, k))

def dec_hex1(k, b, r, ek, hb, ih):
  match k:
    case True{}:
      ih(hex_small(b, hb, Equal.sym(Bool, True{}, Path.is_hex(b), ek)))
    case False{}:
      Unit{}

law dec_hex2:
  for k: Bool
  for +hi: U32
  for +b: U32
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for ek: {k == Path.is_hex(b) : Bool}
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hh: {U32.is_le(hi, 15) == True{} : Bool}
  for ih: Unit -> DecOk(r)
  DecOk(Path.decode.step.hex2(Path.hex_pair(hi, Path.hex_val(b)), r, k))

def dec_hex2(k, hi, b, r, ek, hb, hh, ih):
  match k:
    case True{}:
      dec_okcons(Path.hex_pair(hi, Path.hex_val(b)), r,
        pair_byte(hi, Path.hex_val(b), hh, hex_small(b, hb, Equal.sym(Bool, True{}, Path.is_hex(b), ek))),
        ih(Unit{}))
    case False{}:
      Unit{}

law dec_step:
  for +b: U32
  for st: Path.DecState
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hst: StOk(st)
  for ih: StOk(Path.decode.next(b, st)) -> DecOk(r)
  DecOk(Path.decode.step(b, st, r))

def dec_step(b, st, r, hb, hst, ih):
  match st:
    case Path.Plain{}:
      dec_plain(Path.is_pchar(b), U32.is_eq(b, 37), b, r, hb, ih)
    case Path.Hex1{}:
      dec_hex1(Path.is_hex(b), b, r, {==}, hb, ih)
    case Path.Hex2{+hi}:
      dec_hex2(Path.is_hex(b), hi, b, r, {==}, hb, hst, ih)

law dec_go:
  for seg: List<&2, U32>
  for +st: Path.DecState
  for +hs: {Path.all_bytes(seg) == True{} : Bool}
  for hst: StOk(st)
  DecOk(Path.decode.go(seg, st))

def dec_go(seg, st, hs, hst):
  match seg:
    case Nil{}:
      match st:
        case Path.Plain{}:
          {==}
        case Path.Hex1{}:
          Unit{}
        case Path.Hex2{hi}:
          Unit{}
    case Con{+b, +t}:
      dec_step(b, st, Path.decode.go(t, Path.decode.next(b, st)),
        and_left(U32.is_le(b, 255), Path.all_bytes(t), hs), hst,
        z => dec_go(t, Path.decode.next(b, st), and_right(U32.is_le(b, 255), Path.all_bytes(t), hs), z))


# ---- More about accepted segments: they're bytes, and don't start with ".;" ----

def xseg(+s: List<&2, U32>) -> Bool:
  Bool.and(Path.all_bytes(s), Bool.not(Path.dot_semi(s)))

def xall(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{+s, t}:
      Bool.and(xseg(s), xall(t))

def allb_segs(p: List<&2, List<&2, U32>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(Path.all_bytes(s), allb_segs(t))

def XOk(r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {xall(p) == True{} : Bool}

def SegX(r: Result<&2, &2, Path.PathError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      {xseg(s) == True{} : Bool}

# Splitting bytes gives segments of bytes
law sb_at:
  for k: Bool
  for +h: U32
  for segs: List<&2, List<&2, U32>>
  for hh: {U32.is_le(h, 255) == True{} : Bool}
  for +hs: {allb_segs(segs) == True{} : Bool}
  {allb_segs(Path.split.if(h, segs, k)) == True{} : Bool}

def sb_at(k, h, segs, hh, hs):
  match k:
    case True{}:
      hs
    case False{}:
      match segs:
        case Nil{}:
          and_intro(Path.all_bytes([h]), True{}, and_intro(U32.is_le(h, 255), True{}, hh, {==}), {==})
        case Con{+f, +o}:
          and_intro(Path.all_bytes(Con{h, f}), allb_segs(o),
            and_intro(U32.is_le(h, 255), Path.all_bytes(f), hh, and_left(Path.all_bytes(f), allb_segs(o), hs)),
            and_right(Path.all_bytes(f), allb_segs(o), hs))

law split_bytes:
  for b: List<&2, U32>
  for +hb: {Path.all_bytes(b) == True{} : Bool}
  {allb_segs(Path.split(b)) == True{} : Bool}

def split_bytes(b, hb):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      sb_at(U32.is_eq(h, 47), h, Path.split(t),
        and_left(U32.is_le(h, 255), Path.all_bytes(t), hb),
        split_bytes(t, and_right(U32.is_le(h, 255), Path.all_bytes(t), hb)))

law x_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for +l: Bool
  for ek: {k == Path.seg_ok(raw, d, l) : Bool}
  for hd: {Path.all_bytes(d) == True{} : Bool}
  SegX(Path.check_decoded.if(k, raw, d))

def x_seg_if(k, raw, d, l, ek, hd):
  match k:
    case True{}:
      and_intro(Path.all_bytes(d), Bool.not(Path.dot_semi(d)), hd,
        and_right(Bool.not(Bool.and(Path.is_dot_seg(d), Path.has_byte(raw, 37))), Bool.not(Path.dot_semi(d)),
          and_right(Path.safe_seg(d), Path.seg_ok.dots(raw, d),
            and_left(Path.seg_ok.shape(raw, d), Path.seg_ok.place(d, l),
              Equal.sym(Bool, True{}, Path.seg_ok(raw, d, l), ek)))))
    case False{}:
      Unit{}

law x_seg_d:
  for r: Result<&2, &2, Path.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  for hd: DecOk(r)
  SegX(Path.check_seg.d(r, raw, l))

def x_seg_d(r, raw, l, hd):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      x_seg_if(Path.seg_ok(raw, d, l), raw, d, l, {==}, hd)

law x_cons:
  for a: Result<&2, &2, Path.PathError, List<&2, U32>>
  for b: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for ha: SegX(a)
  for hb: XOk(b)
  XOk(Path.check_all.cons(a, b))

def x_cons(a, b, ha, hb):
  match a:
    case Fail{e}:
      Unit{}
    case Done{+s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{+ss}:
          and_intro(xseg(s), xall(ss), ha, hb)

law x_ca:
  for raws: List<&2, List<&2, U32>>
  for +h: {allb_segs(raws) == True{} : Bool}
  XOk(Path.check_all(raws))

def x_ca(raws, h):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      x_cons(Path.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Path.check_all(rest),
        x_seg_d(Path.decode(r), r, List.is_empty(&2, List<&2, U32>, rest),
          dec_go(r, Path.Plain{}, and_left(Path.all_bytes(r), allb_segs(rest), h), Unit{})),
        x_ca(rest, and_right(Path.all_bytes(r), allb_segs(rest), h)))

law x_step:
  for k: Path.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Path.Dots
  for hs: {xseg(s) == True{} : Bool}
  for ih: {xall(kept_of(d)) == True{} : Bool}
  {xall(kept_of(Path.rd.step(k, s, l, d))) == True{} : Bool}

def x_step(k, s, l, d, hs, ih):
  match k:
    case Path.Other{}:
      match l:
        case True{}:
          and_intro(xseg(s), True{}, hs, {==})
        case False{}:
          match d:
            case Path.Dots{up, +kept}:
              match up:
                case 0n:
                  and_intro(xseg(s), xall(kept), hs, ih)
                case 1n+n:
                  ih
    case Path.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Path.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Path.Dots{up, kept}:
              ih

law x_kept:
  for segs: List<&2, List<&2, U32>>
  for +h: {xall(segs) == True{} : Bool}
  {xall(kept_of(Path.rd(segs))) == True{} : Bool}

def x_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      x_step(Path.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Path.rd(rest),
        and_left(xseg(s), xall(rest), h),
        x_kept(rest, and_right(xseg(s), xall(rest), h)))

law x_end:
  for d: Path.Dots
  for h: {xall(kept_of(d)) == True{} : Bool}
  XOk(Path.rd.end(d))

def x_end(d, h):
  match d:
    case Path.Dots{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law x_dots:
  for r: Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>
  for h: XOk(r)
  XOk(Path.parse.dots(r))

def x_dots(r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      x_end(Path.rd(ds), x_kept(ds, h))

law x_slash:
  for k: Bool
  for +t: List<&2, U32>
  for ht: {Path.all_bytes(t) == True{} : Bool}
  XOk(Path.parse.slash(k, t))

def x_slash(k, t, ht):
  match k:
    case True{}:
      x_dots(Path.check_all(Path.split(t)), x_ca(Path.split(t), split_bytes(t, ht)))
    case False{}:
      Unit{}

law x_first:
  for b: List<&2, U32>
  for hb: {Path.all_bytes(b) == True{} : Bool}
  XOk(Path.parse.first(b))

def x_first(b, hb):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, +t}:
      x_slash(U32.is_eq(c, 47), t, and_right(U32.is_le(c, 255), Path.all_bytes(t), hb))

law x_bytes:
  for k: Bool
  for +b: List<&2, U32>
  for ek: {k == Path.all_bytes(b) : Bool}
  XOk(Path.parse.bytes(k, b))

def x_bytes(k, b, ek):
  match k:
    case True{}:
      x_first(b, Equal.sym(Bool, True{}, Path.all_bytes(b), ek))
    case False{}:
      Unit{}

law x_parse:
  for +b: List<&2, U32>
  for p: List<&2, List<&2, U32>>
  for e: {Path.parse(b) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
  {xall(p) == True{} : Bool}

def x_parse(b, p, e):
  %e : XOk(_)
  x_bytes(Path.all_bytes(b), b, {==})


# ---- U5: parse(render(p)) gives p back ----

# Decoding an encoded byte gives the byte back
law db_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Path.is_pchar(c) : Bool}
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Path.decode.go(Path.enc_byte.if(k, c, r), Path.Plain{}) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}

def db_at(k, c, r, ek, hc):
  match k:
    case True{}:
      %ek : {Path.decode.step.plain(c, Path.decode.go(r, Path.decode.next.plain(_, U32.is_eq(c, 37))), _, U32.is_eq(c, 37)) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}
      {==}
    case False{}:
      +x = Path.hex_digit(Path.hi_nibble(c))
      +y = Path.hex_digit(Path.lo_nibble(c))
      +h = byte_rt(c, hc)
      +h2 = and_right(Path.is_hex(x), Bool.and(Path.is_hex(y), U32.is_eq(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c)), h)
      hx = Equal.sym(Bool, Path.is_hex(x), True{}, and_left(Path.is_hex(x), Bool.and(Path.is_hex(y), U32.is_eq(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c)), h))
      hy = Equal.sym(Bool, Path.is_hex(y), True{}, and_left(Path.is_hex(y), U32.is_eq(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c), h2))
      pe = Equal.sym(U32, Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c,
        MStr.u32_eq_of_is_eq(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c,
          and_right(Path.is_hex(y), U32.is_eq(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), c), h2)))
      %hx : {Path.decode.step.hex1(Path.decode.go(Con{y, r}, Path.Hex2{Path.hex_val(x)}), _) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}
      %hy : {Path.decode.step.hex2(Path.hex_pair(Path.hex_val(x), Path.hex_val(y)), Path.decode.go(r, Path.Plain{}), _) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}
      %pe : {Path.ok_cons(_, Path.decode.go(r, Path.Plain{})) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}
      {==}

law db:
  for +c: U32
  for +r: List<&2, U32>
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Path.decode.go(Path.enc_byte(c, r), Path.Plain{}) == Path.ok_cons(c, Path.decode.go(r, Path.Plain{})) : Result<&2, &2, Path.PathError, List<&2, U32>>}

def db(c, r, hc):
  db_at(Path.is_pchar(c), c, r, {==}, hc)

# Decoding an encoded segment gives the segment back
law dec_enc:
  for s: List<&2, U32>
  for +hs: {Path.all_bytes(s) == True{} : Bool}
  {Path.decode.go(Path.enc_seg(s), Path.Plain{}) == Done{s} : Result<&2, &2, Path.PathError, List<&2, U32>>}

def dec_enc(s, hs):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(Result<&2, &2, Path.PathError, List<&2, U32>>,
        Path.decode.go(Path.enc_byte(c, Path.enc_seg(t)), Path.Plain{}),
        Path.ok_cons(c, Path.decode.go(Path.enc_seg(t), Path.Plain{})),
        Done{Con{c, t}},
        db(c, Path.enc_seg(t), and_left(U32.is_le(c, 255), Path.all_bytes(t), hs)),
        Equal.cong(Result<&2, &2, Path.PathError, List<&2, U32>>, Result<&2, &2, Path.PathError, List<&2, U32>>,
          r => Path.ok_cons(c, r), Path.decode.go(Path.enc_seg(t), Path.Plain{}), Done{t},
          dec_enc(t, and_right(U32.is_le(c, 255), Path.all_bytes(t), hs))))

# A segment that isn't "." or ".." passes the encoded-dot check
law nd_ok:
  for +s: List<&2, U32>
  for +raw: List<&2, U32>
  for hn: {Bool.not(Path.is_dot_seg(s)) == True{} : Bool}
  {Bool.not(Bool.and(Path.is_dot_seg(s), Path.has_byte(raw, 37))) == True{} : Bool}

def nd_ok(s, raw, hn):
  e = Equal.sym(Bool, Path.is_dot_seg(s), False{}, not_true(Path.is_dot_seg(s), hn))
  %e : {Bool.not(Bool.and(_, Path.has_byte(raw, 37))) == True{} : Bool}
  {==}

# Checking an encoded accepted segment gives the segment back
law cs:
  for +s: List<&2, U32>
  for +l: Bool
  for hs1: {Path.safe_seg(s) == True{} : Bool}
  for hn1: {Bool.not(Path.is_dot_seg(s)) == True{} : Bool}
  for +hx1: {xseg(s) == True{} : Bool}
  for hp: {Path.seg_ok.place(s, l) == True{} : Bool}
  {Path.check_seg(Path.enc_seg(s), l) == Done{s} : Result<&2, &2, Path.PathError, List<&2, U32>>}

def cs(s, l, hs1, hn1, hx1, hp):
  de = Equal.sym(Result<&2, &2, Path.PathError, List<&2, U32>>, Path.decode.go(Path.enc_seg(s), Path.Plain{}), Done{s},
    dec_enc(s, and_left(Path.all_bytes(s), Bool.not(Path.dot_semi(s)), hx1)))
  %de : {Path.check_seg.d(_, Path.enc_seg(s), l) == Done{s} : Result<&2, &2, Path.PathError, List<&2, U32>>}
  so = and_intro(Path.seg_ok.shape(Path.enc_seg(s), s), Path.seg_ok.place(s, l),
    and_intro(Path.safe_seg(s), Path.seg_ok.dots(Path.enc_seg(s), s), hs1,
      and_intro(Bool.not(Bool.and(Path.is_dot_seg(s), Path.has_byte(Path.enc_seg(s), 37))), Bool.not(Path.dot_semi(s)),
        nd_ok(s, Path.enc_seg(s), hn1),
        and_right(Path.all_bytes(s), Bool.not(Path.dot_semi(s)), hx1))),
    hp)
  e = Equal.sym(Bool, Path.seg_ok(Path.enc_seg(s), s, l), True{}, so)
  %e : {Path.check_decoded.if(_, Path.enc_seg(s), s) == Done{s} : Result<&2, &2, Path.PathError, List<&2, U32>>}
  {==}

# Checking all the encoded segments gives them back (r first, so it can shrink)
law ca3:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hn: {Path.no_dot_segs(Con{s, r}) == True{} : Bool}
  for +hs: {Path.all_safe(Con{s, r}) == True{} : Bool}
  for +hx: {xall(Con{s, r}) == True{} : Bool}
  for +ho: {Path.only_last_empty(Con{s, r}) == True{} : Bool}
  {Path.check_all(Path.enc_segs(Con{s, r})) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

def ca3(r, s, hn, hs, hx, ho):
  match r:
    case Nil{}:
      c = Equal.sym(Result<&2, &2, Path.PathError, List<&2, U32>>, Path.check_seg(Path.enc_seg(s), True{}), Done{s},
        cs(s, True{}, and_left(Path.safe_seg(s), True{}, hs), and_left(Bool.not(Path.is_dot_seg(s)), True{}, hn),
          and_left(xseg(s), True{}, hx), {==}))
      %c : {Path.check_all.cons(_, Done{Nil{}}) == Done{[s]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
      {==}
    case Con{+r1, +rr}:
      c = Equal.sym(Result<&2, &2, Path.PathError, List<&2, U32>>, Path.check_seg(Path.enc_seg(s), False{}), Done{s},
        cs(s, False{},
          and_left(Path.safe_seg(s), Path.all_safe(Con{r1, rr}), hs),
          and_left(Bool.not(Path.is_dot_seg(s)), Path.no_dot_segs(Con{r1, rr}), hn),
          and_left(xseg(s), xall(Con{r1, rr}), hx),
          and_left(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(Con{r1, rr}), ho)))
      ih = Equal.sym(Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>, Path.check_all(Path.enc_segs(Con{r1, rr})), Done{Con{r1, rr}},
        ca3(rr, r1,
          and_right(Bool.not(Path.is_dot_seg(s)), Path.no_dot_segs(Con{r1, rr}), hn),
          and_right(Path.safe_seg(s), Path.all_safe(Con{r1, rr}), hs),
          and_right(xseg(s), xall(Con{r1, rr}), hx),
          and_right(Bool.not(List.is_empty(&2, U32, s)), Path.only_last_empty(Con{r1, rr}), ho)))
      %c : {Path.check_all.cons(_, Path.check_all(Path.enc_segs(Con{r1, rr}))) == Done{Con{s, Con{r1, rr}}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
      %ih : {Path.check_all.cons(Done{s}, _) == Done{Con{s, Con{r1, rr}}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
      {==}

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

# Splitting bytes with no "/" gives one segment
law sj0:
  for s: List<&2, U32>
  for +h: {Path.has_byte(s, 47) == False{} : Bool}
  {Path.split(s) == [s] : List<&2, List<&2, U32>>}

def sj0(s, h):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      hc = Equal.sym(Bool, U32.is_eq(c, 47), False{}, or_l(U32.is_eq(c, 47), Path.has_byte(t, 47), h))
      ih = Equal.sym(List<&2, List<&2, U32>>, Path.split(t), [t], sj0(t, or_r(U32.is_eq(c, 47), Path.has_byte(t, 47), h)))
      %hc : {Path.split.if(c, Path.split(t), _) == [Con{c, t}] : List<&2, List<&2, U32>>}
      %ih : {Path.add_head(c, _) == [Con{c, t}] : List<&2, List<&2, U32>>}
      {==}

# Splitting "s/rest" with no "/" in s gives s, then the split of rest
law sj1:
  for s: List<&2, U32>
  for +j: List<&2, U32>
  for +h: {Path.has_byte(s, 47) == False{} : Bool}
  {Path.split(List.append(&2, U32, s, Con{47, j})) == Con{s, Path.split(j)} : List<&2, List<&2, U32>>}

def sj1(s, j, h):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      hc = Equal.sym(Bool, U32.is_eq(c, 47), False{}, or_l(U32.is_eq(c, 47), Path.has_byte(t, 47), h))
      ih = Equal.sym(List<&2, List<&2, U32>>, Path.split(List.append(&2, U32, t, Con{47, j})), Con{t, Path.split(j)},
        sj1(t, j, or_r(U32.is_eq(c, 47), Path.has_byte(t, 47), h)))
      %hc : {Path.split.if(c, Path.split(List.append(&2, U32, t, Con{47, j})), _) == Con{Con{c, t}, Path.split(j)} : List<&2, List<&2, U32>>}
      %ih : {Path.add_head(c, _) == Con{Con{c, t}, Path.split(j)} : List<&2, List<&2, U32>>}
      {==}

# An encoded byte adds no "/"
law heb_at:
  for k: Bool
  for +c: U32
  for +e: List<&2, U32>
  for ek: {k == Path.is_pchar(c) : Bool}
  {Path.has_byte(Path.enc_byte.if(k, c, e), 47) == Path.has_byte(e, 47) : Bool}

def heb_at(k, c, e, ek):
  match k:
    case True{}:
      n = Equal.sym(Bool, U32.is_eq(c, 47), False{}, pns(c, Equal.sym(Bool, True{}, Path.is_pchar(c), ek)))
      %n : {Bool.or(_, Path.has_byte(e, 47)) == Path.has_byte(e, 47) : Bool}
      {==}
    case False{}:
      +x = Path.hex_digit(Path.hi_nibble(c))
      +y = Path.hex_digit(Path.lo_nibble(c))
      nx = Equal.sym(Bool, U32.is_eq(x, 47), False{}, not_true(U32.is_eq(x, 47), hd_not_slash(Path.hi_nibble(c))))
      ny = Equal.sym(Bool, U32.is_eq(y, 47), False{}, not_true(U32.is_eq(y, 47), hd_not_slash(Path.lo_nibble(c))))
      %nx : {Bool.or(_, Bool.or(U32.is_eq(y, 47), Path.has_byte(e, 47))) == Path.has_byte(e, 47) : Bool}
      %ny : {Bool.or(_, Path.has_byte(e, 47)) == Path.has_byte(e, 47) : Bool}
      {==}

# An encoded segment has no "/"
law he:
  for s: List<&2, U32>
  {Path.has_byte(Path.enc_seg(s), 47) == False{} : Bool}

def he(s):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(Bool, Path.has_byte(Path.enc_byte(c, Path.enc_seg(t)), 47), Path.has_byte(Path.enc_seg(t), 47), False{},
        heb_at(Path.is_pchar(c), c, Path.enc_seg(t), {==}), he(t))

# Splitting the joined encoded segments gives them back
law sje:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  {Path.split(Path.join(Con{Path.enc_seg(s), Path.enc_segs(r)})) == Con{Path.enc_seg(s), Path.enc_segs(r)} : List<&2, List<&2, U32>>}

def sje(r, s):
  match r:
    case Nil{}:
      sj0(Path.enc_seg(s), he(s))
    case Con{+r1, +rr}:
      +j = {Path.join(Con{Path.enc_seg(r1), Path.enc_segs(rr)}) : List<&2, U32>}
      Equal.trans(List<&2, List<&2, U32>>,
        Path.split(List.append(&2, U32, Path.enc_seg(s), Con{47, j})),
        Con{Path.enc_seg(s), Path.split(j)},
        Con{Path.enc_seg(s), Con{Path.enc_seg(r1), Path.enc_segs(rr)}},
        sj1(Path.enc_seg(s), j, he(s)),
        Equal.cong(List<&2, List<&2, U32>>, List<&2, List<&2, U32>>, x => Con{Path.enc_seg(s), x},
          Path.split(j), Con{Path.enc_seg(r1), Path.enc_segs(rr)}, sje(rr, r1)))

# The encoded bytes are all bytes
law abb_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Path.is_pchar(c) : Bool}
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Path.all_bytes(Path.enc_byte.if(k, c, r)) == Path.all_bytes(r) : Bool}

def abb_at(k, c, r, ek, hc):
  match k:
    case True{}:
      e = Equal.sym(Bool, U32.is_le(c, 255), True{}, hc)
      %e : {Bool.and(_, Path.all_bytes(r)) == Path.all_bytes(r) : Bool}
      {==}
    case False{}:
      +x = Path.hex_digit(Path.hi_nibble(c))
      +y = Path.hex_digit(Path.lo_nibble(c))
      bx = Equal.sym(Bool, U32.is_le(x, 255), True{}, hd_byte(Path.hi_nibble(c)))
      by = Equal.sym(Bool, U32.is_le(y, 255), True{}, hd_byte(Path.lo_nibble(c)))
      %bx : {Bool.and(_, Bool.and(U32.is_le(y, 255), Path.all_bytes(r))) == Path.all_bytes(r) : Bool}
      %by : {Bool.and(_, Path.all_bytes(r)) == Path.all_bytes(r) : Bool}
      {==}

law abe:
  for s: List<&2, U32>
  for +rest: List<&2, U32>
  for +hs: {Path.all_bytes(s) == True{} : Bool}
  {Path.all_bytes(List.append(&2, U32, Path.enc_seg(s), rest)) == Path.all_bytes(rest) : Bool}

def abe(s, rest, hs):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      a = Equal.sym(List<&2, U32>, List.append(&2, U32, Path.enc_byte(c, Path.enc_seg(t)), rest), Path.enc_byte(c, List.append(&2, U32, Path.enc_seg(t), rest)), ae(c, Path.enc_seg(t), rest))
      %a : {Path.all_bytes(_) == Path.all_bytes(rest) : Bool}
      Equal.trans(Bool, Path.all_bytes(Path.enc_byte(c, List.append(&2, U32, Path.enc_seg(t), rest))),
        Path.all_bytes(List.append(&2, U32, Path.enc_seg(t), rest)), Path.all_bytes(rest),
        abb_at(Path.is_pchar(c), c, List.append(&2, U32, Path.enc_seg(t), rest), {==}, and_left(U32.is_le(c, 255), Path.all_bytes(t), hs)),
        abe(t, rest, and_right(U32.is_le(c, 255), Path.all_bytes(t), hs)))

law abj:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hx: {xall(Con{s, r}) == True{} : Bool}
  {Path.all_bytes(Path.join(Con{Path.enc_seg(s), Path.enc_segs(r)})) == True{} : Bool}

def abj(r, s, hx):
  match r:
    case Nil{}:
      a = app_nil(Path.enc_seg(s))
      %a : {Path.all_bytes(_) == True{} : Bool}
      abe(s, Nil{}, and_left(Path.all_bytes(s), Bool.not(Path.dot_semi(s)), and_left(xseg(s), True{}, hx)))
    case Con{+r1, +rr}:
      hs = and_left(Path.all_bytes(s), Bool.not(Path.dot_semi(s)), and_left(xseg(s), xall(Con{r1, rr}), hx))
      +j = {Con{47, Path.join(Con{Path.enc_seg(r1), Path.enc_segs(rr)})} : List<&2, U32>}
      a = Equal.sym(Bool, Path.all_bytes(List.append(&2, U32, Path.enc_seg(s), j)), Path.all_bytes(j), abe(s, j, hs))
      %a : {_ == True{} : Bool}
      abj(rr, r1, and_right(xseg(s), xall(Con{r1, rr}), hx))

# Dot removal leaves an accepted path alone
law rdp_at:
  for k: Path.SegKind
  for +s: List<&2, U32>
  for +r: List<&2, List<&2, U32>>
  for ek: {k == Path.seg_kind(s) : Path.SegKind}
  for hk: {Bool.not(Path.is_dot_seg(s)) == True{} : Bool}
  for ih: {Path.rd(r) == Path.Dots{0n, r} : Path.Dots}
  {Path.rd.step(k, s, List.is_empty(&2, List<&2, U32>, r), Path.rd(r)) == Path.Dots{0n, Con{s, r}} : Path.Dots}

def rdp_at(k, s, r, ek, hk, ih):
  match k:
    case Path.Other{}:
      match r:
        case Nil{}:
          {==}
        case Con{+r1, +rr}:
          e = Equal.sym(Path.Dots, Path.rd(Con{r1, rr}), Path.Dots{0n, Con{r1, rr}}, ih)
          %e : {Path.rd.step(Path.Other{}, s, False{}, _) == Path.Dots{0n, Con{s, Con{r1, rr}}} : Path.Dots}
          {==}
    case Path.Dot{}:
      c = Equal.cong(Path.SegKind, Bool, x => Bool.not(Bool.not(Path.is_other(x))), Path.Dot{}, Path.seg_kind(s), ek)
      absurd({Path.rd.step(Path.Dot{}, s, List.is_empty(&2, List<&2, U32>, r), Path.rd(r)) == Path.Dots{0n, Con{s, r}} : Path.Dots},
        true_ne_false(Equal.trans(Bool, False{}, Bool.not(Bool.not(Path.is_other(Path.seg_kind(s)))), True{}, c, hk)))
    case Path.DotDot{}:
      c = Equal.cong(Path.SegKind, Bool, x => Bool.not(Bool.not(Path.is_other(x))), Path.DotDot{}, Path.seg_kind(s), ek)
      absurd({Path.rd.step(Path.DotDot{}, s, List.is_empty(&2, List<&2, U32>, r), Path.rd(r)) == Path.Dots{0n, Con{s, r}} : Path.Dots},
        true_ne_false(Equal.trans(Bool, False{}, Bool.not(Bool.not(Path.is_other(Path.seg_kind(s)))), True{}, c, hk)))

law rdp:
  for +p: List<&2, List<&2, U32>>
  for +hn: {Path.no_dot_segs(p) == True{} : Bool}
  {Path.rd(p) == Path.Dots{0n, p} : Path.Dots}

def rdp(p, hn):
  match p:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      rdp_at(Path.seg_kind(s), s, r, {==},
        and_left(Bool.not(Path.is_dot_seg(s)), Path.no_dot_segs(r), hn),
        rdp(r, and_right(Bool.not(Path.is_dot_seg(s)), Path.no_dot_segs(r), hn)))

# The round trip, for any segments with the facts parse guarantees
law rt2:
  for +r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hn: {Path.no_dot_segs(Con{s, r}) == True{} : Bool}
  for +hs: {Path.all_safe(Con{s, r}) == True{} : Bool}
  for +he: {Path.empty_only_last(Con{s, r}) == True{} : Bool}
  for +hx: {xall(Con{s, r}) == True{} : Bool}
  {Path.parse(Path.render(Con{s, r})) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

def rt2(r, s, hn, hs, he, hx):
  +j = {Path.join(Con{Path.enc_seg(s), Path.enc_segs(r)}) : List<&2, U32>}
  e1 = Equal.sym(Bool, Path.all_bytes(j), True{}, abj(r, s, hx))
  e2 = Equal.sym(List<&2, List<&2, U32>>, Path.split(j), Con{Path.enc_seg(s), Path.enc_segs(r)}, sje(r, s))
  e3 = Equal.sym(Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>, Path.check_all(Path.enc_segs(Con{s, r})), Done{Con{s, r}}, ca3(r, s, hn, hs, hx, he))
  e4 = Equal.sym(Path.Dots, Path.rd(Con{s, r}), Path.Dots{0n, Con{s, r}}, rdp(Con{s, r}, hn))
  %e1 : {Path.parse.bytes(_, Con{47, j}) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
  %e2 : {Path.parse.dots(Path.check_all(_)) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
  %e3 : {Path.parse.dots(_) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
  %e4 : {Path.rd.end(_) == Done{Con{s, r}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
  {==}

law rt1:
  for p: List<&2, List<&2, U32>>
  for +hn: {Path.no_dot_segs(p) == True{} : Bool}
  for +hs: {Path.all_safe(p) == True{} : Bool}
  for +he: {Path.empty_only_last(p) == True{} : Bool}
  for +hx: {xall(p) == True{} : Bool}
  {Path.parse(Path.render(p)) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

def rt1(p, hn, hs, he, hx):
  match p:
    case Nil{}:
      absurd({Path.parse(Path.render(Nil{})) == Done{Nil{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}, true_ne_false(he))
    case Con{+s, +r}:
      rt2(r, s, hn, hs, he, hx)

def Laws.idempotent(b, p, e):
  rt1(p, Laws.no_dot_segments(b, p, e), Laws.no_unsafe_bytes(b, p, e), Laws.empty_only_last(b, p, e), x_parse(b, p, e))
