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
