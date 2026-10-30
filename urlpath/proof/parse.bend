# What every accepted path satisfies (laws U1-U4, plus facts U5 needs).

import Base
import ../urlpath.bend as Path
import ../src/errors.bend as Error
import ../src/bytes.bend as Byte
import ../src/split.bend as Split
import ../src/decode.bend as Decode
import ../src/dots.bend as Dots
import ../src/check.bend as Check
import ../src/props.bend as Prop
import ./logic.bend as Logic
import ./split.bend as SplitProof
import ./decode.bend as DecodeProof


# The segments kept by dot removal
def kept_of(d: Dots.DotState) -> List<&2, List<&2, U32>>:
  match d:
    case Dots.DotState{up, kept}:
      kept

# What U1 promises about one parse result
def U1ok(b: List<&2, U32>, r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Prop.starts_with_slash(b) == True{} : Bool}

law u1_any:
  for b: List<&2, U32>
  for r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for h: {Prop.starts_with_slash(b) == True{} : Bool}
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
      u1_any(Con{c, t}, Path.parse.dots(Check.check_all(Split.split(t))), Equal.sym(Bool, True{}, U32.is_eq(c, 47), ek))
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

def U2ok(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Prop.no_dot_segs(p) == True{} : Bool}

# One step of dot removal keeps the invariant
law u2_step:
  for k: Dots.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Dots.DotState
  for ek: {k == Dots.seg_kind(s) : Dots.SegKind}
  for ih: {Prop.no_dot_segs(kept_of(d)) == True{} : Bool}
  {Prop.no_dot_segs(kept_of(Dots.rd.step(k, s, l, d))) == True{} : Bool}

def u2_step(k, s, l, d, ek, ih):
  match k:
    case Dots.Other{}:
      match l:
        case True{}:
          %ek : {Bool.and(Bool.not(Bool.not(Dots.is_other(_))), True{}) == True{} : Bool}
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              match up:
                case 0n:
                  %ek : {Bool.and(Bool.not(Bool.not(Dots.is_other(_))), Prop.no_dot_segs(kept)) == True{} : Bool}
                  ih
                case 1n+n:
                  ih
    case Dots.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Dots.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              ih

law u2_kept:
  for segs: List<&2, List<&2, U32>>
  {Prop.no_dot_segs(kept_of(Dots.rd(segs))) == True{} : Bool}

def u2_kept(segs):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u2_step(Dots.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Dots.rd(rest), {==}, u2_kept(rest))

law u2_end:
  for d: Dots.DotState
  for h: {Prop.no_dot_segs(kept_of(d)) == True{} : Bool}
  U2ok(Dots.rd.end(d))

def u2_end(d, h):
  match d:
    case Dots.DotState{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law u2_dots:
  for r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  U2ok(Path.parse.dots(r))

def u2_dots(r):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u2_end(Dots.rd(ds), u2_kept(ds))

law u2_slash:
  for k: Bool
  for +t: List<&2, U32>
  U2ok(Path.parse.slash(k, t))

def u2_slash(k, t):
  match k:
    case True{}:
      u2_dots(Check.check_all(Split.split(t)))
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

def U3ok(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Prop.all_safe(p) == True{} : Bool}

# What U3 needs from one checked segment
def SegOk3(r: Result<&2, &2, Error.PathError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      {Check.safe_seg(s) == True{} : Bool}

law u3_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for l: Bool
  for ek: {k == Check.seg_ok(raw, d, l) : Bool}
  SegOk3(Check.check_decoded.if(k, raw, d))

def u3_seg_if(k, raw, d, l, ek):
  match k:
    case True{}:
      Logic.and_left(Check.safe_seg(d), Check.seg_ok.dots(raw, d),
        Logic.and_left(Check.seg_ok.shape(raw, d), Check.seg_ok.place(d, l),
          Equal.sym(Bool, True{}, Check.seg_ok(raw, d, l), ek)))
    case False{}:
      Unit{}

law u3_seg_d:
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  SegOk3(Check.check_seg.d(r, raw, l))

def u3_seg_d(r, raw, l):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      u3_seg_if(Check.seg_ok(raw, d, l), raw, d, l, {==})

law u3_cons:
  for a: Result<&2, &2, Error.PathError, List<&2, U32>>
  for b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for ha: SegOk3(a)
  for hb: U3ok(b)
  U3ok(Check.check_all.cons(a, b))

def u3_cons(a, b, ha, hb):
  match a:
    case Fail{e}:
      Unit{}
    case Done{+s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{+ss}:
          Logic.and_intro(Check.safe_seg(s), Prop.all_safe(ss), ha, hb)

law u3_check_all:
  for raws: List<&2, List<&2, U32>>
  U3ok(Check.check_all(raws))

def u3_check_all(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u3_cons(Check.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Check.check_all(rest),
        u3_seg_d(Decode.decode(r), r, List.is_empty(&2, List<&2, U32>, rest)), u3_check_all(rest))

# One step of dot removal keeps every segment safe
law u3_step:
  for k: Dots.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Dots.DotState
  for hs: {Check.safe_seg(s) == True{} : Bool}
  for ih: {Prop.all_safe(kept_of(d)) == True{} : Bool}
  {Prop.all_safe(kept_of(Dots.rd.step(k, s, l, d))) == True{} : Bool}

def u3_step(k, s, l, d, hs, ih):
  match k:
    case Dots.Other{}:
      match l:
        case True{}:
          Logic.and_intro(Check.safe_seg(s), True{}, hs, {==})
        case False{}:
          match d:
            case Dots.DotState{up, +kept}:
              match up:
                case 0n:
                  Logic.and_intro(Check.safe_seg(s), Prop.all_safe(kept), hs, ih)
                case 1n+n:
                  ih
    case Dots.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Dots.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              ih

law u3_kept:
  for segs: List<&2, List<&2, U32>>
  for +h: {Prop.all_safe(segs) == True{} : Bool}
  {Prop.all_safe(kept_of(Dots.rd(segs))) == True{} : Bool}

def u3_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u3_step(Dots.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Dots.rd(rest),
        Logic.and_left(Check.safe_seg(s), Prop.all_safe(rest), h),
        u3_kept(rest, Logic.and_right(Check.safe_seg(s), Prop.all_safe(rest), h)))

law u3_end:
  for d: Dots.DotState
  for h: {Prop.all_safe(kept_of(d)) == True{} : Bool}
  U3ok(Dots.rd.end(d))

def u3_end(d, h):
  match d:
    case Dots.DotState{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law u3_dots:
  for r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for h: U3ok(r)
  U3ok(Path.parse.dots(r))

def u3_dots(r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u3_end(Dots.rd(ds), u3_kept(ds, h))

law u3_slash:
  for k: Bool
  for +t: List<&2, U32>
  U3ok(Path.parse.slash(k, t))

def u3_slash(k, t):
  match k:
    case True{}:
      u3_dots(Check.check_all(Split.split(t)), u3_check_all(Split.split(t)))
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

def U4ok(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {Prop.empty_only_last(p) == True{} : Bool}

# Facts about check_all's result: only the last segment is empty,
# it's non-empty, and it's empty exactly when the input was (l)
def OLEok(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      {Prop.only_last_empty(ss) == True{} : Bool}

def NEok(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      Logic.NonEmpty(ss)

def LenOk(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>, l: Bool) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{ss}:
      {List.is_empty(&2, List<&2, U32>, ss) == l : Bool}

# What U4 needs from one checked segment: it's non-empty unless last
def SegOk4(r: Result<&2, &2, Error.PathError, List<&2, U32>>, l: Bool) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      {Check.seg_ok.place(s, l) == True{} : Bool}

law u4_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for +l: Bool
  for ek: {k == Check.seg_ok(raw, d, l) : Bool}
  SegOk4(Check.check_decoded.if(k, raw, d), l)

def u4_seg_if(k, raw, d, l, ek):
  match k:
    case True{}:
      Logic.and_right(Check.seg_ok.shape(raw, d), Check.seg_ok.place(d, l),
        Equal.sym(Bool, True{}, Check.seg_ok(raw, d, l), ek))
    case False{}:
      Unit{}

law u4_seg_d:
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  SegOk4(Check.check_seg.d(r, raw, l), l)

def u4_seg_d(r, raw, l):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      u4_seg_if(Check.seg_ok(raw, d, l), raw, d, l, {==})

law u4_cons:
  for l: Bool
  for a: Result<&2, &2, Error.PathError, List<&2, U32>>
  for b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for ha: SegOk4(a, l)
  for hb: OLEok(b)
  for hlen: LenOk(b, l)
  OLEok(Check.check_all.cons(a, b))

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
              %eh : {Prop.eol.step(_, s, Prop.only_last_empty(ss)) == True{} : Bool}
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
              %eh : {Prop.eol.step(_, s, Prop.only_last_empty(ss)) == True{} : Bool}
              Logic.and_intro(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(ss), ha, hb)

law u4_len_cons:
  for a: Result<&2, &2, Error.PathError, List<&2, U32>>
  for b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  LenOk(Check.check_all.cons(a, b), False{})

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
  LenOk(Check.check_all(raws), List.is_empty(&2, List<&2, U32>, raws))

def u4_len(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u4_len_cons(Check.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Check.check_all(rest))

law u4_ole_ca:
  for raws: List<&2, List<&2, U32>>
  OLEok(Check.check_all(raws))

def u4_ole_ca(raws):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      u4_cons(List.is_empty(&2, List<&2, U32>, rest),
        Check.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Check.check_all(rest),
        u4_seg_d(Decode.decode(r), r, List.is_empty(&2, List<&2, U32>, rest)),
        u4_ole_ca(rest), u4_len(rest))

law u4_ne_cons:
  for a: Result<&2, &2, Error.PathError, List<&2, U32>>
  for b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  NEok(Check.check_all.cons(a, b))

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
  for ne: Logic.NonEmpty(raws)
  NEok(Check.check_all(raws))

def u4_ne_ca(raws, ne):
  match raws:
    case Nil{}:
      ne
    case Con{+r, +rest}:
      u4_ne_cons(Check.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Check.check_all(rest))

# Putting a non-empty segment in front keeps "only the last is empty"
law u4_ole_cons:
  for +s: List<&2, U32>
  for kept: List<&2, List<&2, U32>>
  for hs: {Bool.not(List.is_empty(&2, U32, s)) == True{} : Bool}
  for hk: {Prop.only_last_empty(kept) == True{} : Bool}
  {Prop.only_last_empty(Con{s, kept}) == True{} : Bool}

def u4_ole_cons(s, kept, hs, hk):
  match kept:
    case Nil{}:
      {==}
    case Con{+k1, +kr}:
      Logic.and_intro(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(Con{k1, kr}), hs, hk)

# One step of dot removal keeps "only the last is empty"
law u4_step:
  for k: Dots.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for +rest: List<&2, List<&2, U32>>
  for d: Dots.DotState
  for +h: {Prop.eol.step(l, s, Prop.only_last_empty(rest)) == True{} : Bool}
  for ih: {Prop.only_last_empty(rest) == True{} : Bool} -> {Prop.only_last_empty(kept_of(d)) == True{} : Bool}
  {Prop.only_last_empty(kept_of(Dots.rd.step(k, s, l, d))) == True{} : Bool}

def u4_step(k, s, l, rest, d, h, ih):
  match k:
    case Dots.Other{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, +kept}:
              match up:
                case 0n:
                  u4_ole_cons(s, kept,
                    Logic.and_left(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(rest), h),
                    ih(Logic.and_right(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(rest), h)))
                case 1n+n:
                  ih(Logic.and_right(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(rest), h))
    case Dots.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih(Logic.and_right(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(rest), h))
    case Dots.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              ih(Logic.and_right(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(rest), h))

law u4_kept:
  for segs: List<&2, List<&2, U32>>
  for h: {Prop.only_last_empty(segs) == True{} : Bool}
  {Prop.only_last_empty(kept_of(Dots.rd(segs))) == True{} : Bool}

def u4_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      u4_step(Dots.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rest, Dots.rd(rest), h,
        e2 => u4_kept(rest, e2))

# A list that isn't empty is NonEmpty
law u4_ne_of:
  for rest: List<&2, List<&2, U32>>
  for e: {False{} == List.is_empty(&2, List<&2, U32>, rest) : Bool}
  Logic.NonEmpty(rest)

def u4_ne_of(rest, e):
  match rest:
    case Nil{}:
      Logic.true_ne_false(e)
    case Con{s, r}:
      Unit{}

# Dot removal of a non-empty list keeps at least one segment
law u4_kne_step:
  for k: Dots.SegKind
  for s: List<&2, U32>
  for l: Bool
  for +rest: List<&2, List<&2, U32>>
  for d: Dots.DotState
  for el: {l == List.is_empty(&2, List<&2, U32>, rest) : Bool}
  for ih: Logic.NonEmpty(rest) -> Logic.NonEmpty(kept_of(d))
  Logic.NonEmpty(kept_of(Dots.rd.step(k, s, l, d)))

def u4_kne_step(k, s, l, rest, d, el, ih):
  match k:
    case Dots.Other{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              match up:
                case 0n:
                  Unit{}
                case 1n+n:
                  ih(u4_ne_of(rest, el))
    case Dots.Dot{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          ih(u4_ne_of(rest, el))
    case Dots.DotDot{}:
      match l:
        case True{}:
          Unit{}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              ih(u4_ne_of(rest, el))

law u4_kne:
  for segs: List<&2, List<&2, U32>>
  for ne: Logic.NonEmpty(segs)
  Logic.NonEmpty(kept_of(Dots.rd(segs)))

def u4_kne(segs, ne):
  match segs:
    case Nil{}:
      ne
    case Con{+s, +rest}:
      u4_kne_step(Dots.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), rest, Dots.rd(rest), {==},
        x => u4_kne(rest, x))

law ne_bool:
  for xs: List<&2, List<&2, U32>>
  for ne: Logic.NonEmpty(xs)
  {Bool.not(List.is_empty(&2, List<&2, U32>, xs)) == True{} : Bool}

def ne_bool(xs, ne):
  match xs:
    case Nil{}:
      Logic.absurd({Bool.not(List.is_empty(&2, List<&2, U32>, Nil{})) == True{} : Bool}, ne)
    case Con{s, r}:
      {==}

law u4_end:
  for d: Dots.DotState
  for ho: {Prop.only_last_empty(kept_of(d)) == True{} : Bool}
  for hn: Logic.NonEmpty(kept_of(d))
  U4ok(Dots.rd.end(d))

def u4_end(d, ho, hn):
  match d:
    case Dots.DotState{up, +kept}:
      match up:
        case 0n:
          Logic.and_intro(Bool.not(List.is_empty(&2, List<&2, U32>, kept)), Prop.only_last_empty(kept), ne_bool(kept, hn), ho)
        case 1n+n:
          Unit{}

law u4_dots:
  for r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for h1: OLEok(r)
  for h2: NEok(r)
  U4ok(Path.parse.dots(r))

def u4_dots(r, h1, h2):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      u4_end(Dots.rd(ds), u4_kept(ds, h1), u4_kne(ds, h2))

law u4_slash:
  for k: Bool
  for +t: List<&2, U32>
  U4ok(Path.parse.slash(k, t))

def u4_slash(k, t):
  match k:
    case True{}:
      u4_dots(Check.check_all(Split.split(t)), u4_ole_ca(Split.split(t)), u4_ne_ca(Split.split(t), SplitProof.split_ne(t)))
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

def xseg(+s: List<&2, U32>) -> Bool:
  Bool.and(Byte.all_bytes(s), Bool.not(Check.dot_semi(s)))

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
      Bool.and(Byte.all_bytes(s), allb_segs(t))

def XOk(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{p}:
      {xall(p) == True{} : Bool}

def SegX(r: Result<&2, &2, Error.PathError, List<&2, U32>>) -> Type:
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
  {allb_segs(Split.split.if(h, segs, k)) == True{} : Bool}

def sb_at(k, h, segs, hh, hs):
  match k:
    case True{}:
      hs
    case False{}:
      match segs:
        case Nil{}:
          Logic.and_intro(Byte.all_bytes([h]), True{}, Logic.and_intro(U32.is_le(h, 255), True{}, hh, {==}), {==})
        case Con{+f, +o}:
          Logic.and_intro(Byte.all_bytes(Con{h, f}), allb_segs(o),
            Logic.and_intro(U32.is_le(h, 255), Byte.all_bytes(f), hh, Logic.and_left(Byte.all_bytes(f), allb_segs(o), hs)),
            Logic.and_right(Byte.all_bytes(f), allb_segs(o), hs))

law split_bytes:
  for b: List<&2, U32>
  for +hb: {Byte.all_bytes(b) == True{} : Bool}
  {allb_segs(Split.split(b)) == True{} : Bool}

def split_bytes(b, hb):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      sb_at(U32.is_eq(h, 47), h, Split.split(t),
        Logic.and_left(U32.is_le(h, 255), Byte.all_bytes(t), hb),
        split_bytes(t, Logic.and_right(U32.is_le(h, 255), Byte.all_bytes(t), hb)))

law x_seg_if:
  for k: Bool
  for +raw: List<&2, U32>
  for +d: List<&2, U32>
  for +l: Bool
  for ek: {k == Check.seg_ok(raw, d, l) : Bool}
  for hd: {Byte.all_bytes(d) == True{} : Bool}
  SegX(Check.check_decoded.if(k, raw, d))

def x_seg_if(k, raw, d, l, ek, hd):
  match k:
    case True{}:
      Logic.and_intro(Byte.all_bytes(d), Bool.not(Check.dot_semi(d)), hd,
        Logic.and_right(Bool.not(Bool.and(Dots.is_dot_seg(d), Byte.has_byte(raw, 37))), Bool.not(Check.dot_semi(d)),
          Logic.and_right(Check.safe_seg(d), Check.seg_ok.dots(raw, d),
            Logic.and_left(Check.seg_ok.shape(raw, d), Check.seg_ok.place(d, l),
              Equal.sym(Bool, True{}, Check.seg_ok(raw, d, l), ek)))))
    case False{}:
      Unit{}

law x_seg_d:
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for +raw: List<&2, U32>
  for +l: Bool
  for hd: DecodeProof.DecOk(r)
  SegX(Check.check_seg.d(r, raw, l))

def x_seg_d(r, raw, l, hd):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      x_seg_if(Check.seg_ok(raw, d, l), raw, d, l, {==}, hd)

law x_cons:
  for a: Result<&2, &2, Error.PathError, List<&2, U32>>
  for b: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for ha: SegX(a)
  for hb: XOk(b)
  XOk(Check.check_all.cons(a, b))

def x_cons(a, b, ha, hb):
  match a:
    case Fail{e}:
      Unit{}
    case Done{+s}:
      match b:
        case Fail{e}:
          Unit{}
        case Done{+ss}:
          Logic.and_intro(xseg(s), xall(ss), ha, hb)

law x_ca:
  for raws: List<&2, List<&2, U32>>
  for +h: {allb_segs(raws) == True{} : Bool}
  XOk(Check.check_all(raws))

def x_ca(raws, h):
  match raws:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      x_cons(Check.check_seg(r, List.is_empty(&2, List<&2, U32>, rest)), Check.check_all(rest),
        x_seg_d(Decode.decode(r), r, List.is_empty(&2, List<&2, U32>, rest),
          DecodeProof.dec_go(r, Decode.Plain{}, Logic.and_left(Byte.all_bytes(r), allb_segs(rest), h), Unit{})),
        x_ca(rest, Logic.and_right(Byte.all_bytes(r), allb_segs(rest), h)))

law x_step:
  for k: Dots.SegKind
  for +s: List<&2, U32>
  for l: Bool
  for d: Dots.DotState
  for hs: {xseg(s) == True{} : Bool}
  for ih: {xall(kept_of(d)) == True{} : Bool}
  {xall(kept_of(Dots.rd.step(k, s, l, d))) == True{} : Bool}

def x_step(k, s, l, d, hs, ih):
  match k:
    case Dots.Other{}:
      match l:
        case True{}:
          Logic.and_intro(xseg(s), True{}, hs, {==})
        case False{}:
          match d:
            case Dots.DotState{up, +kept}:
              match up:
                case 0n:
                  Logic.and_intro(xseg(s), xall(kept), hs, ih)
                case 1n+n:
                  ih
    case Dots.Dot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          ih
    case Dots.DotDot{}:
      match l:
        case True{}:
          {==}
        case False{}:
          match d:
            case Dots.DotState{up, kept}:
              ih

law x_kept:
  for segs: List<&2, List<&2, U32>>
  for +h: {xall(segs) == True{} : Bool}
  {xall(kept_of(Dots.rd(segs))) == True{} : Bool}

def x_kept(segs, h):
  match segs:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      x_step(Dots.seg_kind(s), s, List.is_empty(&2, List<&2, U32>, rest), Dots.rd(rest),
        Logic.and_left(xseg(s), xall(rest), h),
        x_kept(rest, Logic.and_right(xseg(s), xall(rest), h)))

law x_end:
  for d: Dots.DotState
  for h: {xall(kept_of(d)) == True{} : Bool}
  XOk(Dots.rd.end(d))

def x_end(d, h):
  match d:
    case Dots.DotState{up, kept}:
      match up:
        case 0n:
          h
        case 1n+n:
          Unit{}

law x_dots:
  for r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>
  for h: XOk(r)
  XOk(Path.parse.dots(r))

def x_dots(r, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+ds}:
      x_end(Dots.rd(ds), x_kept(ds, h))

law x_slash:
  for k: Bool
  for +t: List<&2, U32>
  for ht: {Byte.all_bytes(t) == True{} : Bool}
  XOk(Path.parse.slash(k, t))

def x_slash(k, t, ht):
  match k:
    case True{}:
      x_dots(Check.check_all(Split.split(t)), x_ca(Split.split(t), split_bytes(t, ht)))
    case False{}:
      Unit{}

law x_first:
  for b: List<&2, U32>
  for hb: {Byte.all_bytes(b) == True{} : Bool}
  XOk(Path.parse.first(b))

def x_first(b, hb):
  match b:
    case Nil{}:
      Unit{}
    case Con{+c, +t}:
      x_slash(U32.is_eq(c, 47), t, Logic.and_right(U32.is_le(c, 255), Byte.all_bytes(t), hb))

law x_bytes:
  for k: Bool
  for +b: List<&2, U32>
  for ek: {k == Byte.all_bytes(b) : Bool}
  XOk(Path.parse.bytes(k, b))

def x_bytes(k, b, ek):
  match k:
    case True{}:
      x_first(b, Equal.sym(Bool, True{}, Byte.all_bytes(b), ek))
    case False{}:
      Unit{}

law x_parse:
  for +b: List<&2, U32>
  for p: List<&2, List<&2, U32>>
  for e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
  {xall(p) == True{} : Bool}

def x_parse(b, p, e):
  %e : XOk(_)
  x_bytes(Byte.all_bytes(b), b, {==})
