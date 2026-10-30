# Proofs about render (laws U5-U7).

import Base
import ../urlpath.bend as Path
import ../src/errors.bend as Error
import ../src/bytes.bend as Byte
import ../src/split.bend as Split
import ../src/decode.bend as Decode
import ../src/dots.bend as Dots
import ../src/check.bend as Check
import ../src/render.bend as Render
import ../src/props.bend as Prop
import ./logic.bend as Logic
import ./split.bend as SplitProof
import ./bytes.bend as ByteFacts
import ./decode.bend as DecodeProof
import ./parse.bend as ParseProof


# Appending after an encoded byte is the same as encoding in front of the append
law ae_at:
  for k: Bool
  for +c: U32
  for e: List<&2, U32>
  for rest: List<&2, U32>
  {List.append(&2, U32, Render.enc_byte.if(k, c, e), rest) == Render.enc_byte.if(k, c, List.append(&2, U32, e, rest)) : List<&2, U32>}

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
  {List.append(&2, U32, Render.enc_byte(c, e), rest) == Render.enc_byte(c, List.append(&2, U32, e, rest)) : List<&2, U32>}

def ae(c, e, rest):
  ae_at(Byte.is_pchar(c), c, e, rest)

# The canonical check passes straight over one encoded byte
law cb_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Byte.is_pchar(c) : Bool}
  {Prop.canonical.go(Render.enc_byte.if(k, c, r), 0n) == Prop.canonical.go(r, 0n) : Bool}

def cb_at(k, c, r, ek):
  match k:
    case True{}:
      %ek : {Prop.canonical.plain(_, U32.is_eq(c, 47), U32.is_eq(c, 37), Prop.canonical.go(r, Prop.canonical.next(_, U32.is_eq(c, 37)))) == Prop.canonical.go(r, 0n) : Bool}
      {==}
    case False{}:
      ux = Equal.sym(Bool, Byte.is_upper_hex(Byte.hex_digit(Byte.hi_nibble(c))), True{}, ByteFacts.hd_upper(Byte.hi_nibble(c)))
      uy = Equal.sym(Bool, Byte.is_upper_hex(Byte.hex_digit(Byte.lo_nibble(c))), True{}, ByteFacts.hd_upper(Byte.lo_nibble(c)))
      %ux : {Bool.and(_, Bool.and(Byte.is_upper_hex(Byte.hex_digit(Byte.lo_nibble(c))), Prop.canonical.go(r, 0n))) == Prop.canonical.go(r, 0n) : Bool}
      %uy : {Bool.and(_, Prop.canonical.go(r, 0n)) == Prop.canonical.go(r, 0n) : Bool}
      {==}

law cb:
  for +c: U32
  for +r: List<&2, U32>
  {Prop.canonical.go(Render.enc_byte(c, r), 0n) == Prop.canonical.go(r, 0n) : Bool}

def cb(c, r):
  cb_at(Byte.is_pchar(c), c, r, {==})

# ... and over a whole encoded segment
law ce:
  for s: List<&2, U32>
  for +rest: List<&2, U32>
  {Prop.canonical.go(List.append(&2, U32, Render.enc_seg(s), rest), 0n) == Prop.canonical.go(rest, 0n) : Bool}

def ce(s, rest):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      a = Equal.sym(List<&2, U32>, List.append(&2, U32, Render.enc_byte(c, Render.enc_seg(t)), rest), Render.enc_byte(c, List.append(&2, U32, Render.enc_seg(t), rest)), ae(c, Render.enc_seg(t), rest))
      %a : {Prop.canonical.go(_, 0n) == Prop.canonical.go(rest, 0n) : Bool}
      Equal.trans(Bool, Prop.canonical.go(Render.enc_byte(c, List.append(&2, U32, Render.enc_seg(t), rest)), 0n),
        Prop.canonical.go(List.append(&2, U32, Render.enc_seg(t), rest), 0n), Prop.canonical.go(rest, 0n),
        cb(c, List.append(&2, U32, Render.enc_seg(t), rest)), ce(t, rest))

# The joined encoded segments are canonical (r first, so it can shrink)
law cj:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  {Prop.canonical.go(Split.join(Con{Render.enc_seg(s), Render.enc_segs(r)}), 0n) == True{} : Bool}

def cj(r, s):
  match r:
    case Nil{}:
      a = Logic.app_nil(Render.enc_seg(s))
      %a : {Prop.canonical.go(_, 0n) == True{} : Bool}
      ce(s, Nil{})
    case Con{+r1, +rr}:
      +j = {Con{47, Split.join(Con{Render.enc_seg(r1), Render.enc_segs(rr)})} : List<&2, U32>}
      a = Equal.sym(Bool, Prop.canonical.go(List.append(&2, U32, Render.enc_seg(s), j), 0n), Prop.canonical.go(j, 0n), ce(s, j))
      %a : {_ == True{} : Bool}
      cj(rr, r1)

# An encoded byte never starts with "/"
law fb_at:
  for k: Bool
  for +c: U32
  for r: List<&2, U32>
  for ek: {k == Byte.is_pchar(c) : Bool}
  {Prop.starts_with_double_slash.two(47, Render.enc_byte.if(k, c, r)) == False{} : Bool}

def fb_at(k, c, r, ek):
  match k:
    case True{}:
      ByteFacts.pns(c, Equal.sym(Bool, True{}, Byte.is_pchar(c), ek))
    case False{}:
      {==}

law fb:
  for +c: U32
  for r: List<&2, U32>
  {Prop.starts_with_double_slash.two(47, Render.enc_byte(c, r)) == False{} : Bool}

def fb(c, r):
  fb_at(Byte.is_pchar(c), c, r, {==})

law no_double_slash:
  for p: List<&2, List<&2, U32>>
  for h: {Prop.empty_only_last(p) == True{} : Bool}
  {Prop.starts_with_double_slash(Render.render(p)) == False{} : Bool}

def no_double_slash(p, h):
  match p:
    case Nil{}:
      Logic.absurd({Prop.starts_with_double_slash(Render.render(Nil{})) == False{} : Bool}, Logic.true_ne_false(h))
    case Con{s, r}:
      match s:
        case Nil{}:
          match r:
            case Nil{}:
              {==}
            case Con{r1, rr}:
              Logic.absurd({Prop.starts_with_double_slash(Render.render(Con{Nil{}, Con{r1, rr}})) == False{} : Bool}, Logic.true_ne_false(h))
        case Con{+c, +t}:
          match r:
            case Nil{}:
              fb(c, Render.enc_seg(t))
            case Con{+r1, +rr}:
              +j = {Con{47, Split.join(Con{Render.enc_seg(r1), Render.enc_segs(rr)})} : List<&2, U32>}
              a = Equal.sym(List<&2, U32>, List.append(&2, U32, Render.enc_byte(c, Render.enc_seg(t)), j), Render.enc_byte(c, List.append(&2, U32, Render.enc_seg(t), j)), ae(c, Render.enc_seg(t), j))
              %a : {Prop.starts_with_double_slash.two(47, _) == False{} : Bool}
              fb(c, List.append(&2, U32, Render.enc_seg(t), j))

# A segment that isn't "." or ".." passes the encoded-dot check
law nd_ok:
  for +s: List<&2, U32>
  for +raw: List<&2, U32>
  for hn: {Bool.not(Dots.is_dot_seg(s)) == True{} : Bool}
  {Bool.not(Bool.and(Dots.is_dot_seg(s), Byte.has_byte(raw, 37))) == True{} : Bool}

def nd_ok(s, raw, hn):
  e = Equal.sym(Bool, Dots.is_dot_seg(s), False{}, Logic.not_true(Dots.is_dot_seg(s), hn))
  %e : {Bool.not(Bool.and(_, Byte.has_byte(raw, 37))) == True{} : Bool}
  {==}

# Checking an encoded accepted segment gives the segment back
law cs:
  for +s: List<&2, U32>
  for +l: Bool
  for hs1: {Check.safe_seg(s) == True{} : Bool}
  for hn1: {Bool.not(Dots.is_dot_seg(s)) == True{} : Bool}
  for +hx1: {ParseProof.xseg(s) == True{} : Bool}
  for hp: {Check.seg_ok.place(s, l) == True{} : Bool}
  {Check.check_seg(Render.enc_seg(s), l) == Done{s} : Result<&2, &2, Error.PathError, List<&2, U32>>}

def cs(s, l, hs1, hn1, hx1, hp):
  de = Equal.sym(Result<&2, &2, Error.PathError, List<&2, U32>>, Decode.decode.go(Render.enc_seg(s), Decode.Plain{}), Done{s},
    DecodeProof.dec_enc(s, Logic.and_left(Byte.all_bytes(s), Bool.not(Check.dot_semi(s)), hx1)))
  %de : {Check.check_seg.d(_, Render.enc_seg(s), l) == Done{s} : Result<&2, &2, Error.PathError, List<&2, U32>>}
  so = Logic.and_intro(Check.seg_ok.shape(Render.enc_seg(s), s), Check.seg_ok.place(s, l),
    Logic.and_intro(Check.safe_seg(s), Check.seg_ok.dots(Render.enc_seg(s), s), hs1,
      Logic.and_intro(Bool.not(Bool.and(Dots.is_dot_seg(s), Byte.has_byte(Render.enc_seg(s), 37))), Bool.not(Check.dot_semi(s)),
        nd_ok(s, Render.enc_seg(s), hn1),
        Logic.and_right(Byte.all_bytes(s), Bool.not(Check.dot_semi(s)), hx1))),
    hp)
  e = Equal.sym(Bool, Check.seg_ok(Render.enc_seg(s), s, l), True{}, so)
  %e : {Check.check_decoded.if(_, Render.enc_seg(s), s) == Done{s} : Result<&2, &2, Error.PathError, List<&2, U32>>}
  {==}

# Checking all the encoded segments gives them back (r first, so it can shrink)
law ca3:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hn: {Prop.no_dot_segs(Con{s, r}) == True{} : Bool}
  for +hs: {Prop.all_safe(Con{s, r}) == True{} : Bool}
  for +hx: {ParseProof.xall(Con{s, r}) == True{} : Bool}
  for +ho: {Prop.only_last_empty(Con{s, r}) == True{} : Bool}
  {Check.check_all(Render.enc_segs(Con{s, r})) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

def ca3(r, s, hn, hs, hx, ho):
  match r:
    case Nil{}:
      c = Equal.sym(Result<&2, &2, Error.PathError, List<&2, U32>>, Check.check_seg(Render.enc_seg(s), True{}), Done{s},
        cs(s, True{}, Logic.and_left(Check.safe_seg(s), True{}, hs), Logic.and_left(Bool.not(Dots.is_dot_seg(s)), True{}, hn),
          Logic.and_left(ParseProof.xseg(s), True{}, hx), {==}))
      %c : {Check.check_all.cons(_, Done{Nil{}}) == Done{[s]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
      {==}
    case Con{+r1, +rr}:
      c = Equal.sym(Result<&2, &2, Error.PathError, List<&2, U32>>, Check.check_seg(Render.enc_seg(s), False{}), Done{s},
        cs(s, False{},
          Logic.and_left(Check.safe_seg(s), Prop.all_safe(Con{r1, rr}), hs),
          Logic.and_left(Bool.not(Dots.is_dot_seg(s)), Prop.no_dot_segs(Con{r1, rr}), hn),
          Logic.and_left(ParseProof.xseg(s), ParseProof.xall(Con{r1, rr}), hx),
          Logic.and_left(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(Con{r1, rr}), ho)))
      ih = Equal.sym(Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>, Check.check_all(Render.enc_segs(Con{r1, rr})), Done{Con{r1, rr}},
        ca3(rr, r1,
          Logic.and_right(Bool.not(Dots.is_dot_seg(s)), Prop.no_dot_segs(Con{r1, rr}), hn),
          Logic.and_right(Check.safe_seg(s), Prop.all_safe(Con{r1, rr}), hs),
          Logic.and_right(ParseProof.xseg(s), ParseProof.xall(Con{r1, rr}), hx),
          Logic.and_right(Bool.not(List.is_empty(&2, U32, s)), Prop.only_last_empty(Con{r1, rr}), ho)))
      %c : {Check.check_all.cons(_, Check.check_all(Render.enc_segs(Con{r1, rr}))) == Done{Con{s, Con{r1, rr}}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
      %ih : {Check.check_all.cons(Done{s}, _) == Done{Con{s, Con{r1, rr}}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
      {==}

# An encoded byte adds no "/"
law heb_at:
  for k: Bool
  for +c: U32
  for +e: List<&2, U32>
  for ek: {k == Byte.is_pchar(c) : Bool}
  {Byte.has_byte(Render.enc_byte.if(k, c, e), 47) == Byte.has_byte(e, 47) : Bool}

def heb_at(k, c, e, ek):
  match k:
    case True{}:
      n = Equal.sym(Bool, U32.is_eq(c, 47), False{}, ByteFacts.pns(c, Equal.sym(Bool, True{}, Byte.is_pchar(c), ek)))
      %n : {Bool.or(_, Byte.has_byte(e, 47)) == Byte.has_byte(e, 47) : Bool}
      {==}
    case False{}:
      +x = Byte.hex_digit(Byte.hi_nibble(c))
      +y = Byte.hex_digit(Byte.lo_nibble(c))
      nx = Equal.sym(Bool, U32.is_eq(x, 47), False{}, Logic.not_true(U32.is_eq(x, 47), ByteFacts.hd_not_slash(Byte.hi_nibble(c))))
      ny = Equal.sym(Bool, U32.is_eq(y, 47), False{}, Logic.not_true(U32.is_eq(y, 47), ByteFacts.hd_not_slash(Byte.lo_nibble(c))))
      %nx : {Bool.or(_, Bool.or(U32.is_eq(y, 47), Byte.has_byte(e, 47))) == Byte.has_byte(e, 47) : Bool}
      %ny : {Bool.or(_, Byte.has_byte(e, 47)) == Byte.has_byte(e, 47) : Bool}
      {==}

# An encoded segment has no "/"
law enc_no_slash:
  for s: List<&2, U32>
  {Byte.has_byte(Render.enc_seg(s), 47) == False{} : Bool}

def enc_no_slash(s):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(Bool, Byte.has_byte(Render.enc_byte(c, Render.enc_seg(t)), 47), Byte.has_byte(Render.enc_seg(t), 47), False{},
        heb_at(Byte.is_pchar(c), c, Render.enc_seg(t), {==}), enc_no_slash(t))

# Splitting the joined encoded segments gives them back
law sje:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  {Split.split(Split.join(Con{Render.enc_seg(s), Render.enc_segs(r)})) == Con{Render.enc_seg(s), Render.enc_segs(r)} : List<&2, List<&2, U32>>}

def sje(r, s):
  match r:
    case Nil{}:
      SplitProof.sj0(Render.enc_seg(s), enc_no_slash(s))
    case Con{+r1, +rr}:
      +j = {Split.join(Con{Render.enc_seg(r1), Render.enc_segs(rr)}) : List<&2, U32>}
      Equal.trans(List<&2, List<&2, U32>>,
        Split.split(List.append(&2, U32, Render.enc_seg(s), Con{47, j})),
        Con{Render.enc_seg(s), Split.split(j)},
        Con{Render.enc_seg(s), Con{Render.enc_seg(r1), Render.enc_segs(rr)}},
        SplitProof.sj1(Render.enc_seg(s), j, enc_no_slash(s)),
        Equal.cong(List<&2, List<&2, U32>>, List<&2, List<&2, U32>>, x => Con{Render.enc_seg(s), x},
          Split.split(j), Con{Render.enc_seg(r1), Render.enc_segs(rr)}, sje(rr, r1)))

# The encoded bytes are all bytes
law abb_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Byte.is_pchar(c) : Bool}
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Byte.all_bytes(Render.enc_byte.if(k, c, r)) == Byte.all_bytes(r) : Bool}

def abb_at(k, c, r, ek, hc):
  match k:
    case True{}:
      e = Equal.sym(Bool, U32.is_le(c, 255), True{}, hc)
      %e : {Bool.and(_, Byte.all_bytes(r)) == Byte.all_bytes(r) : Bool}
      {==}
    case False{}:
      +x = Byte.hex_digit(Byte.hi_nibble(c))
      +y = Byte.hex_digit(Byte.lo_nibble(c))
      bx = Equal.sym(Bool, U32.is_le(x, 255), True{}, ByteFacts.hd_byte(Byte.hi_nibble(c)))
      by = Equal.sym(Bool, U32.is_le(y, 255), True{}, ByteFacts.hd_byte(Byte.lo_nibble(c)))
      %bx : {Bool.and(_, Bool.and(U32.is_le(y, 255), Byte.all_bytes(r))) == Byte.all_bytes(r) : Bool}
      %by : {Bool.and(_, Byte.all_bytes(r)) == Byte.all_bytes(r) : Bool}
      {==}

law abe:
  for s: List<&2, U32>
  for +rest: List<&2, U32>
  for +hs: {Byte.all_bytes(s) == True{} : Bool}
  {Byte.all_bytes(List.append(&2, U32, Render.enc_seg(s), rest)) == Byte.all_bytes(rest) : Bool}

def abe(s, rest, hs):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      a = Equal.sym(List<&2, U32>, List.append(&2, U32, Render.enc_byte(c, Render.enc_seg(t)), rest), Render.enc_byte(c, List.append(&2, U32, Render.enc_seg(t), rest)), ae(c, Render.enc_seg(t), rest))
      %a : {Byte.all_bytes(_) == Byte.all_bytes(rest) : Bool}
      Equal.trans(Bool, Byte.all_bytes(Render.enc_byte(c, List.append(&2, U32, Render.enc_seg(t), rest))),
        Byte.all_bytes(List.append(&2, U32, Render.enc_seg(t), rest)), Byte.all_bytes(rest),
        abb_at(Byte.is_pchar(c), c, List.append(&2, U32, Render.enc_seg(t), rest), {==}, Logic.and_left(U32.is_le(c, 255), Byte.all_bytes(t), hs)),
        abe(t, rest, Logic.and_right(U32.is_le(c, 255), Byte.all_bytes(t), hs)))

law abj:
  for r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hx: {ParseProof.xall(Con{s, r}) == True{} : Bool}
  {Byte.all_bytes(Split.join(Con{Render.enc_seg(s), Render.enc_segs(r)})) == True{} : Bool}

def abj(r, s, hx):
  match r:
    case Nil{}:
      a = Logic.app_nil(Render.enc_seg(s))
      %a : {Byte.all_bytes(_) == True{} : Bool}
      abe(s, Nil{}, Logic.and_left(Byte.all_bytes(s), Bool.not(Check.dot_semi(s)), Logic.and_left(ParseProof.xseg(s), True{}, hx)))
    case Con{+r1, +rr}:
      hs = Logic.and_left(Byte.all_bytes(s), Bool.not(Check.dot_semi(s)), Logic.and_left(ParseProof.xseg(s), ParseProof.xall(Con{r1, rr}), hx))
      +j = {Con{47, Split.join(Con{Render.enc_seg(r1), Render.enc_segs(rr)})} : List<&2, U32>}
      a = Equal.sym(Bool, Byte.all_bytes(List.append(&2, U32, Render.enc_seg(s), j)), Byte.all_bytes(j), abe(s, j, hs))
      %a : {_ == True{} : Bool}
      abj(rr, r1, Logic.and_right(ParseProof.xseg(s), ParseProof.xall(Con{r1, rr}), hx))

# Dot removal leaves an accepted path alone
law rdp_at:
  for k: Dots.SegKind
  for +s: List<&2, U32>
  for +r: List<&2, List<&2, U32>>
  for ek: {k == Dots.seg_kind(s) : Dots.SegKind}
  for hk: {Bool.not(Dots.is_dot_seg(s)) == True{} : Bool}
  for ih: {Dots.rd(r) == Dots.DotState{0n, r} : Dots.DotState}
  {Dots.rd.step(k, s, List.is_empty(&2, List<&2, U32>, r), Dots.rd(r)) == Dots.DotState{0n, Con{s, r}} : Dots.DotState}

def rdp_at(k, s, r, ek, hk, ih):
  match k:
    case Dots.Other{}:
      match r:
        case Nil{}:
          {==}
        case Con{+r1, +rr}:
          e = Equal.sym(Dots.DotState, Dots.rd(Con{r1, rr}), Dots.DotState{0n, Con{r1, rr}}, ih)
          %e : {Dots.rd.step(Dots.Other{}, s, False{}, _) == Dots.DotState{0n, Con{s, Con{r1, rr}}} : Dots.DotState}
          {==}
    case Dots.Dot{}:
      c = Equal.cong(Dots.SegKind, Bool, x => Bool.not(Bool.not(Dots.is_other(x))), Dots.Dot{}, Dots.seg_kind(s), ek)
      Logic.absurd({Dots.rd.step(Dots.Dot{}, s, List.is_empty(&2, List<&2, U32>, r), Dots.rd(r)) == Dots.DotState{0n, Con{s, r}} : Dots.DotState},
        Logic.true_ne_false(Equal.trans(Bool, False{}, Bool.not(Bool.not(Dots.is_other(Dots.seg_kind(s)))), True{}, c, hk)))
    case Dots.DotDot{}:
      c = Equal.cong(Dots.SegKind, Bool, x => Bool.not(Bool.not(Dots.is_other(x))), Dots.DotDot{}, Dots.seg_kind(s), ek)
      Logic.absurd({Dots.rd.step(Dots.DotDot{}, s, List.is_empty(&2, List<&2, U32>, r), Dots.rd(r)) == Dots.DotState{0n, Con{s, r}} : Dots.DotState},
        Logic.true_ne_false(Equal.trans(Bool, False{}, Bool.not(Bool.not(Dots.is_other(Dots.seg_kind(s)))), True{}, c, hk)))

law rdp:
  for +p: List<&2, List<&2, U32>>
  for +hn: {Prop.no_dot_segs(p) == True{} : Bool}
  {Dots.rd(p) == Dots.DotState{0n, p} : Dots.DotState}

def rdp(p, hn):
  match p:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      rdp_at(Dots.seg_kind(s), s, r, {==},
        Logic.and_left(Bool.not(Dots.is_dot_seg(s)), Prop.no_dot_segs(r), hn),
        rdp(r, Logic.and_right(Bool.not(Dots.is_dot_seg(s)), Prop.no_dot_segs(r), hn)))

# The round trip, for any segments with the facts parse guarantees
law rt2:
  for +r: List<&2, List<&2, U32>>
  for +s: List<&2, U32>
  for +hn: {Prop.no_dot_segs(Con{s, r}) == True{} : Bool}
  for +hs: {Prop.all_safe(Con{s, r}) == True{} : Bool}
  for +he: {Prop.empty_only_last(Con{s, r}) == True{} : Bool}
  for +hx: {ParseProof.xall(Con{s, r}) == True{} : Bool}
  {Path.parse(Render.render(Con{s, r})) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

def rt2(r, s, hn, hs, he, hx):
  +j = {Split.join(Con{Render.enc_seg(s), Render.enc_segs(r)}) : List<&2, U32>}
  e1 = Equal.sym(Bool, Byte.all_bytes(j), True{}, abj(r, s, hx))
  e2 = Equal.sym(List<&2, List<&2, U32>>, Split.split(j), Con{Render.enc_seg(s), Render.enc_segs(r)}, sje(r, s))
  e3 = Equal.sym(Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>, Check.check_all(Render.enc_segs(Con{s, r})), Done{Con{s, r}}, ca3(r, s, hn, hs, hx, he))
  e4 = Equal.sym(Dots.DotState, Dots.rd(Con{s, r}), Dots.DotState{0n, Con{s, r}}, rdp(Con{s, r}, hn))
  %e1 : {Path.parse.bytes(_, Con{47, j}) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
  %e2 : {Path.parse.dots(Check.check_all(_)) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
  %e3 : {Path.parse.dots(_) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
  %e4 : {Dots.rd.end(_) == Done{Con{s, r}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
  {==}

law rt1:
  for p: List<&2, List<&2, U32>>
  for +hn: {Prop.no_dot_segs(p) == True{} : Bool}
  for +hs: {Prop.all_safe(p) == True{} : Bool}
  for +he: {Prop.empty_only_last(p) == True{} : Bool}
  for +hx: {ParseProof.xall(p) == True{} : Bool}
  {Path.parse(Render.render(p)) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

def rt1(p, hn, hs, he, hx):
  match p:
    case Nil{}:
      Logic.absurd({Path.parse(Render.render(Nil{})) == Done{Nil{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}, Logic.true_ne_false(he))
    case Con{+s, +r}:
      rt2(r, s, hn, hs, he, hx)
