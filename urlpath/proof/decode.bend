# Proofs about decode: plain text passes through, the output is bytes, and
# decoding an encoded segment gives it back.

import Base
import ../src/errors.bend as Error
import ../src/bytes.bend as Byte
import ../src/decode.bend as Decode
import ../src/render.bend as Render
import bend-mathlib@0.7.4.0/string.bend as MStr
import ./logic.bend as Logic
import ./bytes.bend as ByteFacts


# One step of decode_plain, split on whether the first byte is a pchar
law decode_plain.at:
  for k: Bool
  for +h: U32
  for +t: List<&2, U32>
  for e: {Bool.and(k, Byte.all_pchar(t)) == True{} : Bool}
  for ih: {Byte.all_pchar(t) == True{} : Bool} -> {Decode.decode.go(t, Decode.Plain{}) == Done{t} : Result<&2, &2, Error.PathError, List<&2, U32>>}
  {Decode.decode.step.plain(h, Decode.decode.go(t, Decode.decode.next.plain(k, U32.is_eq(h, 37))), k, U32.is_eq(h, 37)) == Done{Con{h, t}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

def decode_plain.at(k, h, t, e, ih):
  match k:
    case True{}:
      %ih(e) : {Decode.ok_cons(h, Decode.decode.go(t, Decode.Plain{})) == Decode.ok_cons(h, _) : Result<&2, &2, Error.PathError, List<&2, U32>>}
      {==}
    case False{}:
      Logic.absurd({Decode.decode.step.plain(h, Decode.decode.go(t, Decode.decode.next.plain(False{}, U32.is_eq(h, 37))), False{}, U32.is_eq(h, 37)) == Done{Con{h, t}} : Result<&2, &2, Error.PathError, List<&2, U32>>}, Logic.true_ne_false(e))

def DecOk(r: Result<&2, &2, Error.PathError, List<&2, U32>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{d}:
      {Byte.all_bytes(d) == True{} : Bool}

# In the middle of an escape, the first digit's value is at most 15
def StOk(st: Decode.DecState) -> Type:
  match st:
    case Decode.Plain{}:
      Unit
    case Decode.Hex1{}:
      Unit
    case Decode.Hex2{hi}:
      {U32.is_le(hi, 15) == True{} : Bool}

law dec_okcons:
  for +b: U32
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hr: DecOk(r)
  DecOk(Decode.ok_cons(b, r))

def dec_okcons(b, r, hb, hr):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+d}:
      Logic.and_intro(U32.is_le(b, 255), Byte.all_bytes(d), hb, hr)

law dec_plain:
  for p: Bool
  for q: Bool
  for +b: U32
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for ih: StOk(Decode.decode.next.plain(p, q)) -> DecOk(r)
  DecOk(Decode.decode.step.plain(b, r, p, q))

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
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for ek: {k == Byte.is_hex(b) : Bool}
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for ih: StOk(Decode.Hex2{Byte.hex_val(b)}) -> DecOk(r)
  DecOk(Decode.decode.step.hex1(r, k))

def dec_hex1(k, b, r, ek, hb, ih):
  match k:
    case True{}:
      ih(ByteFacts.hex_small(b, hb, Equal.sym(Bool, True{}, Byte.is_hex(b), ek)))
    case False{}:
      Unit{}

law dec_hex2:
  for k: Bool
  for +hi: U32
  for +b: U32
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for ek: {k == Byte.is_hex(b) : Bool}
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hh: {U32.is_le(hi, 15) == True{} : Bool}
  for ih: Unit -> DecOk(r)
  DecOk(Decode.decode.step.hex2(Byte.hex_pair(hi, Byte.hex_val(b)), r, k))

def dec_hex2(k, hi, b, r, ek, hb, hh, ih):
  match k:
    case True{}:
      dec_okcons(Byte.hex_pair(hi, Byte.hex_val(b)), r,
        ByteFacts.pair_byte(hi, Byte.hex_val(b), hh, ByteFacts.hex_small(b, hb, Equal.sym(Bool, True{}, Byte.is_hex(b), ek))),
        ih(Unit{}))
    case False{}:
      Unit{}

law dec_step:
  for +b: U32
  for st: Decode.DecState
  for r: Result<&2, &2, Error.PathError, List<&2, U32>>
  for hb: {U32.is_le(b, 255) == True{} : Bool}
  for hst: StOk(st)
  for ih: StOk(Decode.decode.next(b, st)) -> DecOk(r)
  DecOk(Decode.decode.step(b, st, r))

def dec_step(b, st, r, hb, hst, ih):
  match st:
    case Decode.Plain{}:
      dec_plain(Byte.is_pchar(b), U32.is_eq(b, 37), b, r, hb, ih)
    case Decode.Hex1{}:
      dec_hex1(Byte.is_hex(b), b, r, {==}, hb, ih)
    case Decode.Hex2{+hi}:
      dec_hex2(Byte.is_hex(b), hi, b, r, {==}, hb, hst, ih)

law dec_go:
  for seg: List<&2, U32>
  for +st: Decode.DecState
  for +hs: {Byte.all_bytes(seg) == True{} : Bool}
  for hst: StOk(st)
  DecOk(Decode.decode.go(seg, st))

def dec_go(seg, st, hs, hst):
  match seg:
    case Nil{}:
      match st:
        case Decode.Plain{}:
          {==}
        case Decode.Hex1{}:
          Unit{}
        case Decode.Hex2{hi}:
          Unit{}
    case Con{+b, +t}:
      dec_step(b, st, Decode.decode.go(t, Decode.decode.next(b, st)),
        Logic.and_left(U32.is_le(b, 255), Byte.all_bytes(t), hs), hst,
        z => dec_go(t, Decode.decode.next(b, st), Logic.and_right(U32.is_le(b, 255), Byte.all_bytes(t), hs), z))

# Decoding an encoded byte gives the byte back
law db_at:
  for k: Bool
  for +c: U32
  for +r: List<&2, U32>
  for ek: {k == Byte.is_pchar(c) : Bool}
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Decode.decode.go(Render.enc_byte.if(k, c, r), Decode.Plain{}) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}

def db_at(k, c, r, ek, hc):
  match k:
    case True{}:
      %ek : {Decode.decode.step.plain(c, Decode.decode.go(r, Decode.decode.next.plain(_, U32.is_eq(c, 37))), _, U32.is_eq(c, 37)) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}
      {==}
    case False{}:
      +x = Byte.hex_digit(Byte.hi_nibble(c))
      +y = Byte.hex_digit(Byte.lo_nibble(c))
      +h = ByteFacts.byte_rt(c, hc)
      +h2 = Logic.and_right(Byte.is_hex(x), Bool.and(Byte.is_hex(y), U32.is_eq(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c)), h)
      hx = Equal.sym(Bool, Byte.is_hex(x), True{}, Logic.and_left(Byte.is_hex(x), Bool.and(Byte.is_hex(y), U32.is_eq(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c)), h))
      hy = Equal.sym(Bool, Byte.is_hex(y), True{}, Logic.and_left(Byte.is_hex(y), U32.is_eq(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c), h2))
      pe = Equal.sym(U32, Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c,
        MStr.u32_eq_of_is_eq(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c,
          Logic.and_right(Byte.is_hex(y), U32.is_eq(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), c), h2)))
      %hx : {Decode.decode.step.hex1(Decode.decode.go(Con{y, r}, Decode.Hex2{Byte.hex_val(x)}), _) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}
      %hy : {Decode.decode.step.hex2(Byte.hex_pair(Byte.hex_val(x), Byte.hex_val(y)), Decode.decode.go(r, Decode.Plain{}), _) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}
      %pe : {Decode.ok_cons(_, Decode.decode.go(r, Decode.Plain{})) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}
      {==}

law db:
  for +c: U32
  for +r: List<&2, U32>
  for hc: {U32.is_le(c, 255) == True{} : Bool}
  {Decode.decode.go(Render.enc_byte(c, r), Decode.Plain{}) == Decode.ok_cons(c, Decode.decode.go(r, Decode.Plain{})) : Result<&2, &2, Error.PathError, List<&2, U32>>}

def db(c, r, hc):
  db_at(Byte.is_pchar(c), c, r, {==}, hc)

# Decoding an encoded segment gives the segment back
law dec_enc:
  for s: List<&2, U32>
  for +hs: {Byte.all_bytes(s) == True{} : Bool}
  {Decode.decode.go(Render.enc_seg(s), Decode.Plain{}) == Done{s} : Result<&2, &2, Error.PathError, List<&2, U32>>}

def dec_enc(s, hs):
  match s:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(Result<&2, &2, Error.PathError, List<&2, U32>>,
        Decode.decode.go(Render.enc_byte(c, Render.enc_seg(t)), Decode.Plain{}),
        Decode.ok_cons(c, Decode.decode.go(Render.enc_seg(t), Decode.Plain{})),
        Done{Con{c, t}},
        db(c, Render.enc_seg(t), Logic.and_left(U32.is_le(c, 255), Byte.all_bytes(t), hs)),
        Equal.cong(Result<&2, &2, Error.PathError, List<&2, U32>>, Result<&2, &2, Error.PathError, List<&2, U32>>,
          r => Decode.ok_cons(c, r), Decode.decode.go(Render.enc_seg(t), Decode.Plain{}), Done{t},
          dec_enc(t, Logic.and_right(U32.is_le(c, 255), Byte.all_bytes(t), hs))))

law decode_plain:
  for b: List<&2, U32>
  for e: {Byte.all_pchar(b) == True{} : Bool}
  {Decode.decode(b) == Done{b} : Result<&2, &2, Error.PathError, List<&2, U32>>}

def decode_plain(b, e):
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      decode_plain.at(Byte.is_pchar(h), h, t, e, e2 => decode_plain(t, e2))
