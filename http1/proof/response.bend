# Proofs of the response laws R1-R3.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/proof/logic.bend as Logic
import ../../urlpath/proof/bytes.bend as UrlByteProof
import ../../urlpath/src/bytes.bend as UrlByte
import bend-mathlib@0.7.4.0/string.bend as MStr
import bend-mathlib@0.7.4.0/list.bend as MList
import ../src/bytes.bend as Byte
import ../src/fields.bend as Fields
import ../src/request.bend as Req
import ../src/response.bend as Resp


# ---- What a built response promises ----

# What response promises when it answers Done
def Good(r: Resp.Response, +s: U32, +hs: List<&2, Req.Field>, +b: List<&2, U32>) -> Type:
  {Resp.Response{s, hs, b} == r : Resp.Response} & ({Resp.status_ok(s) == True{} : Bool} & ({Resp.fields_ok(hs) == True{} : Bool} & {Resp.all_bytes(b) == True{} : Bool}))

def Ok(res: Result<&2, &2, Resp.ResponseError, Resp.Response>, +s: U32, +hs: List<&2, Req.Field>, +b: List<&2, U32>) -> Type:
  match res:
    case Fail{x}:
      Unit
    case Done{r}:
      Good(r, s, hs, b)

law ok_bytes:
  for k: Bool
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for ek: {k == Resp.all_bytes(b) : Bool}
  for hs1: {Resp.status_ok(s) == True{} : Bool}
  for hf: {Resp.fields_ok(hs) == True{} : Bool}
  Ok(Resp.response.bytes(k, s, hs, b), s, hs, b)

def ok_bytes(k, s, hs, b, ek, hs1, hf):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ({==}, (hs1, (hf, Equal.sym(Bool, True{}, Resp.all_bytes(b), ek))))

law ok_body:
  for k: Bool
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for ek: {k == Bool.or(Resp.has_content(s), List.is_empty(&2, U32, b)) : Bool}
  for hs1: {Resp.status_ok(s) == True{} : Bool}
  for hf: {Resp.fields_ok(hs) == True{} : Bool}
  Ok(Resp.response.body(k, s, hs, b), s, hs, b)

def ok_body(k, s, hs, b, ek, hs1, hf):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ok_bytes(Resp.all_bytes(b), s, hs, b, {==}, hs1, hf)

law ok_fields:
  for k: Bool
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for ek: {k == Resp.fields_ok(hs) : Bool}
  for hs1: {Resp.status_ok(s) == True{} : Bool}
  Ok(Resp.response.fields(k, s, hs, b), s, hs, b)

def ok_fields(k, s, hs, b, ek, hs1):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ok_body(Bool.or(Resp.has_content(s), List.is_empty(&2, U32, b)), s, hs, b, {==}, hs1, Equal.sym(Bool, True{}, Resp.fields_ok(hs), ek))

law ok_status:
  for k: Bool
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for ek: {k == Resp.status_ok(s) : Bool}
  Ok(Resp.response.status(k, s, hs, b), s, hs, b)

def ok_status(k, s, hs, b, ek):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ok_fields(Resp.fields_ok(hs), s, hs, b, {==}, Equal.sym(Bool, True{}, Resp.status_ok(s), ek))

law ok:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  Ok(Resp.response(s, hs, b), s, hs, b)

def ok(s, hs, b):
  ok_status(Resp.status_ok(s), s, hs, b, {==})

# From response(s, hs, b) == Done{r}
law good:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
  Good(r, s, hs, b)

def good(s, hs, b, r, e):
  %e : Ok(_, s, hs, b)
  ok(s, hs, b)


# ---- Single bytes ----

law ne_at:
  for -p: U32 -> Bool
  for k: Bool
  for +c: U32
  for +x: U32
  for ek: {k == U32.is_eq(c, x) : Bool}
  for h: {p(c) == True{} : Bool}
  for hx: {p(x) == False{} : Bool}
  {k == False{} : Bool}

def ne_at(p, k, c, x, ek, h, hx):
  match k:
    case True{}:
      e = MStr.u32_eq_of_is_eq(c, x, Equal.sym(Bool, True{}, U32.is_eq(c, x), ek))
      hp = Equal.trans(Bool, False{}, p(c), True{},
        Equal.trans(Bool, False{}, p(x), p(c), Equal.sym(Bool, p(x), False{}, hx), Equal.cong(U32, Bool, p, x, c, Equal.sym(U32, c, x, e))), h)
      Logic.absurd({True{} == False{} : Bool}, Logic.true_ne_false(hp))
    case False{}:
      {==}

# If p holds for c but not for x, c isn't x
law ne_of:
  for -p: U32 -> Bool
  for +c: U32
  for +x: U32
  for h: {p(c) == True{} : Bool}
  for hx: {p(x) == False{} : Bool}
  {U32.is_eq(c, x) == False{} : Bool}

def ne_of(p, c, x, h, hx):
  ne_at(p, U32.is_eq(c, x), c, x, {==}, h, hx)

# A byte that is neither CR, LF nor NUL is line safe
law safe_of:
  for -p: U32 -> Bool
  for +c: U32
  for +h: {p(c) == True{} : Bool}
  for h13: {p(13) == False{} : Bool}
  for h10: {p(10) == False{} : Bool}
  for h0: {p(0) == False{} : Bool}
  {Resp.is_line_safe(c) == True{} : Bool}

def safe_of(p, c, h, h13, h10, h0):
  %Equal.sym(Bool, U32.is_eq(c, 13), False{}, ne_of(p, c, 13, h, h13)) : {Bool.and(Bool.not(_), Bool.and(Bool.not(U32.is_eq(c, 10)), Bool.not(U32.is_eq(c, 0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(c, 10), False{}, ne_of(p, c, 10, h, h10)) : {Bool.and(Bool.not(_), Bool.not(U32.is_eq(c, 0))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(c, 0), False{}, ne_of(p, c, 0, h, h0)) : {Bool.not(_) == True{} : Bool}
  {==}


# ---- R1: field names and values are line safe ----

law all_tchar_safe:
  for +b: List<&2, U32>
  for +h: {Byte.all_tchar(b) == True{} : Bool}
  {Resp.line_safe(b) == True{} : Bool}

def all_tchar_safe(b, h):
  match b:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Logic.and_intro(Resp.is_line_safe(c), Resp.line_safe(t),
        safe_of(+x => Byte.is_tchar(x), c, Logic.and_left(Byte.is_tchar(c), Byte.all_tchar(t), h), {==}, {==}, {==}),
        all_tchar_safe(t, Logic.and_right(Byte.is_tchar(c), Byte.all_tchar(t), h)))

law token_safe:
  for +b: List<&2, U32>
  for h: {Byte.is_token(b) == True{} : Bool}
  {Resp.line_safe(b) == True{} : Bool}

def token_safe(b, h):
  match b:
    case Nil{}:
      Logic.absurd({Resp.line_safe(Nil{}) == True{} : Bool}, Logic.true_ne_false(h))
    case Con{+c, +t}:
      all_tchar_safe(Con{c, t}, h)

law value_safe:
  for +b: List<&2, U32>
  for +h: {Fields.all_value_bytes(b) == True{} : Bool}
  {Resp.line_safe(b) == True{} : Bool}

def value_safe(b, h):
  match b:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Logic.and_intro(Resp.is_line_safe(c), Resp.line_safe(t),
        safe_of(+x => Fields.is_value_byte(x), c, Logic.and_left(Fields.is_value_byte(c), Fields.all_value_bytes(t), h), {==}, {==}, {==}),
        value_safe(t, Logic.and_right(Fields.is_value_byte(c), Fields.all_value_bytes(t), h)))

law fields_safe:
  for +hs: List<&2, Req.Field>
  for +h: {Resp.fields_ok(hs) == True{} : Bool}
  {Resp.headers_safe(hs) == True{} : Bool}

def fields_safe(hs, h):
  match hs:
    case Nil{}:
      {==}
    case Con{f, +rest}:
      match f:
        case Req.Field{+n, +v}:
          +hf = Logic.and_left(Resp.field_ok(Req.Field{n, v}), Resp.fields_ok(rest), h)
          +hv = Logic.and_right(Byte.is_token(n), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n))), hf)
          Logic.and_intro(Resp.line_safe(n), Bool.and(Resp.line_safe(v), Resp.headers_safe(rest)),
            token_safe(n, Logic.and_left(Byte.is_token(n), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n))), hf)),
            Logic.and_intro(Resp.line_safe(v), Resp.headers_safe(rest),
              value_safe(v, Logic.and_left(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n)), hv)),
              fields_safe(rest, Logic.and_right(Resp.field_ok(Req.Field{n, v}), Resp.fields_ok(rest), h))))

law r1_of:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for g: Good(r, s, hs, b)
  {Resp.headers_safe(Resp.headers(r)) == True{} : Bool}

def r1_of(s, hs, b, r, g):
  (er, rest) = g
  (hst, rest2) = rest
  (hf, hb) = rest2
  %er : {Resp.headers_safe(Resp.headers(_)) == True{} : Bool}
  fields_safe(hs, hf)

# R1
law r1:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
  {Resp.headers_safe(Resp.headers(r)) == True{} : Bool}

def r1(s, hs, b, r, e):
  r1_of(s, hs, b, r, good(s, hs, b, r, e))


# ---- R3: the head ends right before the body ----

# The first CRLF CRLF in x is right before b, so x is h then b
def Ends(x: List<&2, U32>, h: List<&2, U32>, b: List<&2, U32>) -> Type:
  {Resp.head_end(x) == Byte.Cut{h, b} : Byte.Cut} & {x == List.append(&2, U32, h, b) : List<&2, U32>}

# A line safe byte isn't CR
law not_cr:
  for +c: U32
  for h: {Resp.is_line_safe(c) == True{} : Bool}
  {U32.is_eq(c, 13) == False{} : Bool}

def not_cr(c, h):
  Logic.not_true(U32.is_eq(c, 13),
    Logic.and_left(Bool.not(U32.is_eq(c, 13)), Bool.and(Bool.not(U32.is_eq(c, 10)), Bool.not(U32.is_eq(c, 0))), h))

# A byte that isn't CR can't start the CRLF CRLF
law he_skip:
  for +c: U32
  for +t: List<&2, U32>
  for e: {U32.is_eq(c, 13) == False{} : Bool}
  {Resp.head_end(Con{c, t}) == Byte.cut.cons(c, Resp.head_end(t)) : Byte.Cut}

def he_skip(c, t, e):
  %Equal.sym(Bool, U32.is_eq(c, 13), False{}, e) : {Resp.head_end.at(_, c, t, u => Resp.head_end(t)) == Byte.cut.cons(c, Resp.head_end(t)) : Byte.Cut}
  {==}

# A CRLF followed by a byte that isn't CR isn't the end of the head
law he_crlf:
  for +c: U32
  for +z: List<&2, U32>
  for e: {U32.is_eq(c, 13) == False{} : Bool}
  {Resp.head_end(Con{13, Con{10, Con{c, z}}}) == Byte.cut.cons(13, Byte.cut.cons(10, Resp.head_end(Con{c, z}))) : Byte.Cut}

def he_crlf(c, z, e):
  %Equal.sym(Bool, U32.is_eq(c, 13), False{}, e) : {Resp.head_end.found(Byte.drop_prefix_ci.if(_, Byte.drop_prefix([10], z)), 13, u => Resp.head_end(Con{10, Con{c, z}})) == Byte.cut.cons(13, Byte.cut.cons(10, Resp.head_end(Con{c, z}))) : Byte.Cut}
  {==}

law ends_cons:
  for +c: U32
  for +x: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for hc: {Resp.head_end(Con{c, x}) == Byte.cut.cons(c, Resp.head_end(x)) : Byte.Cut}
  for p: Ends(x, h, b)
  Ends(Con{c, x}, Con{c, h}, b)

def ends_cons(c, x, h, b, hc, p):
  (e1, e2) = p
  (Equal.trans(Byte.Cut, Resp.head_end(Con{c, x}), Byte.cut.cons(c, Resp.head_end(x)), Byte.Cut{Con{c, h}, b}, hc,
      Equal.cong(Byte.Cut, Byte.Cut, y => Byte.cut.cons(c, y), Resp.head_end(x), Byte.Cut{h, b}, e1)),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{c, y}, x, List.append(&2, U32, h, b), e2))

# Line safe bytes in front don't move the end of the head
law he_app:
  for +x: List<&2, U32>
  for +rest: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for +hx: {Resp.line_safe(x) == True{} : Bool}
  for p: Ends(rest, h, b)
  Ends(List.append(&2, U32, x, rest), List.append(&2, U32, x, h), b)

def he_app(x, rest, h, b, hx, p):
  match x:
    case Nil{}:
      p
    case Con{+c, +t}:
      ends_cons(c, List.append(&2, U32, t, rest), List.append(&2, U32, t, h), b,
        he_skip(c, List.append(&2, U32, t, rest), not_cr(c, Logic.and_left(Resp.is_line_safe(c), Resp.line_safe(t), hx))),
        he_app(t, rest, h, b, Logic.and_right(Resp.is_line_safe(c), Resp.line_safe(t), hx), p))

# ... nor does a CRLF before a byte that isn't CR
law ends_crlf:
  for +c: U32
  for +z: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for e: {U32.is_eq(c, 13) == False{} : Bool}
  for p: Ends(Con{c, z}, h, b)
  Ends(Con{13, Con{10, Con{c, z}}}, Con{13, Con{10, h}}, b)

def ends_crlf(c, z, h, b, e, p):
  (e1, e2) = p
  (Equal.trans(Byte.Cut, Resp.head_end(Con{13, Con{10, Con{c, z}}}), Byte.cut.cons(13, Byte.cut.cons(10, Resp.head_end(Con{c, z}))), Byte.Cut{Con{13, Con{10, h}}, b}, he_crlf(c, z, e),
      Equal.cong(Byte.Cut, Byte.Cut, y => Byte.cut.cons(13, Byte.cut.cons(10, y)), Resp.head_end(Con{c, z}), Byte.Cut{h, b}, e1)),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{13, Con{10, y}}, Con{c, z}, List.append(&2, U32, h, b), e2))

law ends_field:
  for f: Req.Field
  for +t: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for hf0: {Resp.field_ok(f) == True{} : Bool}
  for p: Ends(t, h, b)
  Ends(Resp.field_into(f, t), Resp.field_into(f, h), b)

def ends_field(f, t, h, b, hf0, p):
  match f:
    case Req.Field{n, +v}:
      match n:
        case Nil{}:
          Logic.absurd(Ends(Resp.field_into(Req.Field{Nil{}, v}, t), Resp.field_into(Req.Field{Nil{}, v}, h), b), Logic.true_ne_false(hf0))
        case Con{+c, +nt}:
          +hf = hf0
          +hn = token_safe(Con{c, nt}, Logic.and_left(Byte.is_token(Con{c, nt}), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt}))), hf))
          hv = value_safe(v, Logic.and_left(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt})),
            Logic.and_right(Byte.is_token(Con{c, nt}), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt}))), hf)))
          ends_crlf(c, List.append(&2, U32, nt, Con{58, Con{32, List.append(&2, U32, v, t)}}), List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, h)}}), b,
            not_cr(c, Logic.and_left(Resp.is_line_safe(c), Resp.line_safe(nt), hn)),
            he_app(Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, t)}}, Con{58, Con{32, List.append(&2, U32, v, h)}}, b, hn,
              he_app([58, 32], List.append(&2, U32, v, t), List.append(&2, U32, v, h), b, {==},
                he_app(v, t, h, b, hv, p))))

law ends_fields:
  for +hs: List<&2, Req.Field>
  for +t: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for +hf: {Resp.fields_ok(hs) == True{} : Bool}
  for p: Ends(t, h, b)
  Ends(Resp.fields_into(hs, t), Resp.fields_into(hs, h), b)

def ends_fields(hs, t, h, b, hf, p):
  match hs:
    case Nil{}:
      p
    case Con{+f, +rest}:
      ends_field(f, Resp.fields_into(rest, t), Resp.fields_into(rest, h), b, Logic.and_left(Resp.field_ok(f), Resp.fields_ok(rest), hf),
        ends_fields(rest, t, h, b, Logic.and_right(Resp.field_ok(f), Resp.fields_ok(rest), hf), p))

# The digits of a length are line safe
law ls_digit:
  for d: Resp.Digit
  for +acc: List<&2, U32>
  for h: {Resp.line_safe(acc) == True{} : Bool}
  {Resp.line_safe(Con{Resp.digit_byte(d), acc}) == True{} : Bool}

def ls_digit(d, acc, h):
  match d:
    case Resp.D0{}:
      h
    case Resp.D1{}:
      h
    case Resp.D2{}:
      h
    case Resp.D3{}:
      h
    case Resp.D4{}:
      h
    case Resp.D5{}:
      h
    case Resp.D6{}:
      h
    case Resp.D7{}:
      h
    case Resp.D8{}:
      h
    case Resp.D9{}:
      h

law ls_rev:
  for +ds: List<&2, Resp.Digit>
  for +acc: List<&2, U32>
  for h: {Resp.line_safe(acc) == True{} : Bool}
  {Resp.line_safe(List.reverse.go(&2, U32, Resp.digit_bytes(ds), acc)) == True{} : Bool}

def ls_rev(ds, acc, h):
  match ds:
    case Nil{}:
      h
    case Con{+d, +rest}:
      ls_rev(rest, Con{Resp.digit_byte(d), acc}, ls_digit(d, acc, h))

law length_safe:
  for +b: List<&2, U32>
  {Resp.line_safe(Resp.length_text(b)) == True{} : Bool}

def length_safe(b):
  ls_rev(Resp.count(b), Nil{}, {==})

law ends_length:
  for has: Bool
  for +b0: List<&2, U32>
  for +t: List<&2, U32>
  for +h: List<&2, U32>
  for +b: List<&2, U32>
  for p: Ends(t, h, b)
  Ends(Resp.length_into(has, b0, t), Resp.length_into(has, b0, h), b)

def ends_length(has, b0, t, h, b, p):
  match has:
    case False{}:
      p
    case True{}:
      ends_crlf(67, List.append(&2, U32, Path.bytes("ontent-Length: "), List.append(&2, U32, Resp.length_text(b0), t)), List.append(&2, U32, Path.bytes("Content-Length: "), List.append(&2, U32, Resp.length_text(b0), h)), b, {==},
        he_app(Path.bytes("Content-Length: "), List.append(&2, U32, Resp.length_text(b0), t), List.append(&2, U32, Resp.length_text(b0), h), b, {==},
          he_app(Resp.length_text(b0), t, h, b, length_safe(b0), p)))

# Every reason phrase is line safe
def phrases_safe(tbl: List<&2, Resp.Phrase>) -> Bool:
  match tbl:
    case Nil{}:
      True{}
    case Con{p, rest}:
      match p:
        case Resp.Phrase{c, text}:
          Bool.and(Resp.line_safe(text), phrases_safe(rest))

law rs_if:
  for k: Bool
  for text: List<&2, U32>
  for other: List<&2, U32>
  for ht: {Resp.line_safe(text) == True{} : Bool}
  for ho: {Resp.line_safe(other) == True{} : Bool}
  {Resp.line_safe(Resp.reason.if(k, text, other)) == True{} : Bool}

def rs_if(k, text, other, ht, ho):
  match k:
    case True{}:
      ht
    case False{}:
      ho

law rs_go:
  for +tbl: List<&2, Resp.Phrase>
  for +s: U32
  for +h: {phrases_safe(tbl) == True{} : Bool}
  {Resp.line_safe(Resp.reason.go(tbl, s)) == True{} : Bool}

def rs_go(tbl, s, h):
  match tbl:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      match p:
        case Resp.Phrase{+c, +text}:
          rs_if(U32.is_eq(c, s), text, Resp.reason.go(rest, s),
            Logic.and_left(Resp.line_safe(text), phrases_safe(rest), h),
            rs_go(rest, s, Logic.and_right(Resp.line_safe(text), phrases_safe(rest), h)))

law reason_safe:
  for +s: U32
  {Resp.line_safe(Resp.reason(s)) == True{} : Bool}

def reason_safe(s):
  rs_go(Resp.phrases(), s, {==})

# A status digit is line safe
law digit_safe:
  for +n: U32
  {Resp.is_line_safe(UrlByte.hex_digit(n)) == True{} : Bool}

def digit_safe(n):
  safe_of(+x => UrlByte.is_upper_hex(x), UrlByte.hex_digit(n), UrlByteProof.hd_upper(n), {==}, {==}, {==})

law status_safe:
  for +s: U32
  {Resp.line_safe(Resp.status_line(s)) == True{} : Bool}

def status_safe(s):
  Logic.and_intro(Resp.is_line_safe(UrlByte.hex_digit(U32.div(s, 100))), Resp.line_safe(Con{UrlByte.hex_digit(U32.mod(U32.div(s, 10), 10)), Con{UrlByte.hex_digit(U32.mod(s, 10)), Con{32, Resp.reason(s)}}}),
    digit_safe(U32.div(s, 100)),
    Logic.and_intro(Resp.is_line_safe(UrlByte.hex_digit(U32.mod(U32.div(s, 10), 10))), Resp.line_safe(Con{UrlByte.hex_digit(U32.mod(s, 10)), Con{32, Resp.reason(s)}}),
      digit_safe(U32.mod(U32.div(s, 10), 10)),
      Logic.and_intro(Resp.is_line_safe(UrlByte.hex_digit(U32.mod(s, 10))), Resp.line_safe(Con{32, Resp.reason(s)}),
        digit_safe(U32.mod(s, 10)),
        reason_safe(s))))

law ends_write:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +h: {Resp.fields_ok(hs) == True{} : Bool}
  Ends(Resp.write(Resp.Response{s, hs, b}), Resp.write_head(Resp.Response{s, hs, b}), b)

def ends_write(s, hs, b, h):
  +nil = {Nil{} : List<&2, U32>}
  he_app(Resp.status_line(s), Resp.fields_into(hs, Resp.length_into(Resp.has_length(s), b, Con{13, Con{10, Con{13, Con{10, b}}}})), Resp.fields_into(hs, Resp.length_into(Resp.has_length(s), b, Con{13, Con{10, Con{13, Con{10, nil}}}})), b, status_safe(s),
    ends_fields(hs, Resp.length_into(Resp.has_length(s), b, Con{13, Con{10, Con{13, Con{10, b}}}}), Resp.length_into(Resp.has_length(s), b, Con{13, Con{10, Con{13, Con{10, nil}}}}), b, h,
      ends_length(Resp.has_length(s), b, Con{13, Con{10, Con{13, Con{10, b}}}}, Con{13, Con{10, Con{13, Con{10, nil}}}}, b,
        ({==}, {==}))))

law r3_of:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for g: Good(r, s, hs, b)
  Ends(Resp.write(r), Resp.write_head(r), b)

def r3_of(s, hs, b, r, g):
  (er, rest) = g
  (hst, rest2) = rest
  (hf, hb) = rest2
  %er : Ends(Resp.write(_), Resp.write_head(_), b)
  ends_write(s, hs, b, hf)

# R3
law r3:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
  Ends(Resp.write(r), Resp.write_head(r), b)

def r3(s, hs, b, r, e):
  r3_of(s, hs, b, r, good(s, hs, b, r, e))


# ---- R2: one Content-Length, and it is the body's length ----

# -- Counting --

def dval(d: Resp.Digit) -> Nat:
  match d:
    case Resp.D0{}:
      0n
    case Resp.D1{}:
      1n
    case Resp.D2{}:
      2n
    case Resp.D3{}:
      3n
    case Resp.D4{}:
      4n
    case Resp.D5{}:
      5n
    case Resp.D6{}:
      6n
    case Resp.D7{}:
      7n
    case Resp.D8{}:
      8n
    case Resp.D9{}:
      9n

# The number digits stand for, ones digit first
def val(ds: List<&2, Resp.Digit>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, rest}:
      Nat.add(dval(d), Resp.times10(val(rest)))

law inc_val:
  for ds: List<&2, Resp.Digit>
  {val(Resp.inc(ds)) == 1n+val(ds) : Nat}

def inc_val(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, +rest}:
      match d:
        case Resp.D0{}:
          {==}
        case Resp.D1{}:
          {==}
        case Resp.D2{}:
          {==}
        case Resp.D3{}:
          {==}
        case Resp.D4{}:
          {==}
        case Resp.D5{}:
          {==}
        case Resp.D6{}:
          {==}
        case Resp.D7{}:
          {==}
        case Resp.D8{}:
          {==}
        case Resp.D9{}:
          Equal.cong(Nat, Nat, y => Resp.times10(y), val(Resp.inc(rest)), 1n+val(rest), inc_val(rest))

law count_val:
  for b: List<&2, U32>
  {val(Resp.count(b)) == List.length(&2, U32, b) : Nat}

def count_val(b):
  match b:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, val(Resp.inc(Resp.count(t))), 1n+val(Resp.count(t)), 1n+List.length(&2, U32, t),
        inc_val(Resp.count(t)),
        Equal.cong(Nat, Nat, y => 1n+y, val(Resp.count(t)), List.length(&2, U32, t), count_val(t)))

# -- Reading the digits back --

law dv:
  for d: Resp.Digit
  {Resp.digit_value(Resp.digit_byte(d)) == Some{dval(d)} : Maybe<&2, Nat>}

def dv(d):
  match d:
    case Resp.D0{}:
      {==}
    case Resp.D1{}:
      {==}
    case Resp.D2{}:
      {==}
    case Resp.D3{}:
      {==}
    case Resp.D4{}:
      {==}
    case Resp.D5{}:
      {==}
    case Resp.D6{}:
      {==}
    case Resp.D7{}:
      {==}
    case Resp.D8{}:
      {==}
    case Resp.D9{}:
      {==}

law of_digits:
  for ds: List<&2, Resp.Digit>
  {Resp.ones_first(Resp.digit_bytes(ds)) == Some{val(ds)} : Maybe<&2, Nat>}

def of_digits(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      %Equal.sym(Maybe<&2, Nat>, Resp.digit_value(Resp.digit_byte(d)), Some{dval(d)}, dv(d)) : {Resp.ones_first.join(_, Resp.ones_first(Resp.digit_bytes(rest))) == Some{val(Con{d, rest})} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Resp.ones_first(Resp.digit_bytes(rest)), Some{val(rest)}, of_digits(rest)) : {Resp.ones_first.join(Some{dval(d)}, _) == Some{val(Con{d, rest})} : Maybe<&2, Nat>}
      {==}

# decimal.go needs at least one digit, and inc always gives one
law dec_inc:
  for ds: List<&2, Resp.Digit>
  {Resp.decimal.go(Resp.digit_bytes(Resp.inc(ds))) == Resp.ones_first(Resp.digit_bytes(Resp.inc(ds))) : Maybe<&2, Nat>}

def dec_inc(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, rest}:
      match d:
        case Resp.D0{}:
          {==}
        case Resp.D1{}:
          {==}
        case Resp.D2{}:
          {==}
        case Resp.D3{}:
          {==}
        case Resp.D4{}:
          {==}
        case Resp.D5{}:
          {==}
        case Resp.D6{}:
          {==}
        case Resp.D7{}:
          {==}
        case Resp.D8{}:
          {==}
        case Resp.D9{}:
          {==}

law dec_count:
  for b: List<&2, U32>
  {Resp.decimal.go(Resp.digit_bytes(Resp.count(b))) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}

def dec_count(b):
  match b:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Maybe<&2, Nat>, Resp.decimal.go(Resp.digit_bytes(Resp.inc(Resp.count(t)))), Resp.ones_first(Resp.digit_bytes(Resp.inc(Resp.count(t)))), Some{List.length(&2, U32, Con{h, t})},
        dec_inc(Resp.count(t)),
        Equal.trans(Maybe<&2, Nat>, Resp.ones_first(Resp.digit_bytes(Resp.inc(Resp.count(t)))), Some{val(Resp.count(Con{h, t}))}, Some{List.length(&2, U32, Con{h, t})},
          of_digits(Resp.inc(Resp.count(t))),
          Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, val(Resp.count(Con{h, t})), List.length(&2, U32, Con{h, t}), count_val(Con{h, t}))))

# -- Trimming leaves the digits alone --

law do_digits:
  for ds: List<&2, Resp.Digit>
  {Fields.drop_ows(Resp.digit_bytes(ds)) == Resp.digit_bytes(ds) : List<&2, U32>}

def do_digits(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, rest}:
      match d:
        case Resp.D0{}:
          {==}
        case Resp.D1{}:
          {==}
        case Resp.D2{}:
          {==}
        case Resp.D3{}:
          {==}
        case Resp.D4{}:
          {==}
        case Resp.D5{}:
          {==}
        case Resp.D6{}:
          {==}
        case Resp.D7{}:
          {==}
        case Resp.D8{}:
          {==}
        case Resp.D9{}:
          {==}

law do_cons:
  for d: Resp.Digit
  for +acc: List<&2, U32>
  {Fields.drop_ows(Con{Resp.digit_byte(d), acc}) == Con{Resp.digit_byte(d), acc} : List<&2, U32>}

def do_cons(d, acc):
  match d:
    case Resp.D0{}:
      {==}
    case Resp.D1{}:
      {==}
    case Resp.D2{}:
      {==}
    case Resp.D3{}:
      {==}
    case Resp.D4{}:
      {==}
    case Resp.D5{}:
      {==}
    case Resp.D6{}:
      {==}
    case Resp.D7{}:
      {==}
    case Resp.D8{}:
      {==}
    case Resp.D9{}:
      {==}

law do_rev:
  for +ds: List<&2, Resp.Digit>
  for +acc: List<&2, U32>
  for h: {Fields.drop_ows(acc) == acc : List<&2, U32>}
  {Fields.drop_ows(List.reverse.go(&2, U32, Resp.digit_bytes(ds), acc)) == List.reverse.go(&2, U32, Resp.digit_bytes(ds), acc) : List<&2, U32>}

def do_rev(ds, acc, h):
  match ds:
    case Nil{}:
      h
    case Con{+d, +rest}:
      do_rev(rest, Con{Resp.digit_byte(d), acc}, do_cons(d, acc))

# Reading the length text gives the body's length back
law read_length:
  for +b: List<&2, U32>
  {Resp.decimal(Fields.trim(Con{32, Resp.length_text(b)})) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}

def read_length(b):
  +db = Resp.digit_bytes(Resp.count(b))
  +rr = MList.reverse_reverse(&2, U32, db)
  %Equal.sym(List<&2, U32>, Fields.drop_ows(List.reverse(&2, U32, db)), List.reverse(&2, U32, db), do_rev(Resp.count(b), Nil{}, {==})) : {Resp.decimal(List.reverse(&2, U32, Fields.drop_ows(List.reverse(&2, U32, _)))) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, List.reverse(&2, U32, List.reverse(&2, U32, db)), db, rr) : {Resp.decimal(List.reverse(&2, U32, Fields.drop_ows(_))) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, Fields.drop_ows(db), db, do_digits(Resp.count(b))) : {Resp.decimal(List.reverse(&2, U32, _)) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, List.reverse(&2, U32, List.reverse(&2, U32, db)), db, rr) : {Resp.decimal.go(_) == Some{List.length(&2, U32, b)} : Maybe<&2, Nat>}
  dec_count(b)

# -- Splitting into lines --

def no_cr(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(U32.is_eq(h, 13)), no_cr(t))

law safe_no_cr:
  for +b: List<&2, U32>
  for +h: {Resp.line_safe(b) == True{} : Bool}
  {no_cr(b) == True{} : Bool}

def safe_no_cr(b, h):
  match b:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %Equal.sym(Bool, U32.is_eq(c, 13), False{}, not_cr(c, Logic.and_left(Resp.is_line_safe(c), Resp.line_safe(t), h))) : {Bool.and(Bool.not(_), no_cr(t)) == True{} : Bool}
      safe_no_cr(t, Logic.and_right(Resp.is_line_safe(c), Resp.line_safe(t), h))

# Bytes with no CR, then a CR: the bytes are one piece
law sp:
  for +x: List<&2, U32>
  for +z: List<&2, U32>
  for +h: {no_cr(x) == True{} : Bool}
  {Byte.split_on(List.append(&2, U32, x, Con{13, z}), 13) == Con{x, Byte.split_on(z, 13)} : List<&2, List<&2, U32>>}

def sp(x, z, h):
  match x:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      ec = Logic.not_true(U32.is_eq(c, 13), Logic.and_left(Bool.not(U32.is_eq(c, 13)), no_cr(t), h))
      %Equal.sym(Bool, U32.is_eq(c, 13), False{}, ec) : {Byte.split_on.if(_, c, Byte.split_on(List.append(&2, U32, t, Con{13, z}), 13)) == Con{Con{c, t}, Byte.split_on(z, 13)} : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, Byte.split_on(List.append(&2, U32, t, Con{13, z}), 13), Con{t, Byte.split_on(z, 13)}, sp(t, z, Logic.and_right(Bool.not(U32.is_eq(c, 13)), no_cr(t), h))) : {Byte.split_on.if(False{}, c, _) == Con{Con{c, t}, Byte.split_on(z, 13)} : List<&2, List<&2, U32>>}
      {==}

# LF, a line with no CR, then a CR: that line is the next field line
law l_line:
  for +c: U32
  for +ft: List<&2, U32>
  for +z: List<&2, U32>
  for +h: {no_cr(Con{c, ft}) == True{} : Bool}
  {Resp.field_lines(Byte.split_on(Con{10, List.append(&2, U32, Con{c, ft}, Con{13, z})}, 13)) == Con{Con{c, ft}, Resp.field_lines(Byte.split_on(z, 13))} : List<&2, List<&2, U32>>}

def l_line(c, ft, z, h):
  %Equal.sym(List<&2, List<&2, U32>>, Byte.split_on(List.append(&2, U32, Con{c, ft}, Con{13, z}), 13), Con{Con{c, ft}, Byte.split_on(z, 13)}, sp(Con{c, ft}, z, h)) : {Resp.field_lines(Byte.split_on.if(False{}, 10, _)) == Con{Con{c, ft}, Resp.field_lines(Byte.split_on(z, 13))} : List<&2, List<&2, U32>>}
  {==}

def after_cr(b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

law starts13:
  for +hs: List<&2, Req.Field>
  for +z: List<&2, U32>
  {Resp.fields_into(hs, Con{13, z}) == Con{13, after_cr(Resp.fields_into(hs, Con{13, z}))} : List<&2, U32>}

def starts13(hs, z):
  match hs:
    case Nil{}:
      {==}
    case Con{f, rest}:
      match f:
        case Req.Field{n, v}:
          {==}

# The field lines response writes for the caller's fields
def texts(hs: List<&2, Req.Field>) -> List<&2, List<&2, U32>>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{f, rest}:
      match f:
        case Req.Field{n, v}:
          Con{List.append(&2, U32, n, Con{58, Con{32, v}}), texts(rest)}

# line_safe holds for two lists put together
law he_safe_app:
  for +x: List<&2, U32>
  for +y: List<&2, U32>
  for +hx: {Resp.line_safe(x) == True{} : Bool}
  for +hy: {Resp.line_safe(y) == True{} : Bool}
  {Resp.line_safe(List.append(&2, U32, x, y)) == True{} : Bool}

def he_safe_app(x, y, hx, hy):
  match x:
    case Nil{}:
      hy
    case Con{+c, +t}:
      Logic.and_intro(Resp.is_line_safe(c), Resp.line_safe(List.append(&2, U32, t, y)),
        Logic.and_left(Resp.is_line_safe(c), Resp.line_safe(t), hx),
        he_safe_app(t, y, Logic.and_right(Resp.is_line_safe(c), Resp.line_safe(t), hx), hy))

law l_fields:
  for +hs: List<&2, Req.Field>
  for +z: List<&2, U32>
  for +h: {Resp.fields_ok(hs) == True{} : Bool}
  {Resp.field_lines(Byte.split_on(after_cr(Resp.fields_into(hs, Con{13, z})), 13)) == List.append(&2, List<&2, U32>, texts(hs), Resp.field_lines(Byte.split_on(z, 13))) : List<&2, List<&2, U32>>}

def l_fields(hs, z, h):
  match hs:
    case Nil{}:
      {==}
    case Con{f, +rest}:
      match f:
        case Req.Field{n, +v}:
          match n:
            case Nil{}:
              Logic.absurd({Resp.field_lines(Byte.split_on(after_cr(Resp.fields_into(Con{Req.Field{Nil{}, v}, rest}, Con{13, z})), 13)) == List.append(&2, List<&2, U32>, texts(Con{Req.Field{Nil{}, v}, rest}), Resp.field_lines(Byte.split_on(z, 13))) : List<&2, List<&2, U32>>}, Logic.true_ne_false(h))
            case Con{+c, +nt}:
              +hf = Logic.and_left(Resp.field_ok(Req.Field{Con{c, nt}, v}), Resp.fields_ok(rest), h)
              +hr = Logic.and_right(Resp.field_ok(Req.Field{Con{c, nt}, v}), Resp.fields_ok(rest), h)
              +hn = token_safe(Con{c, nt}, Logic.and_left(Byte.is_token(Con{c, nt}), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt}))), hf))
              +hv = value_safe(v, Logic.and_left(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt})),
                Logic.and_right(Byte.is_token(Con{c, nt}), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(Con{c, nt}))), hf)))
              +ff = Resp.fields_into(rest, Con{13, z})
              +a = after_cr(ff)
              +line = List.append(&2, U32, Con{c, nt}, Con{58, Con{32, v}})
              # the line has no CR
              hl = safe_no_cr(line, he_safe_app(Con{c, nt}, Con{58, Con{32, v}}, hn, hv))
              # its bytes, then the CR of the next line
              eb = Equal.trans(List<&2, U32>, List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, ff)}}), List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, Con{13, a})}}), List.append(&2, U32, line, Con{13, a}),
                Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, y)}}), ff, Con{13, a}, starts13(rest, z)),
                Equal.sym(List<&2, U32>, List.append(&2, U32, line, Con{13, a}), List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, Con{13, a})}}), MList.append_assoc(&2, U32, Con{c, nt}, Con{58, Con{32, v}}, Con{13, a})))
              %Equal.sym(List<&2, U32>, List.append(&2, U32, Con{c, nt}, Con{58, Con{32, List.append(&2, U32, v, ff)}}), List.append(&2, U32, line, Con{13, a}), eb) : {Resp.field_lines(Byte.split_on(Con{10, _}, 13)) == Con{line, List.append(&2, List<&2, U32>, texts(rest), Resp.field_lines(Byte.split_on(z, 13)))} : List<&2, List<&2, U32>>}
              %Equal.sym(List<&2, List<&2, U32>>, Resp.field_lines(Byte.split_on(Con{10, List.append(&2, U32, line, Con{13, a})}, 13)), Con{line, Resp.field_lines(Byte.split_on(a, 13))}, l_line(c, List.append(&2, U32, nt, Con{58, Con{32, v}}), a, hl)) : {_ == Con{line, List.append(&2, List<&2, U32>, texts(rest), Resp.field_lines(Byte.split_on(z, 13)))} : List<&2, List<&2, U32>>}
              Equal.cong(List<&2, List<&2, U32>>, List<&2, List<&2, U32>>, y => Con{line, y}, Resp.field_lines(Byte.split_on(a, 13)), List.append(&2, List<&2, U32>, texts(rest), Resp.field_lines(Byte.split_on(z, 13))), l_fields(rest, z, hr))

# -- Finding Content-Length --

# A token has no ":", so the line is cut right after the name
law cut_name:
  for +n: List<&2, U32>
  for +y: List<&2, U32>
  for +h: {Byte.all_tchar(n) == True{} : Bool}
  {Byte.cut(List.append(&2, U32, n, Con{58, y}), 58) == Byte.Cut{n, y} : Byte.Cut}

def cut_name(n, y, h):
  match n:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      ec = ne_of(+x => Byte.is_tchar(x), c, 58, Logic.and_left(Byte.is_tchar(c), Byte.all_tchar(t), h), {==})
      %Equal.sym(Bool, U32.is_eq(c, 58), False{}, ec) : {Byte.cut.if(_, c, List.append(&2, U32, t, Con{58, y}), Byte.cut(List.append(&2, U32, t, Con{58, y}), 58)) == Byte.Cut{Con{c, t}, y} : Byte.Cut}
      %Equal.sym(Byte.Cut, Byte.cut(List.append(&2, U32, t, Con{58, y}), 58), Byte.Cut{t, y}, cut_name(t, y, Logic.and_right(Byte.is_tchar(c), Byte.all_tchar(t), h))) : {Byte.cut.if(False{}, c, List.append(&2, U32, t, Con{58, y}), _) == Byte.Cut{Con{c, t}, y} : Byte.Cut}
      {==}

# A token is all token characters
law tok_all:
  for +n: List<&2, U32>
  for h: {Byte.is_token(n) == True{} : Bool}
  {Byte.all_tchar(n) == True{} : Bool}

def tok_all(n, h):
  match n:
    case Nil{}:
      Logic.absurd({Byte.all_tchar(Nil{}) == True{} : Bool}, Logic.true_ne_false(h))
    case Con{+c, +t}:
      h

# The caller's fields are never Content-Length, so the reader skips them
law lv_skip:
  for +hs: List<&2, Req.Field>
  for +rest: List<&2, List<&2, U32>>
  for +h: {Resp.fields_ok(hs) == True{} : Bool}
  {Resp.length_values(List.append(&2, List<&2, U32>, texts(hs), rest)) == Resp.length_values(rest) : List<&2, Maybe<&2, Nat>>}

def lv_skip(hs, rest, h):
  match hs:
    case Nil{}:
      {==}
    case Con{f, +more}:
      match f:
        case Req.Field{+n, +v}:
          +hf = Logic.and_left(Resp.field_ok(Req.Field{n, v}), Resp.fields_ok(more), h)
          +hfr = Logic.and_right(Byte.is_token(n), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n))), hf)
          +ht = Logic.and_left(Byte.is_token(n), Bool.and(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n))), hf)
          +r = Resp.length_values(List.append(&2, List<&2, U32>, texts(more), rest))
          efr = Logic.not_true(Resp.is_framing(n), Logic.and_right(Fields.all_value_bytes(v), Bool.not(Resp.is_framing(n)), hfr))
          ecl = Logic.or_l(Byte.eq(Byte.lower_all(n), Path.bytes("content-length")), Byte.eq(Byte.lower_all(n), Path.bytes("transfer-encoding")), efr)
          %Equal.sym(Byte.Cut, Byte.cut(List.append(&2, U32, n, Con{58, Con{32, v}}), 58), Byte.Cut{n, Con{32, v}}, cut_name(n, Con{32, v}, tok_all(n, ht))) : {Resp.length_values.cut(_, r) == Resp.length_values(rest) : List<&2, Maybe<&2, Nat>>}
          %Equal.sym(Bool, Byte.eq(Byte.lower_all(n), Path.bytes("content-length")), False{}, ecl) : {Resp.length_values.if(_, Con{32, v}, r) == Resp.length_values(rest) : List<&2, Maybe<&2, Nat>>}
          lv_skip(more, rest, Logic.and_right(Resp.field_ok(Req.Field{n, v}), Resp.fields_ok(more), h))

# The Content-Length line write adds
def cl_line(b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Path.bytes("Content-Length: "), Resp.length_text(b))

law l_cl:
  for +b: List<&2, U32>
  for +e: List<&2, U32>
  {Resp.field_lines(Byte.split_on(Con{10, List.append(&2, U32, Path.bytes("Content-Length: "), List.append(&2, U32, Resp.length_text(b), Con{13, Con{10, Con{13, Con{10, e}}}}))}, 13)) == [cl_line(b)] : List<&2, List<&2, U32>>}

def l_cl(b, e):
  +lt = Resp.length_text(b)
  +tail = {Con{13, Con{10, Con{13, Con{10, e}}}} : List<&2, U32>}
  %MList.append_assoc(&2, U32, Path.bytes("Content-Length: "), lt, tail) : {Resp.field_lines(Byte.split_on(Con{10, _}, 13)) == [cl_line(b)] : List<&2, List<&2, U32>>}
  Equal.trans(List<&2, List<&2, U32>>, Resp.field_lines(Byte.split_on(Con{10, List.append(&2, U32, cl_line(b), tail)}, 13)), Con{cl_line(b), Resp.field_lines(Byte.split_on(Con{10, Con{13, Con{10, e}}}, 13))}, [cl_line(b)],
    l_line(67, List.append(&2, U32, Path.bytes("ontent-Length: "), lt), Con{10, Con{13, Con{10, e}}}, safe_no_cr(cl_line(b), he_safe_app(Path.bytes("Content-Length: "), lt, {==}, length_safe(b)))),
    {==})

law r2_into:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +t: List<&2, U32>
  for +hf: {Resp.fields_ok(hs) == True{} : Bool}
  for hb: {Resp.has_length(s) == True{} : Bool}
  {Resp.content_lengths(Resp.head_into(s, hs, b, t)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

def r2_into(s, hs, b, t, hf, hb):
  +st = Resp.status_line(s)
  +c = {Con{13, Con{10, Con{13, Con{10, t}}}} : List<&2, U32>}
  +z = {Con{10, List.append(&2, U32, Path.bytes("Content-Length: "), List.append(&2, U32, Resp.length_text(b), c))} : List<&2, U32>}
  +ff = Resp.fields_into(hs, Con{13, z})
  +want = {[Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(Bool, Resp.has_length(s), True{}, hb) : {Resp.content_lengths(List.append(&2, U32, st, Resp.fields_into(hs, Resp.length_into(_, b, c)))) == want : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(List<&2, U32>, ff, Con{13, after_cr(ff)}, starts13(hs, z)) : {Resp.content_lengths(List.append(&2, U32, st, _)) == want : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, U32>>, Byte.split_on(List.append(&2, U32, st, Con{13, after_cr(ff)}), 13), Con{st, Byte.split_on(after_cr(ff), 13)}, sp(st, after_cr(ff), safe_no_cr(st, status_safe(s)))) : {Resp.content_lengths.go(_) == want : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, U32>>, Resp.field_lines(Byte.split_on(after_cr(ff), 13)), List.append(&2, List<&2, U32>, texts(hs), Resp.field_lines(Byte.split_on(z, 13))), l_fields(hs, z, hf)) : {Resp.length_values(_) == want : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, U32>>, Resp.field_lines(Byte.split_on(z, 13)), [cl_line(b)], l_cl(b, t)) : {Resp.length_values(List.append(&2, List<&2, U32>, texts(hs), _)) == want : List<&2, Maybe<&2, Nat>>}
  %Equal.sym(List<&2, Maybe<&2, Nat>>, Resp.length_values(List.append(&2, List<&2, U32>, texts(hs), [cl_line(b)])), Resp.length_values([cl_line(b)]), lv_skip(hs, [cl_line(b)], hf)) : {_ == want : List<&2, Maybe<&2, Nat>>}
  Equal.cong(Maybe<&2, Nat>, List<&2, Maybe<&2, Nat>>, y => [y], Resp.decimal(Fields.trim(Con{32, Resp.length_text(b)})), Some{List.length(&2, U32, b)}, read_length(b))

law r2_of:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for g: Good(r, s, hs, b)
  for hb: {Resp.has_length(s) == True{} : Bool}
  {Resp.content_lengths(Resp.write(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

def r2_of(s, hs, b, r, g, hb):
  (er, rest) = g
  (hst, rest2) = rest
  (hf, hbo) = rest2
  %er : {Resp.content_lengths(Resp.write(_)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}
  r2_into(s, hs, b, b, hf, hb)

# R2
law r2:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
  for hb: {Resp.has_length(s) == True{} : Bool}
  {Resp.content_lengths(Resp.write(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

def r2(s, hs, b, r, e, hb):
  r2_of(s, hs, b, r, good(s, hs, b, r, e), hb)

law r2h_of:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for g: Good(r, s, hs, b)
  for hb: {Resp.has_length(s) == True{} : Bool}
  {Resp.content_lengths(Resp.write_head(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

def r2h_of(s, hs, b, r, g, hb):
  (er, rest) = g
  (hst, rest2) = rest
  (hf, hbo) = rest2
  %er : {Resp.content_lengths(Resp.write_head(_)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}
  r2_into(s, hs, b, Nil{}, hf, hb)

# R2 for write_head
law r2h:
  for +s: U32
  for +hs: List<&2, Req.Field>
  for +b: List<&2, U32>
  for +r: Resp.Response
  for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
  for hb: {Resp.has_length(s) == True{} : Bool}
  {Resp.content_lengths(Resp.write_head(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

def r2h(s, hs, b, r, e, hb):
  r2h_of(s, hs, b, r, good(s, hs, b, r, e), hb)
