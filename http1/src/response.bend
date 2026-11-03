# Responses: build one from its parts, then write it out as bytes.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ./request.bend as Req
import ./bytes.bend as Byte
import ./fields.bend as Fields


# A response. headers are written in this order; Content-Length is added by
# write, never by the caller.
type Response is Data:
  Response{status: U32, headers: List<&2, Req.Field>, body: List<&2, U32>}


# Why response refused to build a response
type ResponseError is Data:
  InvalidStatus{}
  InvalidHeaderName{}
  InvalidHeaderValue{}
  FramingHeader{}
  BodyNotAllowed{}


# ---- Counting the body in decimal ----

# One decimal digit
type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def digit_byte(d: Digit) -> U32:
  match d:
    case D0{}:
        48
    case D1{}:
        49
    case D2{}:
        50
    case D3{}:
        51
    case D4{}:
        52
    case D5{}:
        53
    case D6{}:
        54
    case D7{}:
        55
    case D8{}:
        56
    case D9{}:
        57

# Add one to a number written ones digit first: [9, 9] (99) -> [0, 0, 1] (100)
def inc(ds: List<&2, Digit>) -> List<&2, Digit>:
  match ds:
    case Nil{}:
        [D1{}]
    case Con{d, rest}:
        match d:
          case D0{}:
              Con{D1{}, rest}
          case D1{}:
              Con{D2{}, rest}
          case D2{}:
              Con{D3{}, rest}
          case D3{}:
              Con{D4{}, rest}
          case D4{}:
              Con{D5{}, rest}
          case D5{}:
              Con{D6{}, rest}
          case D6{}:
              Con{D7{}, rest}
          case D7{}:
              Con{D8{}, rest}
          case D8{}:
              Con{D9{}, rest}
          case D9{}:
              Con{D0{}, inc(rest)}

# The length of b in decimal, ones digit first. Counting up one byte at a
# time keeps the number exact for any length.
def count(b: List<&2, U32>) -> List<&2, Digit>:
  match b:
    case Nil{}:
        [D0{}]
    case Con{h, t}:
        inc(count(t))

# The digit characters, in the same order as ds
def digit_bytes(ds: List<&2, Digit>) -> List<&2, U32>:
  match ds:
    case Nil{}:
        Nil{}
    case Con{d, rest}:
        Con{digit_byte(d), digit_bytes(rest)}

# The length of b as decimal text: "1234"
def length_text(b: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, digit_bytes(count(b)))


# ---- Writing ----

# A status code and its reason phrase
type Phrase is Data:
  Phrase{code: U32, text: List<&2, U32>}

def phrases() -> List<&2, Phrase>:
  [Phrase{100, Path.bytes("Continue")},
   Phrase{101, Path.bytes("Switching Protocols")},
   Phrase{200, Path.bytes("OK")},
   Phrase{201, Path.bytes("Created")},
   Phrase{202, Path.bytes("Accepted")},
   Phrase{204, Path.bytes("No Content")},
   Phrase{206, Path.bytes("Partial Content")},
   Phrase{301, Path.bytes("Moved Permanently")},
   Phrase{302, Path.bytes("Found")},
   Phrase{303, Path.bytes("See Other")},
   Phrase{304, Path.bytes("Not Modified")},
   Phrase{307, Path.bytes("Temporary Redirect")},
   Phrase{308, Path.bytes("Permanent Redirect")},
   Phrase{400, Path.bytes("Bad Request")},
   Phrase{401, Path.bytes("Unauthorized")},
   Phrase{403, Path.bytes("Forbidden")},
   Phrase{404, Path.bytes("Not Found")},
   Phrase{405, Path.bytes("Method Not Allowed")},
   Phrase{408, Path.bytes("Request Timeout")},
   Phrase{409, Path.bytes("Conflict")},
   Phrase{410, Path.bytes("Gone")},
   Phrase{411, Path.bytes("Length Required")},
   Phrase{413, Path.bytes("Content Too Large")},
   Phrase{414, Path.bytes("URI Too Long")},
   Phrase{415, Path.bytes("Unsupported Media Type")},
   Phrase{417, Path.bytes("Expectation Failed")},
   Phrase{426, Path.bytes("Upgrade Required")},
   Phrase{429, Path.bytes("Too Many Requests")},
   Phrase{431, Path.bytes("Request Header Fields Too Large")},
   Phrase{500, Path.bytes("Internal Server Error")},
   Phrase{501, Path.bytes("Not Implemented")},
   Phrase{502, Path.bytes("Bad Gateway")},
   Phrase{503, Path.bytes("Service Unavailable")},
   Phrase{504, Path.bytes("Gateway Timeout")},
   Phrase{505, Path.bytes("HTTP Version Not Supported")}]

def reason.if(same: Bool, text: List<&2, U32>, other: List<&2, U32>) -> List<&2, U32>:
  match same:
    case True{}:
        text
    case False{}:
        other

def reason.go(tbl: List<&2, Phrase>, +s: U32) -> List<&2, U32>:
  match tbl:
    case Nil{}:
        Nil{}
    case Con{p, rest}:
        match p:
          case Phrase{c, text}:
              reason.if(U32.is_eq(c, s), text, reason.go(rest, s))

# The reason phrase for a status; empty for codes not in the table
def reason(+s: U32) -> List<&2, U32>:
  reason.go(phrases(), s)

# 1xx, 204 and 304 never carry a body, so they get no Content-Length
def has_body(+s: U32) -> Bool:
  (s >= 200 : U32) && (Bool.not(U32.is_eq(s, 204)) && Bool.not(U32.is_eq(s, 304)))

# "HTTP/1.1 404 Not Found", without its CRLF. The status is 100-599, so
# each of its three digits is 0-9, which hex_digit writes as "0"-"9".
def status_line(+s: U32) -> List<&2, U32>:
  List.append(&2, U32, Path.bytes("HTTP/1.1 "),
    Con{UrlByte.hex_digit(U32.div(s, 100)), Con{UrlByte.hex_digit(U32.mod(U32.div(s, 10), 10)),
      Con{UrlByte.hex_digit(U32.mod(s, 10)), Con{32, reason(s)}}}})

# CRLF, then "name: value", then t
def field_into(f: Req.Field, t: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Req.Field{name, value}:
        Con{13, Con{10, List.append(&2, U32, name, Con{58, Con{32, List.append(&2, U32, value, t)}})}}

def fields_into(fs: List<&2, Req.Field>, t: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
        t
    case Con{f, rest}:
        field_into(f, fields_into(rest, t))

# CRLF, then "Content-Length: n", then t; nothing for a status without a body
def length_into(has: Bool, b: List<&2, U32>, t: List<&2, U32>) -> List<&2, U32>:
  match has:
    case True{}:
        Con{13, Con{10, List.append(&2, U32, Path.bytes("Content-Length: "), List.append(&2, U32, length_text(b), t))}}
    case False{}:
        t

# The status line, the fields, Content-Length, an empty line, then t
def head_into(+s: U32, hs: List<&2, Req.Field>, b: List<&2, U32>, t: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, status_line(s),
    fields_into(hs, length_into(has_body(s), b, Con{13, Con{10, Con{13, Con{10, t}}}})))

# The bytes to send. Build r with response: the laws only cover responses
# it accepted.
def write(r: Response) -> List<&2, U32>:
  match r:
    case Response{+s, hs, +b}:
        head_into(s, hs, b, b)


# ---- Checking the parts ----

def status_ok(+s: U32) -> Bool:
  (s >= 100 : U32) && (s <= 599 : U32)

# Content-Length and Transfer-Encoding, in any case. write adds the first
# itself and never uses the second.
def is_framing(+name: List<&2, U32>) -> Bool:
  Byte.eq(Byte.lower_all(name), Path.bytes("content-length")) || Byte.eq(Byte.lower_all(name), Path.bytes("transfer-encoding"))

# A name is a token; a value is visible ASCII, space, tab or 0x80-0xFF, so
# no CR, LF or NUL
def field_ok(f: Req.Field) -> Bool:
  match f:
    case Req.Field{+name, value}:
        Byte.is_token(name) && (Fields.all_value_bytes(value) && Bool.not(is_framing(name)))

# Every field is fine
def fields_ok(fs: List<&2, Req.Field>) -> Bool:
  match fs:
    case Nil{}:
        True{}
    case Con{+f, rest}:
        field_ok(f) && fields_ok(rest)

def field_error.value(ok: Bool) -> ResponseError:
  match ok:
    case True{}:
        FramingHeader{}
    case False{}:
        InvalidHeaderValue{}

def field_error.name(ok: Bool, +value: List<&2, U32>) -> ResponseError:
  match ok:
    case True{}:
        field_error.value(Fields.all_value_bytes(value))
    case False{}:
        InvalidHeaderName{}

def field_error.at(ok: Bool, f: Req.Field, k: Unit -> ResponseError) -> ResponseError:
  match ok:
    case True{}:
        k(Unit{})
    case False{}:
        match f:
          case Req.Field{+name, +value}:
              field_error.name(Byte.is_token(name), value)

# What is wrong with the first bad field. Only called when one is bad, so
# the Nil case never happens.
def field_error(fs: List<&2, Req.Field>) -> ResponseError:
  match fs:
    case Nil{}:
        InvalidHeaderName{}
    case Con{+f, rest}:
        field_error.at(field_ok(f), f, u => field_error(rest))

def response.body(ok: Bool, +s: U32, hs: List<&2, Req.Field>, b: List<&2, U32>) -> Result<&2, &2, ResponseError, Response>:
  match ok:
    case True{}:
        Done{Response{s, hs, b}}
    case False{}:
        Fail{BodyNotAllowed{}}

def response.fields(ok: Bool, +s: U32, +hs: List<&2, Req.Field>, +b: List<&2, U32>) -> Result<&2, &2, ResponseError, Response>:
  match ok:
    case True{}:
        response.body(has_body(s) || List.is_empty(&2, U32, b), s, hs, b)
    case False{}:
        Fail{field_error(hs)}

def response.status(ok: Bool, +s: U32, +hs: List<&2, Req.Field>, +b: List<&2, U32>) -> Result<&2, &2, ResponseError, Response>:
  match ok:
    case True{}:
        response.fields(fields_ok(hs), s, hs, b)
    case False{}:
        Fail{InvalidStatus{}}

# Check the parts of a response: status 100-599, safe field names and values,
# no Content-Length or Transfer-Encoding from the caller, and no body on a
# status that can't have one
def response(+s: U32, +hs: List<&2, Req.Field>, +b: List<&2, U32>) -> Result<&2, &2, ResponseError, Response>:
  response.status(status_ok(s), s, hs, b)


# ---- What the response laws read ----

# Neither CR, LF nor NUL: any of them could end a header line early
def is_line_safe(+b: U32) -> Bool:
  Bool.not(U32.is_eq(b, 13)) && (Bool.not(U32.is_eq(b, 10)) && Bool.not(U32.is_eq(b, 0)))

def line_safe(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        is_line_safe(h) && line_safe(t)

# Law R1: every field name and value of a response is line_safe
def headers_safe(fs: List<&2, Req.Field>) -> Bool:
  match fs:
    case Nil{}:
        True{}
    case Con{f, rest}:
        match f:
          case Req.Field{name, value}:
              line_safe(name) && (line_safe(value) && headers_safe(rest))

# The fields of a response
def headers(r: Response) -> List<&2, Req.Field>:
  match r:
    case Response{s, hs, b}:
        hs

def head_end.found(m: Maybe<&2, List<&2, U32>>, +h: U32, k: Unit -> Byte.Cut) -> Byte.Cut:
  match m:
    case Some{rest}:
        Byte.Cut{[13, 10, 13, 10], rest}
    case None{}:
        Byte.cut.cons(h, k(Unit{}))

def head_end.at(cr: Bool, +h: U32, +t: List<&2, U32>, k: Unit -> Byte.Cut) -> Byte.Cut:
  match cr:
    case True{}:
        head_end.found(Byte.drop_prefix([10, 13, 10], t), h, k)
    case False{}:
        Byte.cut.cons(h, k(Unit{}))

# Law R3: cut b just after its first CRLF CRLF, where a reader stops reading
# the head
def head_end(b: List<&2, U32>) -> Byte.Cut:
  match b:
    case Nil{}:
        Byte.NoCut{}
    case Con{+h, +t}:
        head_end.at(U32.is_eq(h, 13), h, t, u => head_end(t))

def digit_value.if(same: Bool, d: Maybe<&2, Nat>, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match same:
    case True{}:
        d
    case False{}:
        other

# The value of one decimal digit byte
def digit_value(+b: U32) -> Maybe<&2, Nat>:
  digit_value.if(U32.is_eq(b, 48), Some{0n}, digit_value.if(U32.is_eq(b, 49), Some{1n},
  digit_value.if(U32.is_eq(b, 50), Some{2n}, digit_value.if(U32.is_eq(b, 51), Some{3n},
  digit_value.if(U32.is_eq(b, 52), Some{4n}, digit_value.if(U32.is_eq(b, 53), Some{5n},
  digit_value.if(U32.is_eq(b, 54), Some{6n}, digit_value.if(U32.is_eq(b, 55), Some{7n},
  digit_value.if(U32.is_eq(b, 56), Some{8n}, digit_value.if(U32.is_eq(b, 57), Some{9n}, None{}))))))))))

# n * 10, written so that times10(n + 1) is ten more than times10(n)
def times10(n: Nat) -> Nat:
  match n:
    case 0n:
        0n
    case 1n+p:
        1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+times10(p)

def ones_first.join(d: Maybe<&2, Nat>, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match d:
    case None{}:
        None{}
    case Some{x}:
        match r:
          case None{}:
              None{}
          case Some{v}:
              Some{Nat.add(x, times10(v))}

# The number written by digit bytes in ones-first order
def ones_first(b: List<&2, U32>) -> Maybe<&2, Nat>:
  match b:
    case Nil{}:
        Some{0n}
    case Con{+h, t}:
        ones_first.join(digit_value(h), ones_first(t))

def decimal.go(r: List<&2, U32>) -> Maybe<&2, Nat>:
  match r:
    case Nil{}:
        None{}
    case Con{+h, t}:
        ones_first.join(digit_value(h), ones_first(t))

# The number a decimal text stands for: "120" -> 120. None if it's empty or
# has a byte that isn't a digit.
def decimal(b: List<&2, U32>) -> Maybe<&2, Nat>:
  decimal.go(List.reverse(&2, U32, b))

def field_lines.lf(lf: Bool, +h: U32, t: List<&2, U32>, k: Unit -> List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match lf:
    case False{}:
        Con{Con{h, t}, k(Unit{})}
    case True{}:
        match t:
          case Nil{}:
              Nil{}
          case Con{+a, b}:
              Con{Con{a, b}, k(Unit{})}

# The lines of a head after the status line, from the pieces between CRs.
# A piece normally starts with the LF of its CRLF, which is dropped; a lone
# LF is the empty line that ends the head. A piece without that LF (a stray
# CR) still counts as a line, so nothing after it goes unread.
def field_lines(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
        Nil{}
    case Con{p, rest}:
        match p:
          case Nil{}:
              field_lines(rest)
          case Con{+h, t}:
              field_lines.lf(U32.is_eq(h, 10), h, t, u => field_lines(rest))

def length_values.if(cl: Bool, +v: List<&2, U32>, r: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match cl:
    case True{}:
        Con{decimal(Fields.trim(v)), r}
    case False{}:
        r

def length_values.cut(c: Byte.Cut, r: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match c:
    case Byte.NoCut{}:
        r
    case Byte.Cut{name, +v}:
        length_values.if(Byte.eq(Byte.lower_all(name), Path.bytes("content-length")), v, r)

# The number in every Content-Length line (any case), in order
def length_values(ls: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Nat>>:
  match ls:
    case Nil{}:
        Nil{}
    case Con{l, rest}:
        length_values.cut(Byte.cut(l, 58), length_values(rest))

def content_lengths.go(ps: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Nat>>:
  match ps:
    case Nil{}:
        Nil{}
    case Con{status, rest}:
        length_values(field_lines(rest))

# Law R2: the Content-Length numbers a reader finds in the head of out
def content_lengths(out: List<&2, U32>) -> List<&2, Maybe<&2, Nat>>:
  content_lengths.go(Byte.split_on(out, 13))
