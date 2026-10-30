# Where the body ends. Only Content-Length and Transfer-Encoding decide this,
# never the method.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req


# How the body is framed
type Framing is Data:
  NoBody{}
  Length{n: U32}
  Chunked{}

def named.if(same: Bool, v: List<&2, U32>, r: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match same:
    case True{}:
        Con{v, r}
    case False{}:
        r

# The values of every field called n (n in lowercase; names match in any case)
def named(fs: List<&2, Req.Field>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
        Nil{}
    case Con{f, rest}:
        match f:
          case Req.Field{name, value}:
              named.if(Byte.eq(Byte.lower_all(name), n), value, named(rest, n))

# Is there a field called n?
def has_field(fs: List<&2, Req.Field>, +n: List<&2, U32>) -> Bool:
  Bool.not(List.is_empty(&2, List<&2, U32>, named(fs, n)))

# Both framing fields at once
def both_framing(+fs: List<&2, Req.Field>) -> Bool:
  has_field(fs, Path.bytes("content-length")) && has_field(fs, Path.bytes("transfer-encoding"))

def all_digits(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        UrlByte.is_digit(h) && all_digits(t)

# 1 to 10 digits, with no leading zero unless the value is "0"
def cl_valid(+v: List<&2, U32>) -> Bool:
  match v:
    case Nil{}:
        False{}
    case Con{+d, +t}:
        all_digits(v) && Nat.is_le(List.length(&2, U32, v), 10n)
        && (Bool.not(U32.is_eq(d, 48)) || List.is_empty(&2, U32, t))

def digits.step(over: Bool, k: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match over:
    case True{}:
        None{}
    case False{}:
        k(Unit{})

# The value of a digit string, or None if it's bigger than a U32 can hold
def digits.go(b: List<&2, U32>, +acc: U32) -> Maybe<&2, U32>:
  match b:
    case Nil{}:
        Some{acc}
    case Con{+h, t}:
        digits.step((acc > 429496729 : U32) || U32.is_eq(acc, 429496729) && (U32.sub(h, 48) > 5 : U32),
          u => digits.go(t, U32.add(U32.mul(acc, 10), U32.sub(h, 48))))

def digits(b: List<&2, U32>) -> Maybe<&2, U32>:
  digits.go(b, 0)

def cl.limit(ok: Bool, n: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match ok:
    case True{}:
        Done{Length{n}}
    case False{}:
        Fail{Reason.ContentTooLarge{}}

def cl.parsed(m: Maybe<&2, U32>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match m:
    case None{}:
        Fail{Reason.ContentTooLarge{}}
    case Some{+n}:
        cl.limit(U32.is_le(n, lim), n)

def cl.valid(ok: Bool, v: List<&2, U32>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match ok:
    case True{}:
        cl.parsed(digits(v), lim)
    case False{}:
        Fail{Reason.InvalidContentLength{}}

# "5, 5" is a list of values, so it counts as more than one
def cl.list(list: Bool, +v: List<&2, U32>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match list:
    case True{}:
        Fail{Reason.MultipleContentLength{}}
    case False{}:
        cl.valid(cl_valid(v), v, lim)

# The Content-Length values: none means no body; two or more lines, even
# identical ones, are rejected
def cl(vs: List<&2, List<&2, U32>>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match vs:
    case Nil{}:
        Done{NoBody{}}
    case Con{+v, rest}:
        match rest:
          case Nil{}:
              cl.list(UrlByte.has_byte(v, 44), v, lim)
          case Con{w, r}:
              Fail{Reason.MultipleContentLength{}}

# Chunked bodies aren't read yet, so any Transfer-Encoding is unsupported
def framing.te(te: Bool, v: Req.Version, vs: List<&2, List<&2, U32>>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match te:
    case True{}:
        match v:
          case Req.Http10{}:
              Fail{Reason.TransferEncodingInHttp10{}}
          case Req.Http11{}:
              Fail{Reason.UnsupportedTransferCoding{}}
    case False{}:
        cl(vs, lim)

def framing.go(both: Bool, te: Bool, v: Req.Version, vs: List<&2, List<&2, U32>>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match both:
    case True{}:
        Fail{Reason.ContentLengthWithTransferEncoding{}}
    case False{}:
        framing.te(te, v, vs, lim)

# Decide the framing from the version, the fields and the body limit
def framing(v: Req.Version, +fs: List<&2, Req.Field>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  framing.go(both_framing(fs), has_field(fs, Path.bytes("transfer-encoding")), v,
    named(fs, Path.bytes("content-length")), lim)

def cl_ok.v(m: Maybe<&2, U32>, b: List<&2, U32>) -> Bool:
  match m:
    case None{}:
        False{}
    case Some{n}:
        Nat.is_eq(List.length(&2, U32, b), U32.to_nat(n))

def cl_ok.go(vs: List<&2, List<&2, U32>>, b: List<&2, U32>) -> Bool:
  match vs:
    case Nil{}:
        True{}
    case Con{v, rest}:
        match rest:
          case Nil{}:
              cl_ok.v(digits(v), b)
          case Con{w, r}:
              False{}

# No Content-Length field, or exactly one whose value is the body's length
def content_length_ok(+fs: List<&2, Req.Field>, b: List<&2, U32>) -> Bool:
  cl_ok.go(named(fs, Path.bytes("content-length")), b)
