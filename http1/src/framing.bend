# Where the body ends. Only Content-Length and Transfer-Encoding decide this,
# never the method.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req
import ./fields.bend as Fields


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

def trim_all(ms: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
        Nil{}
    case Con{m, rest}:
        Con{Fields.trim(m), trim_all(rest)}

# Any empty member, or any member with parameters (";")
def te.bad(ms: List<&2, List<&2, U32>>) -> Bool:
  match ms:
    case Nil{}:
        False{}
    case Con{+m, rest}:
        List.is_empty(&2, U32, m) || UrlByte.has_byte(m, 59) || te.bad(rest)

def is_chunked(m: List<&2, U32>) -> Bool:
  Byte.eq(Byte.lower_all(m), Path.bytes("chunked"))

def te.count.if(c: Bool, n: Nat) -> Nat:
  match c:
    case True{}:
        1n+n
    case False{}:
        n

def count_chunked(ms: List<&2, List<&2, U32>>) -> Nat:
  match ms:
    case Nil{}:
        0n
    case Con{+m, rest}:
        te.count.if(is_chunked(m), count_chunked(rest))

def te.last.if(last: Bool, here: Bool, r: Bool) -> Bool:
  match last:
    case True{}:
        here
    case False{}:
        r

def last_is_chunked(ms: List<&2, List<&2, U32>>) -> Bool:
  match ms:
    case Nil{}:
        False{}
    case Con{+m, +rest}:
        te.last.if(List.is_empty(&2, List<&2, U32>, rest), is_chunked(m), last_is_chunked(rest))

def te.final(last: Bool, one: Bool, any: Bool, identity: Bool) -> Result<&2, &2, Reason.Reason, Framing>:
  match last:
    case True{}:
        match one:
          case True{}:
              Done{Chunked{}}
          case False{}:
              Fail{Reason.UnsupportedTransferCoding{}}
    case False{}:
        match any:
          case True{}:
              Fail{Reason.ChunkedNotFinal{}}
          case False{}:
              match identity:
                case True{}:
                    Fail{Reason.UnsupportedTransferCoding{}}
                case False{}:
                    Fail{Reason.ChunkedNotFinal{}}

def te.members(bad: Bool, twice: Bool, +ms: List<&2, List<&2, U32>>) -> Result<&2, &2, Reason.Reason, Framing>:
  match bad:
    case True{}:
        Fail{Reason.InvalidTransferEncoding{}}
    case False{}:
        match twice:
          case True{}:
              Fail{Reason.ChunkedAppliedTwice{}}
          case False{}:
              te.final(last_is_chunked(ms), Nat.is_eq(List.length(&2, List<&2, U32>, ms), 1n),
                Nat.is_eq(count_chunked(ms), 1n),
                Byte.eq(Byte.lower_all(List.concat(&2, U32, ms)), Path.bytes("identity")) && Nat.is_eq(List.length(&2, List<&2, U32>, ms), 1n))

# One Transfer-Encoding value. The only one accepted is "chunked", alone.
# "gzip, chunked" and "identity" are codings we don't support; chunked must
# come last and only once; empty members and parameters are invalid.
def te.value(+v: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Framing>:
  te.members(te.bad(trim_all(Byte.split_on(v, 44))), Nat.is_le(2n, count_chunked(trim_all(Byte.split_on(v, 44)))),
    trim_all(Byte.split_on(v, 44)))

# The Transfer-Encoding values: two lines count as applying chunked twice
def te(vs: List<&2, List<&2, U32>>) -> Result<&2, &2, Reason.Reason, Framing>:
  match vs:
    case Nil{}:
        Fail{Reason.InvalidTransferEncoding{}}
    case Con{+v, rest}:
        match rest:
          case Nil{}:
              te.value(v)
          case Con{w, r}:
              Fail{Reason.ChunkedAppliedTwice{}}

def framing.te(te_present: Bool, v: Req.Version, vs: List<&2, List<&2, U32>>, tes: List<&2, List<&2, U32>>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match te_present:
    case True{}:
        match v:
          case Req.Http10{}:
              Fail{Reason.TransferEncodingInHttp10{}}
          case Req.Http11{}:
              te(tes)
    case False{}:
        cl(vs, lim)

def framing.go(both: Bool, te_present: Bool, v: Req.Version, vs: List<&2, List<&2, U32>>, tes: List<&2, List<&2, U32>>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  match both:
    case True{}:
        Fail{Reason.ContentLengthWithTransferEncoding{}}
    case False{}:
        framing.te(te_present, v, vs, tes, lim)

# Decide the framing from the version, the fields and the body limit
def framing(v: Req.Version, +fs: List<&2, Req.Field>, +lim: U32) -> Result<&2, &2, Reason.Reason, Framing>:
  framing.go(both_framing(fs), has_field(fs, Path.bytes("transfer-encoding")), v,
    named(fs, Path.bytes("content-length")), named(fs, Path.bytes("transfer-encoding")), lim)

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
