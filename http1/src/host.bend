# The Host and Expect fields.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req
import ./fields.bend as Fields


# ---- Host syntax: host [":" port] (RFC 3986) ----

def reg.plain(ok: Bool, pct: Bool, r: Bool) -> Bool:
  match ok:
    case True{}:
        r
    case False{}:
        match pct:
          case True{}:
              r
          case False{}:
              False{}

def reg.next(ok: Bool, pct: Bool) -> Nat:
  match ok:
    case True{}:
        0n
    case False{}:
        match pct:
          case True{}:
              2n
          case False{}:
              0n

# k is how many hex digits must come next (2 right after "%")
def reg_name.go(b: List<&2, U32>, k: Nat) -> Bool:
  match b:
    case Nil{}:
        match k:
          case 0n:
              True{}
          case 1n+n:
              False{}
    case Con{+c, t}:
        match k:
          case 0n:
              reg.plain(UrlByte.is_unreserved(c) || UrlByte.is_sub_delim(c), U32.is_eq(c, 37),
                reg_name.go(t, reg.next(UrlByte.is_unreserved(c) || UrlByte.is_sub_delim(c), U32.is_eq(c, 37))))
          case 1n+n:
              UrlByte.is_hex(c) && reg_name.go(t, n)

# A host name or IPv4 address: unreserved, sub-delims and %XX. May be empty.
def reg_name(b: List<&2, U32>) -> Bool:
  reg_name.go(b, 0n)

def all_digits(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        UrlByte.is_digit(h) && all_digits(t)

# The value of a digit string (at most 5 digits here, so no overflow)
def digits.go(b: List<&2, U32>, +acc: U32) -> U32:
  match b:
    case Nil{}:
        acc
    case Con{+h, t}:
        digits.go(t, U32.add(U32.mul(acc, 10), U32.sub(h, 48)))

def digits(b: List<&2, U32>) -> Maybe<&2, U32>:
  Some{digits.go(b, 0)}

# 1 to 5 digits, at most 65535
def port.value(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
        False{}
    case Some{+n}:
        U32.is_le(n, 65535)

def port(+p: List<&2, U32>) -> Bool:
  Bool.not(List.is_empty(&2, U32, p)) && Nat.is_le(List.length(&2, U32, p), 5n)
  && all_digits(p) && port.value(digits(p))

def ip_char(+c: U32) -> Bool:
  UrlByte.is_hex(c) || U32.is_eq(c, 58) || U32.is_eq(c, 46)

def all_ip_chars(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        ip_char(h) && all_ip_chars(t)

# After "]": nothing, or ":" and a port
def after_bracket(a: List<&2, U32>) -> Bool:
  match a:
    case Nil{}:
        True{}
    case Con{+c, +t}:
        U32.is_eq(c, 58) && port(t)

def ip_literal(c: Byte.Cut) -> Bool:
  match c:
    case Byte.NoCut{}:
        False{}
    case Byte.Cut{+inside, +after}:
        Bool.not(List.is_empty(&2, U32, inside)) && all_ip_chars(inside) && after_bracket(after)

def reg_host(c: Byte.Cut, +v: List<&2, U32>) -> Bool:
  match c:
    case Byte.NoCut{}:
        reg_name(v)
    case Byte.Cut{+h, +p}:
        reg_name(h) && port(p)

def host_ok.start(bracket: Bool, +v: List<&2, U32>, t: List<&2, U32>) -> Bool:
  match bracket:
    case True{}:
        ip_literal(Byte.cut(t, 93))
    case False{}:
        reg_host(Byte.cut(v, 58), v)

# Is v a valid host [":" port]? A host is a name, an IPv4 address, or an IP
# literal in brackets. The bracket form is only checked loosely: hex digits,
# ":" and ".".
def host_ok(v: List<&2, U32>) -> Bool:
  match v:
    case Nil{}:
        True{}
    case Con{+c, +t}:
        host_ok.start(U32.is_eq(c, 91), Con{c, t}, t)


# ---- Host field ----

# The values of every field called n (n in lowercase; names match in any case)
def named.if(same: Bool, v: List<&2, U32>, r: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match same:
    case True{}:
        Con{v, r}
    case False{}:
        r

def named(fs: List<&2, Req.Field>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
        Nil{}
    case Con{f, rest}:
        match f:
          case Req.Field{name, value}:
              named.if(Byte.eq(Byte.lower_all(name), n), value, named(rest, n))

# With an absolute-form target, Host must name the same authority
def host.same(same: Bool) -> Result<&2, &2, Reason.Reason, Unit>:
  match same:
    case True{}:
        Done{Unit{}}
    case False{}:
        Fail{Reason.HostMismatch{}}

def host.target(t: Req.Target, +h: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Unit>:
  match t:
    case Req.Absolute{s, a, p, q}:
        host.same(Byte.eq(Byte.lower_all(a), Byte.lower_all(h)))
    case other:
        Done{Unit{}}

def host.one(list: Bool, ok: Bool, +h: List<&2, U32>, t: Req.Target) -> Result<&2, &2, Reason.Reason, Unit>:
  match list:
    case True{}:
        Fail{Reason.DuplicateHost{}}
    case False{}:
        match ok:
          case True{}:
              host.target(t, h)
          case False{}:
              Fail{Reason.InvalidHost{}}

# The Host values: HTTP/1.1 needs exactly one; HTTP/1.0 may have none.
# Two lines, or a list ("a, b"), are duplicates.
def host.check(hs: List<&2, List<&2, U32>>, v: Req.Version, t: Req.Target) -> Result<&2, &2, Reason.Reason, Unit>:
  match hs:
    case Nil{}:
        match v:
          case Req.Http11{}:
              Fail{Reason.MissingHost{}}
          case Req.Http10{}:
              Done{Unit{}}
    case Con{+h, rest}:
        match rest:
          case Nil{}:
              host.one(UrlByte.has_byte(h, 44), host_ok(h), h, t)
          case Con{x, r}:
              Fail{Reason.DuplicateHost{}}

# Exactly one Host field
def one_host.go(hs: List<&2, List<&2, U32>>) -> Bool:
  match hs:
    case Nil{}:
        False{}
    case Con{h, rest}:
        List.is_empty(&2, List<&2, U32>, rest)

def one_host(+fs: List<&2, Req.Field>) -> Bool:
  one_host.go(named(fs, Path.bytes("host")))


# ---- Expect field ----

def expect.one(is100: Bool) -> Result<&2, &2, Reason.Reason, Bool>:
  match is100:
    case True{}:
        Done{True{}}
    case False{}:
        Fail{Reason.UnsupportedExpectation{}}

# The Expect values. Only one "100-continue" (any case) is supported, and
# only HTTP/1.1 uses it; HTTP/1.0 ignores Expect. Done says whether the
# client is waiting for "100 Continue".
def expect.check(v: Req.Version, es: List<&2, List<&2, U32>>) -> Result<&2, &2, Reason.Reason, Bool>:
  match v:
    case Req.Http10{}:
        Done{False{}}
    case Req.Http11{}:
        match es:
          case Nil{}:
              Done{False{}}
          case Con{e, rest}:
              match rest:
                case Nil{}:
                    expect.one(Byte.eq(Byte.lower_all(e), Path.bytes("100-continue")))
                case Con{x, r}:
                    Fail{Reason.UnsupportedExpectation{}}

def checks.expect(r: Result<&2, &2, Reason.Reason, Unit>, v: Req.Version, +fs: List<&2, Req.Field>) -> Result<&2, &2, Reason.Reason, Bool>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{u}:
        expect.check(v, named(fs, Path.bytes("expect")))

# The Host and Expect checks. Done says whether the client is waiting for
# "100 Continue".
def checks(+v: Req.Version, t: Req.Target, +fs: List<&2, Req.Field>) -> Result<&2, &2, Reason.Reason, Bool>:
  checks.expect(host.check(named(fs, Path.bytes("host")), v, t), v, fs)
