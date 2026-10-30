# The request line: "GET /a/b?x=1 HTTP/1.1" -> method, target and version.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/src/bytes.bend as UrlByte
import ../../urlpath/src/errors.bend as PathError
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req


# ---- Query ----

def query_ok.plain(ok: Bool, pct: Bool, r: Bool) -> Bool:
  match ok:
    case True{}:
        r
    case False{}:
        match pct:
          case True{}:
              r
          case False{}:
              False{}

def query_ok.next(ok: Bool, pct: Bool) -> Nat:
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
def query_ok.go(b: List<&2, U32>, k: Nat) -> Bool:
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
              query_ok.plain(UrlByte.is_pchar(c) || U32.is_eq(c, 47) || U32.is_eq(c, 63), U32.is_eq(c, 37),
                query_ok.go(t, query_ok.next(UrlByte.is_pchar(c) || U32.is_eq(c, 47) || U32.is_eq(c, 63), U32.is_eq(c, 37))))
          case 1n+n:
              UrlByte.is_hex(c) && query_ok.go(t, n)

# A valid query (RFC 3986): pchars, "/", "?" and %XX escapes
def query_ok(b: List<&2, U32>) -> Bool:
  query_ok.go(b, 0n)


# ---- Path and query ----

type PathQuery is Data:
  PathQuery{path: List<&2, List<&2, U32>>, query: Maybe<&2, List<&2, U32>>}

# A urlpath rejection becomes InvalidPath
def path_of(r: Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>) -> Result<&2, &2, Reason.Reason, List<&2, List<&2, U32>>>:
  match r:
    case Fail{e}:
        Fail{Reason.InvalidPath{e}}
    case Done{p}:
        Done{p}

def pq.with(r: Result<&2, &2, Reason.Reason, List<&2, List<&2, U32>>>, q: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, Reason.Reason, PathQuery>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{p}:
        Done{PathQuery{p, q}}

def pq.query(ok: Bool, +p: List<&2, U32>, q: List<&2, U32>) -> Result<&2, &2, Reason.Reason, PathQuery>:
  match ok:
    case True{}:
        pq.with(path_of(Path.parse(p)), Some{q})
    case False{}:
        Fail{Reason.InvalidTarget{}}

def pq.cut(c: Byte.Cut, +t: List<&2, U32>) -> Result<&2, &2, Reason.Reason, PathQuery>:
  match c:
    case Byte.NoCut{}:
        pq.with(path_of(Path.parse(t)), None{})
    case Byte.Cut{+p, +q}:
        pq.query(query_ok(q), p, q)

# "/a/b?x" -> the decoded path [[97], [98]] and the raw query "x"
def path_query(+t: List<&2, U32>) -> Result<&2, &2, Reason.Reason, PathQuery>:
  pq.cut(Byte.cut(t, 63), t)


# ---- Target ----

def is_path_end(+b: U32) -> Bool:
  U32.is_eq(b, 47) || U32.is_eq(b, 63)

def authority.if(stop: Bool, +h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
        Nil{}
    case False{}:
        Con{h, r}

# The authority: everything before the first "/" or "?"
def authority(b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
        Nil{}
    case Con{+h, t}:
        authority.if(is_path_end(h), h, authority(t))

def after_authority.if(stop: Bool, +b: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
        b
    case False{}:
        r

# Everything from the first "/" or "?" on
def after_authority(+b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
        Nil{}
    case Con{+h, +t}:
        after_authority.if(is_path_end(h), b, after_authority(t))

def abs_path.if(q: Bool, +b: List<&2, U32>) -> List<&2, U32>:
  match q:
    case True{}:
        Con{47, b}
    case False{}:
        b

# An absolute-form path that is empty, or only a query, means "/"
def abs_path(+b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
        [47]
    case Con{+h, t}:
        abs_path.if(U32.is_eq(h, 63), b)

def absolute.done(s: Req.Scheme, a: List<&2, U32>, r: Result<&2, &2, Reason.Reason, PathQuery>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{pq}:
        match pq:
          case PathQuery{p, q}:
              Done{Req.Absolute{s, a, p, q}}

def absolute.auth(empty: Bool, s: Req.Scheme, +a: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match empty:
    case True{}:
        Fail{Reason.InvalidTarget{}}
    case False{}:
        absolute.done(s, a, path_query(abs_path(rest)))

# What follows "http://": an authority, then an optional path and query
def absolute.rest(s: Req.Scheme, +r: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  absolute.auth(List.is_empty(&2, U32, authority(r)), s, authority(r), after_authority(r))

def absolute.http(m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match m:
    case None{}:
        Fail{Reason.InvalidTarget{}}
    case Some{+r}:
        absolute.rest(Req.Http{}, r)

# "http://host/path" or "https://host/path", with the scheme in any case.
# Any other scheme, and authority-form ("host:443"), is InvalidTarget.
def absolute(m: Maybe<&2, List<&2, U32>>, +t: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match m:
    case Some{+r}:
        absolute.rest(Req.Https{}, r)
    case None{}:
        absolute.http(Byte.drop_prefix_ci(Path.bytes("http://"), t))

def origin(r: Result<&2, &2, Reason.Reason, PathQuery>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{pq}:
        match pq:
          case PathQuery{p, q}:
              Done{Req.Origin{p, q}}

def asterisk(options: Bool) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match options:
    case True{}:
        Done{Req.Asterisk{}}
    case False{}:
        Fail{Reason.InvalidTarget{}}

def target.form(star: Bool, slash: Bool, +method: List<&2, U32>, +t: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match star:
    case True{}:
        asterisk(Byte.eq(method, Path.bytes("OPTIONS")))
    case False{}:
        match slash:
          case True{}:
              origin(path_query(t))
          case False{}:
              absolute(Byte.drop_prefix_ci(Path.bytes("https://"), t), t)

# The target: "/path?query", "http://host/path?query", or "*" (OPTIONS only)
def target(+method: List<&2, U32>, t: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Target>:
  match t:
    case Nil{}:
        Fail{Reason.InvalidRequestLine{}}
    case Con{+c, +rest}:
        target.form(U32.is_eq(c, 42) && List.is_empty(&2, U32, rest), U32.is_eq(c, 47), method, Con{c, rest})


# ---- Version ----

# "d.d" after "HTTP/"
def version.digits(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
        False{}
    case Some{r}:
        match r:
          case Nil{}:
              False{}
          case Con{+a, r1}:
              match r1:
                case Nil{}:
                    False{}
                case Con{+d, r2}:
                    match r2:
                      case Nil{}:
                          False{}
                      case Con{+b, r3}:
                          List.is_empty(&2, U32, r3) && UrlByte.is_digit(a) && U32.is_eq(d, 46) && UrlByte.is_digit(b)

def version.pick(v11: Bool, v10: Bool, shape: Bool) -> Result<&2, &2, Reason.Reason, Req.Version>:
  match v11:
    case True{}:
        Done{Req.Http11{}}
    case False{}:
        match v10:
          case True{}:
              Done{Req.Http10{}}
          case False{}:
              match shape:
                case True{}:
                    Fail{Reason.VersionNotSupported{}}
                case False{}:
                    Fail{Reason.InvalidVersion{}}

# Exactly "HTTP/1.0" or "HTTP/1.1". Another "HTTP/d.d" isn't supported;
# anything else (lowercase, "HTTP/1.10") isn't a version.
def version(+v: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Version>:
  version.pick(Byte.eq(v, Path.bytes("HTTP/1.1")), Byte.eq(v, Path.bytes("HTTP/1.0")),
    version.digits(Byte.drop_prefix(Path.bytes("HTTP/"), v)))


# ---- Request line ----

def request_line.version(r: Result<&2, &2, Reason.Reason, Req.Version>, m: List<&2, U32>, t: Req.Target) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{v}:
        Done{Req.RequestLine{m, t, v}}

def request_line.target(r: Result<&2, &2, Reason.Reason, Req.Target>, m: List<&2, U32>, +v: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{t}:
        request_line.version(version(v), m, t)

# A method over 32 bytes isn't one we implement; CONNECT isn't supported
def request_line.method(short: Bool, connect: Bool, +m: List<&2, U32>, t: List<&2, U32>, +v: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match short:
    case False{}:
        Fail{Reason.MethodTooLong{}}
    case True{}:
        match connect:
          case True{}:
              Fail{Reason.MethodNotImplemented{}}
          case False{}:
              request_line.target(target(m, t), m, v)

def request_line.shape(ok: Bool, +m: List<&2, U32>, t: List<&2, U32>, +v: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match ok:
    case False{}:
        Fail{Reason.InvalidRequestLine{}}
    case True{}:
        request_line.method(Nat.is_le(List.length(&2, U32, m), 32n), Byte.eq(m, Path.bytes("CONNECT")), m, t, v)

def shape_ok.rest(+t: List<&2, U32>, v: List<&2, U32>) -> Bool:
  Bool.not(List.is_empty(&2, U32, t)) && Bool.not(Byte.starts_with(t, 32))
  && Bool.not(Byte.ends_with(t, 32)) && Bool.not(List.is_empty(&2, U32, v))

# Exactly one space between the parts: the method is a token, the target is
# non-empty with no space at either end, and there is a version
def shape_ok(m: List<&2, U32>, +t: List<&2, U32>, v: List<&2, U32>) -> Bool:
  Byte.is_token(m) && shape_ok.rest(t, v)

def request_line.second(+m: List<&2, U32>, c: Byte.Cut) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match c:
    case Byte.NoCut{}:
        Fail{Reason.InvalidRequestLine{}}
    case Byte.Cut{+t, +v}:
        request_line.shape(shape_ok(m, t, v), m, t, v)

def request_line.first(c: Byte.Cut) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  match c:
    case Byte.NoCut{}:
        Fail{Reason.InvalidRequestLine{}}
    case Byte.Cut{+m, rest}:
        request_line.second(m, Byte.cut_last(rest, 32))

# Parse a request line, without its CRLF: "GET /a?x HTTP/1.1".
# The method runs to the first space and the version starts after the last
# one, so a space inside the target is a bad target, not a fourth part.
def request_line(line: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  request_line.first(Byte.cut(line, 32))

# What every accepted method is: a token of at most 32 bytes, not CONNECT
def method_ok(+m: List<&2, U32>) -> Bool:
  Byte.is_token(m) && Nat.is_le(List.length(&2, U32, m), 32n) && Bool.not(Byte.eq(m, Path.bytes("CONNECT")))
