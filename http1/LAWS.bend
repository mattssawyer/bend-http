import Base
import ../urlpath/urlpath.bend as Path
import ../urlpath/src/errors.bend as PathError
import ./src/reason.bend as Reason
import ./src/request.bend as Req
import ./src/request_line.bend as Line


# Request line examples (the line without its CRLF)

# The simplest request
law line_root:
    {Line.request_line(Path.bytes("GET / HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# The query is kept as raw bytes
law line_query:
    {Line.request_line(Path.bytes("GET /a/b?x=1 HTTP/1.0")) == Done{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[97], [98]], Some{Path.bytes("x=1")}}, Req.Http10{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# "*" is for OPTIONS
law line_asterisk:
    {Line.request_line(Path.bytes("OPTIONS * HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("OPTIONS"), Req.Asterisk{}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# ... and only OPTIONS
law line_asterisk_get:
    {Line.request_line(Path.bytes("GET * HTTP/1.1")) == Fail{Reason.InvalidTarget{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# Absolute-form
law line_absolute:
    {Line.request_line(Path.bytes("GET http://a.example/x HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("GET"), Req.Absolute{Req.Http{}, Path.bytes("a.example"), [[120]], None{}}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# The scheme is case-insensitive, and an empty path is "/"
law line_absolute_case:
    {Line.request_line(Path.bytes("GET HTTPS://a.example HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("GET"), Req.Absolute{Req.Https{}, Path.bytes("a.example"), [[]], None{}}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A query straight after the authority
law line_absolute_query:
    {Line.request_line(Path.bytes("GET http://a?q HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("GET"), Req.Absolute{Req.Http{}, Path.bytes("a"), [[]], Some{Path.bytes("q")}}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# Only http and https
law line_other_scheme:
    {Line.request_line(Path.bytes("GET ftp://a/x HTTP/1.1")) == Fail{Reason.InvalidTarget{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# No authority
law line_empty_authority:
    {Line.request_line(Path.bytes("GET http:///x HTTP/1.1")) == Fail{Reason.InvalidTarget{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# CONNECT is not supported
law line_connect:
    {Line.request_line(Path.bytes("CONNECT a.example:443 HTTP/1.1")) == Fail{Reason.MethodNotImplemented{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# Authority-form is only for CONNECT
law line_authority_form:
    {Line.request_line(Path.bytes("GET a.example:443 HTTP/1.1")) == Fail{Reason.InvalidTarget{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# Exactly one space between parts
law line_two_spaces:
    {Line.request_line(Path.bytes("GET  / HTTP/1.1")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A tab is not a separator
law line_tab:
    {Line.request_line(Path.bytes("GET\t/ HTTP/1.1")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# No space after the version
law line_trailing_space:
    {Line.request_line(Path.bytes("GET / HTTP/1.1 ")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# No space before the method
law line_leading_space:
    {Line.request_line(Path.bytes(" GET / HTTP/1.1")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# HTTP/0.9 (no version) is not supported
law line_no_version:
    {Line.request_line(Path.bytes("GET /")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A space inside the path
law line_space_in_target:
    {Line.request_line(Path.bytes("GET /a b HTTP/1.1")) == Fail{Reason.InvalidPath{PathError.InvalidByte{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A "#" fragment in the path
law line_fragment:
    {Line.request_line(Path.bytes("GET /index.html#.png HTTP/1.1")) == Fail{Reason.InvalidPath{PathError.InvalidByte{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A space inside the query
law line_bad_query:
    {Line.request_line(Path.bytes("GET /a?x y HTTP/1.1")) == Fail{Reason.InvalidTarget{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# urlpath rejections become InvalidPath
law line_above_root:
    {Line.request_line(Path.bytes("GET /a/../.. HTTP/1.1")) == Fail{Reason.InvalidPath{PathError.AboveRoot{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# "@" is not a token character
law line_bad_method:
    {Line.request_line(Path.bytes("G@T / HTTP/1.1")) == Fail{Reason.InvalidRequestLine{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# Methods are case-sensitive: "get" is a different, unknown method
law line_lowercase_method:
    {Line.request_line(Path.bytes("get / HTTP/1.1")) == Done{Req.RequestLine{Path.bytes("get"), Req.Origin{[[]], None{}}, Req.Http11{}}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A 33-byte method
law line_long_method:
    {Line.request_line(Path.bytes("ABCDEFGHIJKLMNOPQRSTUVWXYZABCDEFG / HTTP/1.1")) == Fail{Reason.MethodTooLong{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# One digit each side of the dot
law line_version_10:
    {Line.request_line(Path.bytes("GET / HTTP/1.10")) == Fail{Reason.InvalidVersion{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# "HTTP" is case-sensitive
law line_version_lower:
    {Line.request_line(Path.bytes("GET / http/1.1")) == Fail{Reason.InvalidVersion{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# A dot instead of "/"
law line_version_dot:
    {Line.request_line(Path.bytes("GET / HTTP.1.1")) == Fail{Reason.InvalidVersion{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# HTTP/2 over this parser
law line_version_2:
    {Line.request_line(Path.bytes("GET / HTTP/2.0")) == Fail{Reason.VersionNotSupported{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}

# HTTP/1.2 is rejected, not treated as 1.1
law line_version_12:
    {Line.request_line(Path.bytes("GET / HTTP/1.2")) == Fail{Reason.VersionNotSupported{}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}


# Statuses
law status_path:
    {Reason.status(Reason.InvalidPath{PathError.AboveRoot{}}) == 400 : U32}

law status_long_method:
    {Reason.status(Reason.MethodTooLong{}) == 501 : U32}

law status_version:
    {Reason.status(Reason.VersionNotSupported{}) == 505 : U32}


# Every accepted method is a token of at most 32 bytes, and not CONNECT
law method_ok:
    for l: List<&2, U32>
    for m: List<&2, U32>
    for t: Req.Target
    for v: Req.Version
    for e: {Line.request_line(l) == Done{Req.RequestLine{m, t, v}} : Result<&2, &2, Reason.Reason, Req.RequestLine>}
    {Line.method_ok(m) == True{} : Bool}
