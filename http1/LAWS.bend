import Base
import ../urlpath/urlpath.bend as Path
import ../urlpath/src/errors.bend as PathError
import ./src/reason.bend as Reason
import ./src/request.bend as Req
import ./src/request_line.bend as Line
import ./src/limits.bend as Limits
import ./src/head.bend as Head


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


# Head examples: the request line and fields, from raw bytes

# A request line and one field; what follows the empty line is left over
law head_simple:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\n\r\nrest")) == Head.HeadParsed{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}], Path.bytes("rest")} : Head.HeadResult}

# Values are trimmed; an empty value is allowed
law head_trim:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost:  a b \t\r\nX-Y:\r\n\r\n")) == Head.HeadParsed{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}, [Req.Field{Path.bytes("Host"), Path.bytes("a b")}, Req.Field{Path.bytes("X-Y"), Path.bytes("")}], []} : Head.HeadResult}

# Bytes 0x80-0xFF in a value are kept as they are
law head_obs_text:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nA: \u{e9}\r\n\r\n")) == Head.HeadParsed{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}, [Req.Field{[65], [233]}], []} : Head.HeadResult}

# No empty line yet
law head_incomplete:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\n")) == Head.HeadNeedMore{} : Head.HeadResult}

# A CR at the end of the input may still be followed by LF
law head_half_crlf:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r")) == Head.HeadNeedMore{} : Head.HeadResult}

# One empty line before the request line is skipped
law head_leading_crlf:
    {Head.head(Limits.default_limits(), Path.bytes("\r\nGET / HTTP/1.1\r\n\r\n")) == Head.HeadParsed{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}, [], []} : Head.HeadResult}

# ... but not two
law head_two_leading_crlf:
    {Head.head(Limits.default_limits(), Path.bytes("\r\n\r\nGET / HTTP/1.1\r\n\r\n")) == Head.HeadRejected{Reason.InvalidRequestLine{}} : Head.HeadResult}

# Lines must end with CRLF, not LF alone
law head_bare_lf:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\nHost: a\n\n")) == Head.HeadRejected{Reason.BareLF{}} : Head.HeadResult}

# A CR without LF
law head_bare_cr:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nA: b\rContent-Length: 10\r\n")) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}

# The head must end with CRLF CRLF
law head_bad_end:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\n\rX")) == Head.HeadRejected{Reason.BareCR{}} : Head.HeadResult}

# An element above 255
law head_not_a_byte:
    {Head.head(Limits.default_limits(), [71, 300]) == Head.HeadRejected{Reason.NotAByte{}} : Head.HeadResult}

# NUL in a value
law head_nul:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nA: x\u{0}y\r\n\r\n")) == Head.HeadRejected{Reason.InvalidFieldValue{}} : Head.HeadResult}

# DEL in a value
law head_del:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nA: x\u{7f}\r\n\r\n")) == Head.HeadRejected{Reason.InvalidFieldValue{}} : Head.HeadResult}

# Space before the colon (the classic TE.TE trick)
law head_space_before_colon:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nTransfer-Encoding : chunked\r\n\r\n")) == Head.HeadRejected{Reason.WhitespaceBeforeColon{}} : Head.HeadResult}

# Tab before the colon
law head_tab_before_colon:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nContent-Length\t: 5\r\n\r\n")) == Head.HeadRejected{Reason.WhitespaceBeforeColon{}} : Head.HeadResult}

# Whitespace before the first field
law head_space_first:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\n Transfer-Encoding: chunked\r\n\r\n")) == Head.HeadRejected{Reason.WhitespaceBeforeFirstField{}} : Head.HeadResult}

# A folded line
law head_obs_fold:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nX: a\r\n b\r\n\r\n")) == Head.HeadRejected{Reason.ObsFold{}} : Head.HeadResult}

# A field line with no colon
law head_no_colon:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nFoo\r\n\r\n")) == Head.HeadRejected{Reason.InvalidFieldLine{}} : Head.HeadResult}

# An empty name
law head_empty_name:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\n: x\r\n\r\n")) == Head.HeadRejected{Reason.InvalidFieldName{}} : Head.HeadResult}

# A control byte in the name
law head_control_name:
    {Head.head(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\n\u{b}Transfer-Encoding: chunked\r\n\r\n")) == Head.HeadRejected{Reason.InvalidFieldName{}} : Head.HeadResult}

# A bad request line is rejected before the fields arrive
law head_bad_request_line:
    {Head.head(Limits.default_limits(), Path.bytes("GET  / HTTP/1.1\r\n")) == Head.HeadRejected{Reason.InvalidRequestLine{}} : Head.HeadResult}

# With small limits: a request line over 20 bytes, rejected before its CRLF
law head_long_line:
    {Head.head(Limits.Limits{20, 12, 40, 2, 100, 10}, Path.bytes("GET /aaaaaaaaaaaaaaaaaaaaaa")) == Head.HeadRejected{Reason.TargetTooLong{}} : Head.HeadResult}

# A field line over 12 bytes
law head_long_field:
    {Head.head(Limits.Limits{20, 12, 40, 2, 100, 10}, Path.bytes("GET / HTTP/1.1\r\nAAAAAAAAAAAAA")) == Head.HeadRejected{Reason.HeaderTooLarge{}} : Head.HeadResult}

# A third field when 2 are allowed
law head_many_fields:
    {Head.head(Limits.Limits{20, 12, 40, 2, 100, 10}, Path.bytes("GET / HTTP/1.1\r\nA: 1\r\nB: 2\r\nC")) == Head.HeadRejected{Reason.TooManyFields{}} : Head.HeadResult}

# Exactly 2 fields is fine
law head_max_fields:
    {Head.head(Limits.Limits{20, 12, 40, 2, 100, 10}, Path.bytes("GET / HTTP/1.1\r\nA: 1\r\nB: 2\r\n\r\n")) == Head.HeadParsed{Req.RequestLine{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}}, [Req.Field{Path.bytes("A"), Path.bytes("1")}, Req.Field{Path.bytes("B"), Path.bytes("2")}], []} : Head.HeadResult}

# The whole head over 40 bytes
law head_section:
    {Head.head(Limits.Limits{20, 12, 40, 2, 100, 10}, Path.bytes("GET / HTTP/1.1\r\nAAAA: 12345\r\nBBBB: 1234")) == Head.HeadRejected{Reason.HeaderTooLarge{}} : Head.HeadResult}
