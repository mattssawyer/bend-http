import Base
import ../urlpath/urlpath.bend as Path
import ../urlpath/src/errors.bend as PathError
import ./src/reason.bend as Reason
import ./src/request.bend as Req
import ./src/request_line.bend as Line
import ./src/limits.bend as Limits
import ./src/head.bend as Head
import ./src/framing.bend as Framing
import ./src/parse.bend as Parse
import ./src/host.bend as Host
import ./src/lines.bend as Lines
import ./src/response.bend as Resp
import ./src/bytes.bend as Byte


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


# Whole requests: framing with Content-Length

# The body is exactly Content-Length bytes; the rest is the next request
law parse_cl:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n\r\nhelloGET")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Content-Length"), Path.bytes("5")}], Path.bytes("hello")}, Path.bytes("GET")} : Parse.Outcome}

# Fewer body bytes than declared: wait for more
law parse_cl_short:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n\r\nhel")) == Parse.NeedMore{False{}} : Parse.Outcome}

# No framing fields: an empty body, whatever the method
law parse_no_framing:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\n\r\nGET")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}], []}, Path.bytes("GET")} : Parse.Outcome}

# Content-Length: 0
law parse_cl_zero:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 0\r\n\r\nX")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Content-Length"), Path.bytes("0")}], []}, Path.bytes("X")} : Parse.Outcome}

# Field names match in any case, and a GET can have a body
law parse_cl_any_case:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\nCONTENT-LENGTH: 2\r\n\r\nab")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("CONTENT-LENGTH"), Path.bytes("2")}], Path.bytes("ab")}, []} : Parse.Outcome}

# Both framing fields (CL.TE / TE.CL smuggling)
law parse_cl_te:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n")) == Parse.Rejected{Reason.ContentLengthWithTransferEncoding{}} : Parse.Outcome}

# Transfer-Encoding in HTTP/1.0
law parse_te_http10:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n")) == Parse.Rejected{Reason.TransferEncodingInHttp10{}} : Parse.Outcome}

# Two Content-Length lines, even identical
law parse_two_cl:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\ncontent-length: 5\r\n\r\nhello")) == Parse.Rejected{Reason.MultipleContentLength{}} : Parse.Outcome}

# A list of values
law parse_cl_list:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5, 5\r\n\r\nhello")) == Parse.Rejected{Reason.MultipleContentLength{}} : Parse.Outcome}

# An empty value
law parse_cl_empty:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: \r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# A sign
law parse_cl_plus:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: +5\r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# Hex
law parse_cl_hex:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 0x10\r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# A space inside the value
law parse_cl_space:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5 5\r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# A leading zero (some servers read 0200 as octal)
law parse_cl_leading_zero:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 0200\r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# More than 10 digits
law parse_cl_eleven_digits:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 99999999999\r\n\r\n")) == Parse.Rejected{Reason.InvalidContentLength{}} : Parse.Outcome}

# Too big for a U32
law parse_cl_overflow:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 4294967296\r\n\r\n")) == Parse.Rejected{Reason.ContentTooLarge{}} : Parse.Outcome}

# Over the body limit
law parse_cl_too_large:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 2000000\r\n\r\n")) == Parse.Rejected{Reason.ContentTooLarge{}} : Parse.Outcome}


# Chunked bodies

# One chunk, then the last chunk; what follows is the next request
law chunked_simple:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nGET")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, Path.bytes("GET")} : Parse.Outcome}

# A huge extension limit can't wrap the size-line budget round to zero
law chunked_huge_ext_limit:
    {Parse.parse(Limits.Limits{8192, 8192, 65536, 100, 1048576, 4294967264}, Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], []}, []} : Parse.Outcome}

# The chunks are joined
law chunked_two:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhe\r\n3\r\nllo\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, []} : Parse.Outcome}

# Part of a chunk: wait for more
law chunked_partial_data:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel")) == Parse.NeedMore{False{}} : Parse.Outcome}

# Half of the CRLF after the data
law chunked_partial_crlf:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r")) == Parse.NeedMore{False{}} : Parse.Outcome}

# No last chunk yet
law chunked_no_last:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n")) == Parse.NeedMore{False{}} : Parse.Outcome}

# Trailers are checked, then dropped
law chunked_trailer:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX-T: 1\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, []} : Parse.Outcome}

# Leading zeros are fine, also in the last chunk
law chunked_leading_zeros:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0005\r\nhello\r\n000\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, []} : Parse.Outcome}

# Sizes are hex, either case
law chunked_hex:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\nA\r\n0123456789\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("0123456789")}, []} : Parse.Outcome}

# "0x" is not part of the size
law chunked_0x:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0x5\r\nhello\r\n0\r\n\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# A sign
law chunked_plus:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n+5\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# A space before the size
law chunked_space_before:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n\u{20}5\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# A space after the size
law chunked_space_after:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5 \r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# No size
law chunked_empty_size:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# More than 8 significant hex digits
law chunked_overflow:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\nffffffffffffffff0000000000000005\r\n")) == Parse.Rejected{Reason.InvalidChunkSize{}} : Parse.Outcome}

# A chunk over the body limit
law chunked_too_large:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n200000\r\n")) == Parse.Rejected{Reason.ContentTooLarge{}} : Parse.Outcome}

# A bare LF in a size line
law chunked_bare_lf_ext:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n2;\nxx\r\n")) == Parse.Rejected{Reason.BareLF{}} : Parse.Outcome}

# A bare CR in a size line
law chunked_bare_cr:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n2\r\r;a")) == Parse.Rejected{Reason.BareCR{}} : Parse.Outcome}

# A size line ended by LF alone
law chunked_lf_size:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n2\nxx\r\n")) == Parse.Rejected{Reason.BareLF{}} : Parse.Outcome}

# Extensions, with a quoted value, are parsed and dropped
law chunked_ext_ok:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=b;c=\"q\\\"x\"\r\nhello\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, []} : Parse.Outcome}

# Spaces after ";" and around "=" are allowed
law chunked_ext_spaces:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5; a = b\r\nhello\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], Path.bytes("hello")}, []} : Parse.Outcome}

# An empty extension
law chunked_ext_empty:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkExtension{}} : Parse.Outcome}

# An extension with no name
law chunked_ext_no_name:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;=x\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkExtension{}} : Parse.Outcome}

# An unterminated quoted value
law chunked_ext_unterminated:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=\"x\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkExtension{}} : Parse.Outcome}

# A space inside a token value
law chunked_ext_space_value:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=b c\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkExtension{}} : Parse.Outcome}

# A space before ";"
law chunked_ext_space_before:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5 ;a\r\nhello\r\n")) == Parse.Rejected{Reason.InvalidChunkExtension{}} : Parse.Outcome}

# More data than the size
law chunked_spill:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nAAAAAXX\r\n")) == Parse.Rejected{Reason.MissingChunkDataCRLF{}} : Parse.Outcome}

# A CR after the data, but not CRLF
law chunked_spill_cr:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nAAAAA\rX2\r\n")) == Parse.Rejected{Reason.MissingChunkDataCRLF{}} : Parse.Outcome}

# Trailers go through the header field checks
law chunked_bad_trailer:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n bad\r\n\r\n")) == Parse.Rejected{Reason.ObsFold{}} : Parse.Outcome}


# Transfer-Encoding values

# "chunked" in any case
law te_upper:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: CHUNKED\r\n\r\n0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("CHUNKED")}], []}, []} : Parse.Outcome}

# Other codings before chunked
law te_gzip_chunked:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip, chunked\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.UnsupportedTransferCoding{}} : Parse.Outcome}

# "identity"
law te_identity:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: identity\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.UnsupportedTransferCoding{}} : Parse.Outcome}

# chunked must come last
law te_not_final:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, gzip\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.ChunkedNotFinal{}} : Parse.Outcome}

# An unknown coding
law te_unknown:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: x\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.ChunkedNotFinal{}} : Parse.Outcome}

# Not quite "chunked"
law te_obfuscated:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: xchunked\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.ChunkedNotFinal{}} : Parse.Outcome}

# chunked twice
law te_twice:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, chunked\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.ChunkedAppliedTwice{}} : Parse.Outcome}

# Parameters on chunked
law te_params:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked;a=b\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.InvalidTransferEncoding{}} : Parse.Outcome}

# An empty value
law te_empty:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: \r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.InvalidTransferEncoding{}} : Parse.Outcome}

# An empty list member (stricter than the RFC)
law te_leading_comma:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: ,chunked\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.InvalidTransferEncoding{}} : Parse.Outcome}

# An empty list member at the end
law te_trailing_comma:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked,\r\n\r\n0\r\n\r\n")) == Parse.Rejected{Reason.InvalidTransferEncoding{}} : Parse.Outcome}

# Two Transfer-Encoding lines
law te_two_lines:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n")) == Parse.Rejected{Reason.ChunkedAppliedTwice{}} : Parse.Outcome}

# Host and Expect

# One Host
law host_ok:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}], []}, []} : Parse.Outcome}

# HTTP/1.1 needs a Host
law host_missing:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\n\r\n")) == Parse.Rejected{Reason.MissingHost{}} : Parse.Outcome}

# HTTP/1.0 doesn't
law host_http10:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.0\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http10{}, [], []}, []} : Parse.Outcome}

# Two Host lines
law host_two:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n")) == Parse.Rejected{Reason.DuplicateHost{}} : Parse.Outcome}

# A list of hosts
law host_list:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a, b\r\n\r\n")) == Parse.Rejected{Reason.DuplicateHost{}} : Parse.Outcome}

# A "/" in the host
law host_slash:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a/b\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# "user@"
law host_userinfo:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: user@a\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# Two colons
law host_two_colons:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a:b:c\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# A port over 65535
law host_big_port:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a:99999\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# Port 65535
law host_max_port:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a:65535\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a:65535")}], []}, []} : Parse.Outcome}

# A space in the host
law host_space:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: a b\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# An empty Host is allowed
law host_empty:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost:\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("")}], []}, []} : Parse.Outcome}

# An IP literal in brackets
law host_ipv6:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: [::1]:80\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("[::1]:80")}], []}, []} : Parse.Outcome}

# Not an IP literal
law host_bad_ipv6:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: [zz]\r\n\r\n")) == Parse.Rejected{Reason.InvalidHost{}} : Parse.Outcome}

# An IPv4 address and port
law host_ipv4:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET / HTTP/1.1\r\nHost: 127.0.0.1:8080\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("127.0.0.1:8080")}], []}, []} : Parse.Outcome}

# Absolute-form with a matching Host (any case)
law host_absolute:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET http://a.example/x HTTP/1.1\r\nHost: A.EXAMPLE\r\n\r\n")) == Parse.Parsed{Req.Request{Path.bytes("GET"), Req.Absolute{Req.Http{}, Path.bytes("a.example"), [[120]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("A.EXAMPLE")}], []}, []} : Parse.Outcome}

# Absolute-form with a different Host
law host_mismatch:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET http://a.example/x HTTP/1.1\r\nHost: b.example\r\n\r\n")) == Parse.Rejected{Reason.HostMismatch{}} : Parse.Outcome}

# "user@" in an absolute-form target
law host_absolute_userinfo:
    {Parse.parse(Limits.default_limits(), Path.bytes("GET http://user@a/x HTTP/1.1\r\nHost: a\r\n\r\n")) == Parse.Rejected{Reason.InvalidTarget{}} : Parse.Outcome}

# 100-continue with the body missing: the caller should send "100 Continue"
law expect_waiting:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\n")) == Parse.NeedMore{True{}} : Parse.Outcome}

# ... also with a chunked body
law expect_chunked:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhe")) == Parse.NeedMore{True{}} : Parse.Outcome}

# Once the body is here, it's parsed as usual
law expect_body_here:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-Continue\r\nContent-Length: 2\r\n\r\nhi")) == Parse.Parsed{Req.Request{Path.bytes("POST"), Req.Origin{[[]], None{}}, Req.Http11{}, [Req.Field{Path.bytes("Host"), Path.bytes("a")}, Req.Field{Path.bytes("Expect"), Path.bytes("100-Continue")}, Req.Field{Path.bytes("Content-Length"), Path.bytes("2")}], Path.bytes("hi")}, []} : Parse.Outcome}

# Any other expectation
law expect_other:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nExpect: y 100-continue\r\nContent-Length: 5\r\n\r\n")) == Parse.Rejected{Reason.UnsupportedExpectation{}} : Parse.Outcome}

# HTTP/1.0 ignores Expect
law expect_http10:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.0\r\nExpect: foo\r\nContent-Length: 5\r\n\r\n")) == Parse.NeedMore{False{}} : Parse.Outcome}

# Without Expect, nobody is waiting for "100 Continue"
law need_more_plain:
    {Parse.parse(Limits.default_limits(), Path.bytes("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n\r\n")) == Parse.NeedMore{False{}} : Parse.Outcome}

# H1: after Parsed, the leftover is the end of the input
law leftover_is_suffix:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for r: Req.Request
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{r, rest} : Parse.Outcome}
    exs used: List<&2, U32>
    {i == List.append(&2, U32, used, rest) : List<&2, U32>}

# H4: a request with both Content-Length and Transfer-Encoding is never Parsed
law cl_and_te_rejected:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for m: List<&2, U32>
    for t: Req.Target
    for v: Req.Version
    for hs: List<&2, Req.Field>
    for body: List<&2, U32>
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{Req.Request{m, t, v, hs, body}, rest} : Parse.Outcome}
    {Framing.both_framing(hs) == False{} : Bool}

# H5: a Parsed request has no Content-Length, or exactly one that is the body's length
law one_content_length:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for m: List<&2, U32>
    for t: Req.Target
    for v: Req.Version
    for hs: List<&2, Req.Field>
    for body: List<&2, U32>
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{Req.Request{m, t, v, hs, body}, rest} : Parse.Outcome}
    {Framing.content_length_ok(hs, body) == True{} : Bool}

# H6: an HTTP/1.1 request that is Parsed has exactly one Host field
law http11_has_one_host:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for m: List<&2, U32>
    for t: Req.Target
    for hs: List<&2, Req.Field>
    for body: List<&2, U32>
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{Req.Request{m, t, Req.Http11{}, hs, body}, rest} : Parse.Outcome}
    {Host.one_host(hs) == True{} : Bool}

# H8: the path of a Parsed request is one that urlpath's parse returned, so
# urlpath's laws (no "." or "..", no unsafe bytes, ...) hold for it
law origin_path_from_urlpath:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for m: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for q: Maybe<&2, List<&2, U32>>
    for v: Req.Version
    for hs: List<&2, Req.Field>
    for body: List<&2, U32>
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{Req.Request{m, Req.Origin{p, q}, v, hs, body}, rest} : Parse.Outcome}
    exs raw: List<&2, U32>
    {Path.parse(raw) == Done{p} : Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>}

law absolute_path_from_urlpath:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for m: List<&2, U32>
    for s: Req.Scheme
    for a: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for q: Maybe<&2, List<&2, U32>>
    for v: Req.Version
    for hs: List<&2, Req.Field>
    for body: List<&2, U32>
    for rest: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{Req.Request{m, Req.Absolute{s, a, p, q}, v, hs, body}, rest} : Parse.Outcome}
    exs raw: List<&2, U32>
    {Path.parse(raw) == Done{p} : Result<&2, &2, PathError.PathError, List<&2, List<&2, U32>>>}

# H2: once a request is Parsed, more input only adds to the leftover
law more_input_keeps_parsed:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for r: Req.Request
    for rest: List<&2, U32>
    for +more: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Parsed{r, rest} : Parse.Outcome}
    {Parse.parse(l, List.append(&2, U32, i, more)) == Parse.Parsed{r, List.append(&2, U32, rest, more)} : Parse.Outcome}

# H3: once a request is Rejected, more input can't change that
law more_input_keeps_rejected:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for x: Reason.Reason
    for +more: List<&2, U32>
    for e: {Parse.parse(l, i) == Parse.Rejected{x} : Parse.Outcome}
    {Parse.parse(l, List.append(&2, U32, i, more)) == Parse.Rejected{x} : Parse.Outcome}

# H7: the head of a request is clean: every CR is followed by LF, and every
# LF has a CR before it. used is the head: the bytes before rest.
law no_bare_cr_lf_in_head:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for rl: Req.RequestLine
    for fs: List<&2, Req.Field>
    for rest: List<&2, U32>
    for e: {Head.head(l, i) == Head.HeadParsed{rl, fs, rest} : Head.HeadResult}
    exs used: List<&2, U32>
    {i == List.append(&2, U32, used, rest) : List<&2, U32>} & {Lines.crlf_clean(used) == True{} : Bool}

# H10: given the same head except for the method, parse ends the request in
# the same place with the same outcome; only the method in it differs
law framing_ignores_method:
    for +l: Limits.Limits
    for +m1: List<&2, U32>
    for +m2: List<&2, U32>
    for +t: Req.Target
    for +v: Req.Version
    for +fs: List<&2, Req.Field>
    for +rest: List<&2, U32>
    {Parse.parse.head(Head.HeadParsed{Req.RequestLine{m1, t, v}, fs, rest}, l) == Parse.with_method(Parse.parse.head(Head.HeadParsed{Req.RequestLine{m2, t, v}, fs, rest}, l), m1) : Parse.Outcome}

# H9: the parser never waits forever. With more input than the largest
# request the limits allow (Parse.max_request), the answer is never NeedMore.
law bounded:
    for +l: Limits.Limits
    for +i: List<&2, U32>
    for hl: {Nat.is_lt(Parse.max_request(l), List.length(&2, U32, i)) == True{} : Bool}
    {Parse.is_need_more(Parse.parse(l, i)) == False{} : Bool}


# ---- Response examples ----

# A plain 200 gets its reason phrase and a Content-Length
law write_ok:
    {Resp.write(Resp.Response{200, [], Path.bytes("hi")}) == Path.bytes("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi") : List<&2, U32>}

# Fields go out in the caller's order, before Content-Length
law write_fields:
    {Resp.write(Resp.Response{404, [Req.Field{Path.bytes("Content-Type"), Path.bytes("text/plain")}, Req.Field{Path.bytes("X-A"), Path.bytes("1")}], Path.bytes("no")}) == Path.bytes("HTTP/1.1 404 Not Found\r\nContent-Type: text/plain\r\nX-A: 1\r\nContent-Length: 2\r\n\r\nno") : List<&2, U32>}

# 204 has no body, so no Content-Length
law write_no_content:
    {Resp.write(Resp.Response{204, [], []}) == Path.bytes("HTTP/1.1 204 No Content\r\n\r\n") : List<&2, U32>}

# A code with no phrase in the table gets an empty one
law write_unknown_code:
    {Resp.write(Resp.Response{599, [], []}) == Path.bytes("HTTP/1.1 599 \r\nContent-Length: 0\r\n\r\n") : List<&2, U32>}

# Ten bytes: the count carries into a second digit
law write_length_ten:
    {Resp.write(Resp.Response{200, [], Path.bytes("0123456789")}) == Path.bytes("HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n0123456789") : List<&2, U32>}

# 100 Continue, the interim answer to "Expect: 100-continue"
law write_continue:
    {Resp.write(Resp.Response{100, [], []}) == Path.bytes("HTTP/1.1 100 Continue\r\n\r\n") : List<&2, U32>}

# Good parts make a response
law response_ok:
    {Resp.response(200, [Req.Field{Path.bytes("X-A"), Path.bytes("1")}], Path.bytes("hi")) == Done{Resp.Response{200, [Req.Field{Path.bytes("X-A"), Path.bytes("1")}], Path.bytes("hi")}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# Status codes are 100-599
law response_status_low:
    {Resp.response(99, [], []) == Fail{Resp.InvalidStatus{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# ...
law response_status_high:
    {Resp.response(600, [], []) == Fail{Resp.InvalidStatus{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# A field name is a token: no spaces
law response_name_space:
    {Resp.response(200, [Req.Field{Path.bytes("X A"), Path.bytes("1")}], []) == Fail{Resp.InvalidHeaderName{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# ... and not empty
law response_name_empty:
    {Resp.response(200, [Req.Field{[], Path.bytes("1")}], []) == Fail{Resp.InvalidHeaderName{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# A CRLF in a value would start a new field (response splitting)
law response_value_crlf:
    {Resp.response(200, [Req.Field{Path.bytes("X-A"), Path.bytes("1\r\nSet-Cookie: x")}], []) == Fail{Resp.InvalidHeaderValue{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# NUL is refused too
law response_value_nul:
    {Resp.response(200, [Req.Field{Path.bytes("X-A"), [49, 0]}], []) == Fail{Resp.InvalidHeaderValue{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# write adds Content-Length itself, so the caller may not, in any case
law response_own_length:
    {Resp.response(200, [Req.Field{Path.bytes("content-LENGTH"), Path.bytes("5")}], []) == Fail{Resp.FramingHeader{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# ... nor Transfer-Encoding
law response_own_te:
    {Resp.response(200, [Req.Field{Path.bytes("Transfer-Encoding"), Path.bytes("chunked")}], []) == Fail{Resp.FramingHeader{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# 204 can't carry a body: the client would read it as the next response
law response_body_204:
    {Resp.response(204, [], Path.bytes("x")) == Fail{Resp.BodyNotAllowed{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# ... nor can 304
law response_body_304:
    {Resp.response(304, [], Path.bytes("x")) == Fail{Resp.BodyNotAllowed{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}


# 205 (Reset Content) can't carry content either...
law response_body_205:
    {Resp.response(205, [], Path.bytes("x")) == Fail{Resp.BodyNotAllowed{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# ... but unlike 204 it says so with Content-Length: 0
law write_reset_content:
    {Resp.write(Resp.Response{205, [], []}) == Path.bytes("HTTP/1.1 205 Reset Content\r\nContent-Length: 0\r\n\r\n") : List<&2, U32>}

# The body must be bytes
law response_not_a_byte:
    {Resp.response(200, [], [104, 256]) == Fail{Resp.NotAByte{}} : Result<&2, &2, Resp.ResponseError, Resp.Response>}

# The answer to HEAD: the head a GET gets, with its Content-Length, and no body
law write_head_ok:
    {Resp.write_head(Resp.Response{200, [], Path.bytes("hello")}) == Path.bytes("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n") : List<&2, U32>}

# ---- Response readers: what the laws look at ----

law reader_lengths:
    {Resp.content_lengths(Path.bytes("HTTP/1.1 200 OK\r\nA: 1\r\ncontent-length:  120 \r\nContent-Length: x\r\n\r\nContent-Length: 9")) == [Some{120n}, None{}] : List<&2, Maybe<&2, Nat>>}

law reader_head_end:
    {Resp.head_end(Path.bytes("HTTP/1.1 200 OK\r\nA: 1\r\n\r\nB\r\n\r\n")) == Byte.Cut{Path.bytes("HTTP/1.1 200 OK\r\nA: 1\r\n\r\n"), Path.bytes("B\r\n\r\n")} : Byte.Cut}

law reader_line_safe:
    {Resp.headers_safe([Req.Field{Path.bytes("A"), Path.bytes("x\ry")}]) == False{} : Bool}


# A stray CR doesn't hide the lines after it from the reader
law reader_stray_cr:
    {Resp.content_lengths(Path.bytes("HTTP/1.1 200 OK\r\nA: 1\rContent-Length: 7\r\n\r\n")) == [Some{7n}] : List<&2, Maybe<&2, Nat>>}


# ---- Response laws ----

# R1: a response that response built has no CR, LF or NUL in any field
# name or value, so no field can end its line early and start another
law response_values_safe:
    for +s: U32
    for +hs: List<&2, Req.Field>
    for +b: List<&2, U32>
    for +r: Resp.Response
    for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
    {Resp.headers_safe(Resp.headers(r)) == True{} : Bool}

# R2: with a status that has a body, a reader finds exactly one
# Content-Length in what write sends, and its number is the body's length
law write_one_length:
    for +s: U32
    for +hs: List<&2, Req.Field>
    for +b: List<&2, U32>
    for +r: Resp.Response
    for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
    for hb: {Resp.has_length(s) == True{} : Bool}
    {Resp.content_lengths(Resp.write(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}

# R3: what write sends is write_head's bytes, then the body, and the head
# ends at the first CRLF CRLF, so no part of the body can be read as a
# header. A HEAD answer is the same head, without the body.
law write_splits:
    for +s: U32
    for +hs: List<&2, Req.Field>
    for +b: List<&2, U32>
    for +r: Resp.Response
    for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
    {Resp.head_end(Resp.write(r)) == Byte.Cut{Resp.write_head(r), b} : Byte.Cut} & {Resp.write(r) == List.append(&2, U32, Resp.write_head(r), b) : List<&2, U32>}

# R2 for write_head: the HEAD answer has the one Content-Length a GET would
# get, the body's length
law write_head_one_length:
    for +s: U32
    for +hs: List<&2, Req.Field>
    for +b: List<&2, U32>
    for +r: Resp.Response
    for e: {Resp.response(s, hs, b) == Done{r} : Result<&2, &2, Resp.ResponseError, Resp.Response>}
    for hb: {Resp.has_length(s) == True{} : Bool}
    {Resp.content_lengths(Resp.write_head(r)) == [Some{List.length(&2, U32, b)}] : List<&2, Maybe<&2, Nat>>}
