# Reading a chunked body: chunks of "size[;ext]\r\n data \r\n", ending with a
# zero-size chunk, then trailer fields, then an empty line.

import Base
import ../../urlpath/src/bytes.bend as UrlByte
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req
import ./limits.bend as Limits
import ./lines.bend as Lines
import ./fields.bend as Fields
import ./head.bend as Head


# What reading a chunked body gives
type ChunkResult is Data:
  ChunkNeedMore{}
  ChunkRejected{reason: Reason.Reason}
  ChunkDone{body: List<&2, U32>, rest: List<&2, U32>}


# ---- Chunk extensions ----
# chunk-ext = *( ";" OWS name [ OWS "=" OWS value ] ), name a token, value a
# token or a quoted string (RFC 9112 section 7.1.1). Unlike the RFC, no
# whitespace is allowed before ";".

# Where the extension parser is
type ExtState is Data:
  ExSemi{}       # expecting ";" or the end
  ExName0{}      # after ";": spaces, then the name
  ExName{}       # in the name
  ExNameWs{}     # spaces after the name: "=" must follow
  ExVal0{}       # after "=": spaces, then the value
  ExTok{}        # in a token value
  ExQ{}          # in a quoted value
  ExQEsc{}       # after a backslash in a quoted value

# A byte allowed in a quoted string: tab, space, visible ASCII except '"' and
# backslash, or 0x80-0xFF
def is_qdtext(+c: U32) -> Bool:
  U32.is_eq(c, 9) || U32.is_eq(c, 32) || U32.is_eq(c, 33) || (c >= 35 : U32) && (c <= 91 : U32)
  || (c >= 93 : U32) && (c <= 126 : U32) || (c >= 128 : U32) && (c <= 255 : U32)

# A byte allowed after a backslash: tab, space, visible ASCII, or 0x80-0xFF
def is_escapable(+c: U32) -> Bool:
  U32.is_eq(c, 9) || U32.is_eq(c, 32) || (c >= 33 : U32) && (c <= 126 : U32) || (c >= 128 : U32) && (c <= 255 : U32)

def pick(ok: Bool, s: ExtState) -> Maybe<&2, ExtState>:
  match ok:
    case True{}:
        Some{s}
    case False{}:
        None{}

def ext.or(a: Maybe<&2, ExtState>, b: Maybe<&2, ExtState>) -> Maybe<&2, ExtState>:
  match a:
    case Some{s}:
        Some{s}
    case None{}:
        b

# The state after byte c, or None if c isn't allowed here
def ext.next(st: ExtState, +c: U32) -> Maybe<&2, ExtState>:
  match st:
    case ExSemi{}:
        pick(U32.is_eq(c, 59), ExName0{})
    case ExName0{}:
        ext.or(pick(Fields.is_ows(c), ExName0{}), pick(Byte.is_tchar(c), ExName{}))
    case ExName{}:
        ext.or(pick(Byte.is_tchar(c), ExName{}), ext.or(pick(Fields.is_ows(c), ExNameWs{}),
          ext.or(pick(U32.is_eq(c, 61), ExVal0{}), pick(U32.is_eq(c, 59), ExName0{}))))
    case ExNameWs{}:
        ext.or(pick(Fields.is_ows(c), ExNameWs{}), pick(U32.is_eq(c, 61), ExVal0{}))
    case ExVal0{}:
        ext.or(pick(Fields.is_ows(c), ExVal0{}), ext.or(pick(Byte.is_tchar(c), ExTok{}), pick(U32.is_eq(c, 34), ExQ{})))
    case ExTok{}:
        ext.or(pick(Byte.is_tchar(c), ExTok{}), pick(U32.is_eq(c, 59), ExName0{}))
    case ExQ{}:
        ext.or(pick(U32.is_eq(c, 34), ExSemi{}), ext.or(pick(U32.is_eq(c, 92), ExQEsc{}), pick(is_qdtext(c), ExQ{})))
    case ExQEsc{}:
        pick(is_escapable(c), ExQ{})

# The extension may end here
def ext.done(st: ExtState) -> Bool:
  match st:
    case ExSemi{}:
        True{}
    case ExName{}:
        True{}
    case ExTok{}:
        True{}
    case other:
        False{}

def ext.step(m: Maybe<&2, ExtState>, k: ExtState -> Bool) -> Bool:
  match m:
    case None{}:
        False{}
    case Some{s}:
        k(s)

def ext_ok.go(b: List<&2, U32>, +st: ExtState) -> Bool:
  match b:
    case Nil{}:
        ext.done(st)
    case Con{+c, t}:
        ext.step(ext.next(st, c), s => ext_ok.go(t, s))

# Does b (from the first ";" on) match the chunk-ext grammar?
def ext_ok(b: List<&2, U32>) -> Bool:
  ext_ok.go(b, ExSemi{})


# ---- Chunk size ----

def drop_zeros.if(zero: Bool, r: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match zero:
    case True{}:
        r
    case False{}:
        b

# Drop leading "0"s
def drop_zeros(b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
        Nil{}
    case Con{+h, +t}:
        drop_zeros.if(U32.is_eq(h, 48), drop_zeros(t), Con{h, t})

def all_hex(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        UrlByte.is_hex(h) && all_hex(t)

# The value of hex digits (at most 8, so it fits in a U32)
def hex.go(b: List<&2, U32>, +acc: U32) -> U32:
  match b:
    case Nil{}:
        acc
    case Con{+h, t}:
        hex.go(t, U32.add(U32.mul(acc, 16), UrlByte.hex_val(h)))

def size.ext(ok: Bool, n: U32) -> Result<&2, &2, Reason.Reason, U32>:
  match ok:
    case True{}:
        Done{n}
    case False{}:
        Fail{Reason.InvalidChunkExtension{}}

def size.ext_len(short: Bool, +ext: List<&2, U32>, n: U32) -> Result<&2, &2, Reason.Reason, U32>:
  match short:
    case True{}:
        size.ext(ext_ok(ext), n)
    case False{}:
        Fail{Reason.ChunkExtensionTooLong{}}

def size.digits(ok: Bool, +d: List<&2, U32>, +ext: List<&2, U32>, +elim: U32) -> Result<&2, &2, Reason.Reason, U32>:
  match ok:
    case True{}:
        size.ext_len(U32.is_le(Head.size(ext), elim), ext, hex.go(d, 0))
    case False{}:
        Fail{Reason.InvalidChunkSize{}}

def size.ws(ws: Bool, +d: List<&2, U32>, +ext: List<&2, U32>, +elim: U32) -> Result<&2, &2, Reason.Reason, U32>:
  match ws:
    case True{}:
        Fail{Reason.InvalidChunkExtension{}}
    case False{}:
        size.digits(Bool.not(List.is_empty(&2, U32, d)) && all_hex(d)
          && Nat.is_le(List.length(&2, U32, drop_zeros(d)), 8n), d, ext, elim)

def size.cut(c: Byte.Cut, +l: List<&2, U32>, +elim: U32) -> Result<&2, &2, Reason.Reason, U32>:
  match c:
    case Byte.NoCut{}:
        size.ws(False{}, l, Nil{}, elim)
    case Byte.Cut{+d, +e}:
        size.ws(Byte.ends_with(d, 32) || Byte.ends_with(d, 9), d, Con{59, e}, elim)

# A chunk-size line, without its CRLF: hex digits (any case, leading zeros
# allowed, at most 8 significant), then an optional extension
def size_line(+l: List<&2, U32>, +elim: U32) -> Result<&2, &2, Reason.Reason, U32>:
  size.cut(Byte.cut(l, 59), l, elim)


# ---- Chunks ----

def chunk.cons(data: List<&2, U32>, r: ChunkResult) -> ChunkResult:
  match r:
    case ChunkDone{b, left}:
        ChunkDone{List.append(&2, U32, data, b), left}
    case other:
        other

def chunk.lf(lf: Bool, k: Unit -> ChunkResult) -> ChunkResult:
  match lf:
    case True{}:
        k(Unit{})
    case False{}:
        ChunkRejected{Reason.MissingChunkDataCRLF{}}

# Only a CR so far: the LF may still come
def chunk.cr(cr: Bool) -> ChunkResult:
  match cr:
    case True{}:
        ChunkNeedMore{}
    case False{}:
        ChunkRejected{Reason.MissingChunkDataCRLF{}}

# After the data: exactly CRLF
def chunk.crlf(r: List<&2, U32>, k: List<&2, U32> -> ChunkResult) -> ChunkResult:
  match r:
    case Nil{}:
        ChunkNeedMore{}
    case Con{+a, t}:
        match t:
          case Nil{}:
              chunk.cr(U32.is_eq(a, 13))
          case Con{+b, t2}:
              chunk.lf(U32.is_eq(a, 13) && U32.is_eq(b, 10), u => k(t2))

def chunk.data(m: Maybe<&2, Byte.Taken>, k: List<&2, U32> -> ChunkResult) -> ChunkResult:
  match m:
    case None{}:
        ChunkNeedMore{}
    case Some{tk}:
        match tk:
          case Byte.Taken{data, r}:
              chunk.cons(data, chunk.crlf(r, k))

# Trailers are read like header fields, with the same checks and limits,
# and then dropped
def chunk.trailers(h: Head.HeadResult) -> ChunkResult:
  match h:
    case Head.HeadNeedMore{}:
        ChunkNeedMore{}
    case Head.HeadRejected{e}:
        ChunkRejected{e}
    case Head.HeadParsed{rl, fs, rest}:
        ChunkDone{Nil{}, rest}

def chunk.fits(fits: Bool, +n: U32, rest: List<&2, U32>, k: List<&2, U32> -> ChunkResult) -> ChunkResult:
  match fits:
    case True{}:
        chunk.data(Byte.take(U32.to_nat(n), rest), k)
    case False{}:
        ChunkRejected{Reason.ContentTooLarge{}}

# A zero-size chunk is the last one. Otherwise the running total must stay
# within the body limit.
def chunk.zero(zero: Bool, +n: U32, rest: List<&2, U32>, +total: U32, +limits: Limits.Limits, k: List<&2, U32> -> U32 -> ChunkResult) -> ChunkResult:
  match zero:
    case True{}:
        chunk.trailers(Head.trailers(limits, rest))
    case False{}:
        chunk.fits(U32.is_le(n, U32.sub(Limits.body(limits), total)), n, rest, r2 => k(r2)(U32.add(total, n)))

def chunk.size(r: Result<&2, &2, Reason.Reason, U32>, rest: List<&2, U32>, +total: U32, +limits: Limits.Limits, k: List<&2, U32> -> U32 -> ChunkResult) -> ChunkResult:
  match r:
    case Fail{e}:
        ChunkRejected{e}
    case Done{+n}:
        chunk.zero(U32.is_zero(n), n, rest, total, limits, k)

def size_budget.cap(fits: Bool, +ext: U32) -> U32:
  match fits:
    case True{}:
        U32.add(ext, 32)
    case False{}:
        4294967295

# A size line can hold the size (32 bytes is plenty) and the extension. The
# sum stops at the largest U32 rather than wrapping round to a tiny budget.
def size_budget(+limits: Limits.Limits) -> U32:
  size_budget.cap(U32.is_le(Limits.chunk_ext(limits), 4294967263), Limits.chunk_ext(limits))

# A size line over the budget: blame the extension if there is one
def chunk.long(ext: Bool) -> ChunkResult:
  match ext:
    case True{}:
        ChunkRejected{Reason.ChunkExtensionTooLong{}}
    case False{}:
        ChunkRejected{Reason.InvalidChunkSize{}}

def chunk.line(scan: Lines.LineScan, +input: List<&2, U32>, +total: U32, +limits: Limits.Limits, k: List<&2, U32> -> U32 -> ChunkResult) -> ChunkResult:
  match scan:
    case Lines.Partial{}:
        ChunkNeedMore{}
    case Lines.TooLong{}:
        chunk.long(Byte.prefix_has(input, size_budget(limits), 59))
    case Lines.NotByte{}:
        ChunkRejected{Reason.NotAByte{}}
    case Lines.LoneLF{}:
        ChunkRejected{Reason.BareLF{}}
    case Lines.LoneCR{}:
        ChunkRejected{Reason.BareCR{}}
    case Lines.Line{+l, rest}:
        chunk.size(size_line(l, Limits.chunk_ext(limits)), rest, total, limits, k)

# Read chunks. fuel only makes the recursion visibly finite: every chunk
# uses at least one byte, so the input's length is always enough.
def chunks(fuel: Nat, +input: List<&2, U32>, +total: U32, +limits: Limits.Limits) -> ChunkResult:
  match fuel:
    case 0n:
        ChunkNeedMore{}
    case 1n+n:
        chunk.line(Lines.next_line(input, size_budget(limits)), input, total, limits,
          r => s => chunks(n, r, s, limits))

# Read a chunked body from the start of input
def read(+limits: Limits.Limits, +input: List<&2, U32>) -> ChunkResult:
  chunks(1n+List.length(&2, U32, input), input, 0, limits)
