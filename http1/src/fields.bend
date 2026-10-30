# One header field line: "Name: value".

import Base
import ./bytes.bend as Byte
import ./reason.bend as Reason
import ./request.bend as Req


# Space or tab
def is_ows(+b: U32) -> Bool:
  U32.is_eq(b, 32) || U32.is_eq(b, 9)

# A byte allowed in a field value: visible ASCII, space, tab, or 0x80-0xFF.
# NUL, other controls and DEL are not.
def is_value_byte(+b: U32) -> Bool:
  (b >= 33 : U32) && (b <= 126 : U32) || is_ows(b) || (b >= 128 : U32) && (b <= 255 : U32)

def all_value_bytes(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        is_value_byte(h) && all_value_bytes(t)

def drop_ows.if(ows: Bool, r: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match ows:
    case True{}:
        r
    case False{}:
        b

# Drop spaces and tabs from the front
def drop_ows(b: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Nil{}:
        Nil{}
    case Con{+h, +t}:
        drop_ows.if(is_ows(h), drop_ows(t), Con{h, t})

# Drop spaces and tabs from both ends
def trim(b: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, drop_ows(List.reverse(&2, U32, drop_ows(b))))

def field.value(ok: Bool, name: List<&2, U32>, +value: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Field>:
  match ok:
    case True{}:
        Done{Req.Field{name, trim(value)}}
    case False{}:
        Fail{Reason.InvalidFieldValue{}}

# A name with a space or tab before the colon gets its own reason
def field.name(token: Bool, ws: Bool, +name: List<&2, U32>, +value: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Field>:
  match token:
    case True{}:
        field.value(all_value_bytes(value), name, value)
    case False{}:
        match ws:
          case True{}:
              Fail{Reason.WhitespaceBeforeColon{}}
          case False{}:
              Fail{Reason.InvalidFieldName{}}

def field.cut(c: Byte.Cut) -> Result<&2, &2, Reason.Reason, Req.Field>:
  match c:
    case Byte.NoCut{}:
        Fail{Reason.InvalidFieldLine{}}
    case Byte.Cut{+name, +value}:
        field.name(Byte.is_token(name), Byte.ends_with(name, 32) || Byte.ends_with(name, 9), name, value)

# A line starting with a space or tab is folded onto the line before it
# (obs-fold). Straight after the request line it gets its own reason.
def field.start(ows: Bool, first: Bool, +line: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.Field>:
  match ows:
    case True{}:
        match first:
          case True{}:
              Fail{Reason.WhitespaceBeforeFirstField{}}
          case False{}:
              Fail{Reason.ObsFold{}}
    case False{}:
        field.cut(Byte.cut(line, 58))

# Parse one field line, without its CRLF. first is True for the line
# straight after the request line.
def field_line(line: List<&2, U32>, first: Bool) -> Result<&2, &2, Reason.Reason, Req.Field>:
  match line:
    case Nil{}:
        Fail{Reason.InvalidFieldLine{}}
    case Con{+c, +t}:
        field.start(is_ows(c), first, Con{c, t})
