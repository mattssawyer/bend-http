# Proofs about the request line.

import Base
import ../../urlpath/urlpath.bend as Path
import ../../urlpath/proof/logic.bend as Logic
import ../src/bytes.bend as Byte
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/request_line.bend as Line


# What method_ok promises about one result
def MOk(r: Result<&2, &2, Reason.Reason, Req.RequestLine>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{rl}:
      match rl:
        case Req.RequestLine{m, t, v}:
          {Line.method_ok(m) == True{} : Bool}

law mo_version:
  for r: Result<&2, &2, Reason.Reason, Req.Version>
  for m: List<&2, U32>
  for tg: Req.Target
  for h: {Line.method_ok(m) == True{} : Bool}
  MOk(Line.request_line.version(r, m, tg))

def mo_version(r, m, tg, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{v}:
      h

law mo_target:
  for r: Result<&2, &2, Reason.Reason, Req.Target>
  for +m: List<&2, U32>
  for +v: List<&2, U32>
  for h: {Line.method_ok(m) == True{} : Bool}
  MOk(Line.request_line.target(r, m, v))

def mo_target(r, m, v, h):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+tg}:
      mo_version(Line.version(v), m, tg, h)

# not x is True when x is False
law not_false:
  for x: Bool
  for e: {False{} == x : Bool}
  {Bool.not(x) == True{} : Bool}

def not_false(x, e):
  %e : {Bool.not(_) == True{} : Bool}
  {==}

law mo_method:
  for short: Bool
  for connect: Bool
  for +m: List<&2, U32>
  for t: List<&2, U32>
  for +v: List<&2, U32>
  for es: {short == Nat.is_le(List.length(&2, U32, m), 32n) : Bool}
  for ec: {connect == Byte.eq(m, Path.bytes("CONNECT")) : Bool}
  for ht: {Byte.is_token(m) == True{} : Bool}
  MOk(Line.request_line.method(short, connect, m, t, v))

def mo_method(short, connect, m, t, v, es, ec, ht):
  match short:
    case False{}:
      Unit{}
    case True{}:
      match connect:
        case True{}:
          Unit{}
        case False{}:
          mo_target(Line.target(m, t), m, v,
            Logic.and_intro(Bool.and(Byte.is_token(m), Nat.is_le(List.length(&2, U32, m), 32n)), Bool.not(Byte.eq(m, Path.bytes("CONNECT"))),
              Logic.and_intro(Byte.is_token(m), Nat.is_le(List.length(&2, U32, m), 32n), ht,
                Equal.sym(Bool, True{}, Nat.is_le(List.length(&2, U32, m), 32n), es)),
              not_false(Byte.eq(m, Path.bytes("CONNECT")), ec)))

law mo_shape:
  for k: Bool
  for +m: List<&2, U32>
  for +t: List<&2, U32>
  for +v: List<&2, U32>
  for ek: {k == Line.shape_ok(m, t, v) : Bool}
  MOk(Line.request_line.shape(k, m, t, v))

def mo_shape(k, m, t, v, ek):
  match k:
    case False{}:
      Unit{}
    case True{}:
      mo_method(Nat.is_le(List.length(&2, U32, m), 32n), Byte.eq(m, Path.bytes("CONNECT")), m, t, v, {==}, {==},
        Logic.and_left(Byte.is_token(m), Line.shape_ok.rest(t, v), Equal.sym(Bool, True{}, Line.shape_ok(m, t, v), ek)))

law mo_second:
  for +m: List<&2, U32>
  for c: Byte.Cut
  MOk(Line.request_line.second(m, c))

def mo_second(m, c):
  match c:
    case Byte.NoCut{}:
      Unit{}
    case Byte.Cut{+t, +v}:
      mo_shape(Line.shape_ok(m, t, v), m, t, v, {==})

law mo_first:
  for c: Byte.Cut
  MOk(Line.request_line.first(c))

def mo_first(c):
  match c:
    case Byte.NoCut{}:
      Unit{}
    case Byte.Cut{+m, rest}:
      mo_second(m, Byte.cut_last(rest, 32))
