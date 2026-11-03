# Proof of law H7: the head of a Parsed request has no bare CR or LF.

import Base
import ../../urlpath/proof/logic.bend as Logic
import bend-mathlib@0.7.4.0/string.bend as MStr
import ../src/reason.bend as Reason
import ../src/request.bend as Req
import ../src/limits.bend as Limits
import ../src/lines.bend as Lines
import ../src/fields.bend as Fields
import ../src/request_line.bend as Line
import ../src/head.bend as Head
import ./suffix.bend as Suffix


# ---- Clean bytes ----

law step_true:
  for p: Bool
  for cr: Bool
  for lf: Bool
  for y: Bool
  for h: {Lines.clean.step(p, cr, lf, y) == True{} : Bool}
  {y == True{} : Bool}

def step_true(p, cr, lf, y, h):
  match p:
    case True{}:
      Logic.and_right(lf, y, h)
    case False{}:
      match cr:
        case True{}:
          h
        case False{}:
          match lf:
            case True{}:
              Logic.absurd({y == True{} : Bool}, Logic.true_ne_false(h))
            case False{}:
              h

law step_id:
  for p: Bool
  for cr: Bool
  for lf: Bool
  for y: Bool
  for x: Bool
  for h: {Lines.clean.step(p, cr, lf, y) == True{} : Bool}
  {Lines.clean.step(p, cr, lf, x) == x : Bool}

def step_id(p, cr, lf, y, x, h):
  match p:
    case True{}:
      match lf:
        case True{}:
          {==}
        case False{}:
          Logic.absurd({Bool.and(False{}, x) == x : Bool}, Logic.true_ne_false(h))
    case False{}:
      match cr:
        case True{}:
          {==}
        case False{}:
          match lf:
            case True{}:
              Logic.absurd({False{} == x : Bool}, Logic.true_ne_false(h))
            case False{}:
              {==}

# A clean start doesn't change how the rest is judged
law clean_go_app:
  for a: List<&2, U32>
  for +b: List<&2, U32>
  for +p: Bool
  for +h: {Lines.clean.go(a, p) == True{} : Bool}
  {Lines.clean.go(List.append(&2, U32, a, b), p) == Lines.clean.go(b, False{}) : Bool}

def clean_go_app(a, b, p, h):
  match a:
    case Nil{}:
      e = Equal.sym(Bool, p, False{}, Logic.not_true(p, h))
      %e : {Lines.clean.go(b, _) == Lines.clean.go(b, False{}) : Bool}
      {==}
    case Con{+c, +t}:
      ih = Equal.sym(Bool, Lines.clean.go(List.append(&2, U32, t, b), Lines.clean.next(p, U32.is_eq(c, 13))), Lines.clean.go(b, False{}),
        clean_go_app(t, b, Lines.clean.next(p, U32.is_eq(c, 13)),
          step_true(p, U32.is_eq(c, 13), U32.is_eq(c, 10), Lines.clean.go(t, Lines.clean.next(p, U32.is_eq(c, 13))), h)))
      %ih : {Lines.clean.step(p, U32.is_eq(c, 13), U32.is_eq(c, 10), _) == Lines.clean.go(b, False{}) : Bool}
      step_id(p, U32.is_eq(c, 13), U32.is_eq(c, 10), Lines.clean.go(t, Lines.clean.next(p, U32.is_eq(c, 13))), Lines.clean.go(b, False{}), h)

law clean_app:
  for +u1: List<&2, U32>
  for +u2: List<&2, U32>
  for c1: {Lines.crlf_clean(u1) == True{} : Bool}
  for c2: {Lines.crlf_clean(u2) == True{} : Bool}
  {Lines.crlf_clean(List.append(&2, U32, u1, u2)) == True{} : Bool}

def clean_app(u1, u2, c1, c2):
  Equal.trans(Bool, Lines.clean.go(List.append(&2, U32, u1, u2), False{}), Lines.clean.go(u2, False{}), True{},
    clean_go_app(u1, u2, False{}, c1), c2)

# No CR or LF
def no_crlf(l: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.and(Bool.not(U32.is_eq(h, 13)), Bool.not(U32.is_eq(h, 10))), no_crlf(t))

# A line without CR or LF, then CRLF, is clean
law clean_crlf:
  for l: List<&2, U32>
  for +u: List<&2, U32>
  for +nc: {no_crlf(l) == True{} : Bool}
  {Lines.clean.go(List.append(&2, U32, l, Con{13, Con{10, u}}), False{}) == Lines.clean.go(u, False{}) : Bool}

def clean_crlf(l, u, nc):
  match l:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +both = Logic.and_left(Bool.and(Bool.not(U32.is_eq(c, 13)), Bool.not(U32.is_eq(c, 10))), no_crlf(t), nc)
      e1 = Equal.sym(Bool, U32.is_eq(c, 13), False{}, Logic.not_true(U32.is_eq(c, 13), Logic.and_left(Bool.not(U32.is_eq(c, 13)), Bool.not(U32.is_eq(c, 10)), both)))
      e2 = Equal.sym(Bool, U32.is_eq(c, 10), False{}, Logic.not_true(U32.is_eq(c, 10), Logic.and_right(Bool.not(U32.is_eq(c, 13)), Bool.not(U32.is_eq(c, 10)), both)))
      %e1 : {Lines.clean.step(False{}, _, U32.is_eq(c, 10), Lines.clean.go(List.append(&2, U32, t, Con{13, Con{10, u}}), Lines.clean.next(False{}, _))) == Lines.clean.go(u, False{}) : Bool}
      %e2 : {Lines.clean.step(False{}, False{}, _, Lines.clean.go(List.append(&2, U32, t, Con{13, Con{10, u}}), False{})) == Lines.clean.go(u, False{}) : Bool}
      clean_crlf(t, u, Logic.and_right(Bool.and(Bool.not(U32.is_eq(c, 13)), Bool.not(U32.is_eq(c, 10))), no_crlf(t), nc))


# ---- Suffixes with a clean start ----

# r is the end of i, and what comes before it is clean
def Suf7(i: List<&2, U32>, r: List<&2, U32>) -> Type:
  &used: List<&2, U32> -> {i == List.append(&2, U32, used, r) : List<&2, U32>} & {Lines.crlf_clean(used) == True{} : Bool}

law suf7_t4:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for +u1: List<&2, U32>
  for e1: {i == List.append(&2, U32, u1, m) : List<&2, U32>}
  for c1: {Lines.crlf_clean(u1) == True{} : Bool}
  for +u2: List<&2, U32>
  for p2: {m == List.append(&2, U32, u2, r) : List<&2, U32>} & {Lines.crlf_clean(u2) == True{} : Bool}
  Suf7(i, r)

def suf7_t4(i, m, r, u1, e1, c1, u2, p2):
  match p2:
    case (e2, c2):
      (List.append(&2, U32, u1, u2), (Suffix.suf_join(i, m, r, u1, u2, e1, e2), clean_app(u1, u2, c1, c2)))

law suf7_t3:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for +u1: List<&2, U32>
  for e1: {i == List.append(&2, U32, u1, m) : List<&2, U32>}
  for c1: {Lines.crlf_clean(u1) == True{} : Bool}
  for s2: Suf7(m, r)
  Suf7(i, r)

def suf7_t3(i, m, r, u1, e1, c1, s2):
  match s2:
    case (+u2, p2):
      suf7_t4(i, m, r, u1, e1, c1, u2, p2)

law suf7_t2:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for +u1: List<&2, U32>
  for p1: {i == List.append(&2, U32, u1, m) : List<&2, U32>} & {Lines.crlf_clean(u1) == True{} : Bool}
  for s2: Suf7(m, r)
  Suf7(i, r)

def suf7_t2(i, m, r, u1, p1, s2):
  match p1:
    case (e1, c1):
      suf7_t3(i, m, r, u1, e1, c1, s2)

law suf7_trans:
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for +r: List<&2, U32>
  for s1: Suf7(i, m)
  for s2: Suf7(m, r)
  Suf7(i, r)

def suf7_trans(i, m, r, s1, s2):
  match s1:
    case (+u1, p1):
      suf7_t2(i, m, r, u1, p1, s2)


# ---- Lines ----

# What next_line promises: the line, its CRLF and the rest make up b, and
# the line has no CR or LF
def LS7(b: List<&2, U32>, scan: Lines.LineScan) -> Type:
  match scan:
    case Lines.Line{l, rest}:
      {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>} & {no_crlf(l) == True{} : Bool}
    case other:
      Unit

law suf7_line2:
  for +b: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for e: {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>}
  for nc: {no_crlf(l) == True{} : Bool}
  Suf7(b, rest)

def suf7_line2(b, l, rest, e, nc):
  (List.append(&2, U32, l, [13, 10]),
    (Equal.trans(List<&2, U32>, b, List.append(&2, U32, l, Con{13, Con{10, rest}}), List.append(&2, U32, List.append(&2, U32, l, [13, 10]), rest), e,
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, l, [13, 10]), rest), List.append(&2, U32, l, Con{13, Con{10, rest}}), Suffix.app_assoc(l, [13, 10], rest))),
     clean_crlf(l, Nil{}, nc)))

law suf7_line:
  for +b: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for hl: {b == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>} & {no_crlf(l) == True{} : Bool}
  Suf7(b, rest)

def suf7_line(b, l, rest, hl):
  match hl:
    case (e, nc):
      suf7_line2(b, l, rest, e, nc)

law not_false:
  for x: Bool
  for e: {False{} == x : Bool}
  {Bool.not(x) == True{} : Bool}

def not_false(x, e):
  %e : {Bool.not(_) == True{} : Bool}
  {==}

law nl7_cons2:
  for +h: U32
  for +t: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for ecr: {False{} == U32.is_eq(h, 13) : Bool}
  for elf: {False{} == U32.is_eq(h, 10) : Bool}
  for e: {t == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>}
  for nc: {no_crlf(l) == True{} : Bool}
  LS7(Con{h, t}, Lines.Line{Con{h, l}, rest})

def nl7_cons2(h, t, l, rest, ecr, elf, e, nc):
  (Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{h, y}, t, List.append(&2, U32, l, Con{13, Con{10, rest}}), e),
   Logic.and_intro(Bool.and(Bool.not(U32.is_eq(h, 13)), Bool.not(U32.is_eq(h, 10))), no_crlf(l),
     Logic.and_intro(Bool.not(U32.is_eq(h, 13)), Bool.not(U32.is_eq(h, 10)), not_false(U32.is_eq(h, 13), ecr), not_false(U32.is_eq(h, 10), elf)),
     nc))

law nl7_cons1:
  for +h: U32
  for +t: List<&2, U32>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for ecr: {False{} == U32.is_eq(h, 13) : Bool}
  for elf: {False{} == U32.is_eq(h, 10) : Bool}
  for ih: {t == List.append(&2, U32, l, Con{13, Con{10, rest}}) : List<&2, U32>} & {no_crlf(l) == True{} : Bool}
  LS7(Con{h, t}, Lines.Line{Con{h, l}, rest})

def nl7_cons1(h, t, l, rest, ecr, elf, ih):
  match ih:
    case (e, nc):
      nl7_cons2(h, t, l, rest, ecr, elf, e, nc)

law nl7_cons:
  for +h: U32
  for +t: List<&2, U32>
  for r: Lines.LineScan
  for ecr: {False{} == U32.is_eq(h, 13) : Bool}
  for elf: {False{} == U32.is_eq(h, 10) : Bool}
  for ih: LS7(t, r)
  LS7(Con{h, t}, Lines.line.cons(h, r))

def nl7_cons(h, t, r, ecr, elf, ih):
  match r:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      nl7_cons1(h, t, l, rest, ecr, elf, ih)

law nl7_crlf:
  for k: Bool
  for +h: U32
  for +h2: U32
  for +r: List<&2, U32>
  for ek: {k == U32.is_eq(h2, 10) : Bool}
  for eh: {U32.is_eq(h, 13) == True{} : Bool}
  LS7(Con{h, Con{h2, r}}, Lines.line.crlf(k, r))

def nl7_crlf(k, h, h2, r, ek, eh):
  match k:
    case True{}:
      (Suffix.nl_crlf(True{}, h, h2, r, ek, eh), {==})
    case False{}:
      Unit{}

law nl7_cr:
  for +h: U32
  for t: List<&2, U32>
  for eh: {U32.is_eq(h, 13) == True{} : Bool}
  LS7(Con{h, t}, Lines.line.cr(t))

def nl7_cr(h, t, eh):
  match t:
    case Nil{}:
      Unit{}
    case Con{+h2, +r}:
      nl7_crlf(U32.is_eq(h2, 10), h, h2, r, {==}, eh)

law nl7_byte:
  for big: Bool
  for cr: Bool
  for lf: Bool
  for +h: U32
  for +t: List<&2, U32>
  for z: Bool
  for k: Unit -> Lines.LineScan
  for ecr: {cr == U32.is_eq(h, 13) : Bool}
  for elf: {lf == U32.is_eq(h, 10) : Bool}
  for ih: LS7(t, k(Unit{}))
  LS7(Con{h, t}, Lines.line.byte(big, cr, lf, h, t, z, k))

def nl7_byte(big, cr, lf, h, t, z, k, ecr, elf, ih):
  match big:
    case True{}:
      Unit{}
    case False{}:
      match cr:
        case True{}:
          nl7_cr(h, t, Equal.sym(Bool, True{}, U32.is_eq(h, 13), ecr))
        case False{}:
          match lf:
            case True{}:
              Unit{}
            case False{}:
              match z:
                case True{}:
                  Unit{}
                case False{}:
                  nl7_cons(h, t, k(Unit{}), ecr, elf, ih)

law nl7:
  for b: List<&2, U32>
  for +budget: U32
  LS7(b, Lines.next_line(b, budget))

def nl7(b, budget):
  match b:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      nl7_byte(Bool.not((h <= 255 : U32)), U32.is_eq(h, 13), U32.is_eq(h, 10), h, t, U32.is_zero(budget),
        u => Lines.next_line(t, U32.sub(budget, 1)), {==}, {==}, nl7(t, U32.sub(budget, 1)))


# ---- Head ----

# What head promises: the rest after the head is the end of the input, and
# the head before it is clean
def HS7(h: Head.HeadResult, i: List<&2, U32>) -> Type:
  match h:
    case Head.HeadParsed{rl, fs, rest}:
      Suf7(i, rest)
    case other:
      Unit

law hs7_trans:
  for h: Head.HeadResult
  for +i: List<&2, U32>
  for +m: List<&2, U32>
  for s: Suf7(i, m)
  for hh: HS7(h, m)
  HS7(h, i)

def hs7_trans(h, i, m, s, hh):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{rl, fs, +r}:
      suf7_trans(i, m, r, s, hh)

law hs7_cons2:
  for f: Req.Field
  for h: Head.HeadResult
  for +b: List<&2, U32>
  for +rest: List<&2, U32>
  for s: Suf7(b, rest)
  for hk: HS7(h, rest)
  HS7(Head.head.cons(f, h), b)

def hs7_cons2(f, h, b, rest, s, hk):
  match h:
    case Head.HeadNeedMore{}:
      Unit{}
    case Head.HeadRejected{e}:
      Unit{}
    case Head.HeadParsed{l, fs, +r}:
      suf7_trans(b, rest, r, s, hk)

law hs7_field2:
  for r: Result<&2, &2, Reason.Reason, Req.Field>
  for +b: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for s: Suf7(b, rest)
  for hk: HS7(k(rest)(sec), rest)
  HS7(Head.head.field2(r, rest, sec, k), b)

def hs7_field2(r, b, rest, sec, k, s, hk):
  match r:
    case Fail{e}:
      Unit{}
    case Done{f}:
      hs7_cons2(f, k(rest)(sec), b, rest, s, hk)

law hs7_field:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for +sec: U32
  for first: Bool
  for rl: Req.RequestLine
  for k: List<&2, U32> -> U32 -> Head.HeadResult
  for hl: LS7(b, scan)
  for ih: @r: List<&2, U32> -> @s: U32 -> HS7(k(r)(s), r)
  HS7(Head.head.field(scan, sec, first, rl, k), b)

def hs7_field(scan, b, sec, first, rl, k, hl, ih):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          suf7_line(b, Nil{}, rest, hl)
        case Con{+c, +t}:
          hs7_field2(Fields.field_line(Con{c, t}, first), b, rest, Head.minus(Head.minus(sec, 2), Head.size(Con{c, t})), k,
            suf7_line(b, Con{c, t}, rest, hl), ih(rest)(Head.minus(Head.minus(sec, 2), Head.size(Con{c, t}))))

law hs7_last:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for rl: Req.RequestLine
  for hl: LS7(b, scan)
  HS7(Head.head.last(scan, rl), b)

def hs7_last(scan, b, rl, hl):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          suf7_line(b, Nil{}, rest, hl)
        case Con{c, t}:
          Unit{}

law hs7_fields:
  for fuel: Nat
  for +input: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for first: Bool
  for +rl: Req.RequestLine
  HS7(Head.head.fields(fuel, input, sec, fl, first, rl), input)

def hs7_fields(fuel, input, sec, fl, first, rl):
  match fuel:
    case 0n:
      hs7_last(Lines.next_line(input, 0), input, rl, nl7(input, 0))
    case 1n+(+n):
      hs7_field(Lines.next_line(input, U32.min(fl, Head.minus(sec, 2))), input, sec, first, rl,
        r => s => Head.head.fields(n, r, s, fl, False{}, rl),
        nl7(input, U32.min(fl, Head.minus(sec, 2))),
        r => s => hs7_fields(n, r, s, fl, False{}, rl))

law hs7_section:
  for k: Bool
  for +rl: Req.RequestLine
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for nf: Nat
  HS7(Head.head.section(k, rl, rest, sec, fl, nf), rest)

def hs7_section(k, rl, rest, sec, fl, nf):
  match k:
    case True{}:
      hs7_fields(nf, rest, sec, fl, True{}, rl)
    case False{}:
      Unit{}

law hs7_line:
  for r: Result<&2, &2, Reason.Reason, Req.RequestLine>
  for +l: List<&2, U32>
  for +rest: List<&2, U32>
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  HS7(Head.head.line(r, l, rest, sec, fl, nf), rest)

def hs7_line(r, l, rest, sec, fl, nf):
  match r:
    case Fail{e}:
      Unit{}
    case Done{+rl}:
      hs7_section(Bool.and(U32.is_le(2, sec), U32.is_le(Head.size(l), Head.minus(sec, 2))), rl, rest, Head.minus(Head.minus(sec, 2), Head.size(l)), fl, nf)

law hs7_request:
  for scan: Lines.LineScan
  for +b: List<&2, U32>
  for empty: Head.HeadResult
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for hl: LS7(b, scan)
  for he: HS7(empty, b)
  HS7(Head.head.request(scan, empty, sec, fl, nf), b)

def hs7_request(scan, b, empty, sec, fl, nf, hl, he):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          he
        case Con{+c, +t}:
          hs7_trans(Head.head.line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf), b, rest,
            suf7_line(b, Con{c, t}, rest, hl),
            hs7_line(Line.request_line(Con{c, t}), Con{c, t}, rest, sec, fl, nf))

law hs7_first:
  for scan: Lines.LineScan
  for +i: List<&2, U32>
  for +rlim: U32
  for +sec: U32
  for +fl: U32
  for +nf: Nat
  for hl: LS7(i, scan)
  HS7(Head.head.first(scan, rlim, sec, fl, nf), i)

def hs7_first(scan, i, rlim, sec, fl, nf, hl):
  match scan:
    case Lines.Partial{}:
      Unit{}
    case Lines.TooLong{}:
      Unit{}
    case Lines.NotByte{}:
      Unit{}
    case Lines.LoneLF{}:
      Unit{}
    case Lines.LoneCR{}:
      Unit{}
    case Lines.Line{+l, +rest}:
      match l:
        case Nil{}:
          hs7_trans(Head.head.request(Lines.next_line(rest, rlim), Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf), i, rest,
            suf7_line(i, Nil{}, rest, hl),
            hs7_request(Lines.next_line(rest, rlim), rest, Head.HeadRejected{Reason.InvalidRequestLine{}}, sec, fl, nf, nl7(rest, rlim), Unit{}))
        case Con{+c, +t}:
          hs7_request(Lines.Line{Con{c, t}, rest}, i, Head.HeadNeedMore{}, sec, fl, nf, hl, Unit{})

law hs7_head:
  for +l: Limits.Limits
  for +i: List<&2, U32>
  HS7(Head.head(l, i), i)

def hs7_head(l, i):
  match l:
    case Limits.Limits{+rl, fl, hs, nf, b, ce}:
      hs7_first(Lines.next_line(i, rl), i, rl, hs, fl, U32.to_nat(nf), nl7(i, rl))


