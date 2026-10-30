# Bytes and byte classes: the ASCII helper, the URL character classes and hex digits.

import Base


# Convert the string to a list of bytes
def bytes(s: String) -> List<&2, U32>: 
  match s: 
    case SNil{}:
        Nil{}
    case SCon{c, t}: 
        Con{Char.to_u32(c), bytes(t)}

# Check if the byte is a digit
def is_digit(+b: U32) -> Bool: 
  (b >= 48 : U32) && (b <= 57 : U32)

# Check if the byte is a letter
def is_alpha(+b: U32) -> Bool: 
  (b >= 65 : U32) && (b <= 90 : U32) || (b >= 97 : U32) && (b <= 122 : U32)

# Check if the byte is a hexadecimal digit
def is_hex(+b: U32) -> Bool: 
  is_digit(b) || (b >= 65 : U32) && (b <= 70 : U32) 
  || (b >= 97 : U32) && (b <= 102 : U32)

# Check if the byte is a unreserved character (letters, digits, -, ., _, ~)
def is_unreserved(+b: U32) -> Bool: 
  is_alpha(b) || is_digit(b)
  || U32.is_eq(b, 45) || U32.is_eq(b, 46)
  || U32.is_eq(b, 95) || U32.is_eq(b, 126)

# Check if the byte is a sub-delim character (! $ & ' ( ) * + , ; =)
def is_sub_delim(+b: U32) -> Bool: 
  U32.is_eq(b, 33) || U32.is_eq(b, 36) || U32.is_eq(b, 38) || U32.is_eq(b, 39)
  || U32.is_eq(b, 40) || U32.is_eq(b, 41) || U32.is_eq(b, 42) || U32.is_eq(b, 43)
  || U32.is_eq(b, 44) || U32.is_eq(b, 59) || U32.is_eq(b, 61)

# Check if the byte is a pchar character (unreserved, sub-delimiter, :, @)
def is_pchar(+b: U32) -> Bool: 
  is_unreserved(b) || is_sub_delim(b) || U32.is_eq(b, 58) || U32.is_eq(b, 64)

def hex_val.if(+b: U32, digit: Bool, upper: Bool) -> U32:
  match digit:
    case True{}:
        U32.sub(b, 48)
    case False{}:
        match upper:
          case True{}:
              U32.sub(b, 55)
          case False{}:
              U32.sub(b, 87)

# The value of one hex digit: "0"-"9" -> 0-9, "A"-"F" and "a"-"f" -> 10-15
def hex_val(+b: U32) -> U32:
  hex_val.if(b, is_digit(b), (b >= 65 : U32) && (b <= 70 : U32))

# The byte written as two hex digit values: hi * 16 + lo
def hex_pair(+hi: U32, +lo: U32) -> U32:
  U32.add(U32.mul(hi, 16), lo)

# True when every byte is a pchar (so there's nothing to decode)
def all_pchar(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        is_pchar(h) && all_pchar(t)

# Every element is a byte (0-255)
def all_bytes(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
        True{}
    case Con{+h, t}:
        (h <= 255 : U32) && all_bytes(t)

# Does the list contain byte x?
def has_byte(b: List<&2, U32>, +x: U32) -> Bool:
  match b:
    case Nil{}:
        False{}
    case Con{+h, t}:
        U32.is_eq(h, x) || has_byte(t, x)

# The uppercase hex digits, "0"-"9" then "A"-"F"
def hex_digits() -> List<&2, U32>:
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70]

def hex_digit.if(eq: Bool, d: U32, other: U32) -> U32:
  match eq:
    case True{}:
        d
    case False{}:
        other

# Find digit number n in the table (i counts from 0). Not found gives "0".
def hex_digit.go(tbl: List<&2, U32>, +n: U32, +i: U32) -> U32:
  match tbl:
    case Nil{}:
        48
    case Con{d, rest}:
        hex_digit.if(U32.is_eq(n, i), d, hex_digit.go(rest, n, U32.inc(i)))

# The uppercase hex digit for a value 0-15
def hex_digit(+n: U32) -> U32:
  hex_digit.go(hex_digits(), n, 0)

# High and low halves of a byte: 0xC3 -> 0xC and 0x3
def hi_nibble(+c: U32) -> U32:
  U32.shrn(c, 4n)

def lo_nibble(+c: U32) -> U32:
  U32.and(c, 15)

# An uppercase hex digit: "0"-"9" or "A"-"F"
def is_upper_hex(+c: U32) -> Bool:
  is_digit(c) || (c >= 65 : U32) && (c <= 70 : U32)
