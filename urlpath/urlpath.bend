import Base

# RFC 3986 - Uniform Resource Identifier (URI): Generic Syntax

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

