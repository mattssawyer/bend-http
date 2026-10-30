# A byte-based implementation of the URL path parser.
# Author: Matthew Sawyer
# Last Updated: 2026-10-29
# Version: 1.0.0

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

# Add head to the linked list 
def add_head(head: U32, segs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>: 
  match segs: 
    case Nil{}:
        [[head]]
    case Con{first, rest}:
        Con{Con{head, first}, rest}

# Helper for split: start a new segment on "/", otherwise grow the first one
def split.if(+h: U32, rest: List<&2, List<&2, U32>>, slash: Bool) -> List<&2, List<&2, U32>>:
  match slash:
    case True{}:
        Con{Nil{}, rest}
    case False{}:
        add_head(h, rest)

# Split bytes on "/" (47). Always returns at least one segment.
# "/a/b" gives [[], [97], [98]]
def split(b: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match b:
    case Nil{}:
        [Nil{}]
    case Con{+h, t}:
        split.if(h, split(t), U32.is_eq(h, 47))

# Glue segments back together with "/" between them (undoes split)
def join(segs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match segs:
    case Nil{}:
        Nil{}
    case Con{s, Nil{}}:
        s
    case Con{s, r}:
        List.append(&2, U32, s, Con{47, join(r)})
