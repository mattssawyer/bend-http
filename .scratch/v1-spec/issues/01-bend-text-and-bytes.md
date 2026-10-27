# What do Bend's TCP receive functions return, and what text and byte operations does Base offer?

Type: research
Status: open
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

What exactly do `TCP.recv` (String) and `TCP.recv_bytes` (List of U32) return for arbitrary bytes, including invalid UTF-8 and NUL? What is a Bend `String` underneath (list of code points?), and which operations does Base provide on strings, lists and U32 (comparison, splitting, digit parsing, length) along with which of them have laws? Sources: `bend guide`, `bend base`, `~/.bend/bend2/effs/tcp_recv.*`, `base.bend`. Output: the facts the input-representation decision needs.
