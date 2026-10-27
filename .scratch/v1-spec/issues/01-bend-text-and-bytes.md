# What do Bend's TCP receive functions return, and what text and byte operations does Base offer?

Type: research
Status: resolved
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

What exactly do `TCP.recv` (String) and `TCP.recv_bytes` (List of U32) return for arbitrary bytes, including invalid UTF-8 and NUL? What is a Bend `String` underneath (list of code points?), and which operations does Base provide on strings, lists and U32 (comparison, splitting, digit parsing, length) along with which of them have laws? Sources: `bend guide`, `bend base`, `~/.bend/bend2/effs/tcp_recv.*`, `base.bend`. Output: the facts the input-representation decision needs.

## Answer

Full findings: branch `research/bend-text-and-bytes`, file `.scratch/v1-spec/research/01-bend-text-and-bytes.md` (commit 35fbf0e; not merged).

- `TCP.recv_bytes` keeps every byte (0..255, NUL and invalid UTF-8 included), split at arbitrary points; `None` at end of stream.
- `TCP.recv` decodes UTF-8 with U+FFFD replacement; a character split across reads is corrupted for good. Unsafe for a parser.
- `String` is a linked list of code points. Base has length, append, equality, comparison, starts/ends-with, contains, single-char split, `U32.read`, `Nat.read`; no `\r\n` split, index-of, hex parsing or byte-list helpers.
- Base has no laws about strings, lists, U32 comparison or read/show: proofs start from scratch.
- Proof workarounds: shrinking argument first (fuel for token loops); helper defs for computed branches; use `Char.is_eq` + helper instead of matching on char literals; U32 not Nat in laws; `--verdict` needs Lean 4.34.0 (not installed).
- `bend-kit-bytes` (`Bytes{len, buf: Array<U32>}`, affine) and `bend-kit-encoding` have almost only example laws; their packed receive goes through foreign code in `bend-kit-wire`, failing the `--verdict` gate.
- Recommendation: state laws over `List<&2, U32>` from `recv_bytes`; `Bytes` as a later fast path. Evaluate `bend-kit-lemmas` and `bend-mathlib` for proof helpers.
