# Map: bend-http v1 spec

Label: wayfinder:map

## Destination

A spec for v1 of two BendHub packages, `urlpath` and `http1` (server side), complete enough to hand to an implementation session: API, laws and package layout settled, nothing left to decide.

## Notes

- Domain: verified libraries in Bend 2 (`bend guide`, `bend base`, `~/.bend/bend2/`). Vocabulary lives in `GLOSSARY.md`; use its terms.
- Planning only: tickets produce decisions, not code (prototypes excepted).
- Skills: `grilling` + `domain-modeling` for grilling tickets; `research` for research tickets; `prototype` for prototype tickets.
- Standing decisions from charting (2026-10-27):
  - The map's output is a spec; building and publishing are a later effort.
  - `urlpath` handles URL paths only (not filesystem paths). `http1` builds on it.
  - Users are Bend programmers via BendHub; the JS module export doesn't shape v1.
  - A package is published only when every law is proven and `bend --verdict` passes.
  - `http1` rejects anything ambiguous or obsolete rather than guessing (strict RFC 9112).
  - `http1` v1 is server side: parse requests, write responses.
  - Parsing is a pure function over the input received so far, returning a parse outcome: Need more, Rejected (reason) or Parsed (request + leftover input).
  - MIT licence. (Names reopened: short names are auctioned; see the package-names ticket.)
- Prior art (found 2026-10-27): `bend-kit-http` already ships HTTP/1.1 and HTTP/2 on BendHub, with mostly example-based laws. http1 must earn its place with general laws; see the positioning ticket. The user chose to continue with HTTP for its learning and portfolio value.

## Decisions so far

<!-- one line per resolved ticket: [title](issues/NN-slug.md): gist -->

- [How do BendHub packages depend on each other, and what does publishing need?](issues/04-bendhub-packages.md): hub imports by name@version or hash; laws and proofs must ship together; publish doesn't enforce --verdict; names under 12 chars are auctioned.
- [Which request-smuggling and parsing attacks must http1 reject?](issues/03-http1-smuggling-cases.md): 43 cases with RFC sections and rejection reasons; rejection ends the connection; 8 edge cases left to decide.
- [Which standard rules and known attacks must urlpath handle?](issues/02-urlpath-rules-and-attacks.md): decode once, then check; `%2F` is not `/`; 20 cases, 7 candidate laws, 6 open decisions; Servlet 6.0 §3.5.2 as the model.
- [What do Bend's TCP receive functions return, and what text and byte operations does Base offer?](issues/01-bend-text-and-bytes.md): `recv_bytes` keeps every byte, `recv` corrupts invalid/split UTF-8; Base has no laws on strings or lists; research suggests laws over `List<U32>` bytes.

## Not yet specified

- **Response writing:** the response type `http1` writes, and its laws (no header injection, correct framing of the body). Depends on the request type.
- **Chunked bodies in detail:** limits on chunk sizes and trailers, and whether trailers are kept or dropped. Likely part of the http1 laws ticket or split from it.
- **Package layout:** how `http1` imports `urlpath` (hub version pin vs local), and whether laws and proofs ship in separate files. Waits on the BendHub research and the urlpath API.
- **Confidence beyond proofs:** whether to also cross-check against another parser on a shared corpus of tricky requests (llhttp, for example), since a law can be stated wrongly.
- **Spec document itself:** its format and where it lives once the decisions are in.

## Out of scope

- Example static-file server (`http1-server`): a later effort built on these packages.
- Client side of HTTP (writing requests, parsing responses).
- HTTP/2, HTTP/3, TLS and DNS.
- Publishing the JS module export.
