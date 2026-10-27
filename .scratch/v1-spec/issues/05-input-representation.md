# Should the parsers take input as a String or as a list of bytes?

Type: grilling
Status: open
Assignee: Matthew Sawyer
Blocked by: 01
Map: [bend-http v1 spec](../map.md)

## Question

Given what Bend's TCP functions return and what Base supports, should `urlpath` and `http1` work on `String` or on `List<U32>` bytes (or bytes for http1 and String for urlpath)? Weigh correctness on non-ASCII and invalid input, proof effort and convenience for callers. A third option: depend on the hub's `bend-kit-bytes` (four bytes packed per U32, bounds-checked; the most-used hub package) and `bend-kit-encoding` (UTF-8).
