# bend-http

Verified HTTP/1.1 building blocks for Bend, published on BendHub: a URL path package and an HTTP/1.1 message library built on it.

## Language

**URL path**:
The path part of an HTTP request target, such as `/a/%2e%2e/b`, before or after percent-decoding.
_Avoid_: path (alone), file path, filesystem path

**Law**:
A precise claim about the library's behaviour, stated in Bend and checked by Bend's proof checker.
_Avoid_: property, spec, invariant

**Proof**:
The Bend code that the checker accepts as evidence that a law holds.
_Avoid_: test, verification

**Parse outcome**:
One of three results from parsing the input received so far: **Need more**, **Rejected** (with a reason) or **Parsed** (a request plus the leftover input).
_Avoid_: parse result, status

**Leftover input**:
The input after the end of a parsed request, which belongs to the next request on the same connection.
_Avoid_: remainder, rest, tail

**Rejection**:
A refusal to interpret input that is malformed or could be read more than one way.
_Avoid_: error, failure, invalid request
