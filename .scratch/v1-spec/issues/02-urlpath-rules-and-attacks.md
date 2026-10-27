# Which standard rules and known attacks must urlpath handle?

Type: research
Status: open
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

Collect the rules for URL paths in an HTTP request target: RFC 3986 syntax, percent-encoding, and dot-segment removal (section 5.2.4); RFC 9112 request-target forms. Collect known path-traversal and normalisation bugs in real servers (encoded `%2e%2e`, `%2f`, `%00`, double encoding, backslashes, overlong UTF-8, empty segments), and how established libraries treat each one. Output: a numbered list of cases, each with the standard's answer and what major servers do.
