# What does an http1 request contain, and what size limits apply?

Type: grilling
Status: open
Blocked by: 03, 05
Map: [bend-http v1 spec](../map.md)

## Question

Decide the request type (method, target, version, headers, body) and how headers are stored (order kept? duplicates? case?). Decide limits on request-line length, header count, header size and body size, and whether callers can configure them. Decide the list of rejection reasons.
