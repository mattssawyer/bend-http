# What does http1 offer that bend-kit-http doesn't?

Type: grilling
Status: open
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

`bend-kit-http` (paymog) already ships an HTTP/1.1 and HTTP/2 client and an HTTP/1.1 server, with 209 laws. Almost all are single examples (one specific request is rejected); about 20 quantify over anything, and then only over the bytes after the headers. Decide http1's distinct claim, e.g. every law holds for all inputs ("every request with both Content-Length and Transfer-Encoding is rejected"), a parser small enough to audit, and a public law list mapped to RFC 9112 sections and the smuggling cases. Decide whether to read bend-kit-http's LAWS.bend as a baseline and whether to compare against it on a shared set of tricky requests. This claim is what the README and a resume line would say.
