# Which request-smuggling and parsing attacks must http1 reject?

Type: research
Status: resolved
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

From RFC 9112 and published research (e.g. PortSwigger request smuggling, the 'HTTP Garden' differential-fuzzing work, CVEs in llhttp, nginx, Apache, Go net/http), list every input pattern known to make two HTTP/1.1 parsers disagree: Content-Length / Transfer-Encoding conflicts, duplicate or malformed headers, whitespace and line-ending tricks, chunk-size edge cases, obsolete line folding, oversized fields. For each, give what RFC 9112 requires and which rejection http1 should give. Also note the common header-size and header-count limits in major servers.

## Answer

Full findings: branch `research/http1-smuggling-cases`, file `.scratch/v1-spec/research/03-http1-smuggling-cases.md` (commit 3c2dc12; not merged). 43 cases in 8 groups (line endings/raw bytes, request line, header lines, body framing, chunked bodies, Host, Expect, default limits), each with its RFC 9112/9110 section and the rejection to give; about 33 suggested rejection reasons mapped to status codes; a limits table for nginx, Apache, Node, Go, h11 and HAProxy.

Two rules cover every case: a rejection ends the connection (leftover input is never parsed), and body length comes only from Content-Length and Transfer-Encoding.

Open questions for a grilling ticket: `Transfer-Encoding: ,chunked`; leading zeros in Content-Length; absolute-form target vs Host; leading empty lines; HTTP/1.2–1.9; whitespace before `;` in chunk extensions; CONNECT support; how the parse outcome signals `100-continue`.
