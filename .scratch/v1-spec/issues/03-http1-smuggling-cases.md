# Which request-smuggling and parsing attacks must http1 reject?

Type: research
Status: open
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

From RFC 9112 and published research (e.g. PortSwigger request smuggling, the 'HTTP Garden' differential-fuzzing work, CVEs in llhttp, nginx, Apache, Go net/http), list every input pattern known to make two HTTP/1.1 parsers disagree: Content-Length / Transfer-Encoding conflicts, duplicate or malformed headers, whitespace and line-ending tricks, chunk-size edge cases, obsolete line folding, oversized fields. For each, give what RFC 9112 requires and which rejection http1 should give. Also note the common header-size and header-count limits in major servers.
