# Which standard rules and known attacks must urlpath handle?

Type: research
Status: resolved
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

Collect the rules for URL paths in an HTTP request target: RFC 3986 syntax, percent-encoding, and dot-segment removal (section 5.2.4); RFC 9112 request-target forms. Collect known path-traversal and normalisation bugs in real servers (encoded `%2e%2e`, `%2f`, `%00`, double encoding, backslashes, overlong UTF-8, empty segments), and how established libraries treat each one. Output: a numbered list of cases, each with the standard's answer and what major servers do.

## Answer

Full findings: branch `research/urlpath-rules-and-attacks`, file `.scratch/v1-spec/research/02-urlpath-rules-and-attacks.md` (commit ff466ff; not merged). 20 cases with the standard's answer, what nginx, Apache, Go, Node/WHATWG, Python, IIS and Tomcat do, and a suggested treatment.

- Order (RFC 3986 §2.4, §7.3): split off the query, split into segments, decode once, then check the decoded result. Invalid targets get 400, never a silent repair (RFC 9112 §3.2).
- Equivalence: `%xx` hex case doesn't matter; encoded unreserved characters (incl. `%2E`) equal the plain character; `%2F` is not `/`; §5.2.4 dot-segment removal clamps `..` at the root.
- Real bugs come from decoding at the wrong point, decoding twice, or two layers disagreeing (Apache CVE-2021-41773/42013, IIS MS00-078/MS01-026, Tomcat `..;/`, Jetty CVE-2021-28164).
- Best model: Jakarta Servlet 6.0 §3.5.2, whose 80-row example table could become a test set.
- Seven candidate laws (decode exactly once; no decoded `.`/`..` segment; idempotent normalisation; output never starts with `//`; …).
- Open decisions: `..` above the root (reject vs clamp); encoded dot segments; `%2F`/`%5C`; empty segments; `.;`/`..;`; when to check UTF-8.
