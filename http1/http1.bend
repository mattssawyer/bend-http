# An HTTP/1.1 request parser and response writer that work on bytes.
# Author: Matthew Sawyer
# Last Updated: 2026-11-03
# Version: 1.0.0
#
# The pieces are in src/. The types are in src/request.bend, the outcome in
# src/parse.bend, the rejection reasons in src/reason.bend and responses in
# src/response.bend.

import Base
import ./src/reason.bend as Reason
import ./src/request.bend as Req
import ./src/request_line.bend as Line
import ./src/limits.bend as Limits
import ./src/head.bend as Head
import ./src/parse.bend as Parse
import ./src/response.bend as Resp


# Parse a request line, without its CRLF: "GET /a?x HTTP/1.1"
def request_line(line: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  Line.request_line(line)

# The status to send for a rejection
def status(r: Reason.Reason) -> U32:
  Reason.status(r)

# The default limits: 8 KiB lines, 64 KiB head, 100 fields, 1 MiB body
def default_limits() -> Limits.Limits:
  Limits.default_limits()

# Read the head of a request (request line and fields) from raw bytes
def head(limits: Limits.Limits, input: List<&2, U32>) -> Head.HeadResult:
  Head.head(limits, input)

# Parse one request from everything received on the connection that hasn't
# been used yet. After Parsed, call parse again on the leftover.
def parse(limits: Limits.Limits, input: List<&2, U32>) -> Parse.Outcome:
  Parse.parse(limits, input)

# Check the parts of a response: status 100-599, field names that are
# tokens, values with no CR, LF or NUL, no Content-Length or
# Transfer-Encoding (write adds Content-Length), no body on 1xx, 204, 205
# or 304, and a body of bytes
def response(s: U32, headers: List<&2, Req.Field>, body: List<&2, U32>) -> Result<&2, &2, Resp.ResponseError, Resp.Response>:
  Resp.response(s, headers, body)

# The bytes to send for a response
def write(r: Resp.Response) -> List<&2, U32>:
  Resp.write(r)

# The head write would send, without the body: the answer to a HEAD request
def write_head(r: Resp.Response) -> List<&2, U32>:
  Resp.write_head(r)
