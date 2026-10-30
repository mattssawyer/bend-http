# An HTTP/1.1 request parser that works on bytes.
# Author: Matthew Sawyer
# Last Updated: 2026-10-30
# Version: 1.0.0
#
# The pieces are in src/. The types are in src/request.bend and the
# rejection reasons in src/reason.bend.

import Base
import ./src/reason.bend as Reason
import ./src/request.bend as Req
import ./src/request_line.bend as Line


# Parse a request line, without its CRLF: "GET /a?x HTTP/1.1"
def request_line(line: List<&2, U32>) -> Result<&2, &2, Reason.Reason, Req.RequestLine>:
  Line.request_line(line)

# The status to send for a rejection
def status(r: Reason.Reason) -> U32:
  Reason.status(r)
