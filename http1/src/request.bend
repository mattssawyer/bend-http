# The parts of a request.

import Base


type Version is Data:
  Http10{}
  Http11{}

type Scheme is Data:
  Http{}
  Https{}

# The request target. path is the decoded segments from urlpath; query is
# the raw bytes after "?", not decoded.
type Target is Data:
  Origin{path: List<&2, List<&2, U32>>, query: Maybe<&2, List<&2, U32>>}
  Absolute{scheme: Scheme, authority: List<&2, U32>, path: List<&2, List<&2, U32>>, query: Maybe<&2, List<&2, U32>>}
  Asterisk{}

# "GET /a?x HTTP/1.1". The method is kept as sent: methods are case-sensitive.
type RequestLine is Data:
  RequestLine{method: List<&2, U32>, target: Target, version: Version}

# One header field: the name as sent, and the value with spaces and tabs
# trimmed from both ends
type Field is Data:
  Field{name: List<&2, U32>, value: List<&2, U32>}
