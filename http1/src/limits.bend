# Size limits, so a client can't make the parser wait forever or hold
# unlimited memory. Going over a limit is a rejection, never a truncation.

import Base


# request_line: bytes in the request line (without CRLF)
# field_line:   bytes in one field line (without CRLF)
# header_section: bytes in the request line and all field lines, CRLFs included
# fields:       number of field lines
# body:         bytes in the body
# chunk_ext:    bytes of chunk extensions in one chunk
type Limits is Data:
  Limits{request_line: U32, field_line: U32, header_section: U32, fields: U32, body: U32, chunk_ext: U32}

def default_limits() -> Limits:
  Limits{8192, 8192, 65536, 100, 1048576, 1024}
