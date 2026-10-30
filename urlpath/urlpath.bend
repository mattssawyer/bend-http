# A byte-based implementation of the URL path parser.
# parse is defined here; the pieces it uses are in src/.
# Author: Matthew Sawyer
# Last Updated: 2026-10-30
# Version: 1.0.0

import Base
import ./src/errors.bend as Error
import ./src/bytes.bend as Byte
import ./src/split.bend as Split
import ./src/dots.bend as Dots
import ./src/check.bend as Check
import ./src/render.bend as Render
import ./src/prefix.bend as Prefix


# Last step: remove "." and ".." from the checked segments
def parse.dots(r: Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match r:
    case Fail{e}:
        Fail{e}
    case Done{ds}:
        Dots.remove_dots(ds)

# The path must start with "/". t is everything after it.
def parse.slash(slash: Bool, t: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match slash:
    case True{}:
        parse.dots(Check.check_all(Split.split(t)))
    case False{}:
        Fail{Error.NotAbsolute{}}

# An empty path doesn't start with "/" either
def parse.first(raw: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match raw:
    case Nil{}:
        Fail{Error.NotAbsolute{}}
    case Con{+c, t}:
        parse.slash(U32.is_eq(c, 47), t)

# First check every element is a byte (0-255)
def parse.bytes(ok: Bool, raw: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  match ok:
    case True{}:
        parse.first(raw)
    case False{}:
        Fail{Error.NotAByte{}}

# Turn the raw path of a request ("/a/b%20c") into its decoded segments,
# or say why it's rejected. In order: every element must be a byte, the path
# must start with "/", it's split on "/", each segment is decoded once and
# checked, and then "." and ".." are removed.
def parse(+raw: List<&2, U32>) -> Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>:
  parse.bytes(Byte.all_bytes(raw), raw)


# The other public functions, so users only need this file.
# PathError lives in src/errors.bend.

# The bytes of an ASCII string: "GET" -> [71, 69, 84]
def bytes(s: String) -> List<&2, U32>:
  Byte.bytes(s)

# Turn segments back into a path. See src/render.bend.
def render(p: List<&2, List<&2, U32>>) -> List<&2, U32>:
  Render.render(p)

# Are a's segments the first segments of b? See src/prefix.bend.
def is_prefix(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Bool:
  Prefix.is_prefix(a, b)
