# Comparing paths segment by segment.

import Base


# Are two segments the same bytes?
def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a:
    case Nil{}:
        List.is_empty(&2, U32, b)
    case Con{+x, at}:
        match b:
          case Nil{}:
              False{}
          case Con{+y, bt}:
              U32.is_eq(x, y) && bytes_eq(at, bt)

# Are a's segments the first segments of b? Compared segment by segment,
# so /static is not a prefix of /static../x
def is_prefix(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Bool:
  match a:
    case Nil{}:
        True{}
    case Con{x, ar}:
        match b:
          case Nil{}:
              False{}
          case Con{y, br}:
              bytes_eq(x, y) && is_prefix(ar, br)
