# Splitting bytes on "/" and joining segments back with "/".

import Base


# Add head to the linked list 
def add_head(head: U32, segs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>: 
  match segs: 
    case Nil{}:
        [[head]]
    case Con{first, rest}:
        Con{Con{head, first}, rest}

# Helper for split: start a new segment on "/", otherwise grow the first one
def split.if(+h: U32, rest: List<&2, List<&2, U32>>, slash: Bool) -> List<&2, List<&2, U32>>:
  match slash:
    case True{}:
        Con{Nil{}, rest}
    case False{}:
        add_head(h, rest)

# Split bytes on "/" (47). Always returns at least one segment.
# "/a/b" gives [[], [97], [98]]
def split(b: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match b:
    case Nil{}:
        [Nil{}]
    case Con{+h, t}:
        split.if(h, split(t), U32.is_eq(h, 47))

# Glue segments back together with "/" between them (undoes split)
def join(segs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match segs:
    case Nil{}:
        Nil{}
    case Con{s, Nil{}}:
        s
    case Con{s, r}:
        List.append(&2, U32, s, Con{47, join(r)})
