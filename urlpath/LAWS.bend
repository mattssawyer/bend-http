import Base
import ./urlpath.bend as Path

# Bytes function
law bytes_get: 
    {Path.bytes("GET") == [71, 69, 84] : List<&2, U32>}

law bytes_post: 
    {Path.bytes("POST") == [80, 79, 83, 84] : List<&2, U32>}

law bytes_put: 
    {Path.bytes("PUT") == [80, 85, 84] : List<&2, U32>}

law bytes_delete: 
    {Path.bytes("DELETE") == [68, 69, 76, 69, 84, 69] : List<&2, U32>}


# Digit function
law digit_7: 
    {Path.is_digit(55) == True{} : Bool}

law digit_A: 
    {Path.is_digit(65) == False{} : Bool}


# Alpha function
law alpha_A: 
    {Path.is_alpha(65) == True{} : Bool}

law alpha_7: 
    {Path.is_alpha(55) == False{} : Bool}


# Hex function
law hex_A: 
    {Path.is_hex(65) == True{} : Bool}

law hex_N: 
    {Path.is_hex(78) == False{} : Bool}


# Unreserved function
law unreserved_A: 
    {Path.is_unreserved(65) == True{} : Bool}

law unreserved_7: 
    {Path.is_unreserved(55) == True{} : Bool}

law unreserved_bang: 
    {Path.is_unreserved(33) == False{} : Bool}



# Sub-delim function
law sub_delim_bang: 
    {Path.is_sub_delim(33) == True{} : Bool}

law sub_delim_qmark: 
    {Path.is_sub_delim(63) == False{} : Bool}



# Pchar function
law pchar_A: 
    {Path.is_pchar(65) == True{} : Bool}

law pchar_7: 
    {Path.is_pchar(55) == True{} : Bool}

law pchar_qmark: 
    {Path.is_pchar(63) == False{} : Bool}

law pchar_slash: 
    {Path.is_pchar(47) == False{} : Bool}

law pchar_mod: 
    {Path.is_pchar(37) == False{} : Bool}


# Split function
law split_empty:
    {Path.split([]) == [[]] : List<&2, List<&2, U32>>}

law split_root:
    {Path.split([47]) == [[], []] : List<&2, List<&2, U32>>}

law split_ab:
    {Path.split([47, 97, 47, 98]) == [[], [97], [98]] : List<&2, List<&2, U32>>}

law split_trailing:
    {Path.split([47, 97, 47]) == [[], [97], []] : List<&2, List<&2, U32>>}


# Join function
law join_ab:
    {Path.join([[], [97], [98]]) == [47, 97, 47, 98] : List<&2, U32>}


# Round trip: joining a split gives back the original bytes
law join_split:
    for b: List<&2, U32>
    {Path.join(Path.split(b)) == b : List<&2, U32>}


# Decode function (one segment)
law decode_plain_abc:
    {Path.decode(Path.bytes("abc")) == Done{[97, 98, 99]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_empty:
    {Path.decode([]) == Done{[]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_upper:
    {Path.decode(Path.bytes("%41")) == Done{[65]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_lower:
    {Path.decode(Path.bytes("%2f")) == Done{[47]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_once:
    {Path.decode(Path.bytes("%2541")) == Done{[37, 52, 49]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_utf8:
    {Path.decode(Path.bytes("%C3%A9")) == Done{[195, 169]} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_bad_hex:
    {Path.decode(Path.bytes("%G1")) == Fail{Path.BadPercent{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_short:
    {Path.decode(Path.bytes("a%4")) == Fail{Path.BadPercent{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_lone_pct:
    {Path.decode(Path.bytes("%")) == Fail{Path.BadPercent{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_space:
    {Path.decode(Path.bytes("a b")) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_high_byte:
    {Path.decode([200]) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}

law decode_first_error:
    {Path.decode(Path.bytes("a b%G1")) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, U32>>}


# Text with nothing to decode comes back unchanged
law decode_plain:
    for b: List<&2, U32>
    for e: {Path.all_pchar(b) == True{} : Bool}
    {Path.decode(b) == Done{b} : Result<&2, &2, Path.PathError, List<&2, U32>>}


# Dot-segment removal (segments here are already split and decoded)

# "/a/./b" becomes "/a/b"
law dots_single:
    {Path.remove_dots([[97], [46], [98]]) == Done{[[97], [98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/../b" becomes "/b"
law dots_parent:
    {Path.remove_dots([[97], [46, 46], [98]]) == Done{[[98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/b/.." becomes "/a/"
law dots_end_parent:
    {Path.remove_dots([[97], [98], [46, 46]]) == Done{[[97], []]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/b/." becomes "/a/b/"
law dots_end_single:
    {Path.remove_dots([[97], [98], [46]]) == Done{[[97], [98], []]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/." becomes "/"
law dots_root_single:
    {Path.remove_dots([[46]]) == Done{[[]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/.." becomes "/"
law dots_to_root:
    {Path.remove_dots([[97], [46, 46]]) == Done{[[]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/b" is unchanged
law dots_none:
    {Path.remove_dots([[97], [98]]) == Done{[[97], [98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# ".a", "..." and "..a" are ordinary names
law dots_lookalikes:
    {Path.remove_dots([[46, 97], [46, 46, 46], [46, 46, 97]]) == Done{[[46, 97], [46, 46, 46], [46, 46, 97]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/.." climbs above the root
law dots_above_root:
    {Path.remove_dots([[46, 46]]) == Fail{Path.AboveRoot{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/a/../.." climbs above the root
law dots_above_root_late:
    {Path.remove_dots([[97], [46, 46], [46, 46]]) == Fail{Path.AboveRoot{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# "/../a" climbs above the root
law dots_above_root_mid:
    {Path.remove_dots([[46, 46], [97]]) == Fail{Path.AboveRoot{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
