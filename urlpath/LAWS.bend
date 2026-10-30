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


# parse examples (the cases from the urlpath research, ticket 02)

# Case 1: "/" is one empty segment
law parse_root:
    {Path.parse(Path.bytes("/")) == Done{[[]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 1: a path must start with "/"
law parse_not_absolute:
    {Path.parse(Path.bytes("a/b")) == Fail{Path.NotAbsolute{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 1: an empty path is not absolute
law parse_empty:
    {Path.parse(Path.bytes("")) == Fail{Path.NotAbsolute{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 2: a raw space is not allowed
law parse_space:
    {Path.parse(Path.bytes("/a b")) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 3: "#" never reaches the path
law parse_fragment:
    {Path.parse(Path.bytes("/a#b")) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 4: "%" needs two hex digits
law parse_bad_percent:
    {Path.parse(Path.bytes("/a%2")) == Fail{Path.BadPercent{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Cases 5 and 6: either hex case, "%41" is "A"
law parse_hex_case:
    {Path.parse(Path.bytes("/%2e%41")) == Done{[[46, 65]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 7: literal dot segments are removed
law parse_dots:
    {Path.parse(Path.bytes("/a/./b/../c")) == Done{[[97], [99]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 7: ".." above the root is rejected
law parse_above_root:
    {Path.parse(Path.bytes("/../a")) == Fail{Path.AboveRoot{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 8: "%2e%2e" is rejected, not treated as ".."
law parse_encoded_dotdot:
    {Path.parse(Path.bytes("/%2e%2e/a")) == Fail{Path.EncodedDotSegment{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 8: mixed ".%2E" too
law parse_mixed_dotdot:
    {Path.parse(Path.bytes("/a/.%2E")) == Fail{Path.EncodedDotSegment{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 9: "%2F" is rejected
law parse_encoded_slash:
    {Path.parse(Path.bytes("/a%2Fb")) == Fail{Path.EncodedSlash{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 10: a raw backslash is not allowed
law parse_raw_backslash:
    {Path.parse(Path.bytes("/a\\b")) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 10: "%5C" is rejected
law parse_encoded_backslash:
    {Path.parse(Path.bytes("/a%5cb")) == Fail{Path.EncodedBackslash{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 11: "%00" is rejected
law parse_nul:
    {Path.parse(Path.bytes("/a%00")) == Fail{Path.ControlByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 11: "%7F" is rejected
law parse_del:
    {Path.parse(Path.bytes("/a%7F")) == Fail{Path.ControlByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 12: "%252e" decodes once, to the text "%2e"
law parse_double_encoding:
    {Path.parse(Path.bytes("/%252e")) == Done{[[37, 50, 101]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 13: overlong UTF-8 stays two opaque bytes, never "."
law parse_overlong:
    {Path.parse(Path.bytes("/%c0%ae")) == Done{[[192, 174]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 14: "//" is rejected
law parse_double_slash:
    {Path.parse(Path.bytes("//a")) == Fail{Path.EmptySegment{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 14: an empty segment in the middle is rejected
law parse_inner_empty:
    {Path.parse(Path.bytes("/a//b")) == Fail{Path.EmptySegment{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 15: "..;" is rejected (Tomcat bug)
law parse_dotdot_semi:
    {Path.parse(Path.bytes("/a/..;/b")) == Fail{Path.DotSemicolonSegment{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 15: other ";" parameters are kept as text
law parse_semi_param:
    {Path.parse(Path.bytes("/a;x=1/b")) == Done{[[97, 59, 120, 61, 49], [98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 17: a trailing slash is a final empty segment
law parse_trailing:
    {Path.parse(Path.bytes("/a/")) == Done{[[97], []]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 17: a final ".." keeps the trailing slash
law parse_trailing_dotdot:
    {Path.parse(Path.bytes("/a/b/..")) == Done{[[97], []]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 18: "%3F" is a plain "?" inside a segment
law parse_encoded_query:
    {Path.parse(Path.bytes("/a%3Fb")) == Done{[[97, 63, 98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 19: letter case is kept
law parse_case_kept:
    {Path.parse(Path.bytes("/A/b")) == Done{[[65], [98]]} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Byte 300 isn't a byte
law parse_not_a_byte:
    {Path.parse([47, 300]) == Fail{Path.NotAByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}

# Case 2: a raw byte above 127 is not allowed
law parse_high_byte:
    {Path.parse([47, 200]) == Fail{Path.InvalidByte{}} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}


# U1: an accepted path started with "/"
law accepts_only_absolute:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
    {Path.starts_with_slash(b) == True{} : Bool}

# U2: no segment of an accepted path is "." or ".."
law no_dot_segments:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
    {Path.no_dot_segs(p) == True{} : Bool}

# U3: no segment of an accepted path contains "/", "\" or a control byte
law no_unsafe_bytes:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
    {Path.all_safe(p) == True{} : Bool}

# U4: an accepted path has at least one segment, and only the last may be empty
law empty_only_last:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Path.PathError, List<&2, List<&2, U32>>>}
    {Path.empty_only_last(p) == True{} : Bool}
