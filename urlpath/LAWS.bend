import Base
import ./urlpath.bend as Path
import ./src/errors.bend as Error
import ./src/bytes.bend as Byte
import ./src/split.bend as Split
import ./src/decode.bend as Decode
import ./src/dots.bend as Dots
import ./src/render.bend as Render
import ./src/prefix.bend as Prefix
import ./src/props.bend as Prop

# Bytes function
law bytes_get: 
    {Byte.bytes("GET") == [71, 69, 84] : List<&2, U32>}

law bytes_post: 
    {Byte.bytes("POST") == [80, 79, 83, 84] : List<&2, U32>}

law bytes_put: 
    {Byte.bytes("PUT") == [80, 85, 84] : List<&2, U32>}

law bytes_delete: 
    {Byte.bytes("DELETE") == [68, 69, 76, 69, 84, 69] : List<&2, U32>}


# Digit function
law digit_7: 
    {Byte.is_digit(55) == True{} : Bool}

law digit_A: 
    {Byte.is_digit(65) == False{} : Bool}


# Alpha function
law alpha_A: 
    {Byte.is_alpha(65) == True{} : Bool}

law alpha_7: 
    {Byte.is_alpha(55) == False{} : Bool}


# Hex function
law hex_A: 
    {Byte.is_hex(65) == True{} : Bool}

law hex_N: 
    {Byte.is_hex(78) == False{} : Bool}


# Unreserved function
law unreserved_A: 
    {Byte.is_unreserved(65) == True{} : Bool}

law unreserved_7: 
    {Byte.is_unreserved(55) == True{} : Bool}

law unreserved_bang: 
    {Byte.is_unreserved(33) == False{} : Bool}



# Sub-delim function
law sub_delim_bang: 
    {Byte.is_sub_delim(33) == True{} : Bool}

law sub_delim_qmark: 
    {Byte.is_sub_delim(63) == False{} : Bool}



# Pchar function
law pchar_A: 
    {Byte.is_pchar(65) == True{} : Bool}

law pchar_7: 
    {Byte.is_pchar(55) == True{} : Bool}

law pchar_qmark: 
    {Byte.is_pchar(63) == False{} : Bool}

law pchar_slash: 
    {Byte.is_pchar(47) == False{} : Bool}

law pchar_mod: 
    {Byte.is_pchar(37) == False{} : Bool}


# Split function
law split_empty:
    {Split.split([]) == [[]] : List<&2, List<&2, U32>>}

law split_root:
    {Split.split([47]) == [[], []] : List<&2, List<&2, U32>>}

law split_ab:
    {Split.split([47, 97, 47, 98]) == [[], [97], [98]] : List<&2, List<&2, U32>>}

law split_trailing:
    {Split.split([47, 97, 47]) == [[], [97], []] : List<&2, List<&2, U32>>}


# Join function
law join_ab:
    {Split.join([[], [97], [98]]) == [47, 97, 47, 98] : List<&2, U32>}


# Round trip: joining a split gives back the original bytes
law join_split:
    for b: List<&2, U32>
    {Split.join(Split.split(b)) == b : List<&2, U32>}


# Decode function (one segment)
law decode_plain_abc:
    {Decode.decode(Byte.bytes("abc")) == Done{[97, 98, 99]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_empty:
    {Decode.decode([]) == Done{[]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_upper:
    {Decode.decode(Byte.bytes("%41")) == Done{[65]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_lower:
    {Decode.decode(Byte.bytes("%2f")) == Done{[47]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_once:
    {Decode.decode(Byte.bytes("%2541")) == Done{[37, 52, 49]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_utf8:
    {Decode.decode(Byte.bytes("%C3%A9")) == Done{[195, 169]} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_bad_hex:
    {Decode.decode(Byte.bytes("%G1")) == Fail{Error.BadPercent{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_short:
    {Decode.decode(Byte.bytes("a%4")) == Fail{Error.BadPercent{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_lone_pct:
    {Decode.decode(Byte.bytes("%")) == Fail{Error.BadPercent{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_space:
    {Decode.decode(Byte.bytes("a b")) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_high_byte:
    {Decode.decode([200]) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}

law decode_first_error:
    {Decode.decode(Byte.bytes("a b%G1")) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, U32>>}


# Text with nothing to decode comes back unchanged
law decode_plain:
    for b: List<&2, U32>
    for e: {Byte.all_pchar(b) == True{} : Bool}
    {Decode.decode(b) == Done{b} : Result<&2, &2, Error.PathError, List<&2, U32>>}


# Dot-segment removal (segments here are already split and decoded)

# "/a/./b" becomes "/a/b"
law dots_single:
    {Dots.remove_dots([[97], [46], [98]]) == Done{[[97], [98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/../b" becomes "/b"
law dots_parent:
    {Dots.remove_dots([[97], [46, 46], [98]]) == Done{[[98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/b/.." becomes "/a/"
law dots_end_parent:
    {Dots.remove_dots([[97], [98], [46, 46]]) == Done{[[97], []]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/b/." becomes "/a/b/"
law dots_end_single:
    {Dots.remove_dots([[97], [98], [46]]) == Done{[[97], [98], []]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/." becomes "/"
law dots_root_single:
    {Dots.remove_dots([[46]]) == Done{[[]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/.." becomes "/"
law dots_to_root:
    {Dots.remove_dots([[97], [46, 46]]) == Done{[[]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/b" is unchanged
law dots_none:
    {Dots.remove_dots([[97], [98]]) == Done{[[97], [98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# ".a", "..." and "..a" are ordinary names
law dots_lookalikes:
    {Dots.remove_dots([[46, 97], [46, 46, 46], [46, 46, 97]]) == Done{[[46, 97], [46, 46, 46], [46, 46, 97]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/.." climbs above the root
law dots_above_root:
    {Dots.remove_dots([[46, 46]]) == Fail{Error.AboveRoot{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/a/../.." climbs above the root
law dots_above_root_late:
    {Dots.remove_dots([[97], [46, 46], [46, 46]]) == Fail{Error.AboveRoot{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "/../a" climbs above the root
law dots_above_root_mid:
    {Dots.remove_dots([[46, 46], [97]]) == Fail{Error.AboveRoot{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}


# parse examples: known path tricks and how each is handled

# "/" is one empty segment
law parse_root:
    {Path.parse(Byte.bytes("/")) == Done{[[]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a path must start with "/"
law parse_not_absolute:
    {Path.parse(Byte.bytes("a/b")) == Fail{Error.NotAbsolute{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# an empty path is not absolute
law parse_empty:
    {Path.parse(Byte.bytes("")) == Fail{Error.NotAbsolute{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a raw space is not allowed
law parse_space:
    {Path.parse(Byte.bytes("/a b")) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "#" never reaches the path
law parse_fragment:
    {Path.parse(Byte.bytes("/a#b")) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%" needs two hex digits
law parse_bad_percent:
    {Path.parse(Byte.bytes("/a%2")) == Fail{Error.BadPercent{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# either hex case, "%41" is "A"
law parse_hex_case:
    {Path.parse(Byte.bytes("/%2e%41")) == Done{[[46, 65]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# literal dot segments are removed
law parse_dots:
    {Path.parse(Byte.bytes("/a/./b/../c")) == Done{[[97], [99]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# ".." above the root is rejected
law parse_above_root:
    {Path.parse(Byte.bytes("/../a")) == Fail{Error.AboveRoot{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%2e%2e" is rejected, not treated as ".."
law parse_encoded_dotdot:
    {Path.parse(Byte.bytes("/%2e%2e/a")) == Fail{Error.EncodedDotSegment{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# mixed ".%2E" too
law parse_mixed_dotdot:
    {Path.parse(Byte.bytes("/a/.%2E")) == Fail{Error.EncodedDotSegment{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%2F" is rejected
law parse_encoded_slash:
    {Path.parse(Byte.bytes("/a%2Fb")) == Fail{Error.EncodedSlash{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a raw backslash is not allowed
law parse_raw_backslash:
    {Path.parse(Byte.bytes("/a\\b")) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%5C" is rejected
law parse_encoded_backslash:
    {Path.parse(Byte.bytes("/a%5cb")) == Fail{Error.EncodedBackslash{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%00" is rejected
law parse_nul:
    {Path.parse(Byte.bytes("/a%00")) == Fail{Error.ControlByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%7F" is rejected
law parse_del:
    {Path.parse(Byte.bytes("/a%7F")) == Fail{Error.ControlByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%252e" decodes once, to the text "%2e"
law parse_double_encoding:
    {Path.parse(Byte.bytes("/%252e")) == Done{[[37, 50, 101]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# overlong UTF-8 stays two opaque bytes, never "."
law parse_overlong:
    {Path.parse(Byte.bytes("/%c0%ae")) == Done{[[192, 174]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "//" is rejected
law parse_double_slash:
    {Path.parse(Byte.bytes("//a")) == Fail{Error.EmptySegment{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# an empty segment in the middle is rejected
law parse_inner_empty:
    {Path.parse(Byte.bytes("/a//b")) == Fail{Error.EmptySegment{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "..;" is rejected (Tomcat bug)
law parse_dotdot_semi:
    {Path.parse(Byte.bytes("/a/..;/b")) == Fail{Error.DotSemicolonSegment{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# other ";" parameters are kept as text
law parse_semi_param:
    {Path.parse(Byte.bytes("/a;x=1/b")) == Done{[[97, 59, 120, 61, 49], [98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a trailing slash is a final empty segment
law parse_trailing:
    {Path.parse(Byte.bytes("/a/")) == Done{[[97], []]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a final ".." keeps the trailing slash
law parse_trailing_dotdot:
    {Path.parse(Byte.bytes("/a/b/..")) == Done{[[97], []]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# "%3F" is a plain "?" inside a segment
law parse_encoded_query:
    {Path.parse(Byte.bytes("/a%3Fb")) == Done{[[97, 63, 98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# letter case is kept
law parse_case_kept:
    {Path.parse(Byte.bytes("/A/b")) == Done{[[65], [98]]} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# 300 isn't a byte
law parse_not_a_byte:
    {Path.parse([47, 300]) == Fail{Error.NotAByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# a raw byte above 127 is not allowed
law parse_high_byte:
    {Path.parse([47, 200]) == Fail{Error.InvalidByte{}} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}


# U1: an accepted path started with "/"
law accepts_only_absolute:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Prop.starts_with_slash(b) == True{} : Bool}

# U2: no segment of an accepted path is "." or ".."
law no_dot_segments:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Prop.no_dot_segs(p) == True{} : Bool}

# U3: no segment of an accepted path contains "/", "\" or a control byte
law no_unsafe_bytes:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Prop.all_safe(p) == True{} : Bool}

# U4: an accepted path has at least one segment, and only the last may be empty
law empty_only_last:
    for +b: List<&2, U32>
    for p: List<&2, List<&2, U32>>
    for e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Prop.empty_only_last(p) == True{} : Bool}


# render examples
law render_ab:
    {Render.render([[97], [98, 32]]) == Byte.bytes("/a/b%20") : List<&2, U32>}

law render_root:
    {Render.render([[]]) == Byte.bytes("/") : List<&2, U32>}

law render_trailing:
    {Render.render([[97], []]) == Byte.bytes("/a/") : List<&2, U32>}

law render_utf8:
    {Render.render([[195, 169]]) == Byte.bytes("/%C3%A9") : List<&2, U32>}

law render_percent:
    {Render.render([[37]]) == Byte.bytes("/%25") : List<&2, U32>}

law render_slash:
    {Render.render([[47]]) == Byte.bytes("/%2F") : List<&2, U32>}

law render_keeps_pchar:
    {Render.render([Byte.bytes("a:b@c!$&'()*+,;=-._~")]) == Byte.bytes("/a:b@c!$&'()*+,;=-._~") : List<&2, U32>}

# is_prefix examples
law prefix_yes:
    {Prefix.is_prefix([[97]], [[97], [98]]) == True{} : Bool}

law prefix_empty:
    {Prefix.is_prefix([], [[97]]) == True{} : Bool}

law prefix_same:
    {Prefix.is_prefix([[97], [98]], [[97], [98]]) == True{} : Bool}

# "/static" is not a prefix of "/static../x"
law prefix_segmentwise:
    {Prefix.is_prefix(Split.split(Byte.bytes("static")), [Byte.bytes("static.."), [120]]) == False{} : Bool}

law prefix_longer:
    {Prefix.is_prefix([[97], [98]], [[97]]) == False{} : Bool}


# U5: rendering an accepted path and parsing it again gives the same segments
law idempotent:
    for +b: List<&2, U32>
    for +p: List<&2, List<&2, U32>>
    for +e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Path.parse(Render.render(p)) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}

# U6: rendering an accepted path never starts with "//"
law render_no_double_slash:
    for +b: List<&2, U32>
    for +p: List<&2, List<&2, U32>>
    for +e: {Path.parse(b) == Done{p} : Result<&2, &2, Error.PathError, List<&2, List<&2, U32>>>}
    {Prop.starts_with_double_slash(Render.render(p)) == False{} : Bool}

# U7: every byte render writes is "/", a pchar, or part of an uppercase %XX
law render_canonical:
    for p: List<&2, List<&2, U32>>
    {Prop.canonical(Render.render(p)) == True{} : Bool}

# U8: if a is a prefix of b, then b is a followed by some more segments
law is_prefix_sound:
    for a: List<&2, List<&2, U32>>
    for +b: List<&2, List<&2, U32>>
    for +h: {Prefix.is_prefix(a, b) == True{} : Bool}
    exs rest: List<&2, List<&2, U32>>
    {b == List.append(&2, List<&2, U32>, a, rest) : List<&2, List<&2, U32>>}
