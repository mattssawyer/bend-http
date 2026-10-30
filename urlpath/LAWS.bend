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
