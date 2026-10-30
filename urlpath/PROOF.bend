# Proofs of every law in LAWS.bend. The helper lemmas are in proof/.

import Base
import ./LAWS.bend as Laws
import ./src/bytes.bend as Byte
import ./proof/split.bend as SplitProof
import ./proof/decode.bend as DecodeProof
import ./proof/parse.bend as ParseProof
import ./proof/prefix.bend as PrefixProof
import ./proof/render.bend as RenderProof


def Laws.bytes_get(): 
  {==}

def Laws.bytes_post(): 
  {==}

def Laws.bytes_put(): 
  {==}

def Laws.bytes_delete(): 
  {==}

def Laws.digit_7(): 
  {==}

def Laws.digit_A(): 
  {==}

def Laws.alpha_7(): 
  {==}

def Laws.alpha_A(): 
  {==}

def Laws.hex_A(): 
  {==}

def Laws.hex_N(): 
  {==}

def Laws.unreserved_A(): 
  {==}

def Laws.unreserved_7(): 
  {==}

def Laws.unreserved_bang(): 
  {==}

def Laws.sub_delim_bang(): 
  {==}

def Laws.sub_delim_qmark(): 
  {==}

def Laws.pchar_A(): 
  {==}

def Laws.pchar_7(): 
  {==}

def Laws.pchar_qmark(): 
  {==}

def Laws.pchar_slash(): 
  {==}

def Laws.pchar_mod(): 
  {==}

def Laws.split_empty():
  {==}

def Laws.split_root():
  {==}

def Laws.split_ab():
  {==}

def Laws.split_trailing():
  {==}

def Laws.join_ab():
  {==}

def Laws.decode_plain_abc():
  {==}

def Laws.decode_empty():
  {==}

def Laws.decode_upper():
  {==}

def Laws.decode_lower():
  {==}

def Laws.decode_once():
  {==}

def Laws.decode_utf8():
  {==}

def Laws.decode_bad_hex():
  {==}

def Laws.decode_short():
  {==}

def Laws.decode_lone_pct():
  {==}

def Laws.decode_space():
  {==}

def Laws.decode_high_byte():
  {==}

def Laws.decode_first_error():
  {==}

def Laws.dots_single():
  {==}

def Laws.dots_parent():
  {==}

def Laws.dots_end_parent():
  {==}

def Laws.dots_end_single():
  {==}

def Laws.dots_root_single():
  {==}

def Laws.dots_to_root():
  {==}

def Laws.dots_none():
  {==}

def Laws.dots_lookalikes():
  {==}

def Laws.dots_above_root():
  {==}

def Laws.dots_above_root_late():
  {==}

def Laws.dots_above_root_mid():
  {==}

def Laws.parse_root():
  {==}

def Laws.parse_not_absolute():
  {==}

def Laws.parse_empty():
  {==}

def Laws.parse_space():
  {==}

def Laws.parse_fragment():
  {==}

def Laws.parse_bad_percent():
  {==}

def Laws.parse_hex_case():
  {==}

def Laws.parse_dots():
  {==}

def Laws.parse_above_root():
  {==}

def Laws.parse_encoded_dotdot():
  {==}

def Laws.parse_mixed_dotdot():
  {==}

def Laws.parse_encoded_slash():
  {==}

def Laws.parse_raw_backslash():
  {==}

def Laws.parse_encoded_backslash():
  {==}

def Laws.parse_nul():
  {==}

def Laws.parse_del():
  {==}

def Laws.parse_double_encoding():
  {==}

def Laws.parse_overlong():
  {==}

def Laws.parse_double_slash():
  {==}

def Laws.parse_inner_empty():
  {==}

def Laws.parse_dotdot_semi():
  {==}

def Laws.parse_semi_param():
  {==}

def Laws.parse_trailing():
  {==}

def Laws.parse_trailing_dotdot():
  {==}

def Laws.parse_encoded_query():
  {==}

def Laws.parse_case_kept():
  {==}

def Laws.parse_not_a_byte():
  {==}

def Laws.parse_high_byte():
  {==}

def Laws.accepts_only_absolute(b, p, e):
  %e : ParseProof.U1ok(b, _)
  ParseProof.u1_bytes(Byte.all_bytes(b), b)

def Laws.no_dot_segments(b, p, e):
  %e : ParseProof.U2ok(_)
  ParseProof.u2_bytes(Byte.all_bytes(b), b)

def Laws.no_unsafe_bytes(b, p, e):
  %e : ParseProof.U3ok(_)
  ParseProof.u3_bytes(Byte.all_bytes(b), b)

def Laws.empty_only_last(b, p, e):
  %e : ParseProof.U4ok(_)
  ParseProof.u4_bytes(Byte.all_bytes(b), b)

def Laws.render_ab():
  {==}

def Laws.render_root():
  {==}

def Laws.render_trailing():
  {==}

def Laws.render_utf8():
  {==}

def Laws.render_percent():
  {==}

def Laws.render_slash():
  {==}

def Laws.render_keeps_pchar():
  {==}

def Laws.prefix_yes():
  {==}

def Laws.prefix_empty():
  {==}

def Laws.prefix_same():
  {==}

def Laws.prefix_segmentwise():
  {==}

def Laws.prefix_longer():
  {==}

def Laws.render_canonical(p):
  match p:
    case Nil{}:
      {==}
    case Con{+s, r}:
      RenderProof.cj(r, s)

def Laws.render_no_double_slash(b, p, e):
  RenderProof.no_double_slash(p, Laws.empty_only_last(b, p, e))

def Laws.idempotent(b, p, e):
  RenderProof.rt1(p, Laws.no_dot_segments(b, p, e), Laws.no_unsafe_bytes(b, p, e), Laws.empty_only_last(b, p, e), ParseProof.x_parse(b, p, e))

def Laws.join_split(b):
  SplitProof.join_split(b)

def Laws.decode_plain(b, e):
  DecodeProof.decode_plain(b, e)

def Laws.is_prefix_sound(a, b, h):
  PrefixProof.is_prefix_sound(a, b, h)
