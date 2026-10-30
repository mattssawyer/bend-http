# Proofs of every law in LAWS.bend. The helper lemmas are in proof/.

import Base
import ./LAWS.bend as Laws
import ./src/bytes.bend as Byte
import ./proof/request_line.bend as LineProof
import ./src/head.bend as Head
import ./src/parse.bend as Parse
import ./proof/framing.bend as FrameProof
import ./proof/suffix.bend as SufProof


def Laws.line_root():
  {==}

def Laws.line_query():
  {==}

def Laws.line_asterisk():
  {==}

def Laws.line_asterisk_get():
  {==}

def Laws.line_absolute():
  {==}

def Laws.line_absolute_case():
  {==}

def Laws.line_absolute_query():
  {==}

def Laws.line_other_scheme():
  {==}

def Laws.line_empty_authority():
  {==}

def Laws.line_connect():
  {==}

def Laws.line_authority_form():
  {==}

def Laws.line_two_spaces():
  {==}

def Laws.line_tab():
  {==}

def Laws.line_trailing_space():
  {==}

def Laws.line_leading_space():
  {==}

def Laws.line_no_version():
  {==}

def Laws.line_space_in_target():
  {==}

def Laws.line_fragment():
  {==}

def Laws.line_bad_query():
  {==}

def Laws.line_above_root():
  {==}

def Laws.line_bad_method():
  {==}

def Laws.line_lowercase_method():
  {==}

def Laws.line_long_method():
  {==}

def Laws.line_version_10():
  {==}

def Laws.line_version_lower():
  {==}

def Laws.line_version_dot():
  {==}

def Laws.line_version_2():
  {==}

def Laws.line_version_12():
  {==}

def Laws.status_path():
  {==}

def Laws.status_long_method():
  {==}

def Laws.status_version():
  {==}

def Laws.method_ok(l, m, t, v, e):
  %e : LineProof.MOk(_)
  LineProof.mo_first(Byte.cut(l, 32))

def Laws.head_simple():
  {==}

def Laws.head_trim():
  {==}

def Laws.head_obs_text():
  {==}

def Laws.head_incomplete():
  {==}

def Laws.head_half_crlf():
  {==}

def Laws.head_leading_crlf():
  {==}

def Laws.head_two_leading_crlf():
  {==}

def Laws.head_bare_lf():
  {==}

def Laws.head_bare_cr():
  {==}

def Laws.head_bad_end():
  {==}

def Laws.head_not_a_byte():
  {==}

def Laws.head_nul():
  {==}

def Laws.head_del():
  {==}

def Laws.head_space_before_colon():
  {==}

def Laws.head_tab_before_colon():
  {==}

def Laws.head_space_first():
  {==}

def Laws.head_obs_fold():
  {==}

def Laws.head_no_colon():
  {==}

def Laws.head_empty_name():
  {==}

def Laws.head_control_name():
  {==}

def Laws.head_bad_request_line():
  {==}

def Laws.head_long_line():
  {==}

def Laws.head_long_field():
  {==}

def Laws.head_many_fields():
  {==}

def Laws.head_max_fields():
  {==}

def Laws.head_section():
  {==}


def Laws.parse_cl():
  {==}

def Laws.parse_cl_short():
  {==}

def Laws.parse_no_framing():
  {==}

def Laws.parse_cl_zero():
  {==}

def Laws.parse_cl_any_case():
  {==}

def Laws.parse_cl_te():
  {==}

def Laws.parse_te_http10():
  {==}

def Laws.parse_two_cl():
  {==}

def Laws.parse_cl_list():
  {==}

def Laws.parse_cl_empty():
  {==}

def Laws.parse_cl_plus():
  {==}

def Laws.parse_cl_hex():
  {==}

def Laws.parse_cl_space():
  {==}

def Laws.parse_cl_leading_zero():
  {==}

def Laws.parse_cl_eleven_digits():
  {==}

def Laws.parse_cl_overflow():
  {==}

def Laws.parse_cl_too_large():
  {==}

def Laws.cl_and_te_rejected(l, i, m, t, v, hs, body, rest, e):
  %e : FrameProof.P4(_)
  FrameProof.p4_head(Head.head(l, i), Parse.body_limit(l))

def Laws.one_content_length(l, i, m, t, v, hs, body, rest, e):
  %e : FrameProof.P5(_)
  FrameProof.p5_head(Head.head(l, i), Parse.body_limit(l))

def Laws.leftover_is_suffix(l, i, r, rest, e):
  %e : SufProof.PS(_, i)
  SufProof.ps_head(Head.head(l, i), i, Parse.body_limit(l), SufProof.hs_head(l, i))

