# Proofs of every law in LAWS.bend. The helper lemmas are in proof/.

import Base
import ./LAWS.bend as Laws
import ./src/bytes.bend as Byte
import ./proof/request_line.bend as LineProof


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

