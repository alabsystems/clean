#!/usr/bin/env bash
# THE LANE-COMPLETENESS MATRIX, PROVED BY MUTATION.
#
# The A1 CFG gate (`crates/clean-verify/tests/crystal_a1_lineage/emitted_cfg.rs`)
# grew lane by lane, each added by whichever chain needed it, and each time the
# author re-checked the earlier chains by hand. Nobody had verified
# SYSTEMATICALLY that every chain is compared on every lane its body exercises.
# The two precedents say that is where the holes are:
#
#   * a cast was in NO lane, so a cast-only body parsed to an ENTIRELY EMPTY Cfg
#     on both sides and two empty CFGs compare EQUAL;
#   * until the `rets` lane landed, NOTHING had ever looked at what a body
#     returns.
#
# READING A MATRIX IS NOT PROVING IT. A cell is "genuinely compared" only if
# mutating that lane's content in the fixture makes the gate go RED. This script
# does exactly that, cell by cell: mutate, require FAIL with a message that names
# the lane, revert, require PASS.
#
# The gates read the fixtures and the spec sources from disk at RUNTIME
# (CARGO_MANIFEST_DIR), so the compiled test binary is driven directly — a
# perturbation is a file edit, no rebuild is involved.
#
# THE RULE INHERITED FROM THE FIVE EARLIER BATTERIES: a FAILED SUBSTITUTION IS
# FATAL. An ambiguous anchor once let 32 cases of the eighth chain's battery run
# against a still-mutated tree, so an anchor that does not match exactly one line
# aborts here instead of quietly making a mutated run look green.
#
# Usage:
#   CRYSTAL_BIN=<compiled crystal_a1_lineage test binary> scripts/crystal_lane_matrix_battery.sh
set -uo pipefail
OUT="$(mktemp)"; TREE="$(mktemp -d)"; trap 'rm -rf "$OUT" "$TREE"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"
FIX="$REPO/crates/clean-verify/tests/fixtures"
SPEC="$REPO/crates/clean-verify/src/spec/core_spec"

pass=0; fail=0; cross=0

# Substitute inside ONE line of a fixture. `\n` in the replacement becomes a real
# newline, which is how the `blocks` lane is perturbed (append an empty block).
# A silent no-substitution would make a MUTATED run look green, so an anchor that
# does not match exactly one line — or matches twice within it — is FATAL.
sub() { python3 - "$1" "$2" "$3" <<'PY'
import sys
p, a, b = sys.argv[1], sys.argv[2], sys.argv[3].replace("\\n", "\n")
lines = open(p).read().split("\n")
# In a spec .rs file the anchor must land on a DECLARATION line. Prose in the
# surrounding doc comments quotes these terms verbatim, and matching one of
# those would mutate a comment and leave the module untouched — a green run
# against an unmutated tree, which is the false negative this script exists to
# rule out.
decl_only = p.endswith(".rs")
hits = [i for i, l in enumerate(lines)
        if a in l and (not decl_only or l.startswith("const SRC_"))]
assert len(hits) == 1, "anchor must match exactly one line, matched %d: %s" % (len(hits), a[:80])
i = hits[0]
assert lines[i].count(a) == 1, "anchor not unique within its line: %s" % a[:80]
lines[i] = lines[i].replace(a, b, 1)
open(p, "w").write("\n".join(lines))
PY
  rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "FATAL: substitution failed in $1 ($2). Every case after this one would run against an"
    echo "       unchanged or still-mutated tree and mean nothing. Aborting."
    exit 2
  fi
}

# chain|test|lane|fixture|anchor|replacement
#
# Each row perturbs ONE lane and leaves every other lane bit-identical, which is
# the design rule the lane set is built on: if the row's token appears, the lane
# is genuinely compared on that chain.
TABLE=$(cat <<'ROWS'
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|blocks|has_cubical_layer.trust-ir.txt|ret %1|ret %1\nbb99:
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|consts|has_cubical_layer.trust-ir.txt|const bool false|const bool true
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|cases|has_cubical_layer.trust-ir.txt|2: bb1|5: bb1
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|default|has_cubical_layer.trust-ir.txt|default: bb3|default: bb2
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|branches|has_cubical_layer.trust-ir.txt|br bb4(%4)|br bb2(%4)
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|param_blocks|has_cubical_layer.trust-ir.txt|bb4(%1: bool):|bb4:
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|extracts|has_cubical_layer.trust-ir.txt|extractfield u8 %2, 0|extractfield u8 %2, 1
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|loads|has_cubical_layer.trust-ir.txt|load enum.13, ptr %0|load enum.13, ptr %1
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|rets|has_cubical_layer.trust-ir.txt|ret %1|ret %0
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|const_tys|has_cubical_layer.trust-ir.txt|%4 = const bool true|%9 = const bool true
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|edge_args|has_cubical_layer.trust-ir.txt|br bb4(%5)|br bb4(%4)
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|block_params|has_cubical_layer.trust-ir.txt|bb4(%1: bool):|bb4(%9: bool):
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|switch_on|has_cubical_layer.trust-ir.txt|switch %3 [|switch %2 [
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|entry_params|has_cubical_layer.trust-ir.txt|bb0(%0: ptr):|bb0(%9: ptr):
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|blocks|level_kind_ord.trust-ir.txt|ret %1|ret %1\nbb99:
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|int_consts|level_kind_ord.trust-ir.txt|const u8 3|const u8 7
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|cases|level_kind_ord.trust-ir.txt|0: bb1|7: bb1
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|default|level_kind_ord.trust-ir.txt|default: bb5|default: bb4
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|branches|level_kind_ord.trust-ir.txt|br bb6(%4)|br bb1(%4)
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|param_blocks|level_kind_ord.trust-ir.txt|bb6(%1: u8):|bb6:
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|extracts|level_kind_ord.trust-ir.txt|extractfield u8 %2, 0|extractfield u8 %2, 1
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|loads|level_kind_ord.trust-ir.txt|load enum.2, ptr %0|load enum.2, ptr %1
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|rets|level_kind_ord.trust-ir.txt|ret %1|ret %0
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|const_tys|level_kind_ord.trust-ir.txt|const u8 0|const u32 0
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|edge_args|level_kind_ord.trust-ir.txt|br bb6(%5)|br bb6(%4)
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|block_params|level_kind_ord.trust-ir.txt|bb6(%1: u8):|bb6(%9: u8):
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|switch_on|level_kind_ord.trust-ir.txt|switch %3 [|switch %2 [
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|entry_params|level_kind_ord.trust-ir.txt|bb0(%0: ptr):|bb0(%9: ptr):
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|blocks|from_source_system.trust-ir.txt|ret %1|ret %1\nbb99:
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|agg_consts|from_source_system.trust-ir.txt|const enum.13 { 2 }|const enum.13 { 7 }
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|cases|from_source_system.trust-ir.txt|0: bb1|7: bb1
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|default|from_source_system.trust-ir.txt|default: bb12|default: bb11
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|branches|from_source_system.trust-ir.txt|br bb13(%3)|br bb1(%3)
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|param_blocks|from_source_system.trust-ir.txt|bb13(%1: enum.13):|bb13:
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|extracts|from_source_system.trust-ir.txt|extractfield u8 %0, 0|extractfield u8 %0, 1
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|rets|from_source_system.trust-ir.txt|ret %1|ret %0
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|const_tys|from_source_system.trust-ir.txt|%3 = const enum.13 { 0 }|%9 = const enum.13 { 0 }
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|edge_args|from_source_system.trust-ir.txt|br bb13(%4)|br bb13(%3)
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|block_params|from_source_system.trust-ir.txt|bb13(%1: enum.13):|bb13(%9: enum.13):
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|switch_on|from_source_system.trust-ir.txt|switch %2 [|switch %0 [
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|entry_params|from_source_system.trust-ir.txt|bb0(%0: enum.175):|bb0(%9: enum.175):
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|blocks|flat_flags_contains.trust-ir.txt|ret %6|ret %6\nbb99:
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|extracts|flat_flags_contains.trust-ir.txt|extractfield u8 %0, 0|extractfield u8 %0, 1
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|icmps|flat_flags_contains.trust-ir.txt|icmp eq u8 %4, %5|icmp eq u8 %5, %4
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|binops|flat_flags_contains.trust-ir.txt|and u8 %2, %3|and u8 %3, %2
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|binop_tys|flat_flags_contains.trust-ir.txt|and u8|and u16
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|icmp_tys|flat_flags_contains.trust-ir.txt|icmp eq u8|icmp eq u16
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|rets|flat_flags_contains.trust-ir.txt|ret %6|ret %0
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|entry_params|flat_flags_contains.trust-ir.txt|bb0(%0: struct.1012, %1: struct.1012):|bb0(%0: struct.1012, %9: struct.1012):
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|blocks|bvar_in_range.trust-ir.txt|ret %3|ret %3\nbb99:
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|consts|bvar_in_range.trust-ir.txt|const bool false|const bool true
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|int_consts|bvar_in_range.trust-ir.txt|const u32 4294967295|const u32 4294967294
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|branches|bvar_in_range.trust-ir.txt|br bb3(%7)|br bb6(%7)
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|param_blocks|bvar_in_range.trust-ir.txt|bb3(%3: bool):|bb3:
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|icmps|bvar_in_range.trust-ir.txt|%7 = icmp uge u32 %0, %1|%7 = icmp uge u32 %1, %0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|condbrs|bvar_in_range.trust-ir.txt|condbr %6, bb1, bb2|condbr %6, bb2, bb1
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|icmp_tys|bvar_in_range.trust-ir.txt|icmp eq u32|icmp eq u16
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|rets|bvar_in_range.trust-ir.txt|ret %3|ret %0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|const_tys|bvar_in_range.trust-ir.txt|const u32 4294967295|const u64 4294967295
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|edge_args|bvar_in_range.trust-ir.txt|br bb6(%9)|br bb6(%10)
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|block_params|bvar_in_range.trust-ir.txt|bb6(%4: bool):|bb6(%9: bool):
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|entry_params|bvar_in_range.trust-ir.txt|bb0(%0: u32, %1: u32, %2: u32):|bb0(%0: u32, %1: u32, %9: u32):
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|blocks|is_valid_char.trust-ir.txt|ret %1|ret %1\nbb99:
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|consts|is_valid_char.trust-ir.txt|const bool false|const bool true
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|int_consts|is_valid_char.trust-ir.txt|const u64 55296|const u64 55295
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|branches|is_valid_char.trust-ir.txt|br bb3(%7)|br bb6(%7)
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|param_blocks|is_valid_char.trust-ir.txt|bb3(%1: bool):|bb3:
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|icmps|is_valid_char.trust-ir.txt|icmp ult u64 %5, %0|icmp ult u64 %0, %5
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|condbrs|is_valid_char.trust-ir.txt|condbr %4, bb2, bb1|condbr %4, bb1, bb2
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|icmp_tys|is_valid_char.trust-ir.txt|icmp ult u64 %0, %3|icmp ult u32 %0, %3
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|rets|is_valid_char.trust-ir.txt|ret %1|ret %0
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|const_tys|is_valid_char.trust-ir.txt|const u64 55296|const u32 55296
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|edge_args|is_valid_char.trust-ir.txt|br bb6(%9)|br bb6(%10)
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|block_params|is_valid_char.trust-ir.txt|bb6(%2: bool):|bb6(%9: bool):
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|entry_params|is_valid_char.trust-ir.txt|bb0(%0: u64):|bb0(%9: u64):
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|blocks|expr_path_step_clone.trust-ir.txt|ret %1|ret %1\nbb99:
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|consts|expr_path_step_clone.trust-ir.txt|%4 = const enum.181 { 0 }|%4 = const enum.181 { 0 }\n    %90 = const bool true
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|agg_consts|expr_path_step_clone.trust-ir.txt|const enum.181 { 2 }|const enum.181 { 7 }
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|cases|expr_path_step_clone.trust-ir.txt|0: bb1|7: bb1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|default|expr_path_step_clone.trust-ir.txt|default: bb11|default: bb10
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|branches|expr_path_step_clone.trust-ir.txt|br bb12(%4)|br bb1(%4)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|param_blocks|expr_path_step_clone.trust-ir.txt|bb12(%1: enum.181):|bb12:
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|extracts|expr_path_step_clone.trust-ir.txt|extractfield u8 %2, 0|extractfield u8 %2, 1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|loads|expr_path_step_clone.trust-ir.txt|load enum.181, ptr %0|load enum.181, ptr %1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|rets|expr_path_step_clone.trust-ir.txt|ret %1|ret %0
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|const_tys|expr_path_step_clone.trust-ir.txt|%4 = const enum.181 { 0 }|%9 = const enum.181 { 0 }
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|edge_args|expr_path_step_clone.trust-ir.txt|br bb12(%5)|br bb12(%4)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|block_params|expr_path_step_clone.trust-ir.txt|bb12(%1: enum.181):|bb12(%9: enum.181):
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|switch_on|expr_path_step_clone.trust-ir.txt|switch %3 [|switch %2 [
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|entry_params|expr_path_step_clone.trust-ir.txt|bb0(%0: ptr):|bb0(%9: ptr):
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|blocks|float_div.trust-ir.txt|ret %3|ret %3\nbb99:
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|binops|float_div.trust-ir.txt|fdiv f64 %1, %2|fdiv f64 %2, %1
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|binop_tys|float_div.trust-ir.txt|fdiv f64|fdiv f32
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|rets|float_div.trust-ir.txt|ret %3|ret %1
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|entry_params|float_div.trust-ir.txt|bb0(%0: ptr, %1: f64, %2: f64):|bb0(%0: ptr, %1: f64, %9: f64):
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|blocks|get_char_val_trunc.trust-ir.txt|ret %2|ret %2\nbb99:
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|casts|get_char_val_trunc.trust-ir.txt|trunc u64 %1 to u32|trunc u64 %0 to u32
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|cast_tys|get_char_val_trunc.trust-ir.txt|to u32|to u16
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|rets|get_char_val_trunc.trust-ir.txt|ret %2|ret %1
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|entry_params|get_char_val_trunc.trust-ir.txt|bb0(%0: (), %1: u64):|bb0(%0: (), %9: u64):
ROWS
)

# THE SPEC PASS. Same cells, mutated on the CLEAN side — the hand-transcribed
# module, which is the side that actually drifts. A chain's own coverage
# denominators read `emitted` only, so they cannot fire here: a RED in this pass
# is necessarily a CROSS-SIDE lane comparison, which is what "the cell is
# compared" means.
#
# chain|test|lane|core_spec file|anchor|replacement
SPEC_TABLE=$(cat <<'ROWS'
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|blocks|eval_ir_mode.rs|IRBlock.mk ir_d3 ir_nl0|IRBlock.mk ir_d7 ir_nl0
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_mode.rs|IRBlock.mk ir_d4 (ir_nl1 ir_d1)|IRBlock.mk ir_d4 ir_nl0
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|entry_params|eval_ir_mode.rs|IRFunc.mk ir_d0 (ir_nl1 ir_d0)|IRFunc.mk ir_d0 (ir_nl1 ir_d9)
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|blocks|eval_ir_kind_ord.rs|IRBlock.mk ir_d5 ir_nl0|IRBlock.mk ir_d9 ir_nl0
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|cases|eval_ir_kind_ord.rs|ir_sc ir_d0 ir_d1|ir_sc ir_d7 ir_d1
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|default|eval_ir_kind_ord.rs|IRInst.switch ir_d3 ir_d5|IRInst.switch ir_d3 ir_d4
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_kind_ord.rs|IRBlock.mk ir_d6 (ir_nl1 ir_d1)|IRBlock.mk ir_d6 ir_nl0
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_kind_ord.rs|IRFunc.mk ir_d0 (ir_nl1 ir_d0)|IRFunc.mk ir_d0 (ir_nl1 ir_d9)
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|blocks|eval_ir_from_source.rs|IRBlock.mk ir_d12 ir_nl0|IRBlock.mk ir_d99 ir_nl0
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|agg_consts|eval_ir_from_source.rs|ir_cvar ir_d2|ir_cvar ir_d7
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|cases|eval_ir_from_source.rs|ir_sc ir_d0 ir_d1|ir_sc ir_d7 ir_d1
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|default|eval_ir_from_source.rs|IRInst.switch ir_d2 ir_d12|IRInst.switch ir_d2 ir_d11
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_from_source.rs|IRBlock.mk ir_d13 (ir_nl1 ir_d1)|IRBlock.mk ir_d13 ir_nl0
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_from_source.rs|IRFunc.mk ir_d0 (ir_nl1 ir_d0)|IRFunc.mk ir_d0 (ir_nl1 ir_d9)
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|blocks|eval_ir_contains.rs|IRBlock.mk ir_d0 ir_nl0|IRBlock.mk ir_d9 ir_nl0
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|extracts|eval_ir_contains.rs|ir_tU8 ir_d0 ir_d0|ir_tU8 ir_d0 ir_d1
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|icmps|eval_ir_contains.rs|IRICmpOp.eq_ ir_tU8 ir_d4 ir_d5|IRICmpOp.eq_ ir_tU8 ir_d5 ir_d4
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|binops|eval_ir_contains.rs|IRBinOp.and_ ir_tU8 ir_d2 ir_d3|IRBinOp.and_ ir_tU8 ir_d3 ir_d2
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_contains.rs|IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1)|IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d9)
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|blocks|eval_ir_bvar_range.rs|IRBlock.mk ir_d5 ir_nl0|IRBlock.mk ir_d9 ir_nl0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|consts|eval_ir_bvar_range.rs|IRConst.bool_ Bool.false|IRConst.bool_ Bool.true
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|int_consts|eval_ir_bvar_range.rs|IRConst.int_ 4294967295|IRConst.int_ 4294967294
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|branches|eval_ir_bvar_range.rs|IRInst.br ir_d3 (ir_nl1 ir_d7)|IRInst.br ir_d6 (ir_nl1 ir_d7)
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_bvar_range.rs|IRBlock.mk ir_d3 (ir_nl1 ir_d3)|IRBlock.mk ir_d3 ir_nl0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|icmps|eval_ir_bvar_range.rs|IRICmpOp.ult ir_br_tu32 ir_d0 ir_d2|IRICmpOp.ult ir_br_tu32 ir_d2 ir_d0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|condbrs|eval_ir_bvar_range.rs|IRInst.condbr ir_d6 ir_d1 ir_nl0 ir_d2 ir_nl0|IRInst.condbr ir_d6 ir_d2 ir_nl0 ir_d1 ir_nl0
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_bvar_range.rs|IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2)|IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d9)
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|blocks|eval_ir_valid_char.rs|IRBlock.mk ir_d5 ir_nl0|IRBlock.mk ir_d9 ir_nl0
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|consts|eval_ir_valid_char.rs|IRConst.bool_ Bool.false|IRConst.bool_ Bool.true
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|int_consts|eval_ir_valid_char.rs|IRConst.int_ 55296|IRConst.int_ 55295
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|branches|eval_ir_valid_char.rs|IRInst.br ir_d3 (ir_nl1 ir_d7)|IRInst.br ir_d6 (ir_nl1 ir_d7)
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_valid_char.rs|IRBlock.mk ir_d3 (ir_nl1 ir_d1)|IRBlock.mk ir_d3 ir_nl0
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|icmps|eval_ir_valid_char.rs|IRICmpOp.ult ir_vc_tu64 ir_d5 ir_d0|IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d5
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|condbrs|eval_ir_valid_char.rs|IRInst.condbr ir_d4 ir_d2 ir_nl0 ir_d1 ir_nl0|IRInst.condbr ir_d4 ir_d1 ir_nl0 ir_d2 ir_nl0
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_valid_char.rs|IRFunc.mk ir_d0 (ir_nl1 ir_d0)|IRFunc.mk ir_d0 (ir_nl1 ir_d9)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|blocks|eval_ir_path_step.rs|IRBlock.mk ir_d11 ir_nl0|IRBlock.mk ir_d99 ir_nl0
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|consts|eval_ir_path_step.rs|ir_bd2 (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d0)) ir_d4)|ir_bd3 (ir_nd1 (IRInst.const_ IRTy.bool_ (IRConst.bool_ Bool.true)) ir_d90) (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d0)) ir_d4)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|agg_consts|eval_ir_path_step.rs|ir_cvar ir_d2|ir_cvar ir_d7
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|cases|eval_ir_path_step.rs|ir_sc ir_d0 ir_d1|ir_sc ir_d7 ir_d1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|default|eval_ir_path_step.rs|IRInst.switch ir_d3 ir_d11|IRInst.switch ir_d3 ir_d10
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|branches|eval_ir_path_step.rs|IRInst.br ir_d12 (ir_nl1 ir_d4)|IRInst.br ir_d1 (ir_nl1 ir_d4)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|param_blocks|eval_ir_path_step.rs|IRBlock.mk ir_d12 (ir_nl1 ir_d1)|IRBlock.mk ir_d12 ir_nl0
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|extracts|eval_ir_path_step.rs|IRInst.extractfield ir_tU8 ir_d2 ir_d0|IRInst.extractfield ir_tU8 ir_d2 ir_d1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|loads|eval_ir_path_step.rs|IRInst.load ir_ep_tstep ir_d0|IRInst.load ir_ep_tstep ir_d1
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_path_step.rs|IRFunc.mk ir_d0 (ir_nl1 ir_d0)|IRFunc.mk ir_d0 (ir_nl1 ir_d9)
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|blocks|eval_ir_float_div.rs|IRBlock.mk ir_d0 ir_nl0|IRBlock.mk ir_d9 ir_nl0
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|binops|eval_ir_float_div.rs|IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2|IRBinOp.fdiv ir_fd_tf64 ir_d2 ir_d1
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|binop_tys|eval_ir_float_div.rs|IRBinOp.fdiv ir_fd_tf64 ir_d1|IRBinOp.fdiv ir_tU8 ir_d1
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|rets|eval_ir_float_div.rs|IRInst.ret (ir_nl1 ir_d3)|IRInst.ret (ir_nl1 ir_d1)
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_float_div.rs|IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2)|IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d9)
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|blocks|eval_ir_trunc.rs|IRBlock.mk ir_d0 ir_nl0|IRBlock.mk ir_d9 ir_nl0
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|casts|eval_ir_trunc.rs|IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1|IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d0
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|cast_tys|eval_ir_trunc.rs|IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32|IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_tU8
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|rets|eval_ir_trunc.rs|IRInst.ret (ir_nl1 ir_d2)|IRInst.ret (ir_nl1 ir_d1)
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|entry_params|eval_ir_trunc.rs|IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1)|IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d9)
has_cubical_layer|has_cubical_layer::proved_module_matches_the_emitted_artifact|order|eval_ir_mode.rs|(ir_nd1 (IRInst.load ir_tLevel ir_d0 Bool.false) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3)|(ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3) (ir_nd1 (IRInst.load ir_tLevel ir_d0 Bool.false) ir_d2)
level_kind_ord|level_kind_ord::kind_ord_proved_module_matches_the_emitted_artifact|order|eval_ir_kind_ord.rs|(ir_nd1 (IRInst.load ir_ko_tenum ir_d0 Bool.false) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3)|(ir_nd1 (IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3) (ir_nd1 (IRInst.load ir_ko_tenum ir_d0 Bool.false) ir_d2)
from_source_system|from_source_system::from_source_system_proved_module_matches_the_emitted_artifact|order|eval_ir_from_source.rs|(ir_nd1 (IRInst.const_ ir_fs_tmode (ir_cvar ir_d0)) ir_d3) (ir_nd (IRInst.br ir_d13 (ir_nl1 ir_d3)))|(ir_nd (IRInst.br ir_d13 (ir_nl1 ir_d3))) (ir_nd1 (IRInst.const_ ir_fs_tmode (ir_cvar ir_d0)) ir_d3)
flat_flags_contains|flat_flags_contains::flat_flags_contains_proved_module_matches_the_emitted_artifact|order|eval_ir_contains.rs|(ir_nd1 (IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3) ir_d4) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d5)|(ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d5) (ir_nd1 (IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3) ir_d4)
bvar_in_range|bvar_in_range::bvar_in_range_proved_module_matches_the_emitted_artifact|order|eval_ir_bvar_range.rs|(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 4294967295)) ir_d5) (ir_nd1 (IRInst.icmp IRICmpOp.eq_ ir_br_tu32 ir_d2 ir_d5) ir_d6)|(ir_nd1 (IRInst.icmp IRICmpOp.eq_ ir_br_tu32 ir_d2 ir_d5) ir_d6) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 4294967295)) ir_d5)
is_valid_char|is_valid_char::is_valid_char_proved_module_matches_the_emitted_artifact|order|eval_ir_valid_char.rs|(ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 55296)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d3) ir_d4)|(ir_nd1 (IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d3) ir_d4) (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 55296)) ir_d3)
expr_path_step_clone|expr_path_step_clone::expr_path_step_clone_proved_module_matches_the_emitted_artifact|order|eval_ir_path_step.rs|(ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d0)) ir_d4) (ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d4)))|(ir_nd (IRInst.br ir_d12 (ir_nl1 ir_d4))) (ir_nd1 (IRInst.const_ ir_ep_tstep (ir_cvar ir_d0)) ir_d4)
float_div|float_div::float_div_proved_module_matches_the_emitted_artifact|order|eval_ir_float_div.rs|(ir_nd1 (IRInst.binop IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3)))|(ir_nd (IRInst.ret (ir_nl1 ir_d3))) (ir_nd1 (IRInst.binop IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2) ir_d3)
get_char_val_trunc|get_char_val_trunc::get_char_val_trunc_proved_module_matches_the_emitted_artifact|order|eval_ir_trunc.rs|(ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2)))|(ir_nd (IRInst.ret (ir_nl1 ir_d2))) (ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2)
ROWS
)

run() { "$BIN" "$1" --exact --test-threads=1 >"$OUT" 2>&1; }
reason() { awk '/panicked at/{f=1} f{print}' "$OUT" | head -3; }

# drive <table> <"fixture"|"spec">
#
# A row is `chain|test|lane|file|anchor|replacement`. `file` is relative to the
# fixture directory in the artifact pass and to `core_spec` in the spec pass.
drive() {
  local table="$1" side="$2" root
  [[ "$side" == fixture ]] && root="$FIX" || root="$SPEC"
  while IFS='|' read -r chain test lane file anchor repl; do
    [[ -z "${chain:-}" ]] && continue
    local f="$root/$file"
    cp "$f" "$TREE/orig"
    sub "$f" "$anchor" "$repl"
    if cmp -s "$f" "$TREE/orig"; then
      echo "FATAL: $chain/$lane — the file is unchanged after substitution. Aborting."
      exit 2
    fi
    run "$test"; local rc=$?
    if [[ $rc -eq 0 ]]; then
      echo "BLIND    [$side] $chain / $lane — MUTATED and the gate stayed GREEN"
      fail=$((fail+1))
    elif [[ "$side" == spec ]] || grep -q "vs Clean" "$OUT"; then
      # In the SPEC pass the emitted side is untouched, so every emitted-only
      # denominator passes by construction and a RED can only come from a
      # comparison that read BOTH sides. In the artifact pass the message has to
      # say so itself.
      echo "CROSS    [$side] $chain / $lane :: $(reason | sed -n 2p | cut -c1-88)"
      pass=$((pass+1))
      [[ "$side" == spec ]] && cross=$((cross+1))
    else
      # An emitted-side coverage denominator caught it first. That is a RED, but
      # it does not by itself prove the lane is compared AGAINST CLEAN — which is
      # exactly what the spec pass supplies for the same cell.
      echo "DENOM    [$side] $chain / $lane :: $(reason | sed -n 2p | cut -c1-88)"
      pass=$((pass+1))
    fi
    cp "$TREE/orig" "$f"
    run "$test"; rc=$?
    if [[ $rc -ne 0 ]]; then
      echo "FATAL: $chain/$lane — the REVERTED tree does not pass. Aborting before the next case"
      echo "       runs against it (the failure mode that cost the eighth chain's battery 32 cases)."
      reason
      exit 2
    fi
  done <<<"$table"
}

echo "=== PASS A — mutate the EMITTED ARTIFACT (the fixture) ==="
drive "$TABLE" fixture
echo
echo "=== PASS B — mutate the HAND-TRANSCRIBED CLEAN MODULE (the spec source) ==="
echo "    The emitted side is untouched here, so every emitted-only denominator"
echo "    passes and a RED can only come from a CROSS-SIDE lane comparison."
drive "$SPEC_TABLE" spec
echo
echo "cells proved RED: $pass ; not proved: $fail ; cross-side proofs from the spec pass: $cross"
[[ $fail -eq 0 ]]
