// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The operands the A1 gate CANNOT compare, pinned and named.**
//!
//! Added 2026-08-19 by the operand-completeness audit, which asked of every
//! instruction form the ten chained bodies contain: which slots does the
//! artifact PRINT, and which does the gate READ? Most of the answers were
//! "all of them". Four were not, and they split into two kinds:
//!
//! * **Parser holes** — the slot exists on both sides and neither parser read
//!   it. Two of these: `load`'s type and `extractfield`'s type. Both are now
//!   lanes (`load_tys`, `extract_tys`), and closing the first one turned the
//!   flagship chain RED, because `ir_h2_b0` loads `ir_tLevel` (`IRTy.enum_ 0`)
//!   where the artifact loads `enum.13`.
//! * **Model holes** — the slot is printed by the artifact and the Clean side
//!   has NOWHERE to put it, or the reverse. A lane cannot close these: there is
//!   nothing on the other side to compare against. This file exists so they are
//!   at least VISIBLE, checked against the registered inductives rather than
//!   asserted in a comment, and pinned so a change in the artifact shows up as
//!   a failing test instead of as nothing at all.
//!
//! ## Mutation coverage of the two new lanes — what is measured, and what is not
//!
//! `lane_matrix.rs` records `scripts/crystal_lane_matrix_battery.sh` at
//! **164/164, 0 blind** (`7093bb0b7`). That number predates this audit and does
//! not cover `load_tys` or `extract_tys`. The script now carries six more rows
//! — three artifact and three spec, for `load_tys`, `load_tys_volatile` and
//! `extract_tys` on the flagship — and **they have not been run**: the battery
//! is a long serial job that this commit did not execute. Quoting "170/170"
//! would be reporting a number nobody measured, which is the one thing a
//! coverage denominator must never do.
//!
//! What IS measured about `load_tys` is stronger than a mutation row, because
//! the mutation was already in the tree: adding the lane took
//! `has_cubical_layer::proved_module_matches_the_emitted_artifact` from passing
//! to `LOAD TYPE lane differs: emitted {0: [(2, "enum13", false)]} vs Clean
//! {0: [(2, "enum0", false)]}` — 68 passed, 1 failed — and it went green again
//! only when the registered module was corrected. `extract_tys` has no such
//! evidence: it agreed on all ten chains, so until the battery runs, "it is
//! compared" rests on reading `assert_lanes`.
//!
//! **A model hole is not a smaller problem than a parser hole.** It is the same
//! silent agreement one level down: `ir_ty_is_agg_enum_any` proves
//! `ir_ty_is_agg (IRTy.enum_ n) = true` for EVERY `n`, which is a kernel-checked
//! statement that Clean's model is blind where the artifact is not. For a gate
//! whose whole claim is "the proved module is the emitted module", that is
//! evidence about the model, not a licence to stop comparing.

use super::*;

/// Every chained fixture's BLOCK PARAMETER TYPES, pinned on the emitted side —
/// because the Clean side has no slot to compare them against.
///
/// `bb4(%1: bool):` prints an id AND a type (`trust-ir/src/display.rs:548`).
/// `header_param_ids` reads the ids; `block_params` compares them. The type is
/// dropped, and it CANNOT be otherwise: `IRBlock.mk : Nat -> IRList Nat ->
/// IRList IRNode -> IRBlock` and `IRFunc.mk : Nat -> IRList Nat -> Nat ->
/// IRList IRBlock -> IRFunc` both carry parameters as a bare list of ids.
/// `ir_bind_params` binds values to ids and never consults a type.
///
/// So this pins the artifact side alone. It proves nothing about the
/// registered module — it makes a change in the emitted parameter types show up
/// HERE, named, instead of being absorbed by a gate that never looked.
const PARAM_TYPES: &[(&str, &str)] = &[
    ("has_cubical_layer", "bb0(%0: ptr) bb4(%1: bool)"),
    ("level_kind_ord", "bb0(%0: ptr) bb6(%1: u8)"),
    ("from_source_system", "bb0(%0: enum.175) bb13(%1: enum.13)"),
    (
        "flat_flags_contains",
        "bb0(%0: struct.1012, %1: struct.1012)",
    ),
    (
        "bvar_in_range",
        "bb0(%0: u32, %1: u32, %2: u32) bb3(%3: bool) bb6(%4: bool)",
    ),
    ("is_valid_char", "bb0(%0: u64) bb3(%1: bool) bb6(%2: bool)"),
    ("expr_path_step_clone", "bb0(%0: ptr) bb12(%1: enum.181)"),
    ("float_div", "bb0(%0: ptr, %1: f64, %2: f64)"),
    ("get_char_val_trunc", "bb0(%0: (), %1: u64)"),
    ("meta_tag_shl", ""),
];

/// The emitted block headers of one fixture, as `bbN(params)` joined by spaces.
fn header_signature(text: &str) -> String {
    text.lines()
        .map(str::trim)
        .filter(|l| l.starts_with("bb") && l.ends_with("):"))
        .map(|l| l.trim_end_matches(':').to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn block_parameter_types_are_pinned_on_the_emitted_side_only() {
    for (who, sig) in PARAM_TYPES {
        let fx = CHAIN_FIXTURES
            .iter()
            .find(|(w, _)| w == who)
            .map(|(_, f)| *f)
            .unwrap_or_else(|| panic!("{who} has no fixture in CHAIN_FIXTURES"));
        assert_eq!(
            &header_signature(&fixture(fx)),
            sig,
            "{who}: the emitted BLOCK PARAMETER list changed. The ids are compared by \
             `block_params` and `assert_entry_params`; the TYPES are compared by NOTHING, \
             because `IRBlock.mk` carries parameters as `IRList Nat` and has no type slot. This \
             pin is the only place a change in them is visible at all."
        );
    }
}

/// The model hole above, checked against the registered inductives instead of
/// asserted in prose.
///
/// If `IRBlock` or `IRFunc` ever GAINS a parameter-type slot, this fails — and
/// the correct response is to add the lane, not to update the string.
#[test]
fn the_clean_block_and_func_shapes_really_have_no_parameter_type_slot() {
    let syntax = spec_source("eval_ir_syntax.rs");
    assert!(
        syntax.contains("| mk : Nat → IRList Nat → IRList IRNode → IRBlock"),
        "IRBlock's shape moved. Its parameter list was `IRList Nat` — ids with no types — which \
         is WHY the emitted `%1: bool` type is uncompared. If it now carries types, delete this \
         test and add the lane."
    );
    assert!(
        syntax.contains("| mk : Nat → IRList Nat → Nat → IRList IRBlock → IRFunc"),
        "IRFunc's shape moved; see the IRBlock assertion above."
    );
}

/// **A slot the CLEAN side has and the artifact does not print.** The reverse
/// direction of the same hole, and the only one in that direction.
///
/// `IRInst.switch : Nat → Nat → IRList Nat → IRList IRSwitchCase → Bool` ends
/// in `exhaustive_enum_unreachable`. trust-ir carries the same flag
/// (`Inst::Switch { .., exhaustive_enum_unreachable }`) but its `Display`
/// matches with `..` and never prints it (`display.rs:827`), so the emitted
/// text does not contain the fact. It is therefore un-comparable in this gate
/// in principle, not by omission — and the registered modules assert it by
/// hand: `ir_h2_b0` claims `Bool.true`.
///
/// The flag licenses nothing in `ir_exec` (`IRInst.switch v dflt dargs cases
/// exh => ir_switch_exec m s (ir_getd s v) dflt dargs cases` — `exh` is bound
/// and dropped), which is what makes the gap survivable. It is named here so
/// nobody reads a green A1 row as covering it.
#[test]
fn the_switch_exhaustiveness_flag_is_uncomparable_and_says_so() {
    let syntax = spec_source("eval_ir_syntax.rs");
    assert!(
        syntax.contains("| switch : Nat → Nat → IRList Nat → IRList IRSwitchCase → Bool → IRInst"),
        "IRInst.switch's shape moved; the flag this test is about is its last operand."
    );
    let machine = spec_source("eval_ir_machine.rs");
    assert!(
        machine.contains(
            "IRInst.switch v dflt dargs cases exh => ir_switch_exec m s (ir_getd s v) dflt dargs \
             cases"
        ),
        "the machine's switch arm moved. It binds `exh` and does not use it, which is the reason \
         a flag the emitted text cannot express is survivable here."
    );
    for (who, fx) in CHAIN_FIXTURES {
        assert!(
            !fixture(fx).contains("exhaustive"),
            "{who}: the emitted text now mentions exhaustiveness. It did not before, which is \
             why the flag was uncomparable; if trust prints it now, compare it."
        );
    }
}

/// **The one registered type alias that reaches NO instruction, gated at last.**
///
/// `ir_fc_tflags : IRTy := IRTy.struct_ 1012` is registered by
/// `eval_ir_contains.rs` and its own description says what it is for: "struct.1012,
/// the struct id the emitted body names in `bb0(%0: struct.1012, %1: struct.1012)`.
/// Transcribed for fidelity". It appears in no `IRInst` — `ir_fc_b0`'s three
/// extractfields are all at `ir_tU8` — so no lane in `Cfg` can ever reach it,
/// and until this test its value was compared by nothing at all.
///
/// It is the block-parameter-type model hole with a registered counterpart, so
/// unlike the other nine chains it CAN be checked: not through the `Cfg`
/// comparison, which has no slot for it, but directly against the fixture's own
/// block header. A fidelity transcription with no gate on it is a number
/// somebody wrote down once, which is the condition this whole gate exists to
/// end.
#[test]
fn the_dead_parameter_type_alias_is_pinned_against_the_fixture() {
    let src = spec_source("eval_ir_contains.rs");
    let decl = src
        .lines()
        .find(|l| l.contains("def ir_fc_tflags : IRTy :="))
        .unwrap_or_else(|| panic!("ir_fc_tflags must still be declared in eval_ir_contains.rs"));
    assert!(
        decl.contains("IRTy.struct_ 1012"),
        "ir_fc_tflags's declaration moved: {decl}"
    );
    let header = fixture("flat_flags_contains.trust-ir.txt")
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("bb0("))
        .map(str::to_string)
        .expect("the emitted body must declare an entry block with parameters");
    assert_eq!(
        header, "bb0(%0: struct.1012, %1: struct.1012):",
        "the emitted PARAMETER TYPE of FlatFlags::contains moved. `ir_fc_tflags` was transcribed          from exactly this header and reaches no instruction, so nothing else in this gate — not          one lane of `Cfg` — would have noticed."
    );
}

/// One `who -> fixture` table, so the two pins above cannot name a chain the
/// gate does not run.
const CHAIN_FIXTURES: &[(&str, &str)] = &[
    ("has_cubical_layer", "has_cubical_layer.trust-ir.txt"),
    ("level_kind_ord", "level_kind_ord.trust-ir.txt"),
    ("from_source_system", "from_source_system.trust-ir.txt"),
    ("flat_flags_contains", "flat_flags_contains.trust-ir.txt"),
    ("bvar_in_range", "bvar_in_range.trust-ir.txt"),
    ("is_valid_char", "is_valid_char.trust-ir.txt"),
    ("expr_path_step_clone", "expr_path_step_clone.trust-ir.txt"),
    ("float_div", "float_div.trust-ir.txt"),
    ("get_char_val_trunc", "get_char_val_trunc.trust-ir.txt"),
    ("meta_tag_shl", "meta_tag_shl.trust-ir.txt"),
];

/// The `PARAM_TYPES` table must cover exactly the chains the gate runs, for the
/// same reason `lane_matrix.rs`'s matrix must: a pin that silently omits a
/// chain is a pin nobody notices the absence of.
#[test]
fn the_pins_cover_exactly_the_chained_bodies() {
    let pinned: BTreeSet<&str> = PARAM_TYPES.iter().map(|(w, _)| *w).collect();
    let chained: BTreeSet<&str> = CHAIN_FIXTURES.iter().map(|(w, _)| *w).collect();
    assert_eq!(
        pinned, chained,
        "the block-parameter-type pins and the chained bodies must be the same set"
    );
}
