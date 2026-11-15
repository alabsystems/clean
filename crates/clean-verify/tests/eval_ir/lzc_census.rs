// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `ir_lzc` chain's declaration census — the producer for a number the
//! status page would otherwise have to be told.
//!
//! `docs/CRYSTAL_STATUS.md` and the decision memo have carried "59
//! declarations" for link 4 since 2026-08-26 (`fc350b9c4`), and the 2026-09-07
//! crystal audit found that figure matched no static count of anything: the
//! standing rule it violated is *no claim-bearing value is typed where a
//! producer exists*. `eval_ir_lzb_declaration_census_is_pinned`
//! (in the parent module) is the producer for the `ir_lzb` half; this is the
//! producer for the chain that is meant to replace it.

use std::collections::BTreeSet;

use clean_verify::test_utils::build_eval_ir_spec_with_stack;

/// Every `ir_lzc` and `ir_lad` name the `EvalIr` bundle registers, counted.
///
/// The filter is `ir_lzc` OR `ir_lad`: the deref's own body is minted under the
/// `ir_lad` prefix that the tag table's `extra_bodies` lane declares, so a
/// census reading only the chain name would silently stop counting two of the
/// sixteen minted definitions.
///
/// `ir_lzb`'s count is asserted here too, and that is why the two are in one
/// test. This chain RE-MINTS function 0 under new names; the thing that must
/// not happen is a declaration migrating out of the frozen `ir_lzb` / `ir_lz`
/// half into the new one with nobody noticing.
///
/// The number is not a target. It is here so the docs can quote something a
/// command re-derives.
#[test]
fn eval_ir_lzc_declaration_census_is_pinned() {
    let spec = build_eval_ir_spec_with_stack();
    let names: BTreeSet<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_lzc") || n.starts_with("ir_lad"))
        .collect();
    assert_eq!(
        names.len(),
        33,
        "the EvalIr bundle's `ir_lzc` / `ir_lad` declarations moved. Update the number \
         rather than the assertion, and say where it moved. Registered: {names:?}"
    );
    for required in [
        "ir_lzc_module",
        "ir_lzc_func",
        "ir_lzc_g0",
        "ir_lad_func",
        "ir_lzc_func0_is_the_lz_mint",
        "ir_lzc_func1_is_the_minted_deref",
        "ir_lzc_callee2_is_a_declaration",
        "ir_lzc_callee3_is_a_declaration",
        "ir_lzc_global_is_declared",
        "ir_lzc_globaladdr_evals",
        "ir_lzc_g0_cell",
        "ir_lzc_init_mem",
        "ir_lzc_global_shadows_cell_zero",
        "ir_lzc_global_shadows_only_cell_zero",
        "ir_lzc_on_zero",
        "ir_lzc_on_succ",
        "ir_lzc_on_param",
        "ir_lzc_on_max_stuck_in_deref",
        "ir_lzc_on_imax_stuck_in_deref",
        "ir_lzc_max_running_at_8",
        "ir_lzc_max_stuck_at_9",
    ] {
        assert!(
            names.contains(required),
            "{required} must be registered by the EvalIr bundle"
        );
    }
    let lzb: BTreeSet<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_lzb"))
        .collect();
    assert_eq!(
        lzb.len(),
        30,
        "the ir_lzb census must be UNCHANGED by the ir_lzc chain: {lzb:?}"
    );
}
