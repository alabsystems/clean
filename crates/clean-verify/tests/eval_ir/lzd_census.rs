// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `ir_lzd` chain's declaration census — the producer for a number the
//! status page would otherwise have to be told.
//!
//! Same rule as [`super::lzc_census`]: no claim-bearing value is typed where a
//! producer exists. This counts the EVALIR half only, and the scope is the
//! point rather than a shortcut. The chain deliberately straddles two bundles:
//! everything that needs only `Nat`/`Bool`/`Eq`, the IR types and `Level`
//! itself — the module, its step and view equations, the freshness substrate,
//! the forty-step deref activation, the three segment lemmas — lives in the
//! EvalIr bundle and builds in half a minute, which is why every iteration of
//! the machine-shape work happened there; what names `level_is_zero` (the cost
//! function, the representation relation, the induction, A4 and A5) has to pay
//! the full spec's twelve minutes. A declaration migrating across that line is
//! exactly what a reader could not see, so this fixes the cheap half and names
//! what the expensive half must contain.
//!
//! 93 -> 109 (E2, 2026-09-24): the sixteen `ir_lzd_*` declarations of
//! `eval_ir_lzd_sctr.rs` -- the step-indexed local obligations -- are in THIS
//! half; what names `Level` (the contract table, `ir_lzd_ctr`, `ir_lzd_pc`) is
//! Full-only and counted by `eval_ir_ctr_census`.
//!
//! 109 -> 125 (2026-09-25): those obligations are minted ONE LEMMA PER CALL
//! (D5's re-decided remedy), which adds their eight resume segments
//! `ir_lzd_*_sseg_r<i>` and eight named frame stacks `ir_lzd_*_sseg_st<i>` to
//! this half; the obligations' statements are unchanged.

use std::collections::BTreeSet;

use clean_verify::test_utils::build_eval_ir_spec_with_stack;

/// The count this test mints. Quote it; do not type it somewhere else.
const EVAL_IR_LZD_DECLS: usize = 125;

#[test]
fn eval_ir_lzd_declaration_census_is_pinned() {
    let spec = build_eval_ir_spec_with_stack();
    let names: BTreeSet<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_lzd"))
        .collect();
    for required in [
        // the module, and the four DERIVED encodings rows that make it readable
        "ir_lzd_module",
        "ir_lzd_func",
        "ir_lzd_f4_func",
        "ir_lzd_e2",
        "ir_lzd_e3",
        // what those rows make the machine SEE, at an abstract base
        "ir_lzd_view_arc",
        "ir_lzd_view_nonnull",
        "ir_lzd_view_optarc",
        "ir_lzd_view_optref",
        // the whole program, executed
        "ir_lzd_max_zz_returns_true_at_107",
        "ir_lzd_max_zz_running_at_106",
        // the derived deref, and the body's own leaves
        "ir_lzd_deref_activation",
        "ir_lzd_activation_zero",
        "ir_lzd_activation_succ",
        "ir_lzd_activation_param",
        // the three segments the induction splices
        "ir_lzd_imax_seg",
        "ir_lzd_max_true_seg",
        "ir_lzd_max_false_seg",
        // the heap the machine actually starts from
        "ir_lzd_init_mem",
        // E2: the same bodies' local obligations in STEP-INDEXED form, the deref
        // chain's contract through the adapter, and the acceptance predicate
        // (eval_ir_lzd_sctr.rs; the table and its soundness are Full-only)
        "ir_lzd_zpost",
        "ir_lzd_deref_ctr",
        "ir_lzd_zero_ctr",
        "ir_lzd_imax_sseg",
        "ir_lzd_max_true_sseg",
        "ir_lzd_max_false_sseg",
        "ir_lzd_pc_ok",
    ] {
        assert!(
            names.contains(required),
            "the EvalIr bundle must register {required}; it has {names:?}"
        );
    }
    assert_eq!(
        names.len(),
        EVAL_IR_LZD_DECLS,
        "the EvalIr bundle's `ir_lzd` declarations moved. Update the number rather than the \
         assertion, and say where it moved. Registered: {names:?}"
    );
}
