// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RC-A / brick T1: every in-crate `decide` fallback must
//! be the kernel-evaluating ladder (`decide::eval_decide`), never the bare SMT
//! bridge (`smt::decide`).
//!
//! Eight files under `tactic/` used to import `super::smt::decide` (four
//! directly, four through the `pub use smt::{… decide …}` re-export in
//! `tactic/mod.rs`), bypassing the ladder the `decide` *token* is registered to
//! in `builtins.rs`. `smt::decide` answers
//! `SmtFailed { detail: "found counterexample — goal is not valid" }` on TRUE
//! ground goals, so `norm_num`, `native_decide`, `positivity`, `norm_cast` and
//! the `decide` rung inside `omega`/`linarith`/`nlinarith` all refuted goals
//! that plain `by decide` proves on the identical prelude.
//!
//! Each `*_closes_*` test below was confirmed RED with the imports reverted to
//! `super::smt::decide`, and each `*_still_rejects_*` test guards the
//! fail-closed direction: the new ladder must not prove a false goal.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

/// Elaborate `code` (one declaration) against a fresh prelude environment and
/// register it, so `Ok` means the kernel accepted the proof term.
fn elab_one(code: &str) -> Result<ElabResult, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).map_err(|e| format!("parse failed: {e:?}"))?;
    let decl = decls.first().ok_or_else(|| "no declaration".to_string())?;
    let processed = preprocess_decl_with_context(decl, &mut file_ctx);
    elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        .map_err(|e| format!("{e:?}"))
}

/// Assert `code` elaborates to a kernel-registered theorem.
#[track_caller]
fn assert_closes(code: &str, what: &str) {
    match elab_one(code) {
        Ok(ElabResult::Theorem { .. }) => {}
        other => panic!("{what}: expected a kernel-registered theorem, got {other:?}"),
    }
}

/// Assert `code` does NOT elaborate — the fail-closed direction.
#[track_caller]
fn assert_rejects(code: &str, what: &str) {
    let result = elab_one(code);
    assert!(
        !matches!(result, Ok(ElabResult::Theorem { .. })),
        "{what}: a false goal must not be closed, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// The three live differentials from the RC-A reproduction, with their
// `by decide` controls in the same test.
// ---------------------------------------------------------------------------

#[test]
fn test_norm_num_closes_true_nat_le_like_decide() {
    assert_closes(
        "theorem ctl : (2:Nat) <= 3 := by decide\n",
        "control: by decide",
    );
    assert_closes(
        "theorem tst : (2:Nat) <= 3 := by norm_num\n",
        "norm_num on the identical goal",
    );
}

#[test]
fn test_native_decide_closes_true_nat_disequality_like_decide() {
    assert_closes(
        "theorem ctl : ¬((3:Nat) = 4) := by decide\n",
        "control: by decide",
    );
    assert_closes(
        "theorem tst : ¬((3:Nat) = 4) := by native_decide\n",
        "native_decide on the identical goal",
    );
}

#[test]
fn test_positivity_closes_true_nat_lt_like_decide() {
    assert_closes(
        "theorem ctl : (0:Nat) < 1 := by decide\n",
        "control: by decide",
    );
    assert_closes(
        "theorem tst : (0:Nat) < 1 := by positivity\n",
        "positivity on the identical goal",
    );
}

#[test]
fn test_norm_cast_closes_true_nat_le() {
    assert_closes("theorem tst : (2:Nat) <= 3 := by norm_cast\n", "norm_cast");
}

// ---------------------------------------------------------------------------
// Fail-closed: routing to the kernel ladder must not make false goals provable.
// ---------------------------------------------------------------------------

#[test]
fn test_decide_fallback_still_rejects_false_goals() {
    for (tactic, code) in [
        ("norm_num", "theorem bad : (3:Nat) <= 2 := by norm_num\n"),
        (
            "native_decide",
            "theorem bad : (3:Nat) = 4 := by native_decide\n",
        ),
        ("positivity", "theorem bad : (1:Nat) < 0 := by positivity\n"),
        ("norm_cast", "theorem bad : (3:Nat) <= 2 := by norm_cast\n"),
        ("omega", "theorem bad : (3:Nat) <= 2 := by omega\n"),
        ("linarith", "theorem bad : (3:Nat) <= 2 := by linarith\n"),
        ("nlinarith", "theorem bad : (3:Nat) <= 2 := by nlinarith\n"),
    ] {
        assert_rejects(code, tactic);
    }
}

// ---------------------------------------------------------------------------
// Source ratchet: the defect was an import, so guard the import.
//
// `smt::decide` is legitimately reachable exactly once — as the LAST rung of
// `decide::eval_decide` itself. Any other file under `tactic/` that names it is
// the RC-A defect coming back.
// ---------------------------------------------------------------------------

/// The eight files that used to bypass the ladder, paired with their source.
const LADDER_CALLERS: &[(&str, &str)] = &[
    ("norm_num.rs", include_str!("../norm_num.rs")),
    ("norm.rs", include_str!("../norm.rs")),
    ("norm_num_ext.rs", include_str!("../norm_num_ext.rs")),
    ("term_close/mod.rs", include_str!("../term_close/mod.rs")),
    ("arith_nlinarith.rs", include_str!("../arith_nlinarith.rs")),
    ("arith_norm_cast.rs", include_str!("../arith_norm_cast.rs")),
    (
        "omega_tactic/mod.rs",
        include_str!("../omega_tactic/mod.rs"),
    ),
    (
        "arith_linarith/mod.rs",
        include_str!("../arith_linarith/mod.rs"),
    ),
];

#[test]
fn test_ladder_callers_do_not_import_the_smt_decide_bridge() {
    for (path, source) in LADDER_CALLERS {
        assert!(
            !source.contains("use super::smt::decide;"),
            "{path} imports the SMT `decide` bridge directly, bypassing the \
             kernel-evaluating `eval_decide` ladder (RC-A). Use \
             `use super::decide::eval_decide as decide;` instead."
        );
    }
}

#[test]
fn test_ladder_callers_import_eval_decide() {
    for (path, source) in LADDER_CALLERS {
        assert!(
            source.contains("use super::decide::eval_decide as decide;"),
            "{path} must route its `decide` fallback through \
             `decide::eval_decide` (RC-A / brick T1)"
        );
    }
}
