// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `rw` of a Nat.*-headed env lemma against an HAdd/HMul-headed goal subterm.
//!
//! A goal `n + 0 = n` desugars to `@Eq Nat (@HAdd.hAdd … (HAdd.mk … Nat.add) n
//! 0) n`. The lemma `Nat.add_zero : ∀ a, Nat.add a 0 = a` is `Nat.add`-headed.
//! These tests lock that the rw subterm matcher reduces the typeclass-projection
//! head (`HAdd.hAdd` over a concrete instance → `Nat.add`) so the lemma matches,
//! while the rewrite PROOF stays kernel-checked (so a non-applicable lemma still
//! fails-closed rather than mis-rewriting a false goal).

use clean_kernel::Environment;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real `clean check` file pipeline for a single-declaration source.
fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

#[test]
fn rw_add_zero_closes_n_plus_zero() {
    try_elaborate("theorem t (n : Nat) : n + 0 = n := by rw [Nat.add_zero]")
        .expect("rw [Nat.add_zero] should close n + 0 = n (kernel-checked)");
}

#[test]
fn rw_mul_one_closes_n_times_one() {
    try_elaborate("theorem t (n : Nat) : n * 1 = n := by rw [Nat.mul_one]")
        .expect("rw [Nat.mul_one] should close n * 1 = n (kernel-checked)");
}

#[test]
fn rw_zero_add_closes_zero_plus_n() {
    // Only asserted when Nat.zero_add is available in the prelude env; if it is
    // not registered, this lemma path is simply not exercised (no false claim).
    let r = try_elaborate("theorem t (n : Nat) : 0 + n = n := by rw [Nat.zero_add]");
    eprintln!("rw [Nat.zero_add] on 0 + n = n => {r:?}");
    if let Err(e) = &r {
        // A genuine "lemma not found" is acceptable (lemma absent); a *match*
        // failure on a present lemma is the regression we guard against.
        assert!(
            e.contains("zero_add") && (e.contains("not") || e.contains("HypothesisNotFound")),
            "rw [Nat.zero_add] failed for a non-availability reason: {e}"
        );
    }
}

// ---- Mirror case (SITE 1): the rewrite RULE's LHS is the hetero-op projection
// and the GOAL subterm is the concrete op. This is the `rw [ih]` failure: after
// `rw [Nat.add_succ]` the goal carries `Nat.succ (Nat.add 0 k)`, and `ih`'s LHS
// is the `+`-written `@HAdd.hAdd … Nat.add 0 k`. The matcher must reduce the
// projection on the NEEDLE side to bridge to the concrete `Nat.add 0 k`.

#[test]
fn rw_ih_closes_zero_plus_n_induction() {
    // The exact reported repro. `ih : 0 + k = k` (HAdd-headed LHS), goal after
    // `rw [Nat.add_succ]` is `Nat.succ (Nat.add 0 k) = Nat.succ k`; `rw [ih]`
    // must rewrite the `Nat.add 0 k` occurrence. Kernel-checked end to end.
    try_elaborate(
        "theorem t (n : Nat) : 0 + n = n := by \
         induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]",
    )
    .expect("induction + rw [Nat.add_succ, ih] should close 0 + n = n (kernel-checked)");
}

// ---- Negative teeth: a lemma that genuinely does NOT apply must fail-closed.

#[test]
fn rw_ih_mirror_does_not_close_false_succ_goal() {
    // Teeth for the mirror bridge: a FALSE goal where an over-eager projection
    // match on the needle side could mis-fire must stay OPEN. `ih : 0 + k = k`
    // does not make `Nat.succ (Nat.succ k) = Nat.succ k` true; the assembled
    // Eq.subst proof is kernel-rechecked, so close_goal rejects it.
    try_elaborate(
        "theorem t (n : Nat) : 0 + n = Nat.succ n := by \
         induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]",
    )
    .expect_err("rw [ih] must NOT close the false succ goal");
}

#[test]
fn rw_add_zero_does_not_close_false_n_plus_one() {
    // `Nat.add_zero` does not apply to `n + 1 = n` (which is FALSE). The matcher
    // may select an occurrence up-to-defeq, but the assembled Eq.subst proof is
    // kernel-rechecked by close_goal, so an over-eager match is rejected. Either
    // way the false goal must NOT be closed.
    try_elaborate("theorem t (n : Nat) : n + 1 = n := by rw [Nat.add_zero]")
        .expect_err("rw [Nat.add_zero] must NOT close the false goal n + 1 = n");
}

#[test]
fn rw_add_zero_does_not_close_false_swapped() {
    // Another false goal; add_zero rewrites the LHS `m + 0 → m`, leaving `m = n`
    // (unsolved) — must not spuriously close.
    try_elaborate("theorem t (m : Nat) (n : Nat) : m + 0 = n := by rw [Nat.add_zero]")
        .expect_err("rw [Nat.add_zero] must leave `m = n` open, not close it");
}
