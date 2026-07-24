// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track GG surface gate: the `WellFounded.fixF` unfolding equation.
//!
//! `WellFounded.fixFEq` is the propositional equation that lets a well-founded
//! recursive definition unfold one step:
//!
//! ```text
//! fixF F x acx = F x (fun y p => fixF F y (Acc.inv acx p))
//! ```
//!
//! Track GG discharged the *general* `WellFounded.fixFEq` from a bare
//! `Declaration::Axiom` to a genuine kernel-checked `Declaration::Theorem`
//! (proof: `@Acc.rec` on the accessibility witness, the `Acc.intro` minor
//! closing by `Eq.refl`); that discharge — and its EMPTY axiom closure — is
//! pinned by the kernel unit test
//! `clean_kernel::env::wf_recursion_support::tests::test_fix_f_eq_is_axiom_free_theorem`.
//!
//! This file is the *surface* companion gate. It drives the SAME pipeline as
//! `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register`) over the `with_prelude` environment, so a
//! pass/fail here matches an observable `clean check` pass/fail. It witnesses
//! the unfolding equation for a concrete `F` over `Nat.lt` (the relation
//! `Nat.lt_wf` is built on, which is what the `Nat.bitwise` WF foundation
//! consumes) by `rfl` — i.e. the well-founded unfolding holds DEFINITIONALLY
//! through an inlined `Acc.intro` witness via the `Acc.rec` iota rule that
//! backs `fixF`.

use clean_kernel::env::Environment;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real `clean check` file pipeline for a multi-declaration source.
/// Returns Ok if every declaration elaborates and kernel-checks, Err otherwise.
fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("declaration {i}: {e}"))?;
    }
    Ok(())
}

/// POSITIVE gate: the `fixF` unfolding equation for a concrete `F` over
/// `Nat.lt`, applied to an inlined `Acc.intro` accessibility witness, holds by
/// `rfl`. This is the definitional one-step unfolding that `WellFounded.fixFEq`
/// generalizes; the proof term is pure iota (no `Acc.inv`, no `Acc.rec` in the
/// proof) so it is robust to surface universe inference.
#[test]
fn fixf_unfold_on_acc_intro_holds_by_rfl() {
    let src = "\
def ggC (a : Nat) : Type := Nat\n\
def ggF (x : Nat) (ih : (y : Nat) -> Nat.lt y x -> Nat) : Nat := 7\n\
theorem gg_fixF_unfold_intro\n  \
    (x : Nat) (h : (y : Nat) -> Nat.lt y x -> Acc Nat.lt y) :\n    \
    @WellFounded.fixF Nat Nat.lt ggC ggF x (@Acc.intro Nat Nat.lt x h)\n      \
    = ggF x (fun (y : Nat) (p : Nat.lt y x) =>\n          \
        @WellFounded.fixF Nat Nat.lt ggC ggF y (h y p)) :=\n  \
    rfl";
    try_elaborate(src)
        .expect("fixF unfolding on an Acc.intro witness (over Nat.lt) must kernel-check by rfl");
}

/// CONTROL: `WellFounded.fix` over the genuine `Nat.lt_wf` witness computes at
/// a concrete point. Confirms the whole WF stack (Acc / Acc.rec / fixF / fix /
/// Nat.lt_wf) reduces end to end — the accessibility proof from `Nat.lt_wf`
/// is not opaque to `whnf`.
#[test]
fn fix_over_nat_lt_wf_computes_at_concrete_point() {
    let src = "\
def ggC2 (a : Nat) : Type := Nat\n\
def ggF2 (x : Nat) (ih : (y : Nat) -> Nat.lt y x -> Nat) : Nat := 7\n\
theorem gg_fix_eval_3 :\n    \
    @WellFounded.fix Nat ggC2 Nat.lt Nat.lt_wf ggF2 3 = 7 := rfl";
    try_elaborate(src)
        .expect("WellFounded.fix over Nat.lt_wf must compute to 7 at the concrete point 3");
}

/// NEGATIVE control: a FALSE unfolding (wrong RHS body constant) must be
/// REJECTED — guards against a false-green `rfl` accepting any `Eq` goal.
#[test]
fn fixf_unfold_with_wrong_body_is_rejected() {
    let src = "\
def ggC3 (a : Nat) : Type := Nat\n\
def ggF3 (x : Nat) (ih : (y : Nat) -> Nat.lt y x -> Nat) : Nat := 7\n\
theorem gg_fixF_unfold_wrong\n  \
    (x : Nat) (h : (y : Nat) -> Nat.lt y x -> Acc Nat.lt y) :\n    \
    @WellFounded.fixF Nat Nat.lt ggC3 ggF3 x (@Acc.intro Nat Nat.lt x h) = 8 :=\n  \
    rfl";
    let err = try_elaborate(src)
        .expect_err("fixF unfolds to 7, so a stated value of 8 must be rejected by the kernel");
    assert!(
        err.to_lowercase().contains("type")
            || err.contains("KernelCheckFailed")
            || err.to_lowercase().contains("mismatch")
            || err.to_lowercase().contains("not definitionally equal"),
        "rejection must come from the kernel def-eq check, got: {err}"
    );
}
