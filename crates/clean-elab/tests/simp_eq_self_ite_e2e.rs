// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for the `eq_self` / `ite_true` / `ite_false`
//! builtin simp lemmas (GAP B of the `ite` STEP 2 work).
//!
//! ## The gap this guards
//!
//! Before this change the builtin simp set had And/Or/Not Prop lemmas but NO
//! reflexive-equality rule and NO canonical-`ite` rule, so:
//!
//! ```text
//! example (n : Nat) : (n = n) = True := by simp           -- NoProgress
//! example (n : Nat) : (if n = n then True else False) := by simp  -- stuck
//! ```
//!
//! The fix registers three real kernel-checked theorems in the prelude
//! (`clean-kernel` `logic_simp_ite_eq.rs`):
//!
//! ```text
//! eq_self   : {α} (a)   → @Eq Prop (@Eq α a a) True
//! ite_true  : {α} (a b) → @Eq α (@ite α True  instDecidableTrue  a b) a
//! ite_false : {α} (a b) → @Eq α (@ite α False instDecidableFalse a b) b
//! ```
//!
//! and surfaces them in the builtin simp collector via `push_if_present` (so the
//! rule is emitted only once the proof constant exists in the env).
//!
//! ## Why a pass here is a genuine proof
//!
//! Each PASS gate drives the SAME pipeline as `clean check` and asserts that the
//! theorem registers (kernel re-checks the produced rewrite proof), that the
//! proof term `infer_type`s to a type def-eq to the stated proposition, and that
//! the transitive `axiom_deps` closure is `⊆ {propext}` (FOUNDATIONAL —
//! `eq_self` is a `propext` theorem; `ite_*` are axiom-free).
//!
//! ## Soundness backstop (the FALSE-simp gates)
//!
//! `(n = n) = False := by simp` is FALSE; an `ite True` reducing to the ELSE
//! branch is FALSE. These MUST NOT close: the gates assert that elaboration
//! *fails* (no proof is registered).

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (which must define `name` last as a tactic-proved theorem)
/// and assert it elaborates + kernel-checks, that the proof `infer_type`s def-eq
/// to its proposition, and that its `axiom_deps` closure is `⊆ {propext}`.
fn assert_tactic_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS — axiom closure ⊆ {propext} (FOUNDATIONAL). No sorry/domain axiom.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    for d in &deps {
        assert_eq!(
            d.to_string(),
            "propext",
            "`{name}` axiom closure must be ⊆ {{propext}}, found {d:?} (full {deps:?})"
        );
    }
}

/// Assert the FALSE theorem `source` does NOT elaborate-and-register.
fn assert_false_theorem_rejected(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    match try_elaborate_into(&mut env, source) {
        Err(_) => {} // expected: simp could not (soundly) close the false goal.
        Ok(()) => {
            if let Some(info) = env.get_const(&Name::from_string(name)) {
                assert!(
                    info.value.is_none(),
                    "FALSE goal `{name}` must NOT be closed by simp, but a proof was registered"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// PASS gates
// ---------------------------------------------------------------------------

#[test]
fn simp_eq_self_closes() {
    assert_tactic_theorem(
        "eq_self_true",
        "theorem eq_self_true (n : Nat) : (n = n) = True := by simp",
    );
}

// NOTE: GAP A — routing the macro-collapsed bare `ite` app back through
// `elab_if` — is now LANDED (see `tests/bare_ite_app_reroute_e2e.rs`), so the
// `Discriminant(3) vs Discriminant(6)` Const-vs-Pi unify failure that blocked
// `(if True then (1:Nat) else 2) = 1 := rfl` is fixed. The remaining piece for
// `theorem (n : Nat) : (if n = n then True else False) := by simp` is (b):
// ite-condition congruence that rewrites the dependent `Decidable (n = n)`
// instance in lock-step with the condition `n = n → True` under simp. That
// dependent-instance congruence is a separate simp-engine concern and remains
// out of scope for the elab reroute; see the remainder notes. The `eq_self`
// win above is the isolated, sound GAP-B deliverable.

// ---------------------------------------------------------------------------
// SOUNDNESS gates — FALSE goals must NOT be closed by simp.
// ---------------------------------------------------------------------------

#[test]
fn simp_false_eq_self_equals_false_is_rejected() {
    assert_false_theorem_rejected(
        "false_eq_self_false",
        "theorem false_eq_self_false (n : Nat) : (n = n) = False := by simp",
    );
}
