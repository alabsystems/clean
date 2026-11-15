// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for `decide` on universally quantified goals (2026-09-28).
//!
//! Clean's prelude has no `Decidable (∀ x : Bool, p x)` instance, so
//! `∀ a : Bool, (a && true) = a` fell past every kernel-evaluation rung of
//! `eval_decide` into the SMT bridge. The bridge lowers `&&`, `^^^`, `UInt32`
//! arithmetic, … to uninterpreted functions without marking the translation
//! lossy, so `¬goal` was satisfiable in the abstraction and `decide` reported
//! "SMT found counterexample — goal is not valid" for VALID goals.
//!
//! The fix, per Lean's `decide` semantics:
//! * `∀` over `Bool` is decided by evaluating both cases (Lean core's
//!   `Decidable (∀ x : Bool, p x)` instance), with a kernel-checked
//!   `Bool.casesOn` proof — so the scout goal and ay's `gMaj_is_majority`
//!   elaborate;
//! * a goal with no `Decidable` instance (Lean has none for `∀ c : UInt32`)
//!   is refused with "failed to synthesize `Decidable …`";
//! * an SMT satisfying assignment is never reported as a counterexample; a
//!   proposition is called false only when kernel evaluation showed it.
//!
//! The soundness direction: none of this may close a false goal. Every
//! `*_refuses_*` test asserts the kernel never registers the theorem.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

/// Elaborate every declaration of `code` in order against a fresh prelude
/// environment and return the LAST declaration's result. An earlier
/// declaration that fails to elaborate is an error of the fixture itself.
fn elab_file(code: &str) -> Result<ElabResult, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).map_err(|e| format!("parse failed: {e:?}"))?;
    let (last, setup) = decls
        .split_last()
        .ok_or_else(|| "no declaration".to_string())?;
    for decl in setup {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| format!("fixture setup declaration failed: {e}"))?;
    }
    let processed = preprocess_decl_with_context(last, &mut file_ctx);
    elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        .map_err(|e| e.to_string())
}

/// Assert the last declaration of `code` is a kernel-registered theorem.
#[track_caller]
fn assert_closes(code: &str) {
    match elab_file(code) {
        Ok(ElabResult::Theorem { .. }) => {}
        other => panic!("expected a kernel-registered theorem for\n{code}\ngot {other:?}"),
    }
}

/// Assert the last declaration of `code` is NOT registered, and return the
/// refusal message.
#[track_caller]
fn assert_refused(code: &str) -> String {
    match elab_file(code) {
        Ok(ElabResult::Theorem { .. }) => {
            panic!("SOUNDNESS: a false or undecidable goal was closed:\n{code}")
        }
        Ok(other) => panic!("expected a refusal for\n{code}\ngot {other:?}"),
        Err(message) => message,
    }
}

/// The old message must never come back: it claimed a counterexample the
/// bridge had not validated.
#[track_caller]
fn assert_no_unvalidated_counterexample_claim(message: &str) {
    assert!(
        !message.contains("found counterexample") && !message.contains("goal is not valid"),
        "decide claimed an unvalidated SMT counterexample: {message}"
    );
}

// ---------------------------------------------------------------------------
// The two scout goals, with Lean's verdict for each.
// ---------------------------------------------------------------------------

/// Lean's `decide` proves this through core's `Decidable (∀ x : Bool, p x)`.
#[test]
fn test_decide_closes_scout_bool_forall() {
    assert_closes("theorem t : ∀ a : Bool, (a && true) = a := by decide\n");
}

/// Lean core has no `Decidable (∀ c : UInt32, p c)` instance, so Lean's
/// `decide` fails to synthesize one. Clean must refuse the same way — and in
/// particular must not call this VALID goal "not valid". The registered
/// `decide` follows Lean's procedure (`decide_lean`, DECISIONS R127), which
/// consults no SMT solver, so the refusal is Lean's synthesis failure alone
/// (pinned v4.30.0-rc2: "failed to synthesize\n  Decidable (…)").
#[test]
fn test_decide_refuses_scout_uint32_forall_with_synthesis_failure() {
    let message = assert_refused("theorem t : ∀ c : UInt32, (c ^^^ 1) ^^^ 1 = c := by decide\n");
    assert!(
        message.contains("failed to synthesize\n  Decidable"),
        "expected Lean's synthesis-failure refusal, got: {message}"
    );
    assert!(
        !message.contains("SMT"),
        "the registered `decide` must not consult the SMT bridge, got: {message}"
    );
    assert_no_unvalidated_counterexample_claim(&message);
}

// ---------------------------------------------------------------------------
// Finite Bool quantification beyond the scout goal.
// ---------------------------------------------------------------------------

/// ay `verification/lean/AySoundness/BitVecThy.lean` `gMaj_is_majority` and
/// `gSum_is_parity`: three nested `Bool` binders, eight cases each. (`gSum` is
/// spelled with `xor` here because Clean's parser does not yet accept Lean's
/// `^^` Bool-xor notation.)
#[test]
fn test_decide_closes_three_binder_majority_and_parity_gates() {
    let gates = "def gSum (a b c : Bool) : Bool := xor (xor a b) c\n\
                 def gMaj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)\n";
    assert_closes(&format!(
        "{gates}theorem gMaj_is_majority : \
         ∀ a b c : Bool, gMaj a b c = ((a && b) || (a && c) || (b && c)) := by decide\n"
    ));
    assert_closes(&format!(
        "{gates}theorem gSum_is_parity : \
         ∀ a b c : Bool, gSum a b c = xor a (xor b c) := by decide\n"
    ));
}

#[test]
fn test_decide_closes_bool_forall_identities() {
    for code in [
        "theorem t : ∀ a : Bool, (a || false) = a := by decide\n",
        "theorem t : ∀ a : Bool, (!(!a)) = a := by decide\n",
        "theorem t : ∀ a b : Bool, (a && b) = (b && a) := by decide\n",
        "theorem t : ∀ a b : Bool, (!(a && b)) = (!a || !b) := by decide\n",
        "theorem t : ∀ a : Bool, a = true ∨ a = false := by decide\n",
    ] {
        assert_closes(code);
    }
}

/// Lean decides `p → q` through core's `Decidable (p → q)` instance, so
/// `decide` closes Bool statements with hypotheses.
#[test]
fn test_decide_closes_bool_forall_with_implications() {
    assert_closes("theorem t : ∀ a b : Bool, a = true → b = true → (a && b) = true := by decide\n");
    assert_closes("theorem t : ∀ a : Bool, a ≠ true → a = false := by decide\n");
}

// ---------------------------------------------------------------------------
// Fail-closed: false goals are refused, and only evaluation may call them false.
// ---------------------------------------------------------------------------

/// A false Bool `∀` is refused with the case kernel evaluation found false.
#[test]
fn test_decide_refuses_false_bool_forall_with_validated_case() {
    for code in [
        "theorem f : ∀ a : Bool, (a && false) = a := by decide\n",
        "theorem f : ∀ a : Bool, (a || true) = a := by decide\n",
        "theorem f : ∀ a b : Bool, (a && b) = (a || b) := by decide\n",
        "theorem f : ∀ a : Bool, a = true := by decide\n",
        "theorem f : ∀ a : Bool, (!a) = a := by decide\n",
        "theorem f : ∀ a b : Bool, a = b := by decide\n",
        "theorem f : ∀ a : Bool, a ≠ true → a = true := by decide\n",
    ] {
        let message = assert_refused(code);
        assert!(
            message.contains("is false")
                && message.contains("counterexample (Bool binders, outermost first): "),
            "a false Bool goal must be refused with its evaluated case:\n{code}\ngot: {message}"
        );
        assert_no_unvalidated_counterexample_claim(&message);
    }
}

/// False goals over types with no `Decidable ∀` instance, including ones that
/// are VALID under unbounded integer semantics (so an SMT encoding that read
/// `UInt8` / `Nat` operations as `Int` ones would call them valid). None may
/// close; none may be called "not valid" on the SMT abstraction's say-so.
#[test]
fn test_decide_refuses_false_goals_over_unbounded_and_machine_types() {
    for code in [
        "theorem f : ∀ a : UInt8, a + 1 > a := by decide\n",
        "theorem f : ∀ a : UInt8, a < a + 1 := by decide\n",
        "theorem f : ∀ a b : UInt8, a ≤ a + b := by decide\n",
        "theorem f : ∀ a : UInt32, a * 2 / 2 = a := by decide\n",
        "theorem f : ∀ c : UInt32, (c ^^^ 1) ^^^ 2 = c := by decide\n",
        "theorem f : ∀ a : Nat, a - 1 + 1 = a := by decide\n",
        "theorem f : ∀ a : Nat, a - 1 < a := by decide\n",
        "theorem f : ∀ a : Nat, a - 5 = 0 → a = 5 := by decide\n",
        "theorem f : ∀ a : Int, a / 2 * 2 = a := by decide\n",
        "theorem f : ∀ a : Nat, a < a := by decide\n",
    ] {
        let message = assert_refused(code);
        assert_no_unvalidated_counterexample_claim(&message);
    }
}

/// Ground false goals are refused because evaluation says so.
#[test]
fn test_decide_refuses_false_ground_goals() {
    for code in [
        "theorem f : (true && false) = true := by decide\n",
        "theorem f : (255 : UInt8) + 1 > 255 := by decide\n",
    ] {
        let message = assert_refused(code);
        assert_no_unvalidated_counterexample_claim(&message);
    }
    let message = assert_refused("theorem f : (true && false) = true := by decide\n");
    assert!(
        message.contains("is false"),
        "kernel evaluation reduces this instance to isFalse, got: {message}"
    );
}

/// The SMT bridge maps a string literal `"a"` and a constant named `str_a` to
/// the SAME solver constant, so it answers UNSAT for this FALSE goal and
/// reconstructs `Eq.refl "a"`. Only the kernel check stands between that and
/// a proof of `"a" = str_a` — this pins that the check still refuses it.
///
/// The registered `decide` no longer reaches the bridge (DECISIONS R127: it
/// refuses with Lean's "proved that the proposition … is false"), so the
/// bridge is driven directly, as `eval_decide`'s last rung and every internal
/// caller drive it, and the rejected candidate is asserted on the ledger.
#[test]
fn test_decide_kernel_gate_refuses_smt_name_collision() {
    let message = assert_refused(
        "def str_a : String := \"b\"\n\
         theorem f : \"a\" = str_a := by decide\n",
    );
    assert!(
        message.contains("proved that the proposition"),
        "the registered decide refuses in Lean's words: {message}"
    );

    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls =
        parse_file("def str_a : String := \"b\"\ndef G : Prop := \"a\" = str_a\n").expect("parse");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .expect("the fixture elaborates");
    }
    let target = env
        .get_const(&clean_kernel::Name::from_string("G"))
        .and_then(|info| info.value.clone())
        .expect("G has a value");
    let mut state = crate::tactic::ProofState::new(env, target);
    let error = crate::tactic::smt::decide(&mut state)
        .expect_err("SOUNDNESS: the SMT bridge closed a false goal");
    assert_no_unvalidated_counterexample_claim(&error.to_string());
    assert!(
        state.trust_ledger().smt_recovery.invalid_bridge_candidates > 0,
        "the bridge must have produced a candidate the kernel gate rejected; \
         otherwise this test no longer reaches its subject: {error}"
    );
}

/// Once kernel evaluation has PROVED a proposition false, `decide` refuses it
/// at once and never asks the SMT bridge. For this goal (decide review, probe
/// a07) the bridge merged `b` and `c`, answered "Verified", and reconstructed
/// a proof of `b = true → b = true` that only `validate_proof_term` rejected —
/// visible here as an invalid bridge candidate on the proof state's ledger.
#[test]
fn test_decide_does_not_consult_smt_once_evaluation_proves_false() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file("def A07 : Prop := ∀ b c : Bool, b = true → c = true\n").expect("parse");
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        .expect("the proposition elaborates");
    let target = env
        .get_const(&clean_kernel::Name::from_string("A07"))
        .and_then(|info| info.value.clone())
        .expect("A07 has a value");
    let mut state = crate::tactic::ProofState::new(env, target);
    let error = crate::tactic::decide::eval_decide(&mut state)
        .expect_err("SOUNDNESS: a false goal was closed");
    let message = error.to_string();
    assert!(
        message.contains("is false") && message.contains("counterexample (Bool binders"),
        "the refusal is evaluation's: {message}"
    );
    assert!(
        !message.contains("SMT"),
        "the SMT fallback must not have been consulted: {message}"
    );
    assert_eq!(
        state.trust_ledger().smt_recovery.invalid_bridge_candidates,
        0,
        "no bridge candidate may have been produced (and rejected) for a goal \
         evaluation already proved false"
    );
}

// ---------------------------------------------------------------------------
// Source ratchet: the unvalidated claim is gone from the SMT bridge tactic.
// ---------------------------------------------------------------------------

#[test]
fn test_smt_decide_no_longer_claims_counterexamples() {
    let source = include_str!("../smt/decide/mod.rs");
    assert!(
        !source.contains("found counterexample — goal is not valid"),
        "smt::decide must not report an unvalidated SMT model as a counterexample"
    );
}
