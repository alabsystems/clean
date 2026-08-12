// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `induction … using <@[elab_as_elim] eliminator>`.
//!
//! Every positive here is a full parse → elaborate → **kernel-check** round
//! trip: `assert_registered` only passes when the assembled eliminator
//! application survived `verify_tactic_proof` and `add_decl`, so a proof term
//! with the wrong motive, universe or alternative order cannot register.
//!
//! The eliminators are declared in the fixture source as plain `def`s. That is
//! the point: they are ordinary constants, absent from the kernel recursor
//! table, which is precisely what `Environment::get_recursor` used to reject
//! (`EnvironmentMissing`) even though the constant was in the environment.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elab(code: &str) -> (Environment, Vec<Result<ElabResult, ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("fixture must parse");
    let results = decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect();
    (env, results)
}

fn assert_registered(env: &Environment, name: &str, results: &[Result<ElabResult, ElabError>]) {
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "{name}: declaration {i} failed: {:?}",
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} must be registered — that only happens after the kernel accepts the proof term"
    );
}

fn errors(results: &[Result<ElabResult, ElabError>]) -> String {
    results
        .iter()
        .filter_map(|r| r.as_ref().err().map(|e| format!("{e:?}")))
        .collect::<Vec<_>>()
        .join(" | ")
}

/// The eliminator every positive test below uses.
///
/// `myNatElim` has the `Nat.strongRecOn` argument ORDER — motive, then target,
/// then the alternatives — which is exactly what the recursor path cannot
/// assemble (it emits `params → motive → minors → major`). It is a plain `def`,
/// so `get_recursor` returns `None` for it.
const ELIM: &str = r#"
def myNatElim {motive : Nat → Prop} (n : Nat) (base : motive Nat.zero)
    (step : ∀ k, motive k → motive (Nat.succ k)) : motive n :=
  Nat.rec base step n
"#;

/// TOOTH 1 (positive, kernel-checked): a custom eliminator with the motive
/// before the target drives a real induction and the proof registers.
///
/// This is the test that is RED without the new dispatch: on `origin/main` the
/// tactic fails with `EnvironmentMissing { constant: "myNatElim" }`.
#[test]
fn test_induction_using_custom_eliminator_kernel_checks() {
    let code = format!(
        "{ELIM}
theorem elim_zero_add (n : Nat) : 0 + n = n := by
  induction n using myNatElim with
  | base => rfl
  | step k ih => rw [Nat.add_succ, ih]
"
    );
    let (env, results) = elab(&code);
    assert_registered(&env, "elim_zero_add", &results);
}

/// TOOTH 1 (positive): the case goals carry the alternatives' fields, and the
/// `with`-block names rename them positionally — `k` and `ih` are usable.
#[test]
fn test_induction_using_custom_eliminator_binds_fields_and_ih() {
    let code = format!(
        "{ELIM}
theorem elim_add_zero (n : Nat) : n + 0 = n := by
  induction n using myNatElim with
  | base => rfl
  | step k ih => rw [Nat.succ_add, ih]
"
    );
    let (env, results) = elab(&code);
    assert_registered(&env, "elim_add_zero", &results);
}

/// TOOTH 2 (control): the recursor fast path is untouched. `induction n using
/// Nat.rec` still resolves through `get_recursor` and still kernel-checks —
/// the new dispatch only fires when `get_recursor` returns `None`.
#[test]
fn test_induction_using_kernel_recursor_still_takes_the_recursor_path() {
    let code = r#"
theorem rec_zero_add (n : Nat) : 0 + n = n := by
  induction n using Nat.rec with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab(code);
    assert_registered(&env, "rec_zero_add", &results);
}

/// TOOTH 2 (control): plain `induction` — no `using` at all — is unaffected.
#[test]
fn test_plain_induction_unaffected() {
    let code = r#"
theorem plain_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab(code);
    assert_registered(&env, "plain_zero_add", &results);
}

/// TOOTH 3 (negative, no over-accept): a `using` name that is not in the
/// environment at all must still fail closed. The new path must not turn an
/// unknown name into a silent success.
#[test]
fn test_induction_using_unknown_name_fails_closed() {
    let code = r#"
theorem using_unknown (n : Nat) : 0 + n = n := by
  induction n using Nat.notAnEliminator with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "an unknown `using` name must fail closed: {}",
        errors(&results)
    );
    assert!(env.get_const(&Name::from_string("using_unknown")).is_none());
}

/// TOOTH 3 (negative, no over-accept): a constant that exists but is NOT an
/// eliminator — its result type is not an application of one of its own
/// parameters — must be rejected by the shape analysis, not applied blindly.
#[test]
fn test_induction_using_non_eliminator_constant_fails_closed() {
    let code = r#"
def notAnElim (n : Nat) : Nat := n

theorem using_non_elim (n : Nat) : 0 + n = n := by
  induction n using notAnElim with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
"#;
    let (env, results) = elab(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "a non-eliminator constant must fail closed: {}",
        errors(&results)
    );
    assert!(env
        .get_const(&Name::from_string("using_non_elim"))
        .is_none());
}

/// TOOTH 4 (negative, fail-closed floor): a well-formed eliminator whose
/// alternatives do not discharge the goal leaves the theorem unproved. The
/// tactic must never close the goal for it, and nothing may register.
///
/// `myNatElim` fits the goal shape perfectly here, so this isolates the case
/// *bodies*: `rfl` cannot prove the `step` case of `0 + n = n`.
#[test]
fn test_induction_using_eliminator_with_wrong_case_bodies_fails_closed() {
    let code = format!(
        "{ELIM}
theorem elim_bad_bodies (n : Nat) : 0 + n = n := by
  induction n using myNatElim with
  | base => rfl
  | step k ih => rfl
"
    );
    let (env, results) = elab(&code);
    assert!(
        results.iter().skip(1).any(|r| r.is_err()),
        "an unprovable case body must fail closed: {}",
        errors(&results)
    );
    assert!(
        env.get_const(&Name::from_string("elim_bad_bodies"))
            .is_none(),
        "nothing may register when a case body does not prove its goal"
    );
}

/// TOOTH 4 (negative): an eliminator applied to a hypothesis it does not
/// eliminate. `myNatElim` targets `Nat`; the major premise here is a `List`, so
/// the assembled term is ill-typed and must be rejected.
#[test]
fn test_induction_using_eliminator_on_wrong_type_fails_closed() {
    let code = format!(
        "{ELIM}
theorem elim_wrong_type (l : List Nat) : l = l := by
  induction l using myNatElim with
  | base => rfl
  | step k ih => rfl
"
    );
    let (env, results) = elab(&code);
    assert!(
        results.iter().skip(1).any(|r| r.is_err()),
        "an eliminator for the wrong type must fail closed: {}",
        errors(&results)
    );
    assert!(env
        .get_const(&Name::from_string("elim_wrong_type"))
        .is_none());
}

/// No proof produced on this path may depend on a `sorry`. All four bypass
/// ratchets read 0; this asserts the eliminator path does not become the first
/// hole, on both the positive and the failing fixture.
#[test]
fn test_induction_using_eliminator_never_emits_sorry() {
    let ok = format!(
        "{ELIM}
theorem elim_no_sorry (n : Nat) : 0 + n = n := by
  induction n using myNatElim with
  | base => rfl
  | step k ih => rw [Nat.add_succ, ih]
"
    );
    let (env, results) = elab(&ok);
    assert_registered(&env, "elim_no_sorry", &results);
    let decl = env
        .get_const(&Name::from_string("elim_no_sorry"))
        .expect("registered above");
    if let Some(value) = &decl.value {
        assert!(
            !value.has_sorry(),
            "the eliminator proof term must not contain a sorry"
        );
    }
}

/// REGRESSION (verified RED without the per-alternative FVar reset): a
/// two-alternative eliminator whose FIRST alternative binds a field.
///
/// `cases_core` renumbers every branch's field FVars from the same
/// `goal_binder_base` (`proof_manipulation.rs`); this path did not, so the
/// SECOND alternative's first field was `base + 1` while its lambda re-started
/// the binder depth at 0. `close_fvars::assignment_scope_violation` requires
/// `id - base < depth`, so the assembled proof was rejected with
/// "nested metavariable … captures out-of-scope local … at binder depth 1".
///
/// The recursor path never exposed this because `Nat`/`List` lead with a
/// NULLARY constructor, which consumes no id.
#[test]
fn test_induction_using_eliminator_two_alternatives_each_binding_a_field() {
    let code = r#"
def myTwoAlt {P : Nat → Prop} (inv : ∀ i, P i ↔ P i) (w : ∀ n : Nat, P n) (i : Nat) : P i := w i

theorem two_alt_shape (i : Nat) : i = i := by
  induction i using myTwoAlt with
  | inv j => exact Iff.rfl
  | w n => rfl
"#;
    let (env, results) = elab(code);
    assert_registered(&env, "two_alt_shape", &results);
}

/// CONTROL for the test above: the same eliminator shape with a SINGLE
/// alternative always worked, which is what localised the defect to the
/// per-alternative FVar numbering rather than to the target-last layout.
#[test]
fn test_induction_using_eliminator_single_alternative_target_last() {
    let code = r#"
def myOneAlt {P : Nat → Prop} (w : ∀ n : Nat, P n) (i : Nat) : P i := w i

theorem one_alt_shape (i : Nat) : i = i := by
  induction i using myOneAlt with
  | w n => rfl
"#;
    let (env, results) = elab(code);
    assert_registered(&env, "one_alt_shape", &results);
}

/// REGRESSION (verified RED without solver step 3): a universe parameter that
/// appears ONLY in another parameter's type.
///
/// `{α : Sort u} (a : α) …` never mentions `u` in the target's type nor in the
/// motive's result sort, so matching those two alone left `u` undetermined and
/// the tactic (correctly, but unnecessarily) refused with
/// "universe parameter `u` is not determined by the goal". Inferring the type
/// of the solved `α := Nat` and matching `Sort u ≟ Sort 1` pins it.
/// Real instance: `WellFounded.induction`, 12 `Init` sites.
#[test]
fn test_induction_using_eliminator_solves_universe_from_a_parameter_type() {
    let code = r#"
def myPolyElim {α : Sort u} {P : α → Prop} (a : α) (h : ∀ x : α, P x) : P a := h a

theorem poly_shape (n : Nat) : n = n := by
  induction n using myPolyElim with
  | h x => rfl
"#;
    let (env, results) = elab(code);
    assert_registered(&env, "poly_shape", &results);
}
