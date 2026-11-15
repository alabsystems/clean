// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression battery: the library check API's "uses sorry" verdict is its
//! constant closure's, never a syntactic match on `sorryAx`'s Bool flag.
//!
//! MEASURED before the fix (2026-09-28): on origin/main `f501f6a77` every
//! `FALSE_PROOFS` row below was `is_fully_verified() == true` through this API
//! (it carries no closure gate; `clean check`'s CLI gate caught some rows
//! there as "cited closure not credited" with `sorry_axioms: 0`), and on
//! `df2e47d78` `clean check` itself passed rows 1–8 and 10 with exit 0.

use super::{check_source, CheckConfig, CheckResult};

fn check_source_parallel_for_tests(source: &str) -> crate::parallel::ParallelCheckResult {
    crate::parallel::check_source_parallel(source, &crate::parallel::ParallelCheckConfig::default())
        .expect("the parallel pipeline must run")
}

/// Each source proves something false (or rests on a proof of it) through a
/// `sorryAx` the old recognizer could not see. `(label, source, the
/// declaration that must fail)`.
const FALSE_PROOFS: &[(&str, &str, &str)] = &[
    (
        "non-literal flag (!true)",
        "theorem bad : False := @sorryAx False (!true)\n",
        "bad",
    ),
    (
        "partial application",
        // Lean v4.30.0-rc2 types `sorryAx False` as `∀ (synthetic : Bool),
        // False` (the flag is explicit), so the partial application proves
        // `Bool → False`; ascribed `False` it is an elaboration error in Lean
        // and in Clean (`partial_and_implicit_alias_forms_are_elaboration_errors`).
        "theorem bad : Bool → False := sorryAx False\n",
        "bad",
    ),
    (
        "eta-expanded",
        "theorem bad : False := (fun (b : Bool) => @sorryAx False b) true\n",
        "bad",
    ),
    (
        "under a binder",
        "theorem bad : ∀ n : Nat, n = n + 1 := fun n => @sorryAx (n = n + 1) (!false)\n",
        "bad",
    ),
    (
        "in a let",
        "theorem bad : False := let f := @sorryAx False; f (!true)\n",
        "bad",
    ),
    (
        "behind a definition alias",
        "def mysorry := @sorryAx\ntheorem bad : False := mysorry False true\n",
        "bad",
    ),
    (
        "inside an instance",
        "class Holds (p : Prop) : Prop where\n  proof : p\n\
         instance bogusInst : Holds False := ⟨@sorryAx False (!true)⟩\n\
         theorem bad : False := Holds.proof\n",
        "bad",
    ),
    (
        "in a type",
        "def T : Prop := @sorryAx Prop (!true)\ntheorem bad (h : T) : T := h\n",
        "bad",
    ),
    (
        "only through a sorry'd lemma",
        "theorem lemma1 : False := sorry\ntheorem uses_lemma : 1 = 2 := False.elim lemma1\n",
        "uses_lemma",
    ),
    (
        "decide-coerced flag",
        "theorem bad : False := @sorryAx False (decide False)\n",
        "bad",
    ),
];

fn check(source: &str) -> CheckResult {
    check_source(source, &CheckConfig::default()).expect("the check pipeline must run")
}

fn decl<'a>(result: &'a CheckResult, name: &str) -> &'a super::DeclResult {
    result
        .declarations
        .iter()
        .find(|d| d.name.ends_with(name))
        .unwrap_or_else(|| panic!("no row for `{name}`: {result:?}"))
}

#[test]
fn every_false_proof_through_sorry_is_refused() {
    for (label, source, culprit) in FALSE_PROOFS {
        let result = check(source);
        let row = decl(&result, culprit);
        assert!(
            !row.passed,
            "[{label}] `{culprit}` must FAIL: its closure reaches sorryAx: {result:?}"
        );
        assert!(
            row.warning
                .as_ref()
                .is_some_and(super::DeclWarning::is_sorry),
            "[{label}] `{culprit}` must carry a sorry warning: {row:?}"
        );
        assert!(
            result.sorry_count >= 1,
            "[{label}] sorry_count is the closure census and must see it: {result:?}"
        );
        assert!(!result.is_fully_verified(), "[{label}] {result:?}");
    }
}

#[test]
fn a_dependent_names_the_lemma_it_inherits_sorry_through() {
    let result = check(FALSE_PROOFS[8].1);
    let row = decl(&result, "uses_lemma");
    let error = row.error.as_deref().unwrap_or_default();
    assert!(
        error.contains("through lemma1"),
        "the refusal must name the cited lemma: {error:?}"
    );
    assert_eq!(
        result.sorry_count, 2,
        "both declarations use sorry: {result:?}"
    );
}

#[test]
fn allow_sorry_passes_them_but_never_as_sorry_free() {
    let config = CheckConfig {
        allow_sorry: true,
        ..CheckConfig::default()
    };
    for (label, source, culprit) in FALSE_PROOFS {
        let result = check_source(source, &config).expect("pipeline");
        let row = decl(&result, culprit);
        assert!(
            row.passed,
            "[{label}] allow_sorry waives the sorry: {row:?}"
        );
        assert!(
            result.sorry_count >= 1 && !result.is_fully_verified(),
            "[{label}] the waived pass must still be visible as sorry-tainted: {result:?}"
        );
    }
}

#[test]
fn a_user_axiom_is_disclosed_not_counted_as_sorry_and_not_axiom_free() {
    let result =
        check("axiom bogus : (1 : Nat) = 2\ntheorem uses_bogus : (1 : Nat) = 2 := bogus\n");
    assert!(
        result
            .declarations
            .iter()
            .all(|d| d.passed && d.warning.is_none()),
        "an axiom is not a sorry: both rows pass without a trust warning: {result:?}"
    );
    assert_eq!(result.sorry_count, 0, "{result:?}");
    let disclosed: Vec<(&str, Vec<&str>)> = result
        .assumptions
        .iter()
        .map(|(n, a)| (n.as_str(), a.iter().map(String::as_str).collect()))
        .collect();
    assert_eq!(
        disclosed,
        vec![("bogus", vec!["bogus"]), ("uses_bogus", vec!["bogus"])],
        "both passes rest on `bogus`, and say so"
    );
    assert!(
        !result.is_fully_verified(),
        "a pass under a domain axiom is not unconditional"
    );
}

#[test]
fn controls_literal_sorry_fails_and_a_real_proof_passes() {
    let literal = check("theorem bad : False := @sorryAx False false\n");
    assert!(!decl(&literal, "bad").passed);
    assert_eq!(literal.sorry_count, 1);
    let good = check("theorem good : 1 + 1 = 2 := rfl\n");
    assert!(good.is_fully_verified(), "{good:?}");
    assert_eq!(good.sorry_count, 0);
    assert!(good.assumptions.is_empty());
}

/// The parallel API used to drop every non-sorry warning, so a proof of
/// `False` through `trustedAy` behind an alias was `is_fully_verified()`.
#[test]
fn parallel_check_keeps_closure_trust_debt() {
    let result = check_source_parallel_for_tests(
        "def myTrusted := @trustedAy\ntheorem bad : False := @myTrusted False\n",
    );
    assert!(
        result
            .trust_debt
            .iter()
            .any(|(name, _)| name.ends_with("bad")),
        "`bad` reaches trustedAy through `myTrusted`: {:?}",
        result.trust_debt
    );
    assert!(!result.is_fully_verified());
    let sorry = check_source_parallel_for_tests("theorem bad : False := @sorryAx False (!true)\n");
    assert!(
        sorry.total_failed >= 1 && !sorry.is_fully_verified(),
        "a non-literal-flag sorry is refused by the parallel API too: {:?}",
        sorry.errors
    );
}

/// The two forms these tests used to write are not Lean: pinned v4.30.0-rc2
/// refuses `sorryAx False : False` ("Type mismatch ... ∀ (synthetic : Bool),
/// False") and `myTrusted False` for `def myTrusted := @trustedAy`, whose
/// binder stays implicit ("Function expected"). Clean refuses both at
/// elaboration, and neither may pass as a checked declaration.
#[test]
fn partial_and_implicit_alias_forms_are_elaboration_errors() {
    for source in [
        "theorem bad : False := sorryAx False\n",
        "def myTrusted := @trustedAy\ntheorem bad : False := myTrusted False\n",
    ] {
        let result = check(source);
        assert!(!result.is_fully_verified(), "{source}: {result:?}");
        assert!(
            result
                .errors
                .iter()
                .any(|(_, msg)| msg.contains("TypeMismatch")
                    || msg.contains("TooManyArguments")
                    || msg.contains("not a function type")),
            "{source}: expected an elaboration refusal, got {result:?}"
        );
        assert!(
            !result
                .declarations
                .iter()
                .any(|d| d.name.ends_with("bad") && d.passed),
            "{source}: `bad` passed: {result:?}"
        );
    }
}
