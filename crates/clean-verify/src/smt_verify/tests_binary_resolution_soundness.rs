// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness regression tests for binary resolution (#3346).
//!
//! These tests exercise the #3346 soundness contract:
//! *Binary resolution on pivot `p` must remove only `+p` from the premise
//! containing `+p` and only `~p` from the premise containing `~p`.*
//! Any literal whose variable is not the pivot — including the opposite
//! polarity of the pivot in a tautological premise — must survive.
//!
//! The production fix landed in commit 144a1de48 (`[U]3195: Harden SMT
//! resolution checker with correct pivot elimination`), which replaced the
//! pre-existing buggy single-filter implementation that stripped BOTH
//! polarities from BOTH premises with the polarity-aware `c1_strip` /
//! `c2_strip` logic in `check_binary_resolution`.
//!
//! Pre-fix behavior (#3346 example): with `C1 = {a, ~a, b}` and
//! `C2 = {a, c}`, resolving on pivot `a` produced `{b, c}` because the
//! checker removed BOTH `a` and `~a` from BOTH premises. The attacker could
//! exploit tautological premises to drop arbitrary literals and claim
//! strengthened (or even empty) resolvents.
//!
//! The tests here target the binary-resolution surface with:
//!   1. **Positive controls** — the polarity-correct resolvent is accepted.
//!   2. **Forgery battery** — every shape of buggy "strip-both" claim is
//!      rejected as `Trusted`.
//!   3. **Premise-order invariance** — swapping `C1` and `C2` produces the
//!      same accept/reject verdicts. A regression re-introducing the old
//!      single-filter logic (or any claim-guided strip) would typically
//!      leave fingerprints as order-dependent verdicts when one premise is
//!      tautological and the other is not.
//!
//! Source: `designs/2026-04-17-AI Model-soundness-review-sat-smt.md` finding F2.

use super::dag::{SmtProofDag, SmtProofStep, SmtSort, SmtStepId, SmtTerm, SmtTermId};
use super::resolution::check_resolution;
use super::trust::StepTrustLevel;

/// Build the canonical #3346 example DAG:
/// `C1 = {a, ~a, b}`, `C2 = {a, c}`, pivot `a`.
///
/// Returns `(dag, derived, a, b, c, not_a)` so tests can reuse term IDs
/// for both positive-control and forgery claims, and for premise-order
/// permutations.
fn build_issue_3346_dag() -> (
    SmtProofDag,
    Vec<Option<Vec<SmtTermId>>>,
    SmtTermId, // a
    SmtTermId, // b
    SmtTermId, // c
    SmtTermId, // not_a
) {
    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
    let not_a = dag.add_term(SmtTerm::Not(a));

    // Placeholder steps so premise step IDs line up with indices 0, 1.
    let _s0 = dag.add_step(SmtProofStep::Assume(a));
    let _s1 = dag.add_step(SmtProofStep::Assume(not_a));

    // C1 contains the pivot variable in BOTH polarities (tautological).
    // C2 contains only the positive polarity. This is the exact scenario
    // from the #3346 issue body.
    let derived = vec![
        Some(vec![a, not_a, b]), // premise 0 = C1 (tautological)
        Some(vec![a, c]),        // premise 1 = C2
    ];
    (dag, derived, a, b, c, not_a)
}

#[test]
fn test_3346_issue_example_accepts_correct_resolvent() {
    // Positive control: claim the polarity-correct resolvent {a, b, c}.
    //
    // C1 = {a, ~a, b} contains ~a (negative polarity of pivot a);
    // C2 = {a, c}     contains  a (positive polarity of pivot a).
    // Strip ~a from C1: {a, b}.  Strip  a from C2: {c}.
    // Resolvent = {a, b, c}.  `a` (the positive polarity, present in C1
    // in its tautological form) survives because it is NOT the polarity
    // being eliminated from C1.
    let (dag, derived, a, b, c, _not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[a, b, c],
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::KernelVerified,
        "#3346 positive control: polarity-correct resolvent {{a, b, c}} \
         must be accepted: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_forgery_strip_both_polarities_rejected() {
    // Forgery battery #1: the exact buggy resolvent {b, c} from the issue
    // body. This is what the pre-144a1de48 single-filter implementation
    // produced by stripping BOTH `a` AND `~a` from both premises.
    // The fixed checker MUST reject this claim.
    let (dag, derived, a, b, c, _not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[b, c], // buggy claim: `a` silently dropped
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::Trusted,
        "#3346 forgery: claim {{b, c}} from stripping BOTH polarities must \
         be rejected (Trusted), got {:?}: {:?}",
        verdict.trust_level,
        verdict.detail
    );
}

#[test]
fn test_3346_forgery_drop_non_pivot_literal_rejected() {
    // Forgery battery #2: attacker claims {a, b} — drops the non-pivot
    // literal `c` from C2. Even though the positive polarity of the pivot
    // is preserved, dropping a non-pivot literal is still a fabrication.
    let (dag, derived, a, b, _c, _not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[a, b], // missing `c`
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::Trusted,
        "#3346 forgery: dropping non-pivot literal `c` must be rejected: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_forgery_drop_both_polarity_of_pivot_rejected() {
    // Forgery battery #3: attacker claims {b, c} with ~a dropped even
    // though ~a should survive from C1 (it is not the pivot's polarity
    // being eliminated from C1 under the current polarity choice).
    //
    // This is the exact forgery the OLD single-filter implementation
    // accepted: `pivot_ids = [a, not_a]` followed by an unconditional
    // `c1.chain(c2).filter(|l| !pivot_ids.contains(l))` would drop both
    // `a` and `~a` from BOTH premises.
    let (dag, derived, a, _b, c, _not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[c], // only c survives — maximally strengthened forgery
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::Trusted,
        "#3346 forgery: maximally-strengthened claim {{c}} must be rejected: \
         {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_forgery_empty_clause_rejected() {
    // Forgery battery #4: attacker claims the empty clause. This is the
    // most extreme "strip everything" variant — the pre-fix checker's
    // vacuous subset check (`expected.iter().all(|l| result.contains(l))`
    // being trivially true when `expected` is empty) let this claim
    // through. The fixed checker must reject it since the true resolvent
    // is {a, b, c}, not the empty set.
    let (dag, derived, a, _b, _c, _not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[],
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::Trusted,
        "#3346 forgery: empty-clause claim must be rejected: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_premise_order_invariance_positive() {
    // Invariance: swapping the order of C1 and C2 must not change the
    // accept verdict for the polarity-correct resolvent.
    //
    // With premises in order [C2, C1], C1 now has index 1, C2 has index 0.
    // The pivot is still `a`:
    //   C2 = {a, c}        — new index 0 — has positive polarity.
    //   C1 = {a, ~a, b}    — new index 1 — has both polarities.
    // The checker's `(p1_has_pivot && p2_has_neg) || (p1_has_neg &&
    // p2_has_pivot)` branch logic must still identify the complementary
    // pair and strip correctly regardless of order.
    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
    let not_a = dag.add_term(SmtTerm::Not(a));
    let _s0 = dag.add_step(SmtProofStep::Assume(a));
    let _s1 = dag.add_step(SmtProofStep::Assume(not_a));

    // Swapped order: C2 first, then C1.
    let derived = vec![
        Some(vec![a, c]),        // premise 0 = C2
        Some(vec![a, not_a, b]), // premise 1 = C1 (tautological)
    ];
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[a, b, c],
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::KernelVerified,
        "#3346 invariance: premise order [C2, C1] must still accept the \
         polarity-correct resolvent {{a, b, c}}: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_premise_order_invariance_forgery() {
    // Invariance: swapping C1 and C2 must not change the REJECT verdict
    // for the pre-fix buggy resolvent {b, c}. A regression to the old
    // single-filter logic might happen to produce order-dependent verdicts
    // when one premise is tautological — e.g., a future refactor that
    // chose `c1_strip` before checking which premise contains which
    // polarity could flip one ordering's verdict.
    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
    let not_a = dag.add_term(SmtTerm::Not(a));
    let _s0 = dag.add_step(SmtProofStep::Assume(a));
    let _s1 = dag.add_step(SmtProofStep::Assume(not_a));

    let derived = vec![
        Some(vec![a, c]),        // premise 0 = C2
        Some(vec![a, not_a, b]), // premise 1 = C1 (tautological)
    ];
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[b, c], // same buggy claim, swapped order
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::Trusted,
        "#3346 invariance: buggy claim {{b, c}} must remain rejected \
         under premise order [C2, C1]: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_pivot_passed_as_negative_polarity_invariance() {
    // The checker accepts either `pivot` or `neg_pivot` as the `pivot`
    // argument. Pass `~a` as the pivot token instead of `a` and confirm
    // the same polarity-correct resolvent is accepted.
    //
    // This guards against a future bug where the polarity branch logic
    // was tied to the pivot *token*'s polarity rather than to which
    // premise contains which polarity.
    let (dag, derived, a, b, c, not_a) = build_issue_3346_dag();
    let step_id = SmtStepId(2);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[a, b, c],
        &[SmtStepId(0), SmtStepId(1)],
        Some(not_a), // pass negative polarity as pivot token
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::KernelVerified,
        "#3346 invariance: pivot passed as `~a` must still accept the \
         polarity-correct resolvent {{a, b, c}}: {:?}",
        verdict.detail
    );
}

#[test]
fn test_3346_both_tautological_preserves_all_non_pivot_polarities() {
    // Adversarial construction: BOTH premises are tautological on the
    // pivot variable. The correct resolvent preserves the non-pivot
    // polarity from each side:
    //   C1 = {a, ~a, b}       — tautological.
    //   C2 = {a, ~a, c}       — tautological.
    //   pivot = a.
    //   Strip `a` from C1  -> {~a, b}
    //   Strip `~a` from C2 -> {a, c}
    //   Resolvent = {~a, b, a, c} = {a, ~a, b, c}.
    //
    // The pre-fix implementation would strip both `a` and `~a` from BOTH
    // premises, producing {b, c}. The fixed checker must reject that
    // forgery and accept the true (still-tautological) resolvent.
    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
    let not_a = dag.add_term(SmtTerm::Not(a));
    let _s0 = dag.add_step(SmtProofStep::Assume(a));
    let _s1 = dag.add_step(SmtProofStep::Assume(not_a));

    let derived = vec![Some(vec![a, not_a, b]), Some(vec![a, not_a, c])];
    let step_id = SmtStepId(2);

    // Accept the true resolvent {a, ~a, b, c}.
    let verdict_accept = check_resolution(
        &dag,
        step_id,
        &[a, not_a, b, c],
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict_accept.trust_level,
        StepTrustLevel::KernelVerified,
        "#3346 both-tautological: true resolvent {{a, ~a, b, c}} must be \
         accepted: {:?}",
        verdict_accept.detail
    );

    // Reject the buggy "strip both from both" resolvent {b, c}.
    let verdict_reject = check_resolution(
        &dag,
        step_id,
        &[b, c],
        &[SmtStepId(0), SmtStepId(1)],
        Some(a),
        &derived,
    );
    assert_eq!(
        verdict_reject.trust_level,
        StepTrustLevel::Trusted,
        "#3346 both-tautological: buggy claim {{b, c}} (strip both from \
         both) must be rejected: {:?}",
        verdict_reject.detail
    );
}
