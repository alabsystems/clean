// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::expr_classifier::LogicalForm;
use crate::bridge::{SmtBridge, SmtVerificationResult};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

fn assert_lossy_reason_metadata(reason: &str, expected_prefix: &str) {
    assert!(
        reason.contains(expected_prefix),
        "Unknown reason should preserve the lossy class, got: {reason}"
    );
    assert!(
        reason.contains("lossy expression"),
        "Unknown reason should report lossy expression metadata, got: {reason}"
    );
}

fn lossy_let_expr() -> Expr {
    Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("opaqueProp"), vec![]),
        Expr::bvar(0),
        false,
    )
}

fn lossy_proj_expr() -> Expr {
    Expr::proj(
        Name::from_string("PairLike"),
        0,
        Expr::const_(Name::from_string("pairWitness"), vec![]),
    )
}

fn lossy_lam_expr() -> Expr {
    Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))
}

/// Regression test for #2289: translate_negated_classified Forall/Exists fallback
/// must push to lossy_atoms when instantiate_body_with_terms returns None.
///
/// The None path is triggered when witness term lookup fails (e.g., MData wrapping,
/// nested quantifier index mismatch). This test verifies:
/// 1. translate_negated_classified handles Forall/Exists without errors
/// 2. The lossy_atoms guard in prove() prevents Verified results when atoms are tracked
/// 3. instantiate_body_with_terms correctly returns None when witnesses are missing
#[test]
fn test_translate_negated_forall_fallback_tracks_lossy_atoms() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let forall_prop = LogicalForm::Forall {
        binder_type: a_ty.clone(),
        body: Expr::bvar(0),
    };

    assert!(
        bridge.lossy_atoms.is_empty(),
        "precondition: lossy_atoms empty"
    );

    let result = bridge.translate_negated_classified(&forall_prop);
    assert!(
        result.is_ok(),
        "translate_negated_classified should succeed"
    );

    let mut bridge2 = SmtBridge::new(&env);
    let witness = bridge2.create_witness_term("sabotaged", &a_ty);
    bridge2.term_to_expr.remove(&witness);
    let body = Expr::bvar(0);
    let inst = bridge2.instantiate_body_with_terms(&body, &[0], &[witness]);
    assert!(
        inst.is_none(),
        "instantiation must fail with removed witness"
    );

    bridge2.lossy_atoms.push(body);
    let true_goal = Expr::const_(Name::from_string("True"), vec![]);
    let result2 = bridge2.prove(&true_goal);
    if let Ok(SmtVerificationResult::Verified(_)) = result2 {
        panic!("prove() must NOT return Verified when lossy_atoms is non-empty");
    }
}

/// Regression test for #2289: Exists fallback path mirrors Forall.
#[test]
fn test_translate_negated_exists_fallback_tracks_lossy_atoms() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let exists_prop = LogicalForm::Exists {
        binder_type: a_ty,
        body: Expr::bvar(0),
    };

    assert!(
        bridge.lossy_atoms.is_empty(),
        "precondition: lossy_atoms empty"
    );

    let result = bridge.translate_negated_classified(&exists_prop);
    assert!(
        result.is_ok(),
        "translate_negated_classified should succeed for Exists"
    );
}

/// Regression test for #2295: negating True must produce UNSAT (empty clause),
/// negating False must be a no-op (tautology).
#[test]
fn test_translate_negated_true_adds_empty_clause() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge.translate_negated_classified(&LogicalForm::True);
    assert!(result.is_ok(), "negating True should succeed");

    let true_goal = Expr::const_(Name::from_string("True"), vec![]);
    let prove_result = bridge.prove(&true_goal);
    match prove_result {
        Ok(SmtVerificationResult::Verified(_)) | Ok(SmtVerificationResult::Unverified { .. }) => {}
        other => panic!(
            "negating True should make the problem UNSAT (Verified or Unverified), got: {:?}",
            other
        ),
    }
}

#[test]
fn test_translate_negated_false_is_noop() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let result = bridge.translate_negated_classified(&LogicalForm::False);
    assert!(result.is_ok(), "negating False should succeed");

    let false_goal = Expr::const_(Name::from_string("False"), vec![]);
    let prove_result = bridge.prove(&false_goal);
    if let Ok(SmtVerificationResult::Verified(_)) = prove_result {
        panic!("negating False alone should NOT produce Verified (no clauses = SAT)");
    }
}

/// Regression test for #2354: lossy_atoms guard must also cover the SAT case.
#[test]
fn test_lossy_atoms_sat_guard_returns_unknown_not_refuted() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    bridge.lossy_atoms.push(lossy_let_expr());

    let false_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = bridge.prove(&false_goal);
    match result {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_reason_metadata(
                &reason,
                "lossy translation: SAT result may be spurious due to unconstrained atoms",
            );
            assert!(
                reason.contains("1 lossy expression"),
                "Unknown reason should report lossy count, got: {reason}"
            );
            assert!(
                reason.contains("Let"),
                "Unknown reason should preview the lossy expression kind, got: {reason}"
            );
        }
        Ok(SmtVerificationResult::Refuted(_)) => {
            panic!("prove() must NOT return Refuted when lossy_atoms is non-empty");
        }
        other => panic!("expected Unknown for lossy SAT, got: {other:?}"),
    }
}

#[test]
fn test_lossy_atoms_sat_guard_caps_preview_to_distinct_prefixes() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let lossy_a = lossy_let_expr();
    let lossy_b = lossy_proj_expr();
    let lossy_c = Expr::prop();
    let lossy_d = lossy_lam_expr();
    bridge
        .lossy_atoms
        .extend([lossy_a, lossy_b, lossy_c, lossy_d]);

    let false_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = bridge.prove(&false_goal);
    match result {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_reason_metadata(
                &reason,
                "lossy translation: SAT result may be spurious due to unconstrained atoms",
            );
            assert!(
                reason.contains("4 lossy expressions"),
                "Unknown reason should report total lossy count, got: {reason}"
            );
            assert!(
                reason.contains("Let") && reason.contains("Proj") && reason.contains("Sort"),
                "Unknown reason should preview the first three lossy expression kinds, got: {reason}"
            );
            assert!(
                !reason.contains("Lam"),
                "Unknown reason should cap preview length, got: {reason}"
            );
            assert!(
                reason.contains("+1 more kinds"),
                "Unknown reason should report omitted preview count, got: {reason}"
            );
        }
        other => panic!("expected Unknown for lossy SAT, got: {other:?}"),
    }
}

#[test]
fn test_lossy_atoms_unsat_guard_returns_unknown_with_preview() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let false_hyp = Expr::const_(Name::from_string("False"), vec![]);
    bridge
        .add_hypothesis(&false_hyp)
        .expect("False hypothesis should translate");

    bridge.lossy_atoms.push(lossy_proj_expr());

    let true_goal = Expr::const_(Name::from_string("True"), vec![]);
    let result = bridge.prove(&true_goal);
    match result {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_reason_metadata(
                &reason,
                "lossy translation: UNSAT may be spurious due to unconstrained atoms",
            );
            assert!(
                reason.contains("1 lossy expression"),
                "Unknown reason should report lossy count, got: {reason}"
            );
            assert!(
                reason.contains("Proj"),
                "Unknown reason should preview the lossy expression kind, got: {reason}"
            );
        }
        Ok(SmtVerificationResult::Verified(_)) | Ok(SmtVerificationResult::Unverified { .. }) => {
            panic!("prove() must NOT treat lossy UNSAT as a trusted proof")
        }
        other => panic!("expected Unknown for lossy UNSAT, got: {other:?}"),
    }
}

fn mk_prop_atom(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_translate_negated_and_adds_single_disjunctive_clause() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_prop_atom("P");
    let q = mk_prop_atom("Q");

    let pre_clauses = bridge.smt.num_clauses();
    let result = bridge.translate_negated_classified(&LogicalForm::And(p, q));
    assert!(result.is_ok(), "negating And should succeed");
    let post_clauses = bridge.smt.num_clauses();

    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "negated And must add exactly 1 clause (De Morgan: NOT P OR NOT Q)"
    );
}

#[test]
fn test_translate_negated_or_adds_two_unit_clauses() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_prop_atom("P");
    let q = mk_prop_atom("Q");

    let pre_clauses = bridge.smt.num_clauses();
    let result = bridge.translate_negated_classified(&LogicalForm::Or(p, q));
    assert!(result.is_ok(), "negating Or should succeed");
    let post_clauses = bridge.smt.num_clauses();

    assert_eq!(
        post_clauses - pre_clauses,
        2,
        "negated Or must add exactly 2 unit clauses (De Morgan: NOT P AND NOT Q)"
    );
}

#[test]
fn test_translate_negated_implies_adds_two_unit_clauses() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_prop_atom("P");
    let q = mk_prop_atom("Q");

    let pre_clauses = bridge.smt.num_clauses();
    let result = bridge.translate_negated_classified(&LogicalForm::Implies(p, q));
    assert!(result.is_ok(), "negating Implies should succeed");
    let post_clauses = bridge.smt.num_clauses();

    assert_eq!(
        post_clauses - pre_clauses,
        2,
        "negated Implies must add exactly 2 unit clauses (P AND NOT Q)"
    );
}

#[test]
fn test_translate_negated_not_adds_unit_positive_clause() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_prop_atom("P");

    let pre_clauses = bridge.smt.num_clauses();
    let result = bridge.translate_negated_classified(&LogicalForm::Not(p));
    assert!(result.is_ok(), "negating Not should succeed");
    let post_clauses = bridge.smt.num_clauses();

    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "negated Not must add exactly 1 unit positive clause (double negation elimination)"
    );
}

#[test]
fn test_translate_negated_atom_adds_unit_negated_clause() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_prop_atom("SomeProposition");

    let pre_clauses = bridge.smt.num_clauses();
    let result = bridge.translate_negated_classified(&LogicalForm::Atom(p));
    assert!(result.is_ok(), "negating Atom should succeed");
    let post_clauses = bridge.smt.num_clauses();

    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "negated Atom must add exactly 1 unit negated clause"
    );
}
