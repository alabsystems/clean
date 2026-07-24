// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for existential/Skolem handling and atom deduplication in the bridge.
//! Covers flatten_exists, add_hypothesis for existentials, negated existentials,
//! and opaque atom deduplication.
//! Split from bridge/tests.rs as part of #307.

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use crate::smt::TheoryLiteral;

/// Helper to create an Exists expression: ∃ x : T, P(x)
fn make_exists(ty: Expr, body: Expr) -> Expr {
    // Exists T (fun x : T => body)
    // where body contains BVar(0) for the bound variable
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            ty.clone(),
        ),
        Expr::lam(BinderInfo::Default, ty, body),
    )
}

// ========================================================================
// Nested Existential Handling Tests
// ========================================================================

#[test]
fn test_flatten_exists_single() {
    // Test flattening a single existential: ∃ x : A, P(x)
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);

    // Body: P(BVar(0))
    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));

    let (types, body) = bridge.flatten_exists(&ty_a, &p_x);

    assert_eq!(types.len(), 1, "Single existential should have 1 type");
    assert!(
        matches!(types[0].kind(), ExprKind::Const(ref name, _) if name.to_string() == "A"),
        "Type should be A"
    );

    // Body should be unchanged: P(BVar(0))
    // Check it is an App with head function P and argument BVar(0)
    let head = body.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "P"),
        "Body head should be P, got {head:?}"
    );
    let args = body.get_app_args();
    assert_eq!(args.len(), 1, "P should have exactly 1 argument");
    assert!(
        matches!(args[0].kind(), ExprKind::BVar(0)),
        "P's argument should be BVar(0), got {:?}",
        args[0].kind()
    );
}

#[test]
fn test_flatten_exists_nested() {
    // Test flattening nested existentials: ∃ x : A, ∃ y : B, P(x, y)
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);

    // Inner body: P(BVar(1), BVar(0)) - x is BVar(1), y is BVar(0) after flattening
    let p_x_y = Expr::app(
        Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );

    // Inner existential: ∃ y : B, P(x, y)
    // In the context of the outer existential, x is BVar(0)
    // so the inner body has x as BVar(1) (after the inner binder) and y as BVar(0)
    let inner_exists = make_exists(ty_b.clone(), p_x_y.clone());

    let (types, _body) = bridge.flatten_exists(&ty_a, &inner_exists);

    assert_eq!(
        types.len(),
        2,
        "Nested existential should flatten to 2 types, got {}",
        types.len()
    );
    assert!(
        matches!(types[0].kind(), ExprKind::Const(ref name, _) if name.to_string() == "A"),
        "First type should be A"
    );
    assert!(
        matches!(types[1].kind(), ExprKind::Const(ref name, _) if name.to_string() == "B"),
        "Second type should be B"
    );
}

#[test]
fn test_flatten_exists_triple_nested() {
    // Test flattening triple nested existentials: ∃ x : A, ∃ y : B, ∃ z : C, P(x, y, z)
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let ty_c = Expr::const_(Name::from_string("C"), vec![]);

    // Innermost body: P(BVar(2), BVar(1), BVar(0))
    let p_x_y_z = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(2)),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    // Build from inside out:
    // ∃ z : C, P(x, y, z)
    let inner1 = make_exists(ty_c.clone(), p_x_y_z);
    // ∃ y : B, (∃ z : C, P(x, y, z))
    let inner2 = make_exists(ty_b.clone(), inner1);

    let (types, _body) = bridge.flatten_exists(&ty_a, &inner2);

    assert_eq!(
        types.len(),
        3,
        "Triple nested existential should flatten to 3 types, got {}",
        types.len()
    );
    assert!(
        matches!(types[0].kind(), ExprKind::Const(ref name, _) if name.to_string() == "A"),
        "First type should be A"
    );
    assert!(
        matches!(types[1].kind(), ExprKind::Const(ref name, _) if name.to_string() == "B"),
        "Second type should be B"
    );
    assert!(
        matches!(types[2].kind(), ExprKind::Const(ref name, _) if name.to_string() == "C"),
        "Third type should be C"
    );
}

#[test]
fn test_exists_hypothesis_single() {
    // Test adding a single existential hypothesis: ∃ x : A, P(x)
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));

    let exists_expr = make_exists(ty_a, p_x);

    let fresh_before = bridge.fresh_counter;
    let smt_terms_before = bridge.stats().num_terms;

    let result = bridge.add_hypothesis(&exists_expr);
    assert!(
        result.is_ok(),
        "Should be able to add single existential hypothesis"
    );

    // Skolem witness creation advances fresh_counter: 1 for the witness itself,
    // plus potentially more when the instantiated body (P(witness)) is processed
    // as an atom and gets a fresh boolean variable.
    let fresh_advance = bridge.fresh_counter - fresh_before;
    assert!(
        fresh_advance >= 1,
        "Single ∃ should create at least 1 Skolem witness, \
         fresh_counter advanced by {fresh_advance}"
    );
    // SMT solver should have new terms from the Skolem instantiation
    let new_terms = bridge.stats().num_terms - smt_terms_before;
    assert!(
        new_terms >= 1,
        "Adding ∃ hypothesis should create at least 1 new SMT term \
         (the Skolem witness), got {new_terms} new terms"
    );
    // Verify the Skolem witness term exists in the SMT solver with expected naming
    let witness_name = format!("exists_witness_0_{fresh_before}");
    let has_witness = (0..bridge.stats().num_terms).any(|i| {
        matches!(
            bridge.smt.get_term(TermId(i as u32)),
            Some(crate::smt::SmtTerm::Const(sym)) if sym.name() == witness_name
        )
    });
    assert!(
        has_witness,
        "SMT solver should contain Skolem witness term named '{witness_name}'"
    );
}

#[test]
fn test_exists_hypothesis_nested() {
    // Test adding a nested existential hypothesis: ∃ x : A, ∃ y : B, R(x, y)
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);

    // R(BVar(1), BVar(0)) - R applied to both bound vars
    let r_x_y = Expr::app(
        Expr::app(Expr::const_(Name::from_string("R"), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );

    let inner_exists = make_exists(ty_b, r_x_y);
    let outer_exists = make_exists(ty_a, inner_exists);

    let fresh_before = bridge.fresh_counter;
    let terms_before = bridge.stats().num_terms;

    let result = bridge.add_hypothesis(&outer_exists);
    assert!(
        result.is_ok(),
        "Should be able to add nested existential hypothesis"
    );

    // Two Skolem witnesses must have been created (one per ∃ variable)
    let fresh_advance = bridge.fresh_counter - fresh_before;
    assert!(
        fresh_advance >= 2,
        "Nested ∃ x, ∃ y should create at least 2 Skolem witnesses, \
         fresh_counter advanced by {fresh_advance} (expected >= 2)"
    );
    // Verify that new SMT terms were created for both witnesses
    let new_terms = bridge.stats().num_terms - terms_before;
    assert!(
        new_terms >= 2,
        "Nested ∃ should create at least 2 new SMT terms (one per witness), got {new_terms}"
    );
    // Verify both witness terms exist with the exists_witness naming pattern
    let witness_0 = format!("exists_witness_0_{fresh_before}");
    let witness_1 = format!("exists_witness_1_{}", fresh_before + 1);
    let term_names: Vec<String> = (0..bridge.stats().num_terms)
        .filter_map(|i| match bridge.smt.get_term(TermId(i as u32)) {
            Some(crate::smt::SmtTerm::Const(sym)) => Some(sym.name().to_string()),
            _ => None,
        })
        .collect();
    assert!(
        term_names.iter().any(|n| n == &witness_0),
        "Should contain first Skolem witness '{witness_0}', got const terms: {term_names:?}"
    );
    assert!(
        term_names.iter().any(|n| n == &witness_1),
        "Should contain second Skolem witness '{witness_1}', got const terms: {term_names:?}"
    );
}

#[test]
fn test_exists_hypothesis_with_equality_conclusion() {
    // Test: from ∃ x : A, ∃ y : A, x = y, we can derive witness equalities
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);

    // x = y where x is BVar(1), y is BVar(0)
    let eq_body = make_eq(ty_a.clone(), Expr::bvar(1), Expr::bvar(0));

    let inner_exists = make_exists(ty_a.clone(), eq_body);
    let outer_exists = make_exists(ty_a, inner_exists);

    let fresh_before = bridge.fresh_counter;
    let terms_before = bridge.stats().num_terms;

    // Add the hypothesis
    let result = bridge.add_hypothesis(&outer_exists);
    assert!(
        result.is_ok(),
        "Should handle nested existential with equality body"
    );

    // Two Skolem witnesses must have been created
    let fresh_advance = bridge.fresh_counter - fresh_before;
    assert!(
        fresh_advance >= 2,
        "∃ x, ∃ y with equality body should create at least 2 Skolem witnesses, \
         fresh_counter advanced by {fresh_advance}"
    );

    // The Skolem witnesses should have been asserted as equal in the SMT context.
    // The body is sk_x = sk_y, so the SMT solver should have received an equality
    // assertion between the two witness terms. This means new terms were created:
    // 2 witness constants + any terms from the equality assertion.
    let new_terms = bridge.stats().num_terms - terms_before;
    assert!(
        new_terms >= 2,
        "∃ x, ∃ y, x = y should create at least 2 new SMT terms \
         (the two Skolem witnesses), got {new_terms}"
    );
    // Verify the witness terms exist with correct naming
    let witness_0 = format!("exists_witness_0_{fresh_before}");
    let witness_1 = format!("exists_witness_1_{}", fresh_before + 1);
    let has_w0 = (0..bridge.stats().num_terms).any(|i| {
        matches!(
            bridge.smt.get_term(TermId(i as u32)),
            Some(crate::smt::SmtTerm::Const(sym)) if sym.name() == witness_0
        )
    });
    let has_w1 = (0..bridge.stats().num_terms).any(|i| {
        matches!(
            bridge.smt.get_term(TermId(i as u32)),
            Some(crate::smt::SmtTerm::Const(sym)) if sym.name() == witness_1
        )
    });
    assert!(has_w0, "Should contain Skolem witness '{witness_0}'");
    assert!(has_w1, "Should contain Skolem witness '{witness_1}'");
}

// --- Negated existential tests (#2126) ---

#[test]
fn test_negated_exists_creates_witness_not_opaque_atom() {
    // ¬(∃ x : A, P(x)) ≡ ∀ x : A, ¬P(x)
    // When the goal is ∃ x : A, P(x), the bridge negates it.
    // Previously this fell back to an opaque atom — verify it now creates
    // proper witness terms and negates the body.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));

    // Goal: ∃ x : A, P(x)
    let exists_goal = make_exists(ty_a, p_x);

    let fresh_before = bridge.fresh_counter;

    // Add a False hypothesis so UNSAT is reachable after negation processing
    let false_hyp = Expr::const_(Name::from_string("False"), vec![]);
    bridge.add_hypothesis(&false_hyp).unwrap();

    let result = bridge.prove(&exists_goal).unwrap();

    // The negation should have created at least 1 witness
    // (fresh_counter advances for witness name + possibly body atoms)
    let fresh_advance = bridge.fresh_counter - fresh_before;
    assert!(
        fresh_advance >= 1,
        "Negated ∃ should create at least 1 witness term, \
         fresh_counter only advanced by {fresh_advance}"
    );

    // With a False hypothesis, SMT should prove UNSAT.
    // After #2393: non-equality goals return Unverified (no proof reconstruction).
    assert!(
        result.is_verified() || result.is_unverified(),
        "∃ goal with False hypothesis should be provable (Verified or Unverified), got {:?}",
        result
    );
}

#[test]
fn test_negated_exists_stores_pending_forall_for_ematching() {
    // Verify that ¬(∃ x : A, P(x)) creates a PendingForall entry
    // so E-matching can find additional instantiations.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    // Body: f(x) = g(x) — contains function applications that yield E-matching triggers
    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let eq_body = make_eq(ty_a.clone(), f_x, g_x);

    let exists_goal = make_exists(ty_a, eq_body);

    let pending_before = bridge.pending_foralls.len();

    // Directly invoke translate_negated_classified to test the negation path
    let goal_class = bridge.classify_prop(&exists_goal);
    let result = bridge.translate_negated_classified(&goal_class);

    assert!(
        result.is_ok(),
        "translate_negated_classified should succeed for Exists goal"
    );

    // Should have stored at least one PendingForall for E-matching
    // (only if triggers were extracted from the body)
    let pending_after = bridge.pending_foralls.len();
    assert!(
        pending_after > pending_before,
        "Negated ∃ with function applications should create PendingForall \
         for E-matching, but pending_foralls count unchanged: {pending_before} → {pending_after}"
    );

    // The PendingForall body should be Not(original_body)
    let last_pending = bridge.pending_foralls.last().unwrap();
    let body_head = last_pending.body.get_app_fn();
    if let ExprKind::Const(name, _) = body_head.kind() {
        assert_eq!(
            name.to_string(),
            "Not",
            "PendingForall body should be wrapped with Not, got head: {name}"
        );
    } else {
        panic!(
            "PendingForall body should be App(Not, ...), got: {:?}",
            body_head.kind()
        );
    }
}

#[test]
fn test_negated_exists_witness_naming() {
    // Verify that negated ∃ creates witnesses with "neg_exists_witness_" prefix
    // (distinct from positive ∃ which uses "exists_witness_" prefix)
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    let exists_goal = make_exists(ty_a, p_x);

    let fresh_before = bridge.fresh_counter;

    let goal_class = bridge.classify_prop(&exists_goal);
    bridge.translate_negated_classified(&goal_class).unwrap();

    // Check that the witness term uses the correct naming prefix
    let expected_prefix = format!("neg_exists_witness_0_{fresh_before}");
    let has_witness = (0..bridge.stats().num_terms).any(|i| {
        matches!(
            bridge.smt.get_term(TermId(i as u32)),
            Some(crate::smt::SmtTerm::Const(sym)) if sym.name().starts_with("neg_exists_witness_")
        )
    });
    assert!(
        has_witness,
        "SMT solver should contain witness term with 'neg_exists_witness_' prefix \
         (expected: '{expected_prefix}')"
    );
}

// --- Atom deduplication tests (#2251) ---

#[test]
fn test_atom_dedup_same_opaque_atom_same_variable() {
    // The same opaque atom expression appearing in hypothesis and goal
    // must map to the same SAT variable. Without dedup, each occurrence
    // gets a fresh variable and the solver treats them as independent.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Create an opaque atom: `Prime p` (unknown to the bridge)
    let prime_p = Expr::app(
        Expr::const_(Name::from_string("Prime"), vec![]),
        Expr::const_(Name::from_string("p"), vec![]),
    );

    // Translate the same atom twice with positive polarity
    let lit1 = bridge.prop_to_literal(&prime_p, true);
    let lit2 = bridge.prop_to_literal(&prime_p, true);

    assert_eq!(
        lit1, lit2,
        "Same opaque atom must produce the same TheoryLiteral (dedup). \
         Got {:?} and {:?}",
        lit1, lit2
    );
}

#[test]
fn test_atom_dedup_opposite_polarity_same_variable() {
    // Same atom with opposite polarity must use the same variable ID
    // but different polarity (Bool vs NegBool).
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let prime_p = Expr::app(
        Expr::const_(Name::from_string("Prime"), vec![]),
        Expr::const_(Name::from_string("p"), vec![]),
    );

    let pos = bridge.prop_to_literal(&prime_p, true);
    let neg = bridge.prop_to_literal(&prime_p, false);

    // Should be Bool(v) and NegBool(v) for the same v
    match (&pos, &neg) {
        (Ok(TheoryLiteral::Bool(v1)), Ok(TheoryLiteral::NegBool(v2))) => {
            assert_eq!(
                v1, v2,
                "Same atom at opposite polarity must use same variable: Bool({v1}) vs NegBool({v2})"
            );
        }
        _ => panic!(
            "Expected Bool(v) and NegBool(v), got {:?} and {:?}",
            pos, neg
        ),
    }
}

#[test]
fn test_atom_dedup_different_atoms_different_variables() {
    // Different atoms must get different variables.
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let prime_p = Expr::app(
        Expr::const_(Name::from_string("Prime"), vec![]),
        Expr::const_(Name::from_string("p"), vec![]),
    );
    let prime_q = Expr::app(
        Expr::const_(Name::from_string("Prime"), vec![]),
        Expr::const_(Name::from_string("q"), vec![]),
    );

    let lit1 = bridge.prop_to_literal(&prime_p, true);
    let lit2 = bridge.prop_to_literal(&prime_q, true);

    assert_ne!(
        lit1, lit2,
        "Different atoms must produce different TheoryLiterals. \
         Got {:?} and {:?}",
        lit1, lit2
    );
}
