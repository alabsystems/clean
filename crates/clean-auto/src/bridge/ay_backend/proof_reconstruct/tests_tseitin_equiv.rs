// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for equivalence Tseitin clausification rule handlers.
//!
//! Tests equiv_pos1, equiv_pos2, equiv_neg1, equiv_neg2 kernel proof
//! reconstruction with type-checking through the clean kernel.
//!
//! Part of #302.

use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};

/// Create an environment with propext, Iff, Classical.em, Eq, and propositional axioms.
fn mk_env_with_propext() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_iff().expect("init_iff");
    env.init_propext().expect("init_propext");

    // Add propositional axioms: testP, testQ : Prop
    let prop = Expr::sort(Level::zero());
    for name in ["testP", "testQ"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

/// Build ay terms for equiv scenarios: p, q are Bool-sorted propositions.
///
/// Returns (terms, map, ay_p, ay_q, ay_eq_pq, ay_not_eq_pq, ay_not_p, ay_not_q).
fn mk_bool_eq_terms() -> (
    TermStore,
    VariableMapping,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop = Expr::sort(Level::zero());
    let ay_p = terms.mk_var("fvar_p", Sort::Bool);
    let ay_q = terms.mk_var("fvar_q", Sort::Bool);

    map.register_var(
        "fvar_p",
        Expr::const_(Name::from_string("testP"), vec![]),
        prop.clone(),
    );
    map.register_var(
        "fvar_q",
        Expr::const_(Name::from_string("testQ"), vec![]),
        prop,
    );

    // Use mk_app to create raw (= p q) — mk_eq for Bool-sorted terms
    // applies ITE optimization, but Alethe proof clauses use raw equality.
    let ay_eq_pq = terms.mk_app(ay_core::Symbol::named("="), vec![ay_p, ay_q], Sort::Bool);
    let ay_not_eq_pq = terms.mk_not_raw(ay_eq_pq);
    let ay_not_p = terms.mk_not_raw(ay_p);
    let ay_not_q = terms.mk_not_raw(ay_q);

    (
        terms,
        map,
        ay_p,
        ay_q,
        ay_eq_pq,
        ay_not_eq_pq,
        ay_not_p,
        ay_not_q,
    )
}

/// Build expected clause type for equiv tests.
fn mk_eq_prop(x: &str, y: &str) -> Expr {
    let prop = Expr::sort(Level::zero());
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), prop),
            Expr::const_(Name::from_string(x), vec![]),
        ),
        Expr::const_(Name::from_string(y), vec![]),
    )
}

/// EquivPos1 proof term type-checks through the kernel.
///
/// equiv_pos1 clause: {¬(p = q), p, ¬q}. Proof by nested Classical.em on p and q
/// with Eq.mpr transport to derive the contradiction when ¬p and q both hold.
///
/// Part of #302.
#[test]
fn test_equiv_pos1_type_checks() {
    let env = mk_env_with_propext();
    let (terms, map, ay_p, _ay_q, _ay_eq_pq, ay_not_eq_pq, _ay_not_p, ay_not_q) =
        mk_bool_eq_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::EquivPos1,
        vec![ay_not_eq_pq, ay_p, ay_not_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert!(
        result.proof_term.is_some(),
        "equiv_pos1 should produce a proof term, stats: {:?}, error: {:?}",
        result.stats.rule_attempts,
        result.stats.error,
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "equiv_pos1 proof should have no trust sub-terms"
    );

    let proof_term = result.proof_term.unwrap();
    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("EquivPos1 proof term should type-check");

    // Expected: Or (Not (Eq Prop p q)) (Or p (Not q))
    let eq_pq = mk_eq_prop("testP", "testQ");
    let p_prop = Expr::const_(Name::from_string("testP"), vec![]);
    let q_prop = Expr::const_(Name::from_string("testQ"), vec![]);
    let not_eq = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_pq);
    let not_q = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), q_prop);
    let inner = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_prop),
        not_q,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_eq),
        inner,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "equiv_pos1 proof type should be def-eq to Or (Not (Eq Prop p q)) (Or p (Not q))"
    );
}

/// EquivPos2 proof term type-checks through the kernel.
///
/// equiv_pos2 clause: {¬(p = q), ¬p, q}. Proof by nested Classical.em on p and q
/// with Eq.mp transport to derive the contradiction when p and ¬q both hold.
///
/// Part of #302.
#[test]
fn test_equiv_pos2_type_checks() {
    let env = mk_env_with_propext();
    let (terms, map, _ay_p, ay_q, _ay_eq_pq, ay_not_eq_pq, ay_not_p, _ay_not_q) =
        mk_bool_eq_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::EquivPos2,
        vec![ay_not_eq_pq, ay_not_p, ay_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert!(
        result.proof_term.is_some(),
        "equiv_pos2 should produce a proof term"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "equiv_pos2 proof should have no trust sub-terms"
    );

    let proof_term = result.proof_term.unwrap();
    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("EquivPos2 proof term should type-check");

    // Expected: Or (Not (Eq Prop p q)) (Or (Not p) q)
    let eq_pq = mk_eq_prop("testP", "testQ");
    let p_prop = Expr::const_(Name::from_string("testP"), vec![]);
    let q_prop = Expr::const_(Name::from_string("testQ"), vec![]);
    let not_eq = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_pq);
    let not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_prop);
    let inner = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_p),
        q_prop,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_eq),
        inner,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "equiv_pos2 proof type should be def-eq to Or (Not (Eq Prop p q)) (Or (Not p) q)"
    );
}

/// EquivNeg1 proof term type-checks through the kernel.
///
/// equiv_neg1 clause: {(p = q), ¬p, ¬q}. Proof by nested Classical.em on p and q
/// with propext to construct the propositional equality when both hold.
///
/// Part of #302.
#[test]
fn test_equiv_neg1_type_checks() {
    let env = mk_env_with_propext();
    let (terms, map, _ay_p, _ay_q, ay_eq_pq, _ay_not_eq_pq, ay_not_p, ay_not_q) =
        mk_bool_eq_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::EquivNeg1,
        vec![ay_eq_pq, ay_not_p, ay_not_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert!(
        result.proof_term.is_some(),
        "equiv_neg1 should produce a proof term"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "equiv_neg1 proof should have no trust sub-terms"
    );

    let proof_term = result.proof_term.unwrap();
    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("EquivNeg1 proof term should type-check");

    // Expected: Or (Eq Prop p q) (Or (Not p) (Not q))
    let eq_pq = mk_eq_prop("testP", "testQ");
    let p_prop = Expr::const_(Name::from_string("testP"), vec![]);
    let q_prop = Expr::const_(Name::from_string("testQ"), vec![]);
    let not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_prop);
    let not_q = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), q_prop);
    let inner = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_p),
        not_q,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_pq),
        inner,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "equiv_neg1 proof type should be def-eq to Or (Eq Prop p q) (Or (Not p) (Not q))"
    );
}

/// EquivNeg2 proof term type-checks through the kernel.
///
/// equiv_neg2 clause: {(p = q), p, q}. Proof by nested Classical.em on p and q
/// with propext + absurd to construct the equality when both negations hold.
///
/// Part of #302.
#[test]
fn test_equiv_neg2_type_checks() {
    let env = mk_env_with_propext();
    let (terms, map, ay_p, ay_q, ay_eq_pq, _ay_not_eq_pq, _ay_not_p, _ay_not_q) =
        mk_bool_eq_terms();

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::EquivNeg2,
        vec![ay_eq_pq, ay_p, ay_q],
        vec![],
        vec![],
    );

    let neg_goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    assert!(
        result.proof_term.is_some(),
        "equiv_neg2 should produce a proof term"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "equiv_neg2 proof should have no trust sub-terms"
    );

    let proof_term = result.proof_term.unwrap();
    let ctx = LocalContext::new();
    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof_term)
        .expect("EquivNeg2 proof term should type-check");

    // Expected: Or (Eq Prop p q) (Or p q)
    let eq_pq = mk_eq_prop("testP", "testQ");
    let p_prop = Expr::const_(Name::from_string("testP"), vec![]);
    let q_prop = Expr::const_(Name::from_string("testQ"), vec![]);
    let inner = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_prop),
        q_prop,
    );
    let expected = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_pq),
        inner,
    );

    assert!(
        tc.is_def_eq(&ty, &expected),
        "equiv_neg2 proof type should be def-eq to Or (Eq Prop p q) (Or p q)"
    );
}
