// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::{SmtBridge, SmtVerificationResult};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            lhs,
        ),
        rhs,
    )
}

fn assert_lossy_unknown_reason(
    reason: &str,
    expected_prefix: &str,
    expected_count: &str,
    expected_kind: &str,
) {
    assert!(
        reason.contains(expected_prefix),
        "Unknown reason should preserve the lossy class, got: {reason}"
    );
    assert!(
        reason.contains(expected_count),
        "Unknown reason should report lossy count, got: {reason}"
    );
    assert!(
        reason.contains(expected_kind),
        "Unknown reason should preview the lossy expression kind `{expected_kind}`, got: {reason}"
    );
}

#[test]
fn test_prove_let_equality_goal_returns_unknown_when_term_lowering_is_lossy() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let let_expr = Expr::let_named(Name::anon(), nat_ty, Expr::nat_lit(0), Expr::bvar(0), false);
    let goal = nat_eq(let_expr.clone(), Expr::nat_lit(0));

    match bridge.prove(&goal) {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_unknown_reason(
                &reason,
                "lossy translation: SAT result may be spurious due to unconstrained atoms",
                "2 lossy expressions",
                "Let",
            );
        }
        other => panic!("lossy let-term lowering must return Unknown, got: {other:?}"),
    }

    assert!(
        bridge.lossy_atoms.iter().any(|expr| expr == &let_expr),
        "let-term fallback must register in lossy_atoms"
    );
}

#[test]
fn test_prove_proj_equality_goal_returns_unknown_when_term_lowering_is_lossy() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let proj_expr = Expr::proj(
        Name::from_string("PairLike"),
        0,
        Expr::const_(Name::from_string("pairWitness"), vec![]),
    );
    let goal = nat_eq(proj_expr.clone(), Expr::nat_lit(0));

    match bridge.prove(&goal) {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_unknown_reason(
                &reason,
                "lossy translation: SAT result may be spurious due to unconstrained atoms",
                "2 lossy expressions",
                "Proj",
            );
        }
        other => panic!("lossy proj-term lowering must return Unknown, got: {other:?}"),
    }

    assert!(
        bridge.lossy_atoms.iter().any(|expr| expr == &proj_expr),
        "projection fallback must register in lossy_atoms"
    );
}

#[test]
fn test_prove_let_prop_goal_returns_unknown_when_atom_lowering_is_lossy() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let let_prop = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("opaqueProp"), vec![]),
        Expr::bvar(0),
        false,
    );

    match bridge.prove(&let_prop) {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert_lossy_unknown_reason(
                &reason,
                "lossy translation: SAT result may be spurious due to unconstrained atoms",
                "1 lossy expression",
                "Let",
            );
        }
        other => panic!("lossy let-atom lowering must return Unknown, got: {other:?}"),
    }

    assert!(
        bridge.lossy_atoms.iter().any(|expr| expr == &let_prop),
        "let-atom fallback must register in lossy_atoms"
    );
}

#[test]
fn test_translate_term_nat_literal_produces_int() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let nat_42 = Expr::nat_lit(42);
    let term_id = bridge
        .translate_term(&nat_42)
        .expect("Nat literal should translate");

    assert!(
        bridge.term_to_expr.contains_key(&term_id),
        "Nat literal must be registered in term_to_expr"
    );
    let smt_term = bridge
        .smt
        .get_term(term_id)
        .expect("term must exist in solver");
    assert!(
        matches!(smt_term, crate::smt::SmtTerm::Int(_)),
        "Nat literal must produce SmtTerm::Int, got {smt_term:?}"
    );
}

#[test]
fn test_translate_term_nat_literal_caches() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let nat_7 = Expr::nat_lit(7);
    let id1 = bridge.translate_term(&nat_7).expect("first translate");
    let id2 = bridge.translate_term(&nat_7).expect("second translate");

    assert_eq!(id1, id2, "repeated Nat literal must return same TermId");
}

#[test]
fn test_translate_term_string_literal_produces_const() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let str_hello = Expr::str_lit("hello");
    let term_id = bridge
        .translate_term(&str_hello)
        .expect("String literal should translate");

    assert!(
        bridge.term_to_expr.contains_key(&term_id),
        "String literal must be registered in term_to_expr"
    );
    let smt_term = bridge
        .smt
        .get_term(term_id)
        .expect("term must exist in solver");
    match smt_term {
        crate::smt::SmtTerm::Const(name) => {
            let name_str = name.name();
            assert!(
                name_str.starts_with("str_"),
                "String literal const must have str_ prefix, got {name_str}"
            );
            assert!(
                name_str.contains("hello"),
                "String literal const must contain the value, got {name_str}"
            );
        }
        other => panic!("String literal must produce SmtTerm::Const, got {other:?}"),
    }
}

#[test]
fn test_translate_term_string_literal_caches() {
    let env = clean_kernel::Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let str_world = Expr::str_lit("world");
    let id1 = bridge.translate_term(&str_world).expect("first translate");
    let id2 = bridge.translate_term(&str_world).expect("second translate");

    assert_eq!(id1, id2, "repeated String literal must return same TermId");
}
