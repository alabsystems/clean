// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the calc_trans transitivity resolution module.
//!
//! Covers: rule lookup, match_goal_rel, build_trans_chain, and integration
//! with calc_block for mixed-relation chains.

use super::*;

use crate::tactic::calc::{CalcJustification, CalcRel, CalcStep};
use crate::tactic::calc_trans::{build_trans_chain, calc_trans_rules, lookup_trans_rule};
use crate::tactic::calc_trans_match::match_goal_rel;

// =========================================================================
// Rule lookup tests
// =========================================================================

#[test]
fn test_lookup_eq_eq_returns_eq_trans() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Eq);
    assert!(rule.is_some(), "Eq+Eq should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Eq);
    assert_eq!(r.lemma_name, "Eq.trans");
}

#[test]
fn test_lookup_le_le_returns_le_trans() {
    let rule = lookup_trans_rule(CalcRel::Le, CalcRel::Le);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Le);
    assert_eq!(r.lemma_name, "le_trans");
}

#[test]
fn test_lookup_le_lt_returns_lt() {
    let rule = lookup_trans_rule(CalcRel::Le, CalcRel::Lt);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Lt);
    assert_eq!(r.lemma_name, "lt_of_le_of_lt");
}

#[test]
fn test_lookup_lt_le_returns_lt() {
    let rule = lookup_trans_rule(CalcRel::Lt, CalcRel::Le);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Lt);
    assert_eq!(r.lemma_name, "lt_of_lt_of_le");
}

#[test]
fn test_lookup_eq_le_returns_le() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Le);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Le);
    assert_eq!(r.lemma_name, "le_of_eq_of_le");
}

#[test]
fn test_lookup_le_eq_returns_le() {
    let rule = lookup_trans_rule(CalcRel::Le, CalcRel::Eq);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Le);
    assert_eq!(r.lemma_name, "le_of_le_of_eq");
}

#[test]
fn test_lookup_eq_lt_returns_lt() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Lt);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Lt);
    assert_eq!(r.lemma_name, "lt_of_eq_of_lt");
}

#[test]
fn test_lookup_lt_eq_returns_lt() {
    let rule = lookup_trans_rule(CalcRel::Lt, CalcRel::Eq);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Lt);
    assert_eq!(r.lemma_name, "lt_of_lt_of_eq");
}

#[test]
fn test_lookup_iff_iff_returns_iff_trans() {
    let rule = lookup_trans_rule(CalcRel::Iff, CalcRel::Iff);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Iff);
    assert_eq!(r.lemma_name, "Iff.trans");
}

#[test]
fn test_lookup_ge_ge_returns_ge_trans() {
    let rule = lookup_trans_rule(CalcRel::Ge, CalcRel::Ge);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Ge);
    assert_eq!(r.lemma_name, "ge_trans");
}

#[test]
fn test_lookup_gt_gt_returns_gt_trans() {
    let rule = lookup_trans_rule(CalcRel::Gt, CalcRel::Gt);
    assert!(rule.is_some());
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Gt);
    assert_eq!(r.lemma_name, "gt_trans");
}

#[test]
fn test_lookup_unsupported_le_iff_returns_none() {
    assert!(lookup_trans_rule(CalcRel::Le, CalcRel::Iff).is_none());
}

#[test]
fn test_lookup_unsupported_iff_lt_returns_none() {
    assert!(lookup_trans_rule(CalcRel::Iff, CalcRel::Lt).is_none());
}

#[test]
fn test_lookup_unsupported_le_gt_returns_none() {
    assert!(lookup_trans_rule(CalcRel::Le, CalcRel::Gt).is_none());
}

// =========================================================================
// Rule table completeness
// =========================================================================

#[test]
fn test_rule_table_has_expected_count() {
    assert_eq!(
        calc_trans_rules().len(),
        20,
        "Expected 20 transitivity rules (Eq, Le/Lt+Eq, Ge/Gt+Eq, Iff, Ne)"
    );
}

#[test]
fn test_all_rules_have_nonzero_arg_count() {
    for rule in calc_trans_rules() {
        assert!(
            rule.arg_count > 0,
            "Rule {} should have positive arg_count",
            rule.lemma_name
        );
    }
}

#[test]
fn test_all_rules_have_nonempty_lemma_name() {
    for rule in calc_trans_rules() {
        assert!(!rule.lemma_name.is_empty(), "Rule should have a lemma name");
    }
}

// =========================================================================
// match_goal_rel tests
// =========================================================================

#[test]
fn test_match_goal_rel_eq() {
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Eq);
}

#[test]
fn test_match_goal_rel_le() {
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Le);
}

#[test]
fn test_match_goal_rel_lt() {
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Lt);
}

#[test]
fn test_match_goal_rel_iff() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Iff"), vec![]),
            Expr::const_(Name::from_string("P"), vec![]),
        ),
        Expr::const_(Name::from_string("Q"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Iff);
}

#[test]
fn test_match_goal_rel_ge() {
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Ge);
}

#[test]
fn test_match_goal_rel_gt() {
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("GT.gt"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some());
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Gt);
}

#[test]
fn test_match_goal_rel_unrecognized() {
    let expr = Expr::const_(Name::from_string("Something"), vec![]);
    assert!(match_goal_rel(&expr).is_none());
}

#[test]
fn test_match_goal_rel_sort_unrecognized() {
    let expr = Expr::sort(Level::zero());
    assert!(match_goal_rel(&expr).is_none());
}

// =========================================================================
// Chained rule resolution tests
// =========================================================================

#[test]
fn test_chain_le_lt_eq_yields_lt() {
    // a LE b, b LT c => a LT c
    let r1 = lookup_trans_rule(CalcRel::Le, CalcRel::Lt).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Lt);
    // (a LT c), c EQ d => a LT d
    let r2 = lookup_trans_rule(CalcRel::Lt, CalcRel::Eq).unwrap();
    assert_eq!(r2.result_rel, CalcRel::Lt);
}

#[test]
fn test_chain_eq_le_lt_yields_lt() {
    // a EQ b => LE relation
    let r1 = lookup_trans_rule(CalcRel::Eq, CalcRel::Le).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Le);
    // a LE c, c LT d => a LT d
    let r2 = lookup_trans_rule(CalcRel::Le, CalcRel::Lt).unwrap();
    assert_eq!(r2.result_rel, CalcRel::Lt);
}

// =========================================================================
// build_trans_chain error tests
// =========================================================================

#[test]
fn test_build_trans_chain_empty_steps_returns_error() {
    let env = Environment::new();
    let target = Expr::const_(Name::from_string("Goal"), vec![]);
    let mut state = ProofState::new(env, target);
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let start = Expr::const_(Name::from_string("a"), vec![]);

    let result = build_trans_chain(&mut state, &[], &[], &start, &ty, &[]);
    assert!(result.is_err());
}

#[test]
fn test_build_trans_chain_mismatched_proof_count_returns_error() {
    let env = Environment::new();
    let target = Expr::const_(Name::from_string("Goal"), vec![]);
    let mut state = ProofState::new(env, target);
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let start = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let proof1 = Expr::const_(Name::from_string("h1"), vec![]);

    let steps = vec![
        CalcStep {
            rel: CalcRel::Eq,
            rhs: b.clone(),
            justification: CalcJustification::Term(proof1.clone()),
        },
        CalcStep {
            rel: CalcRel::Eq,
            rhs: Expr::const_(Name::from_string("c"), vec![]),
            justification: CalcJustification::Term(proof1.clone()),
        },
    ];

    // Only 1 proof for 2 steps
    let result = build_trans_chain(&mut state, &steps, &[proof1], &start, &ty, &[]);
    assert!(result.is_err());
}

#[test]
fn test_build_trans_chain_single_step_returns_proof() {
    let env = Environment::new();
    let target = Expr::const_(Name::from_string("Goal"), vec![]);
    let mut state = ProofState::new(env, target);
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let start = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let proof1 = Expr::const_(Name::from_string("h1"), vec![]);

    let steps = vec![CalcStep {
        rel: CalcRel::Eq,
        rhs: b,
        justification: CalcJustification::Term(proof1.clone()),
    }];

    let result = build_trans_chain(
        &mut state,
        &steps,
        std::slice::from_ref(&proof1),
        &start,
        &ty,
        &[],
    );
    assert!(result.is_ok(), "Single step should succeed");
    // For single step, should return the proof directly (instantiated)
    let built = result.unwrap();
    // The proof should be the instantiated version of proof1
    assert_eq!(built, proof1);
}

#[test]
fn test_build_trans_chain_unsupported_pair_returns_error() {
    let env = Environment::new();
    let target = Expr::const_(Name::from_string("Goal"), vec![]);
    let mut state = ProofState::new(env, target);
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let start = Expr::const_(Name::from_string("a"), vec![]);
    let proof1 = Expr::const_(Name::from_string("h1"), vec![]);
    let proof2 = Expr::const_(Name::from_string("h2"), vec![]);

    let steps = vec![
        CalcStep {
            rel: CalcRel::Le,
            rhs: Expr::const_(Name::from_string("b"), vec![]),
            justification: CalcJustification::Term(proof1.clone()),
        },
        CalcStep {
            rel: CalcRel::Iff, // Le + Iff not supported
            rhs: Expr::const_(Name::from_string("c"), vec![]),
            justification: CalcJustification::Term(proof2.clone()),
        },
    ];

    let result = build_trans_chain(&mut state, &steps, &[proof1, proof2], &start, &ty, &[]);
    assert!(result.is_err(), "Le + Iff should be unsupported");
}

// =========================================================================
// Ge/Gt cross-relation rule lookup tests
// =========================================================================

#[test]
fn test_lookup_ge_gt_returns_gt() {
    let rule = lookup_trans_rule(CalcRel::Ge, CalcRel::Gt);
    assert!(rule.is_some(), "Ge+Gt should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Gt);
    assert_eq!(r.lemma_name, "gt_of_ge_of_gt");
}

#[test]
fn test_lookup_gt_ge_returns_gt() {
    let rule = lookup_trans_rule(CalcRel::Gt, CalcRel::Ge);
    assert!(rule.is_some(), "Gt+Ge should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Gt);
    assert_eq!(r.lemma_name, "gt_of_gt_of_ge");
}

#[test]
fn test_lookup_ge_eq_returns_ge() {
    let rule = lookup_trans_rule(CalcRel::Ge, CalcRel::Eq);
    assert!(rule.is_some(), "Ge+Eq should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Ge);
    assert_eq!(r.lemma_name, "ge_of_ge_of_eq");
}

#[test]
fn test_lookup_eq_ge_returns_ge() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Ge);
    assert!(rule.is_some(), "Eq+Ge should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Ge);
    assert_eq!(r.lemma_name, "ge_of_eq_of_ge");
}

#[test]
fn test_lookup_gt_eq_returns_gt() {
    let rule = lookup_trans_rule(CalcRel::Gt, CalcRel::Eq);
    assert!(rule.is_some(), "Gt+Eq should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Gt);
    assert_eq!(r.lemma_name, "gt_of_gt_of_eq");
}

#[test]
fn test_lookup_eq_gt_returns_gt() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Gt);
    assert!(rule.is_some(), "Eq+Gt should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Gt);
    assert_eq!(r.lemma_name, "gt_of_eq_of_gt");
}

// =========================================================================
// Ne (disequality) rule lookup tests
// =========================================================================

#[test]
fn test_lookup_eq_ne_returns_ne() {
    let rule = lookup_trans_rule(CalcRel::Eq, CalcRel::Ne);
    assert!(rule.is_some(), "Eq+Ne should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Ne);
    assert_eq!(r.lemma_name, "ne_of_eq_of_ne");
}

#[test]
fn test_lookup_ne_eq_returns_ne() {
    let rule = lookup_trans_rule(CalcRel::Ne, CalcRel::Eq);
    assert!(rule.is_some(), "Ne+Eq should be supported");
    let r = rule.unwrap();
    assert_eq!(r.result_rel, CalcRel::Ne);
    assert_eq!(r.lemma_name, "ne_of_ne_of_eq");
}

#[test]
fn test_lookup_ne_ne_unsupported() {
    // Ne is not transitive: a != b and b != c does not imply a != c
    assert!(
        lookup_trans_rule(CalcRel::Ne, CalcRel::Ne).is_none(),
        "Ne+Ne should not be supported (Ne is not transitive)"
    );
}

// =========================================================================
// match_goal_rel Ne test
// =========================================================================

#[test]
fn test_match_goal_rel_ne() {
    // @Ne.{0} Nat a b
    let expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::zero()]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = match_goal_rel(&expr);
    assert!(result.is_some(), "Ne goal should be matched");
    let (rel, _ty, _lhs, _rhs, _levels) = result.unwrap();
    assert_eq!(rel, CalcRel::Ne);
}

// =========================================================================
// Chained Ge/Gt rule resolution tests
// =========================================================================

#[test]
fn test_chain_ge_gt_eq_yields_gt() {
    // a >= b, b > c => a > c
    let r1 = lookup_trans_rule(CalcRel::Ge, CalcRel::Gt).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Gt);
    // (a > c), c = d => a > d
    let r2 = lookup_trans_rule(CalcRel::Gt, CalcRel::Eq).unwrap();
    assert_eq!(r2.result_rel, CalcRel::Gt);
}

#[test]
fn test_chain_eq_ge_gt_yields_gt() {
    // a = b => b >= b (with eq_of_ge then chain)
    let r1 = lookup_trans_rule(CalcRel::Eq, CalcRel::Ge).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Ge);
    // a >= c, c > d => a > d
    let r2 = lookup_trans_rule(CalcRel::Ge, CalcRel::Gt).unwrap();
    assert_eq!(r2.result_rel, CalcRel::Gt);
}

#[test]
fn test_chain_eq_ne_yields_ne() {
    // a = b, b != c => a != c
    let r1 = lookup_trans_rule(CalcRel::Eq, CalcRel::Ne).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Ne);
}

#[test]
fn test_chain_ne_eq_yields_ne() {
    // a != b, b = c => a != c
    let r1 = lookup_trans_rule(CalcRel::Ne, CalcRel::Eq).unwrap();
    assert_eq!(r1.result_rel, CalcRel::Ne);
}
