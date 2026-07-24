// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for verified proof search correctness formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_verified_proof_search()
        .expect("init_verified_proof_search");
    env
}

// ====================================================================
// Type registration tests
// ====================================================================

#[test]
fn test_all_types_registered() {
    let env = make_env();
    for name in [
        "VerifiedProofSearch.Goal",
        "VerifiedProofSearch.Goal.target",
        "VerifiedProofSearch.Goal.context",
        "VerifiedProofSearch.ProofTerm",
        "VerifiedProofSearch.SearchBound",
        "VerifiedProofSearch.SearchBound.max_depth",
        "VerifiedProofSearch.SearchBound.max_width",
        "VerifiedProofSearch.SearchBound.max_nodes",
        "VerifiedProofSearch.TacticApplication",
        "VerifiedProofSearch.TacticApplication.tactic_name",
        "VerifiedProofSearch.TacticApplication.produces_subgoals",
        "VerifiedProofSearch.SearchTree",
        "VerifiedProofSearch.SearchTree.root",
        "VerifiedProofSearch.SearchTree.node_count",
        "VerifiedProofSearch.SearchTree.depth",
        "VerifiedProofSearch.SearchState",
        "VerifiedProofSearch.SearchState.frontier_size",
        "VerifiedProofSearch.SearchState.explored_count",
        "VerifiedProofSearch.SearchState.current_tree",
        "VerifiedProofSearch.SearchResult",
        "VerifiedProofSearch.SearchResult.is_proved",
        "VerifiedProofSearch.SearchResult.is_exhausted",
        "VerifiedProofSearch.SearchResult.proof",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// Operation registration tests
// ====================================================================

#[test]
fn test_all_operations_registered() {
    let env = make_env();
    for name in [
        "VerifiedProofSearch.search_step",
        "VerifiedProofSearch.apply_tactic",
        "VerifiedProofSearch.run_search",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// Predicate registration tests
// ====================================================================

#[test]
fn test_all_predicates_registered() {
    let env = make_env();
    for name in [
        "VerifiedProofSearch.type_checks",
        "VerifiedProofSearch.within_bounds",
        "VerifiedProofSearch.proof_exists_within",
        "VerifiedProofSearch.search_space_finite",
        "VerifiedProofSearch.bound_le",
        "VerifiedProofSearch.tactic_preserves_validity",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

// ====================================================================
// Theorem registration tests
// ====================================================================

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "VerifiedProofSearch.search_soundness",
        "VerifiedProofSearch.search_completeness",
        "VerifiedProofSearch.search_terminates",
        "VerifiedProofSearch.budget_monotonicity",
        "VerifiedProofSearch.composition_soundness",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_all_helpers_registered() {
    let env = make_env();
    for name in [
        "VerifiedProofSearch.search_soundness_helper",
        "VerifiedProofSearch.search_completeness_helper",
        "VerifiedProofSearch.search_terminates_helper",
        "VerifiedProofSearch.budget_monotonicity_helper",
        "VerifiedProofSearch.composition_soundness_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered",
        );
    }
}

// ====================================================================
// Type checking tests
// ====================================================================

#[test]
fn test_goal_type_checks() {
    let env = make_env();
    let goal = crate::expr::Expr::const_(Name::from_string("VerifiedProofSearch.Goal"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&goal)
        .expect("infer VerifiedProofSearch.Goal type");
    // Goal : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_search_bound_type_checks() {
    let env = make_env();
    let sb =
        crate::expr::Expr::const_(Name::from_string("VerifiedProofSearch.SearchBound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&sb)
        .expect("infer VerifiedProofSearch.SearchBound type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_type_checks_predicate_type_checks() {
    let env = make_env();
    let tc_const =
        crate::expr::Expr::const_(Name::from_string("VerifiedProofSearch.type_checks"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&tc_const)
        .expect("infer VerifiedProofSearch.type_checks type");
    // type_checks : Goal -> ProofTerm -> Prop (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_run_search_type_checks() {
    let env = make_env();
    let rs = crate::expr::Expr::const_(Name::from_string("VerifiedProofSearch.run_search"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rs)
        .expect("infer VerifiedProofSearch.run_search type");
    // run_search : Goal -> SearchBound -> SearchResult (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_search_soundness_type_checks() {
    let env = make_env();
    let ss = crate::expr::Expr::const_(
        Name::from_string("VerifiedProofSearch.search_soundness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ss)
        .expect("infer VerifiedProofSearch.search_soundness type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_budget_monotonicity_type_checks() {
    let env = make_env();
    let bm = crate::expr::Expr::const_(
        Name::from_string("VerifiedProofSearch.budget_monotonicity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&bm)
        .expect("infer VerifiedProofSearch.budget_monotonicity type");
    // forall (g : Goal) (b1 b2 : SearchBound), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Classification and naming tests
// ====================================================================

#[test]
fn test_all_are_axioms() {
    let env = make_env();
    let axiom_names = [
        "VerifiedProofSearch.Goal",
        "VerifiedProofSearch.ProofTerm",
        "VerifiedProofSearch.SearchBound",
        "VerifiedProofSearch.TacticApplication",
        "VerifiedProofSearch.SearchTree",
        "VerifiedProofSearch.SearchState",
        "VerifiedProofSearch.SearchResult",
        "VerifiedProofSearch.search_step",
        "VerifiedProofSearch.apply_tactic",
        "VerifiedProofSearch.run_search",
        "VerifiedProofSearch.type_checks",
        "VerifiedProofSearch.within_bounds",
        "VerifiedProofSearch.proof_exists_within",
        "VerifiedProofSearch.search_space_finite",
        "VerifiedProofSearch.bound_le",
        "VerifiedProofSearch.tactic_preserves_validity",
        "VerifiedProofSearch.search_soundness",
        "VerifiedProofSearch.search_completeness",
        "VerifiedProofSearch.search_terminates",
        "VerifiedProofSearch.budget_monotonicity",
        "VerifiedProofSearch.composition_soundness",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // Bare names should NOT exist
    for name in [
        "Goal",
        "ProofTerm",
        "SearchBound",
        "SearchTree",
        "type_checks",
        "run_search",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without VerifiedProofSearch. prefix",
        );
    }
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_verified_proof_search().expect("first init");
    env.init_verified_proof_search()
        .expect("second init (idempotent)");
}

#[test]
fn test_total_declaration_count() {
    let env = make_env();
    // 7 base types (Goal, ProofTerm, SearchBound, TacticApplication, SearchTree, SearchState, SearchResult)
    // 16 projections
    // = 23 type declarations
    // 3 operations
    // 6 predicates
    // 5 theorems + 5 helpers = 10
    // Total: 23 + 3 + 6 + 10 = 42
    let all_names = [
        // Types + projections (23)
        "VerifiedProofSearch.Goal",
        "VerifiedProofSearch.Goal.target",
        "VerifiedProofSearch.Goal.context",
        "VerifiedProofSearch.ProofTerm",
        "VerifiedProofSearch.SearchBound",
        "VerifiedProofSearch.SearchBound.max_depth",
        "VerifiedProofSearch.SearchBound.max_width",
        "VerifiedProofSearch.SearchBound.max_nodes",
        "VerifiedProofSearch.TacticApplication",
        "VerifiedProofSearch.TacticApplication.tactic_name",
        "VerifiedProofSearch.TacticApplication.produces_subgoals",
        "VerifiedProofSearch.SearchTree",
        "VerifiedProofSearch.SearchTree.root",
        "VerifiedProofSearch.SearchTree.node_count",
        "VerifiedProofSearch.SearchTree.depth",
        "VerifiedProofSearch.SearchState",
        "VerifiedProofSearch.SearchState.frontier_size",
        "VerifiedProofSearch.SearchState.explored_count",
        "VerifiedProofSearch.SearchState.current_tree",
        "VerifiedProofSearch.SearchResult",
        "VerifiedProofSearch.SearchResult.is_proved",
        "VerifiedProofSearch.SearchResult.is_exhausted",
        "VerifiedProofSearch.SearchResult.proof",
        // Operations (3)
        "VerifiedProofSearch.search_step",
        "VerifiedProofSearch.apply_tactic",
        "VerifiedProofSearch.run_search",
        // Predicates (6)
        "VerifiedProofSearch.type_checks",
        "VerifiedProofSearch.within_bounds",
        "VerifiedProofSearch.proof_exists_within",
        "VerifiedProofSearch.search_space_finite",
        "VerifiedProofSearch.bound_le",
        "VerifiedProofSearch.tactic_preserves_validity",
        // Theorems (5)
        "VerifiedProofSearch.search_soundness",
        "VerifiedProofSearch.search_completeness",
        "VerifiedProofSearch.search_terminates",
        "VerifiedProofSearch.budget_monotonicity",
        "VerifiedProofSearch.composition_soundness",
        // Helpers (5)
        "VerifiedProofSearch.search_soundness_helper",
        "VerifiedProofSearch.search_completeness_helper",
        "VerifiedProofSearch.search_terminates_helper",
        "VerifiedProofSearch.budget_monotonicity_helper",
        "VerifiedProofSearch.composition_soundness_helper",
    ];
    let mut count = 0;
    for name in all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should exist in environment",
        );
        count += 1;
    }
    assert_eq!(count, 42, "expected 42 verified proof search declarations");
}
