// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for learned clause minimality formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_learned_clause_minimality()
        .expect("init_learned_clause_minimality");
    env
}

#[test]
fn test_learned_clause_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.LearnedClause"))
        .is_some());
}

#[test]
fn test_learned_clause_projections_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.LearnedClause.literals",
        "ProofTheory.LearnedClause.size",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_conflict_graph_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.ConflictGraph",
        "ProofTheory.ConflictGraph.conflict_level",
        "ProofTheory.ConflictGraph.num_literals",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.LearnedClause",
        "ProofTheory.LearnedClause.literals",
        "ProofTheory.LearnedClause.size",
        "ProofTheory.clause_strength",
        "ProofTheory.interpolation_clause",
        "ProofTheory.clause_subsumes",
        "ProofTheory.ConflictGraph",
        "ProofTheory.ConflictGraph.conflict_level",
        "ProofTheory.ConflictGraph.num_literals",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.interpolation_clause_sound",
        "ProofTheory.interpolation_clause_minimal",
        "ProofTheory.subsumption_strength",
        "ProofTheory.learned_clause_no_redundant_literals",
        "ProofTheory.backtrack_level_optimal",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.interpolation_clause_sound_helper",
        "ProofTheory.interpolation_clause_minimal_helper",
        "ProofTheory.subsumption_strength_helper",
        "ProofTheory.learned_clause_no_redundant_literals_helper",
        "ProofTheory.backtrack_level_optimal_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_learned_clause_type_checks() {
    let env = make_env();
    let lc = crate::expr::Expr::const_(Name::from_string("ProofTheory.LearnedClause"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&lc)
        .expect("infer ProofTheory.LearnedClause type");
    // LearnedClause : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_conflict_graph_type_checks() {
    let env = make_env();
    let cg = crate::expr::Expr::const_(Name::from_string("ProofTheory.ConflictGraph"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cg)
        .expect("infer ProofTheory.ConflictGraph type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_clause_strength_type_checks() {
    let env = make_env();
    let cs = crate::expr::Expr::const_(Name::from_string("ProofTheory.clause_strength"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cs)
        .expect("infer ProofTheory.clause_strength type");
    // clause_strength : LearnedClause -> LearnedClause -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interpolation_clause_type_checks() {
    let env = make_env();
    let ic = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.interpolation_clause"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ic)
        .expect("infer ProofTheory.interpolation_clause type");
    // interpolation_clause : ConflictGraph -> LearnedClause
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_clause_subsumes_type_checks() {
    let env = make_env();
    let sub = crate::expr::Expr::const_(Name::from_string("ProofTheory.clause_subsumes"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&sub)
        .expect("infer ProofTheory.clause_subsumes type");
    // clause_subsumes : LearnedClause -> LearnedClause -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interpolation_clause_sound_type_checks() {
    let env = make_env();
    let snd = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.interpolation_clause_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&snd)
        .expect("infer ProofTheory.interpolation_clause_sound type");
    // forall (g : ConflictGraph), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_backtrack_level_optimal_type_checks() {
    let env = make_env();
    let bt = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.backtrack_level_optimal"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&bt)
        .expect("infer ProofTheory.backtrack_level_optimal type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_learned_clause_minimality().expect("first init");
    env.init_learned_clause_minimality().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.LearnedClause",
        "ProofTheory.ConflictGraph",
        "ProofTheory.clause_strength",
        "ProofTheory.interpolation_clause",
        "ProofTheory.clause_subsumes",
        "ProofTheory.interpolation_clause_sound",
        "ProofTheory.interpolation_clause_minimal",
        "ProofTheory.subsumption_strength",
        "ProofTheory.learned_clause_no_redundant_literals",
        "ProofTheory.backtrack_level_optimal",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "LearnedClause",
        "ConflictGraph",
        "clause_strength",
        "interpolation_clause",
        "clause_subsumes",
        "interpolation_clause_sound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix",
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // All type declarations and operations should be axioms (opaque)
    let axiom_names = [
        "ProofTheory.LearnedClause",
        "ProofTheory.LearnedClause.literals",
        "ProofTheory.LearnedClause.size",
        "ProofTheory.clause_strength",
        "ProofTheory.interpolation_clause",
        "ProofTheory.clause_subsumes",
        "ProofTheory.ConflictGraph",
        "ProofTheory.ConflictGraph.conflict_level",
        "ProofTheory.ConflictGraph.num_literals",
        "ProofTheory.interpolation_clause_sound",
        "ProofTheory.interpolation_clause_minimal",
        "ProofTheory.subsumption_strength",
        "ProofTheory.learned_clause_no_redundant_literals",
        "ProofTheory.backtrack_level_optimal",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_craig_interpolation_also_initialized() {
    let env = make_env();
    // init_learned_clause_minimality depends on init_craig_interpolation,
    // so all Craig interpolation declarations should also be available.
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PropFormula"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.Resolution.Proof"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.interpolant"))
        .is_some());
}

#[test]
fn test_total_declaration_count() {
    let env = make_env();
    // Count all ProofTheory.LearnedClause* and ProofTheory.ConflictGraph*
    // and theorem declarations
    let expected_names = [
        // Definitions (5 main + projections/constructors)
        "ProofTheory.LearnedClause",
        "ProofTheory.LearnedClause.literals",
        "ProofTheory.LearnedClause.size",
        "ProofTheory.clause_strength",
        "ProofTheory.interpolation_clause",
        "ProofTheory.clause_subsumes",
        "ProofTheory.ConflictGraph",
        "ProofTheory.ConflictGraph.conflict_level",
        "ProofTheory.ConflictGraph.num_literals",
        // Theorems (5)
        "ProofTheory.interpolation_clause_sound",
        "ProofTheory.interpolation_clause_minimal",
        "ProofTheory.subsumption_strength",
        "ProofTheory.learned_clause_no_redundant_literals",
        "ProofTheory.backtrack_level_optimal",
        // Helpers (5)
        "ProofTheory.interpolation_clause_sound_helper",
        "ProofTheory.interpolation_clause_minimal_helper",
        "ProofTheory.subsumption_strength_helper",
        "ProofTheory.learned_clause_no_redundant_literals_helper",
        "ProofTheory.backtrack_level_optimal_helper",
    ];
    for name in expected_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should exist in environment"
        );
    }
}
