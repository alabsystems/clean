// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tree-width bounds on resolution proof length formalization.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_tree_width_resolution()
        .expect("init_tree_width_resolution");
    env
}

// ====================================================================
// Definition registration tests
// ====================================================================

#[test]
fn test_primal_graph_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("TreeWidthRes.PrimalGraph"))
        .is_some());
}

#[test]
fn test_tree_decomposition_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("TreeWidthRes.TreeDecomposition"))
        .is_some());
}

#[test]
fn test_resolution_proof_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("TreeWidthRes.ResolutionProof"))
        .is_some());
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "TreeWidthRes.PrimalGraph",
        "TreeWidthRes.primal_graph",
        "TreeWidthRes.TreeDecomposition",
        "TreeWidthRes.is_valid_decomposition",
        "TreeWidthRes.bag_size",
        "TreeWidthRes.tree_width_of",
        "TreeWidthRes.tree_width",
        "TreeWidthRes.ResolutionProof",
        "TreeWidthRes.res_proof_width",
        "TreeWidthRes.resolution_width",
        "TreeWidthRes.res_proof_size",
        "TreeWidthRes.resolution_size",
        "TreeWidthRes.initial_width",
        "TreeWidthRes.num_variables",
        "TreeWidthRes.is_refutation",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
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
        "TreeWidthRes.atserias_dalmau",
        "TreeWidthRes.ben_sasson_wigderson",
        "TreeWidthRes.bounded_tw_poly_size",
        "TreeWidthRes.width_lower_bound",
        "TreeWidthRes.size_lower_bound",
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
        "TreeWidthRes.atserias_dalmau_helper",
        "TreeWidthRes.ben_sasson_wigderson_helper",
        "TreeWidthRes.bounded_tw_poly_size_helper",
        "TreeWidthRes.width_lower_bound_helper",
        "TreeWidthRes.size_lower_bound_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

// ====================================================================
// Type-checking tests
// ====================================================================

#[test]
fn test_primal_graph_type_checks() {
    let env = make_env();
    let pg = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.PrimalGraph"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pg)
        .expect("infer TreeWidthRes.PrimalGraph type");
    // PrimalGraph : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_tree_decomposition_type_checks() {
    let env = make_env();
    let td = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.TreeDecomposition"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&td)
        .expect("infer TreeWidthRes.TreeDecomposition type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_resolution_proof_type_checks() {
    let env = make_env();
    let rp = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.ResolutionProof"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rp)
        .expect("infer TreeWidthRes.ResolutionProof type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_primal_graph_fn_type_checks() {
    let env = make_env();
    let pg_fn = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.primal_graph"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pg_fn)
        .expect("infer TreeWidthRes.primal_graph type");
    // primal_graph : CNF -> PrimalGraph
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_is_valid_decomposition_type_checks() {
    let env = make_env();
    let ivd = crate::expr::Expr::const_(
        Name::from_string("TreeWidthRes.is_valid_decomposition"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ivd)
        .expect("infer TreeWidthRes.is_valid_decomposition type");
    // is_valid_decomposition : PrimalGraph -> TreeDecomposition -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_is_refutation_type_checks() {
    let env = make_env();
    let ir = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.is_refutation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ir)
        .expect("infer TreeWidthRes.is_refutation type");
    // is_refutation : ResolutionProof -> CNF -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_atserias_dalmau_type_checks() {
    let env = make_env();
    let ad = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.atserias_dalmau"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ad)
        .expect("infer TreeWidthRes.atserias_dalmau type");
    // forall (f : CNF), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ben_sasson_wigderson_type_checks() {
    let env = make_env();
    let bsw = crate::expr::Expr::const_(
        Name::from_string("TreeWidthRes.ben_sasson_wigderson"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&bsw)
        .expect("infer TreeWidthRes.ben_sasson_wigderson type");
    // forall (f : CNF), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_bounded_tw_poly_size_type_checks() {
    let env = make_env();
    let btps = crate::expr::Expr::const_(
        Name::from_string("TreeWidthRes.bounded_tw_poly_size"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&btps)
        .expect("infer TreeWidthRes.bounded_tw_poly_size type");
    // forall (f : CNF) (k : Nat), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_width_lower_bound_type_checks() {
    let env = make_env();
    let wlb =
        crate::expr::Expr::const_(Name::from_string("TreeWidthRes.width_lower_bound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&wlb)
        .expect("infer TreeWidthRes.width_lower_bound type");
    // forall (f : CNF) (p : ResolutionProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_size_lower_bound_type_checks() {
    let env = make_env();
    let slb = crate::expr::Expr::const_(Name::from_string("TreeWidthRes.size_lower_bound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&slb)
        .expect("infer TreeWidthRes.size_lower_bound type");
    // forall (f : CNF) (p : ResolutionProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_init_idempotent() {
    let mut env = Environment::new();
    env.init_tree_width_resolution()
        .expect("first init_tree_width_resolution");
    env.init_tree_width_resolution()
        .expect("second init_tree_width_resolution should be idempotent");
}

// ====================================================================
// Total count test
// ====================================================================

#[test]
fn test_declaration_count() {
    let env = make_env();
    let all_names = [
        // 15 definitions
        "TreeWidthRes.PrimalGraph",
        "TreeWidthRes.primal_graph",
        "TreeWidthRes.TreeDecomposition",
        "TreeWidthRes.is_valid_decomposition",
        "TreeWidthRes.bag_size",
        "TreeWidthRes.tree_width_of",
        "TreeWidthRes.tree_width",
        "TreeWidthRes.ResolutionProof",
        "TreeWidthRes.res_proof_width",
        "TreeWidthRes.resolution_width",
        "TreeWidthRes.res_proof_size",
        "TreeWidthRes.resolution_size",
        "TreeWidthRes.initial_width",
        "TreeWidthRes.num_variables",
        "TreeWidthRes.is_refutation",
        // 5 helpers + 5 theorems = 10
        "TreeWidthRes.atserias_dalmau_helper",
        "TreeWidthRes.atserias_dalmau",
        "TreeWidthRes.ben_sasson_wigderson_helper",
        "TreeWidthRes.ben_sasson_wigderson",
        "TreeWidthRes.bounded_tw_poly_size_helper",
        "TreeWidthRes.bounded_tw_poly_size",
        "TreeWidthRes.width_lower_bound_helper",
        "TreeWidthRes.width_lower_bound",
        "TreeWidthRes.size_lower_bound_helper",
        "TreeWidthRes.size_lower_bound",
    ];
    for name in &all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} not found"
        );
    }
    // 15 definitions + 10 theorem/helper = 25 total TreeWidthRes declarations
    assert_eq!(all_names.len(), 25);
}
