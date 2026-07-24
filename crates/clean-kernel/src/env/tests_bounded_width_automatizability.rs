// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for bounded-width resolution automatizability formalization.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_bounded_width_automatizability()
        .expect("init_bounded_width_automatizability");
    env
}

// ====================================================================
// Definition registration tests
// ====================================================================

#[test]
fn test_partial_assignment_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoundedWidth.PartialAssignment"))
        .is_some());
}

#[test]
fn test_primal_graph_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoundedWidth.PrimalGraph"))
        .is_some());
}

#[test]
fn test_tree_decomposition_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoundedWidth.TreeDecomposition"))
        .is_some());
}

#[test]
fn test_res_proof_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoundedWidth.ResProof"))
        .is_some());
}

#[test]
fn test_cdcl_trace_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("BoundedWidth.CDCLTrace"))
        .is_some());
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "BoundedWidth.PartialAssignment",
        "BoundedWidth.PartialAssignment.width",
        "BoundedWidth.PrimalGraph",
        "BoundedWidth.TreeDecomposition",
        "BoundedWidth.tree_width",
        "BoundedWidth.has_tree_width_le",
        "BoundedWidth.ResProof",
        "BoundedWidth.res_proof_width",
        "BoundedWidth.res_proof_size",
        "BoundedWidth.res_refutes",
        "BoundedWidth.k_consistency",
        "BoundedWidth.CDCLTrace",
        "BoundedWidth.cdcl_simulates",
        "BoundedWidth.poly_bound",
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
        "BoundedWidth.consistency_detects_unsat",
        "BoundedWidth.consistency_to_refutation",
        "BoundedWidth.bounded_width_automatizable",
        "BoundedWidth.general_res_non_automatizable",
        "BoundedWidth.cdcl_simulates_bounded_width",
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
        "BoundedWidth.consistency_detects_unsat_helper",
        "BoundedWidth.consistency_to_refutation_helper",
        "BoundedWidth.bounded_width_automatizable_helper",
        "BoundedWidth.general_res_non_automatizable_helper",
        "BoundedWidth.cdcl_simulates_bounded_width_helper",
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
fn test_partial_assignment_type_checks() {
    let env = make_env();
    let pa = crate::expr::Expr::const_(Name::from_string("BoundedWidth.PartialAssignment"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pa)
        .expect("infer BoundedWidth.PartialAssignment type");
    // PartialAssignment : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_res_proof_type_checks() {
    let env = make_env();
    let rp = crate::expr::Expr::const_(Name::from_string("BoundedWidth.ResProof"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rp)
        .expect("infer BoundedWidth.ResProof type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_cdcl_trace_type_checks() {
    let env = make_env();
    let ct = crate::expr::Expr::const_(Name::from_string("BoundedWidth.CDCLTrace"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ct)
        .expect("infer BoundedWidth.CDCLTrace type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_res_proof_width_type_checks() {
    let env = make_env();
    let rpw = crate::expr::Expr::const_(Name::from_string("BoundedWidth.res_proof_width"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rpw)
        .expect("infer BoundedWidth.res_proof_width type");
    // res_proof_width : ResProof -> Nat, so type is Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_k_consistency_type_checks() {
    let env = make_env();
    let kc = crate::expr::Expr::const_(Name::from_string("BoundedWidth.k_consistency"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&kc)
        .expect("infer BoundedWidth.k_consistency type");
    // k_consistency : CNF -> Nat -> Prop, so type is Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_automatizability_theorem_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("BoundedWidth.bounded_width_automatizable"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer BoundedWidth.bounded_width_automatizable type");
    // forall (f : CNF) (k : Nat), ... so type is Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cdcl_simulates_theorem_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("BoundedWidth.cdcl_simulates_bounded_width"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer BoundedWidth.cdcl_simulates_bounded_width type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_non_automatizability_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("BoundedWidth.general_res_non_automatizable"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    // This is just Prop (the helper itself is a Prop), so infer_type
    // should yield Sort(0) = Prop's type is Sort(1).
    let _ty = tc
        .infer_type(&thm)
        .expect("infer BoundedWidth.general_res_non_automatizable type");
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_init_idempotent() {
    let mut env = Environment::new();
    env.init_bounded_width_automatizability()
        .expect("first init");
    env.init_bounded_width_automatizability()
        .expect("second init should be idempotent");
}

// ====================================================================
// Dependency test — resolution_complexity types are available
// ====================================================================

#[test]
fn test_resolution_complexity_deps_available() {
    let env = make_env();
    // BoundedWidth depends on ResComplexity.CNF and ResComplexity.Clause
    for name in ["ResComplexity.CNF", "ResComplexity.Clause"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} from resolution_complexity should be available"
        );
    }
}
