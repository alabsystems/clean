// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #1488 universe-level call-site fixes.

use super::*;
use crate::tc::TypeChecker;

fn peel_pi_codomain(mut expr: Expr, count: usize, context: &str) -> Expr {
    for _ in 0..count {
        expr = match &expr.kind {
            ExprKind::Pi(_, _, body) => body.as_ref().clone(),
            _ => panic!("{context} should expose {count} Pi binders"),
        };
    }
    expr
}

#[test]
fn test_issue_1488_unit_interval_topological_space_uses_level_zero() {
    let mut env = Environment::new();
    env.init_topology_path_connected()
        .expect("init_topology_path_connected");

    let info = env
        .get_const(&Name::from_string("Topology.UnitInterval.topologicalSpace"))
        .expect("Topology.UnitInterval.topologicalSpace should exist");

    let (topological_space_app, carrier) = match &info.type_.kind {
        ExprKind::App(fun, arg) => (fun.as_ref(), arg.as_ref()),
        _ => panic!("Topology.UnitInterval.topologicalSpace type should be an application"),
    };

    match &carrier.kind {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Topology.UnitInterval"));
            assert!(
                levels.is_empty(),
                "Topology.UnitInterval should be monomorphic"
            );
        }
        _ => panic!("Topology.UnitInterval.topologicalSpace carrier should be UnitInterval"),
    }

    assert!(
        matches!(&topological_space_app.kind, ExprKind::Const(..)),
        "TopologicalSpace application head should be a constant"
    );
    if let ExprKind::Const(name, levels) = &topological_space_app.kind {
        assert_eq!(name, &Name::from_string("TopologicalSpace"));
        assert_eq!(
            levels.as_slice(),
            &[Level::zero()],
            "TopologicalSpace should be instantiated at universe level 0 for UnitInterval"
        );
    }
}

#[test]
fn test_issue_1488_metric_continuous_codomain_is_prop() {
    let mut env = Environment::new();
    env.init_metric_continuous()
        .expect("init_metric_continuous");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let continuous = Expr::const_(
        Name::from_string("Metric.Continuous"),
        vec![Level::param(u)],
    );
    let continuous_ty = tc
        .infer_type(&continuous)
        .expect("infer_type Metric.Continuous");
    let codomain = peel_pi_codomain(continuous_ty, 5, "Metric.Continuous");

    match &codomain.kind {
        ExprKind::Sort(level) => assert_eq!(
            level,
            &Level::zero(),
            "Metric.Continuous codomain should be Prop (Sort 0)"
        ),
        _ => panic!("Metric.Continuous codomain should be Sort(0)"),
    }
}

#[test]
fn test_issue_1488_metric_bounded_spec_is_prop_and_exists_rat() {
    let mut env = Environment::new();
    env.init_metric_bounded().expect("init_metric_bounded");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let bounded_spec = Expr::const_(
        Name::from_string("Metric.bounded_spec"),
        vec![Level::param(u)],
    );
    let bounded_spec_ty = tc
        .infer_type(&bounded_spec)
        .expect("infer_type bounded_spec");
    let codomain = peel_pi_codomain(bounded_spec_ty, 3, "Metric.bounded_spec");

    let (exists_with_witness, predicate) = match &codomain.kind {
        ExprKind::App(fun, arg) => (fun.as_ref(), arg.as_ref()),
        _ => panic!("Metric.bounded_spec codomain should be an Exists application"),
    };
    assert!(
        matches!(&predicate.kind, ExprKind::Lam(..)),
        "Metric.bounded_spec should apply Exists to a predicate lambda"
    );

    let (exists_const, witness_ty) = match &exists_with_witness.kind {
        ExprKind::App(fun, arg) => (fun.as_ref(), arg.as_ref()),
        _ => panic!("Metric.bounded_spec codomain should apply Exists to witness type"),
    };

    match &exists_const.kind {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Exists"));
            assert_eq!(
                levels.as_slice(),
                &[Level::succ(Level::zero())],
                "Exists witness universe should be level 1 for Rat"
            );
        }
        _ => panic!("Metric.bounded_spec codomain should start with Exists"),
    }

    let exists_ty = tc
        .infer_type(exists_const)
        .expect("Exists should type-check");
    let exists_result = peel_pi_codomain(exists_ty, 2, "Exists");
    assert!(
        matches!(&exists_result.kind, ExprKind::Sort(..)),
        "Exists result type should be Sort(0)"
    );
    if let ExprKind::Sort(level) = &exists_result.kind {
        assert_eq!(
            level,
            &Level::zero(),
            "Exists should produce Prop (Sort 0), so Metric.bounded_spec codomain is Prop"
        );
    }

    match &witness_ty.kind {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Rat"));
            assert!(levels.is_empty(), "Rat witness type should be monomorphic");
        }
        _ => panic!("Metric.bounded_spec witness type should be Rat"),
    }
}

#[test]
fn test_issue_1488_topology_compact_image_typechecks() {
    let mut env = Environment::new();
    env.init_topology_compact().expect("init_topology_compact");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let compact_image = Expr::const_(
        Name::from_string("Topology.compact_image"),
        vec![Level::param(u), Level::param(v)],
    );
    let _ = tc
        .infer_type(&compact_image)
        .expect("Topology.compact_image should type-check");
}

#[test]
fn test_issue_1488_topology_compact_set_image_typechecks() {
    let mut env = Environment::new();
    env.init_topology_compact().expect("init_topology_compact");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let compact_set_image = Expr::const_(
        Name::from_string("Topology.compact_set_image"),
        vec![Level::param(u), Level::param(v)],
    );
    let _ = tc
        .infer_type(&compact_set_image)
        .expect("Topology.compact_set_image should type-check");
}

#[test]
fn test_issue_1488_topology_homeomorphism_symm_typechecks() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism()
        .expect("init_topology_homeomorphism");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let homeomorphism_symm = Expr::const_(
        Name::from_string("Topology.homeomorphism_symm"),
        vec![Level::param(u), Level::param(v)],
    );
    let _ = tc
        .infer_type(&homeomorphism_symm)
        .expect("Topology.homeomorphism_symm should type-check");
}

#[test]
fn test_issue_1488_topology_homeomorphism_comp_typechecks() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism()
        .expect("init_topology_homeomorphism");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let w = Name::from_string("w");
    let homeomorphism_comp = Expr::const_(
        Name::from_string("Topology.homeomorphism_comp"),
        vec![Level::param(u), Level::param(v), Level::param(w)],
    );
    let _ = tc
        .infer_type(&homeomorphism_comp)
        .expect("Topology.homeomorphism_comp should type-check");
}

#[test]
fn test_issue_1488_topology_homeomorphism_to_homotopy_equiv_typechecks() {
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence()
        .expect("init_topology_homotopy_equivalence");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let homeo_to_he = Expr::const_(
        Name::from_string("Topology.homeomorphism_to_homotopy_equiv"),
        vec![Level::param(u)],
    );
    let _ = tc
        .infer_type(&homeo_to_he)
        .expect("Topology.homeomorphism_to_homotopy_equiv should type-check");
}
