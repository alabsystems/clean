// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused topology manifold type-shape regression tests.
use super::*;

fn infer_const_type(env: &Environment, name: &str, level: Level) -> Expr {
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    tc.infer_type(&Expr::const_(Name::from_string(name), vec![level]))
        .expect("invariant: manifold declaration should type-check")
}

fn infer_const_type_levels(env: &Environment, name: &str, levels: Vec<Level>) -> Expr {
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    tc.infer_type(&Expr::const_(Name::from_string(name), levels))
        .expect("invariant: manifold declaration should type-check")
}

fn count_pi_binders(mut expr: Expr) -> (usize, Expr) {
    let mut count = 0;
    while let ExprKind::Pi(_, _, body) = &expr.kind {
        count += 1;
        expr = body.as_ref().clone();
    }
    (count, expr)
}

fn expr_head_const_name(expr: &Expr) -> Option<&Name> {
    let mut cur = expr;
    loop {
        match &cur.kind {
            ExprKind::App(f, _) => cur = f.as_ref(),
            ExprKind::Const(name, _) => return Some(name),
            _ => return None,
        }
    }
}

#[test]
fn test_topology_manifold_chart_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.Chart", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 3,
        "Topology.Manifold.Chart should have 3 Pi binders (M, [TopologicalSpace M], n)"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Succ(_))),
        "Topology.Manifold.Chart codomain should be Type u"
    );
}

#[test]
fn test_topology_manifold_chart_to_fun_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.Chart.toFun", u_level);
    let (count, tail) = count_pi_binders(ty);
    // count_pi_binders counts ALL Pi nodes including the Fin n -> Rat arrow.
    // 5 named binders (M, [TopologicalSpace M], n, c, x) + 1 arrow (Fin n -> Rat) = 6.
    assert_eq!(
        count, 6,
        "Topology.Manifold.Chart.toFun should have 6 Pi binders (M, [TopologicalSpace M], n, c, x, Fin n -> _)"
    );

    // After stripping all 6 Pi binders, the tail is Rat (the codomain of Fin n -> Rat).
    let rat = Name::from_string("Rat");
    assert!(
        matches!(expr_head_const_name(&tail), Some(name) if name == &rat),
        "Topology.Manifold.Chart.toFun final codomain should be Rat"
    );
}

#[test]
fn test_topology_manifold_atlas_charts_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.Atlas.charts", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 4,
        "Topology.Manifold.Atlas.charts should have 4 Pi binders (M, [TopologicalSpace M], n, atlas)"
    );

    let list = Name::from_string("List");
    assert!(
        matches!(expr_head_const_name(&tail), Some(name) if name == &list),
        "Topology.Manifold.Atlas.charts codomain should reduce to List"
    );
}

#[test]
fn test_topology_manifold_tangent_space_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.TangentSpace", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 5,
        "Topology.Manifold.TangentSpace should have 5 Pi binders (M, [TopologicalSpace M], n, [SmoothManifold M n], x)"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Succ(_))),
        "Topology.Manifold.TangentSpace codomain should be Type u"
    );
}

#[test]
fn test_topology_manifold_tangent_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.TangentBundle", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 4,
        "Topology.Manifold.TangentBundle should have 4 Pi binders (M, [TopologicalSpace M], n, [SmoothManifold M n])"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Succ(_))),
        "Topology.Manifold.TangentBundle codomain should be Type u"
    );
}

#[test]
fn test_topology_manifold_cotangent_space_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.CotangentSpace", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 5,
        "Topology.Manifold.CotangentSpace should have 5 Pi binders (M, [TopologicalSpace M], n, [SmoothManifold M n], x)"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Succ(_))),
        "Topology.Manifold.CotangentSpace codomain should be Type u"
    );
}

#[test]
fn test_topology_manifold_smooth_map_predicate_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let v_level = Level::param(Name::from_string("v"));
    let ty = infer_const_type_levels(&env, "Topology.Manifold.SmoothMap", vec![u_level, v_level]);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 9,
        "Topology.Manifold.SmoothMap should have 9 Pi binders \
         (M, N, [TS M], [TS N], m, n, [SmoothManifold M m], [SmoothManifold N n], f)"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Zero)),
        "Topology.Manifold.SmoothMap codomain should be Prop"
    );
}

#[test]
fn test_topology_manifold_diffeomorphism_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let v_level = Level::param(Name::from_string("v"));
    let ty = infer_const_type_levels(
        &env,
        "Topology.Manifold.Diffeomorphism",
        vec![u_level, v_level],
    );
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 8,
        "Topology.Manifold.Diffeomorphism should have 8 Pi binders \
         (M, N, [TS M], [TS N], m, n, [SmoothManifold M m], [SmoothManifold N n])"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(_)),
        "Topology.Manifold.Diffeomorphism codomain should be Type max(u,v)"
    );
}

#[test]
fn test_topology_manifold_is_diffeomorphic_type() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let v_level = Level::param(Name::from_string("v"));
    let ty = infer_const_type_levels(
        &env,
        "Topology.Manifold.IsDiffeomorphic",
        vec![u_level, v_level],
    );
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 8,
        "Topology.Manifold.IsDiffeomorphic should have 8 Pi binders \
         (M, N, [TS M], [TS N], m, n, [SmoothManifold M m], [SmoothManifold N n])"
    );
    assert!(
        matches!(&tail.kind, ExprKind::Sort(Level::Zero)),
        "Topology.Manifold.IsDiffeomorphic codomain should be Prop"
    );
}

#[test]
fn test_topology_manifold_exterior_derivative_type_shape() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("invariant: manifold init should succeed");

    let u_level = Level::param(Name::from_string("u"));
    let ty = infer_const_type(&env, "Topology.Manifold.ExteriorDerivative", u_level);
    let (count, tail) = count_pi_binders(ty);
    assert_eq!(
        count, 6,
        "Topology.Manifold.ExteriorDerivative should have 6 Pi binders \
         (M, [TS M], n, [SmoothManifold M n], k, mathverse)"
    );

    let differential_form = Name::from_string("Topology.Manifold.DifferentialForm");
    assert!(
        matches!(expr_head_const_name(&tail), Some(name) if name == &differential_form),
        "Topology.Manifold.ExteriorDerivative codomain head should be DifferentialForm"
    );
}
