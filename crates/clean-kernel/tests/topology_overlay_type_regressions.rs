// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Requires math-overlays feature: init_topology_manifold and init_topology_lie_group
// are defined in topology_diff.rs, which is gated behind cfg(any(test, feature = "math-overlays")).
// Integration tests compile the library WITHOUT cfg(test), so the feature is needed.
#![cfg(feature = "math-overlays")]

//! Regression tests for topology overlay declaration type shapes.
//!
//! These guards validate non-trivial binder/application structure so we catch
//! semantic drift in generated overlay payloads, not just declaration presence.

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};

fn collect_pi_binders(mut ty: Expr) -> (Vec<Expr>, Expr) {
    let mut binders = Vec::new();
    while let ExprKind::Pi(_, domain, body) = ty.kind() {
        binders.push(domain.as_ref().clone());
        ty = body.as_ref().clone();
    }
    (binders, ty)
}

fn app_head_and_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = expr;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

fn head_const_name(expr: &Expr) -> Option<&Name> {
    let (head, _) = app_head_and_args(expr);
    match head.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    }
}

#[test]
fn topology_manifold_exterior_derivative_domain_uses_full_differential_form_app() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("init_topology_manifold should succeed");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let ext = Expr::const_(
        Name::from_string("Topology.Manifold.ExteriorDerivative"),
        vec![Level::param(u)],
    );
    let ty = tc
        .infer_type(&ext)
        .expect("ExteriorDerivative should type-check");

    let (binders, codomain) = collect_pi_binders(ty);
    assert_eq!(
        binders.len(),
        6,
        "ExteriorDerivative should have 6 Pi binders: M, TS, n, SmoothManifold, k, mathverse"
    );

    assert!(
        matches!(
            head_const_name(&binders[3]),
            Some(name) if name == &Name::from_string("Topology.Manifold.SmoothManifold")
        ),
        "4th binder domain should be SmoothManifold instance"
    );

    let (mathverse_head, mathverse_args) = app_head_and_args(&binders[5]);
    assert!(
        matches!(
            mathverse_head.kind(),
            ExprKind::Const(name, _) if name == &Name::from_string("Topology.Manifold.DifferentialForm")
        ),
        "mathverse binder domain head should be DifferentialForm"
    );
    assert_eq!(
        mathverse_args.len(),
        5,
        "mathverse binder domain should apply DifferentialForm to 5 args (M, TS, n, sm, k)"
    );

    let (ret_head, ret_args) = app_head_and_args(&codomain);
    assert!(
        matches!(
            ret_head.kind(),
            ExprKind::Const(name, _) if name == &Name::from_string("Topology.Manifold.DifferentialForm")
        ),
        "ExteriorDerivative codomain head should be DifferentialForm"
    );
    assert_eq!(
        ret_args.len(),
        5,
        "ExteriorDerivative codomain should apply DifferentialForm to 5 args"
    );
}

#[test]
fn topology_lie_algebra_hom_phi_uses_lie_algebra_types() {
    let mut env = Environment::new();
    env.init_topology_lie_group()
        .expect("init_topology_lie_group should succeed");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let lie_alg_hom = Expr::const_(
        Name::from_string("Topology.LieGroup.LieAlgebraHom"),
        vec![Level::param(u), Level::param(v)],
    );
    let ty = tc
        .infer_type(&lie_alg_hom)
        .expect("LieAlgebraHom should type-check");

    let (binders, codomain) = collect_pi_binders(ty);
    assert_eq!(binders.len(), 11, "LieAlgebraHom should have 11 Pi binders");

    let phi_ty = &binders[10];
    match phi_ty.kind() {
        ExprKind::Pi(_, phi_domain, phi_codomain) => {
            let lie_algebra = Name::from_string("Topology.LieGroup.LieAlgebra");
            assert!(
                matches!(head_const_name(phi_domain), Some(name) if name == &lie_algebra),
                "phi domain should be LieAlgebra"
            );
            assert!(
                matches!(head_const_name(phi_codomain), Some(name) if name == &lie_algebra),
                "phi codomain should be LieAlgebra"
            );
        }
        _ => panic!("phi binder should be an arrow type"),
    }

    assert!(
        matches!(codomain.kind(), ExprKind::Sort(level) if level.is_zero()),
        "LieAlgebraHom codomain should be Prop"
    );
}

#[test]
fn topology_manifold_chart_to_fun_returns_fin_to_rat() {
    let mut env = Environment::new();
    env.init_topology_manifold()
        .expect("init_topology_manifold should succeed");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let chart_to_fun = Expr::const_(
        Name::from_string("Topology.Manifold.Chart.toFun"),
        vec![Level::param(u)],
    );
    let ty = tc
        .infer_type(&chart_to_fun)
        .expect("Chart.toFun should type-check");

    let (binders, codomain) = collect_pi_binders(ty);
    assert!(
        binders.len() >= 5,
        "Chart.toFun should have at least 5 Pi binders; got {}",
        binders.len()
    );
    assert!(
        binders.iter().any(|domain| {
            matches!(
                head_const_name(domain),
                Some(name) if name == &Name::from_string("Topology.Manifold.Chart")
            )
        }),
        "Chart.toFun should include a Chart binder domain"
    );

    let has_fin_binder = binders.iter().any(|domain| {
        matches!(
            head_const_name(domain),
            Some(name) if name == &Name::from_string("Fin")
        )
    });

    match codomain.kind() {
        ExprKind::Pi(_, fin_domain, rat_codomain) => {
            assert!(
                matches!(
                    head_const_name(fin_domain),
                    Some(name) if name == &Name::from_string("Fin")
                ),
                "Chart.toFun codomain domain should be Fin n"
            );
            assert!(
                matches!(
                    rat_codomain.kind(),
                    ExprKind::Const(name, _) if name == &Name::from_string("Rat")
                ),
                "Chart.toFun codomain should be Rat"
            );
        }
        ExprKind::Const(name, _) if name == &Name::from_string("Rat") => {
            assert!(
                has_fin_binder,
                "Chart.toFun ending in Rat should have a Fin binder in preceding Pi domains"
            );
        }
        _ => panic!("Chart.toFun codomain should be an arrow Fin n -> Rat"),
    }
}
