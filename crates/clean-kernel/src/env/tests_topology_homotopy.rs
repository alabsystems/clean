// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Topology tests for Environment
use super::test_helpers::{assert_const, expr_contains_const};
use super::*;

fn collect_const_app_arities(expr: &Expr, target: &Name, out: &mut Vec<usize>) {
    collect_const_app_arities_impl(expr, target, false, out);
}

fn collect_const_app_arities_impl(
    expr: &Expr,
    target: &Name,
    is_app_fn_child: bool,
    out: &mut Vec<usize>,
) {
    match &expr.kind {
        ExprKind::App(f, a) => {
            // Only inspect maximal application nodes so we do not treat partial
            // heads inside an application spine as independent applications.
            if !is_app_fn_child {
                let mut head = expr;
                let mut arity = 0usize;
                while let ExprKind::App(fun, _) = &head.kind {
                    arity += 1;
                    head = fun.as_ref();
                }
                if let ExprKind::Const(name, _) = &head.kind {
                    if name == target {
                        out.push(arity);
                    }
                }
            }
            collect_const_app_arities_impl(f, target, true, out);
            collect_const_app_arities_impl(a, target, false, out);
        }
        ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
            collect_const_app_arities_impl(f, target, false, out);
            collect_const_app_arities_impl(a, target, false, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_const_app_arities_impl(ty, target, false, out);
            collect_const_app_arities_impl(val, target, false, out);
            collect_const_app_arities_impl(body, target, false, out);
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => {
            collect_const_app_arities_impl(e, target, false, out);
        }
        ExprKind::CubicalPath { ty, left, right } => {
            collect_const_app_arities_impl(ty, target, false, out);
            collect_const_app_arities_impl(left, target, false, out);
            collect_const_app_arities_impl(right, target, false, out);
        }
        ExprKind::CubicalPathLam { body } => {
            collect_const_app_arities_impl(body, target, false, out);
        }
        ExprKind::CubicalPathApp { path, arg } => {
            collect_const_app_arities_impl(path, target, false, out);
            collect_const_app_arities_impl(arg, target, false, out);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            collect_const_app_arities_impl(ty, target, false, out);
            collect_const_app_arities_impl(phi, target, false, out);
            collect_const_app_arities_impl(u, target, false, out);
            collect_const_app_arities_impl(base, target, false, out);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            collect_const_app_arities_impl(ty, target, false, out);
            collect_const_app_arities_impl(phi, target, false, out);
            collect_const_app_arities_impl(base, target, false, out);
        }
        ExprKind::ZFCMem { element, set } => {
            collect_const_app_arities_impl(element, target, false, out);
            collect_const_app_arities_impl(set, target, false, out);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            collect_const_app_arities_impl(domain, target, false, out);
            collect_const_app_arities_impl(pred, target, false, out);
        }
        _ => {}
    }
}

// ================================================================
// TopologicalSpace Tests
// ================================================================

#[test]
fn test_topology_fundamental_group_dependencies_initialized() {
    // Test that initializing FundamentalGroup initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_fundamental_group().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_simply_connected());
    assert!(env.has_topology_path_connected());
    assert!(env.has_eq());
    assert!(env.has_iff());
}

// ================================================================
// Topology.HomotopyEquivalence Tests
// ================================================================

#[test]
fn test_topology_homotopy_equivalence_init() {
    // Topology.HomotopyEquivalence initializes successfully
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();
    assert!(env.has_topology_homotopy_equivalence());
}

#[test]
fn test_topology_homotopy_equivalence_idempotent() {
    // Topology.HomotopyEquivalence initialization is idempotent
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();
    env.init_topology_homotopy_equivalence().unwrap();
    assert!(env.has_topology_homotopy_equivalence());
}

#[test]
fn test_topology_continuous_homotopy_type() {
    use crate::tc::TypeChecker;
    // Topology.ContinuousHomotopy : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (α → β) → (α → β) → Type u
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ch = Expr::const_(
        Name::from_string("Topology.ContinuousHomotopy"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ch)
        .expect("invariant: ContinuousHomotopy should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "ContinuousHomotopy should have 6 Pi binders (α, β, [TS α], [TS β], f, g)"
    );
}

#[test]
fn test_topology_continuous_homotopy_refl_type() {
    use crate::tc::TypeChecker;
    // Topology.ContinuousHomotopy.refl : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (f : α → β) → Continuous f → ContinuousHomotopy f f
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ch_refl = Expr::const_(
        Name::from_string("Topology.ContinuousHomotopy.refl"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ch_refl)
        .expect("invariant: ContinuousHomotopy.refl should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "ContinuousHomotopy.refl should have 6 Pi binders (α, β, [TS α], [TS β], f, hcont)"
    );
}

#[test]
fn test_topology_continuous_homotopy_symm_type() {
    use crate::tc::TypeChecker;
    // Topology.ContinuousHomotopy.symm : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → {f g : α → β} → ContinuousHomotopy f g → ContinuousHomotopy g f
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ch_symm = Expr::const_(
        Name::from_string("Topology.ContinuousHomotopy.symm"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ch_symm)
        .expect("invariant: ContinuousHomotopy.symm should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 7,
        "ContinuousHomotopy.symm should have 7 Pi binders (α, β, [TS α], [TS β], f, g, h)"
    );
}

#[test]
fn test_topology_continuous_homotopy_trans_type() {
    use crate::tc::TypeChecker;
    // Topology.ContinuousHomotopy.trans : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → {f g h : α → β} → ContinuousHomotopy f g →
    //   ContinuousHomotopy g h → ContinuousHomotopy f h
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ch_trans = Expr::const_(
        Name::from_string("Topology.ContinuousHomotopy.trans"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ch_trans)
        .expect("invariant: ContinuousHomotopy.trans should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 9,
        "ContinuousHomotopy.trans should have 9 Pi binders (α, β, [TS α], [TS β], f, g, h, h1, h2)"
    );
}

#[test]
fn test_topology_homotopy_equiv_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → Type u
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let he = Expr::const_(Name::from_string("Topology.HomotopyEquiv"), vec![u_level]);
    let ty = tc
        .infer_type(&he)
        .expect("invariant: HomotopyEquiv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "HomotopyEquiv should have 4 Pi binders (α, β, [TS α], [TS β])"
    );
}

#[test]
fn test_topology_homotopy_equiv_to_fun_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.toFun : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → HomotopyEquiv α β → (α → β)
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let to_fun = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.toFun"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&to_fun)
        .expect("invariant: HomotopyEquiv.toFun should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "HomotopyEquiv.toFun should have 6 Pi binders (α, β, [TS α], [TS β], e, and return α→β)"
    );
}

#[test]
fn test_topology_homotopy_equiv_inv_fun_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.invFun : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → HomotopyEquiv α β → (β → α)
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let inv_fun = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.invFun"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&inv_fun)
        .expect("invariant: HomotopyEquiv.invFun should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "HomotopyEquiv.invFun should have 6 Pi binders (α, β, [TS α], [TS β], e, and return β→α)"
    );
}

#[test]
fn test_topology_homotopy_equiv_continuous_to_fun_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.continuous_toFun : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (e : HomotopyEquiv α β) → Continuous (toFun e)
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ct = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.continuous_toFun"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ct)
        .expect("invariant: HomotopyEquiv.continuous_toFun should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "HomotopyEquiv.continuous_toFun should have 5 Pi binders (α, β, [TS α], [TS β], e)"
    );
}

#[test]
fn test_topology_homotopy_equiv_continuous_inv_fun_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.continuous_invFun : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (e : HomotopyEquiv α β) → Continuous (invFun e)
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ci = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.continuous_invFun"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ci)
        .expect("invariant: HomotopyEquiv.continuous_invFun should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "HomotopyEquiv.continuous_invFun should have 5 Pi binders (α, β, [TS α], [TS β], e)"
    );
}

#[test]
fn test_topology_homotopy_equiv_left_inv_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.left_inv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (e : HomotopyEquiv α β) → Prop
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let li = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.left_inv"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&li)
        .expect("invariant: HomotopyEquiv.left_inv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "HomotopyEquiv.left_inv should have 5 Pi binders (α, β, [TS α], [TS β], e)"
    );
}

#[test]
fn test_topology_homotopy_equiv_right_inv_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.right_inv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (e : HomotopyEquiv α β) → Prop
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let ri = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.right_inv"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&ri)
        .expect("invariant: HomotopyEquiv.right_inv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "HomotopyEquiv.right_inv should have 5 Pi binders (α, β, [TS α], [TS β], e)"
    );
}

#[test]
fn test_topology_homotopy_equiv_refl_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.refl : {α : Type u} → [TopologicalSpace α] → HomotopyEquiv α α
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let he_refl = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.refl"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&he_refl)
        .expect("invariant: HomotopyEquiv.refl should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 2,
        "HomotopyEquiv.refl should have 2 Pi binders (α, [TS α])"
    );
}

#[test]
fn test_topology_homotopy_equiv_symm_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.symm : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → HomotopyEquiv α β → HomotopyEquiv β α
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let he_symm = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.symm"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&he_symm)
        .expect("invariant: HomotopyEquiv.symm should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "HomotopyEquiv.symm should have 5 Pi binders (α, β, [TS α], [TS β], e)"
    );
}

#[test]
fn test_topology_homotopy_equiv_trans_type() {
    use crate::tc::TypeChecker;
    // Topology.HomotopyEquiv.trans : {α β γ : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → [TopologicalSpace γ] →
    //   HomotopyEquiv α β → HomotopyEquiv β γ → HomotopyEquiv α γ
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let he_trans = Expr::const_(
        Name::from_string("Topology.HomotopyEquiv.trans"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&he_trans)
        .expect("invariant: HomotopyEquiv.trans should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 8,
        "HomotopyEquiv.trans should have 8 Pi binders (α, β, γ, [TS α], [TS β], [TS γ], e1, e2)"
    );
}

#[test]
fn test_topology_are_homotopy_equiv_type() {
    use crate::tc::TypeChecker;
    // Topology.AreHomotopyEquiv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → Prop
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let are_he = Expr::const_(
        Name::from_string("Topology.AreHomotopyEquiv"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&are_he)
        .expect("invariant: AreHomotopyEquiv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "AreHomotopyEquiv should have 4 Pi binders (α, β, [TS α], [TS β])"
    );
}

#[test]
fn test_topology_are_homotopy_equiv_def_type() {
    use crate::tc::TypeChecker;
    // Topology.are_homotopy_equiv_def : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → Iff (AreHomotopyEquiv α β) (Nonempty (HomotopyEquiv α β))
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let are_he_def = Expr::const_(
        Name::from_string("Topology.are_homotopy_equiv_def"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&are_he_def)
        .expect("invariant: are_homotopy_equiv_def should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "are_homotopy_equiv_def should have 4 Pi binders (α, β, [TS α], [TS β])"
    );
}

#[test]
fn test_topology_are_homotopy_equiv_refl_type() {
    use crate::tc::TypeChecker;
    // Topology.are_homotopy_equiv_refl : {α : Type u} → [TopologicalSpace α] →
    //   AreHomotopyEquiv α α
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let are_he_refl = Expr::const_(
        Name::from_string("Topology.are_homotopy_equiv_refl"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&are_he_refl)
        .expect("invariant: are_homotopy_equiv_refl should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 2,
        "are_homotopy_equiv_refl should have 2 Pi binders (α, [TS α])"
    );
}

#[test]
fn test_topology_are_homotopy_equiv_symm_type() {
    use crate::tc::TypeChecker;
    // Topology.are_homotopy_equiv_symm : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → AreHomotopyEquiv α β → AreHomotopyEquiv β α
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let are_he_symm = Expr::const_(
        Name::from_string("Topology.are_homotopy_equiv_symm"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&are_he_symm)
        .expect("invariant: are_homotopy_equiv_symm should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "are_homotopy_equiv_symm should have 5 Pi binders (α, β, [TS α], [TS β], h)"
    );
}

#[test]
fn test_topology_are_homotopy_equiv_trans_type() {
    use crate::tc::TypeChecker;
    // Topology.are_homotopy_equiv_trans : {α β γ : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → [TopologicalSpace γ] →
    //   AreHomotopyEquiv α β → AreHomotopyEquiv β γ → AreHomotopyEquiv α γ
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let are_he_trans = Expr::const_(
        Name::from_string("Topology.are_homotopy_equiv_trans"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&are_he_trans)
        .expect("invariant: are_homotopy_equiv_trans should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 8,
        "are_homotopy_equiv_trans should have 8 Pi binders (α, β, γ, [TS α], [TS β], [TS γ], h1, h2)"
    );
}

#[test]
fn test_topology_homeomorphism_to_homotopy_equiv_type() {
    use crate::tc::TypeChecker;
    // Topology.homeomorphism_to_homotopy_equiv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → (f : α → β) → (g : β → α) → Homeomorphism α β f g →
    //   HomotopyEquiv α β
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let homeo_to_he = Expr::const_(
        Name::from_string("Topology.homeomorphism_to_homotopy_equiv"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&homeo_to_he)
        .expect("invariant: homeomorphism_to_homotopy_equiv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 7,
        "homeomorphism_to_homotopy_equiv should have 7 Pi binders (α, β, [TS α], [TS β], f, g, h)"
    );
}

#[test]
fn test_topology_contractible_are_homotopy_equiv_type() {
    use crate::tc::TypeChecker;
    // Topology.contractible_are_homotopy_equiv : {α β : Type u} → [TopologicalSpace α] →
    //   [TopologicalSpace β] → Contractible α → Contractible β → AreHomotopyEquiv α β
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let contr_he = Expr::const_(
        Name::from_string("Topology.contractible_are_homotopy_equiv"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&contr_he)
        .expect("invariant: contractible_are_homotopy_equiv should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "contractible_are_homotopy_equiv should have 6 Pi binders (α, β, [TS α], [TS β], hα, hβ)"
    );
}

#[test]
fn test_topology_homotopy_equiv_preserves_path_connected_type() {
    use crate::tc::TypeChecker;
    // Topology.homotopy_equiv_preserves_path_connected : {α β : Type u} →
    //   [TopologicalSpace α] → [TopologicalSpace β] →
    //   HomotopyEquiv α β → PathConnected α → PathConnected β
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let he_pc = Expr::const_(
        Name::from_string("Topology.homotopy_equiv_preserves_path_connected"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&he_pc)
        .expect("invariant: homotopy_equiv_preserves_path_connected should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "homotopy_equiv_preserves_path_connected should have 6 Pi binders (α, β, [TS α], [TS β], e, h)"
    );
}

#[test]
fn test_topology_homotopy_equivalence_all_constants_exist() {
    // Test that all 20 HomotopyEquivalence constants exist
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    let constants = [
        "Topology.ContinuousHomotopy",
        "Topology.ContinuousHomotopy.refl",
        "Topology.ContinuousHomotopy.symm",
        "Topology.ContinuousHomotopy.trans",
        "Topology.HomotopyEquiv",
        "Topology.HomotopyEquiv.toFun",
        "Topology.HomotopyEquiv.invFun",
        "Topology.HomotopyEquiv.continuous_toFun",
        "Topology.HomotopyEquiv.continuous_invFun",
        "Topology.HomotopyEquiv.left_inv",
        "Topology.HomotopyEquiv.right_inv",
        "Topology.HomotopyEquiv.refl",
        "Topology.HomotopyEquiv.symm",
        "Topology.HomotopyEquiv.trans",
        "Topology.AreHomotopyEquiv",
        "Topology.are_homotopy_equiv_def",
        "Topology.are_homotopy_equiv_refl",
        "Topology.are_homotopy_equiv_symm",
        "Topology.are_homotopy_equiv_trans",
        "Topology.homeomorphism_to_homotopy_equiv",
        "Topology.contractible_are_homotopy_equiv",
        "Topology.homotopy_equiv_preserves_path_connected",
    ];

    for const_name in &constants {
        assert_const(&env, const_name);
    }
}

#[test]
fn test_topology_homotopy_equivalence_dependencies_initialized() {
    // Test that initializing HomotopyEquivalence initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_homotopy_equivalence().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_contractible());
    assert!(env.has_topology_homeomorphism());
    assert!(env.has_topology_path_connected());
    assert!(env.has_classical());
    assert!(env.has_iff());
}

// ================================================================
// Tests for Topology.Retract
// ================================================================

#[test]
fn test_topology_retract_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_retract());
    env.init_topology_retract().unwrap();
    assert!(env.has_topology_retract());
}

#[test]
fn test_topology_retract_idempotent() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();
    env.init_topology_retract().unwrap();
    assert!(env.has_topology_retract());
}

#[test]
fn test_topology_is_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsRetract"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {X : Type u} → [TopologicalSpace X] → (X → Prop) → Prop
}

#[test]
fn test_topology_retraction_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Retraction"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {X : Type u} → [TopologicalSpace X] → (X → Prop) → Type u
}

#[test]
fn test_topology_retraction_map_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Retraction.map"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {X : Type u} → [TopologicalSpace X] → {A : X → Prop} → Retraction A → (X → X)
}

#[test]
fn test_topology_retraction_continuous_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Retraction.continuous"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_retraction_maps_into_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Retraction.maps_into"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_retraction_fixes_subset_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Retraction.fixes_subset"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_retract_def_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.is_retract_def"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_deformation_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsDeformationRetract"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_deformation_retraction_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.DeformationRetraction"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_deformation_retraction_to_retraction_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.DeformationRetraction.toRetraction",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_deformation_retraction_homotopy_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.DeformationRetraction.homotopy",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_deformation_retract_def_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.is_deformation_retract_def"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_strong_deformation_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsStrongDeformationRetract"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_strong_deformation_retraction_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.StrongDeformationRetraction"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_strong_deformation_retraction_to_deformation_retraction_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.StrongDeformationRetraction.toDeformationRetraction",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_strong_deformation_retraction_fixes_points_rel_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.StrongDeformationRetraction.fixes_points_rel",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_strong_deformation_retract_def_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.is_strong_deformation_retract_def",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_strong_deformation_retract_is_deformation_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.strong_deformation_retract_is_deformation_retract",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_deformation_retract_is_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.deformation_retract_is_retract",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_deformation_retract_homotopy_equiv_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.deformation_retract_homotopy_equiv",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_contractible_iff_point_deformation_retract_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.contractible_iff_point_deformation_retract",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_retract_of_contractible_is_contractible_type() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.retract_of_contractible_is_contractible",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_retract_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    // List of all constants that should exist
    let constants = vec![
        "Topology.IsRetract",
        "Topology.Retraction",
        "Topology.Retraction.map",
        "Topology.Retraction.continuous",
        "Topology.Retraction.maps_into",
        "Topology.Retraction.fixes_subset",
        "Topology.is_retract_def",
        "Topology.IsDeformationRetract",
        "Topology.DeformationRetraction",
        "Topology.DeformationRetraction.toRetraction",
        "Topology.DeformationRetraction.homotopy",
        "Topology.is_deformation_retract_def",
        "Topology.IsStrongDeformationRetract",
        "Topology.StrongDeformationRetraction",
        "Topology.StrongDeformationRetraction.toDeformationRetraction",
        "Topology.StrongDeformationRetraction.fixes_points_rel",
        "Topology.is_strong_deformation_retract_def",
        "Topology.strong_deformation_retract_is_deformation_retract",
        "Topology.deformation_retract_is_retract",
        "Topology.deformation_retract_homotopy_equiv",
        "Topology.contractible_iff_point_deformation_retract",
        "Topology.retract_of_contractible_is_contractible",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_retract_dependencies_initialized() {
    // Test that initializing Retract initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_retract().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_homotopy_equivalence());
    assert!(env.has_classical());
    assert!(env.has_iff());
    assert!(env.has_eq());
}

// ================================================================
// Tests for Topology.FiberBundle
// ================================================================

#[test]
fn test_topology_fiber_bundle_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_fiber_bundle());
    env.init_topology_fiber_bundle().unwrap();
    assert!(env.has_topology_fiber_bundle());
}

#[test]
fn test_topology_fiber_bundle_idempotent() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();
    env.init_topology_fiber_bundle().unwrap();
    assert!(env.has_topology_fiber_bundle());
}

#[test]
fn test_topology_fiber_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.FiberBundle"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {E B F : Type u} → [TopologicalSpace E] → [TopologicalSpace B] → [TopologicalSpace F] → (E → B) → Type u
}

#[test]
fn test_topology_fiber_bundle_proj_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.FiberBundle.proj"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_fiber_bundle_continuous_proj_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.FiberBundle.continuous_proj"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_fiber_bundle_fiber_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.FiberBundle.fiber"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_base_set_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization.baseSet"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_base_set_open_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization.baseSet_open"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_to_fun_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization.toFun"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_inv_fun_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization.invFun"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivialization_proj_to_fun_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Trivialization.proj_toFun"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_trivial_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsTrivialBundle"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_trivial_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.trivial_bundle"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_bundle_map_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsBundleMap"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_locally_trivial_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsLocallyTrivial"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_fiber_bundle_locally_trivial_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.fiber_bundle_locally_trivial"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_pullback_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsPullbackBundle"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_bundle_fiber_homeomorphic_type() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.bundle_fiber_homeomorphic"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_fiber_bundle_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    let constants = [
        "Topology.FiberBundle",
        "Topology.FiberBundle.proj",
        "Topology.FiberBundle.continuous_proj",
        "Topology.FiberBundle.fiber",
        "Topology.Trivialization",
        "Topology.Trivialization.baseSet",
        "Topology.Trivialization.baseSet_open",
        "Topology.Trivialization.toFun",
        "Topology.Trivialization.invFun",
        "Topology.Trivialization.proj_toFun",
        "Topology.IsTrivialBundle",
        "Topology.trivial_bundle",
        "Topology.IsBundleMap",
        "Topology.IsLocallyTrivial",
        "Topology.fiber_bundle_locally_trivial",
        "Topology.IsPullbackBundle",
        "Topology.bundle_fiber_homeomorphic",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_fiber_bundle_dependencies_initialized() {
    // Test that initializing FiberBundle initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_fiber_bundle().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_prod());
    assert!(env.has_classical());
    assert!(env.has_eq());
}

// ================================================================
// Topology.Quotient Tests
// ================================================================

#[test]
fn test_topology_quotient_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_quotient());
    env.init_topology_quotient().unwrap();
    assert!(env.has_topology_quotient());
}

#[test]
fn test_topology_quotient_idempotent() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();
    env.init_topology_quotient().unwrap();
    assert!(env.has_topology_quotient());
}

#[test]
fn test_topology_quotient_topology_type() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.QuotientTopology"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {X Y : Type u} → [TopologicalSpace X] → (X → Y) → TopologicalSpace Y
}

#[test]
fn test_topology_quotient_is_open_iff() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.QuotientTopology.isOpen_iff"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_is_closed_iff() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.QuotientTopology.isClosed_iff"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_quotient_map() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsQuotientMap"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_quotient_map_continuous() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsQuotientMap.continuous"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_quotient_map_is_open_preimage() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsQuotientMap.isOpen_preimage"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_continuous_iff() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.QuotientTopology.continuous_iff",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_mk_continuous() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.QuotientTopology.mk_continuous",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_quotient_map_comp() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsQuotientMap.comp"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_open_map() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsOpenMap"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_closed_map() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsClosedMap"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_map_of_surjective_open() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.quotient_map_of_surjective_continuous_open",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_map_of_surjective_closed() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.quotient_map_of_surjective_continuous_closed",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_coinduced_eq() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.QuotientTopology.coinduced_eq"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_is_finest() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.QuotientTopology.isFinest"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_quotient_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    let constants = [
        "Topology.QuotientTopology",
        "Topology.QuotientTopology.isOpen_iff",
        "Topology.QuotientTopology.isClosed_iff",
        "Topology.IsQuotientMap",
        "Topology.IsQuotientMap.continuous",
        "Topology.IsQuotientMap.isOpen_preimage",
        "Topology.QuotientTopology.continuous_iff",
        "Topology.QuotientTopology.mk_continuous",
        "Topology.IsQuotientMap.comp",
        "Topology.quotient_map_of_surjective_continuous_open",
        "Topology.IsOpenMap",
        "Topology.IsClosedMap",
        "Topology.quotient_map_of_surjective_continuous_closed",
        "Topology.QuotientTopology.coinduced_eq",
        "Topology.QuotientTopology.isFinest",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_quotient_dependencies_initialized() {
    // Test that initializing Quotient initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_quotient().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_prod());
    assert!(env.has_classical());
    assert!(env.has_eq());
}

// ================================================================
// Topology.Subspace Tests
// ================================================================

#[test]
fn test_topology_subspace_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_subspace());
    env.init_topology_subspace().unwrap();
    assert!(env.has_topology_subspace());
}

#[test]
fn test_topology_subspace_idempotent() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();
    env.init_topology_subspace().unwrap();
    assert!(env.has_topology_subspace());
}

#[test]
fn test_topology_subspace_topology_type() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.SubspaceTopology"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
    // {X : Type u} → [TopologicalSpace X] → (X → Prop) → TopologicalSpace (Subtype A)
}

#[test]
fn test_topology_subspace_is_open_iff() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.SubspaceTopology.isOpen_iff"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_subspace_is_closed_iff() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.SubspaceTopology.isClosed_iff"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_inclusion_continuous() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.inclusion_continuous"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsEmbedding"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_embedding_continuous() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsEmbedding.continuous"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_embedding_injective() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsEmbedding.injective"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_inclusion_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.inclusion_embedding"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_subspace_induced_eq() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.SubspaceTopology.induced_eq"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_subspace_restrict_continuous() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.SubspaceTopology.restrict_continuous",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_open_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsOpenEmbedding"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_is_closed_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsClosedEmbedding"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_open_embedding_to_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.IsOpenEmbedding.toIsEmbedding"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_closed_embedding_to_embedding() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.IsClosedEmbedding.toIsEmbedding",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_open_embedding_of_open_inclusion() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.open_embedding_of_open_inclusion",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_closed_embedding_of_closed_inclusion() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.closed_embedding_of_closed_inclusion",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_subspace_is_coarsest() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.SubspaceTopology.isCoarsest"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_subspace_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    let constants = [
        "Topology.SubspaceTopology",
        "Topology.SubspaceTopology.isOpen_iff",
        "Topology.SubspaceTopology.isClosed_iff",
        "Topology.inclusion_continuous",
        "Topology.IsEmbedding",
        "Topology.IsEmbedding.continuous",
        "Topology.IsEmbedding.injective",
        "Topology.inclusion_embedding",
        "Topology.SubspaceTopology.induced_eq",
        "Topology.SubspaceTopology.restrict_continuous",
        "Topology.IsOpenEmbedding",
        "Topology.IsClosedEmbedding",
        "Topology.IsOpenEmbedding.toIsEmbedding",
        "Topology.IsClosedEmbedding.toIsEmbedding",
        "Topology.open_embedding_of_open_inclusion",
        "Topology.closed_embedding_of_closed_inclusion",
        "Topology.SubspaceTopology.isCoarsest",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_subspace_subtype_applications_have_base_type_arg() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_subspace()
        .expect("invariant: init_topology_subspace should succeed");

    let tc = TypeChecker::new(&env);
    let u_level = Level::param(Name::from_string("u"));
    let subtype_name = Name::from_string("Subtype");
    let declarations = [
        "Topology.SubspaceTopology",
        "Topology.SubspaceTopology.isOpen_iff",
        "Topology.SubspaceTopology.isClosed_iff",
        "Topology.inclusion_continuous",
        "Topology.inclusion_embedding",
        "Topology.SubspaceTopology.induced_eq",
        "Topology.SubspaceTopology.restrict_continuous",
        "Topology.open_embedding_of_open_inclusion",
        "Topology.closed_embedding_of_closed_inclusion",
        "Topology.SubspaceTopology.isCoarsest",
    ];

    for decl in declarations {
        let decl_const = Expr::const_(Name::from_string(decl), vec![u_level.clone()]);
        let ty = match tc.infer_type(&decl_const) {
            Ok(t) => t,
            Err(err) => panic!("invariant: {decl} should type-check: {err:?}"),
        };

        let mut subtype_app_arities = Vec::new();
        collect_const_app_arities(&ty, &subtype_name, &mut subtype_app_arities);
        assert!(
            !subtype_app_arities.is_empty(),
            "{decl} type should contain at least one Subtype application"
        );
        assert!(
            subtype_app_arities.iter().all(|arity| *arity >= 2),
            "Subtype must include base type and predicate in {decl}; arities={subtype_app_arities:?}"
        );
    }
}

#[test]
fn test_topology_subspace_dependencies_initialized() {
    // Test that initializing Subspace initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_subspace().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_exists());
    assert!(env.has_eq());
}

// ================================================================
// Topology.Product tests
// ================================================================

#[test]
fn test_topology_product_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_product());
    env.init_topology_product().unwrap();
    assert!(env.has_topology_product());

    // Second initialization should be a no-op
    env.init_topology_product().unwrap();
    assert!(env.has_topology_product());
}

#[test]
fn test_topology_product_topology_exists() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology"))
        .unwrap();
    // Two universe params: u, v
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_product_fst_continuous() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.ProductTopology.fst_continuous",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_product_snd_continuous() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.ProductTopology.snd_continuous",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_product_is_open_prod() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology.isOpen_prod"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_product_is_closed_prod() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology.isClosed_prod"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_product_continuous_prod_mk() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.ProductTopology.continuous_prod_mk",
        ))
        .unwrap();
    // Single universe for same-universe case
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_product_prod_continuous() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string(
            "Topology.ProductTopology.prod_continuous",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_product_is_open_iff() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology.isOpen_iff"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_product_induced_eq() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology.induced_eq"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_product_is_coarsest() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.ProductTopology.isCoarsest"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_product_homeomorphism_when_available() {
    let mut env = Environment::new();
    // Initialize Homeomorphism first to get the optional constants
    env.init_topology_homeomorphism().unwrap();
    env.init_topology_product().unwrap();

    // prod_homeomorphism and prod_assoc should exist
    for s in [
        "Topology.ProductTopology.prod_homeomorphism",
        "Topology.ProductTopology.prod_assoc",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_product_homeomorphism_not_available_without_init() {
    let mut env = Environment::new();
    // Don't initialize Homeomorphism - just init product directly
    env.init_topology_product().unwrap();

    // These optional constants should NOT exist
    assert!(
        env.get_const(&Name::from_string("Topology.ProductTopology.prod_homeomorphism"))
            .is_none(),
        "Topology.ProductTopology.prod_homeomorphism should NOT exist when Homeomorphism is not initialized"
    );
}

#[test]
fn test_topology_product_connected_when_available() {
    let mut env = Environment::new();
    env.init_topology_connected().unwrap();
    env.init_topology_product().unwrap();

    assert_const(&env, "Topology.ProductTopology.prod_connected");
}

#[test]
fn test_topology_product_compact_when_available() {
    let mut env = Environment::new();
    env.init_topology_compact().unwrap();
    env.init_topology_product().unwrap();

    assert_const(&env, "Topology.ProductTopology.prod_compact");
}

#[test]
fn test_topology_product_hausdorff_when_available() {
    let mut env = Environment::new();
    env.init_topology_hausdorff().unwrap();
    env.init_topology_product().unwrap();

    for s in [
        "Topology.ProductTopology.prod_hausdorff",
        "Topology.ProductTopology.diagonal_closed",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_product_all_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    let core_constants = [
        "Topology.ProductTopology",
        "Topology.ProductTopology.fst_continuous",
        "Topology.ProductTopology.snd_continuous",
        "Topology.ProductTopology.isOpen_prod",
        "Topology.ProductTopology.isClosed_prod",
        "Topology.ProductTopology.continuous_prod_mk",
        "Topology.ProductTopology.prod_continuous",
        "Topology.ProductTopology.isOpen_iff",
        "Topology.ProductTopology.induced_eq",
        "Topology.ProductTopology.isCoarsest",
    ];

    for name in core_constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_product_all_optional_constants_with_deps() {
    let mut env = Environment::new();
    // Initialize all dependencies for optional constants
    env.init_topology_homeomorphism().unwrap();
    env.init_topology_connected().unwrap();
    env.init_topology_compact().unwrap();
    env.init_topology_hausdorff().unwrap();
    env.init_topology_product().unwrap();

    let optional_constants = [
        "Topology.ProductTopology.prod_homeomorphism",
        "Topology.ProductTopology.prod_assoc",
        "Topology.ProductTopology.prod_connected",
        "Topology.ProductTopology.prod_compact",
        "Topology.ProductTopology.prod_hausdorff",
        "Topology.ProductTopology.diagonal_closed",
    ];

    for name in optional_constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_product_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_product().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_prod());
    assert!(env.has_eq());
}

// ================================================================
// TOPOLOGY.HIGHERHOMOTOPY TESTS
// ================================================================

#[test]
fn test_topology_higher_homotopy_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_higher_homotopy());
    env.init_topology_higher_homotopy().unwrap();
    assert!(env.has_topology_higher_homotopy());

    // Second initialization should be a no-op
    env.init_topology_higher_homotopy().unwrap();
    assert!(env.has_topology_higher_homotopy());
}

#[test]
fn test_topology_sphere_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Sphere"))
        .unwrap();
    // No universe params (Sphere : ℕ → Type 0)
    assert_eq!(c.level_params.len(), 0);
}

#[test]
fn test_topology_sphere_basepoint_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Sphere.basepoint"))
        .unwrap();
    assert_eq!(c.level_params.len(), 0);
}

#[test]
fn test_topology_sphere_topological_space_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Sphere.topological_space"))
        .unwrap();
    assert_eq!(c.level_params.len(), 0);
}

#[test]
fn test_topology_based_map_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.BasedMap"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_based_map_eval_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.BasedMap.eval"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_based_map_preserves_basepoint_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.BasedMap.preserves_basepoint"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_based_homotopy_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.BasedHomotopy"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_class_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.class"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_class_eq_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.class_eq"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_mul_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.mul"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_one_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.one"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_inv_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.inv"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_mul_assoc_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.mul_assoc"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_one_mul_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.one_mul"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_mul_one_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.mul_one"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_mul_inv_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.mul_inv"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_group_mul_comm_exists() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.HigherHomotopyGroup.mul_comm"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_pi_one_eq_fundamental_group() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    // Should exist because fundamental group is initialized as dependency
    let c = env
        .get_const(&Name::from_string(
            "Topology.HigherHomotopyGroup.pi_one_eq_fundamental_group",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_contractible_trivial_when_available() {
    let mut env = Environment::new();
    // First initialize contractible, then higher homotopy
    env.init_topology_contractible().unwrap();
    env.init_topology_higher_homotopy().unwrap();

    // Should exist when contractible is initialized first
    let c = env
        .get_const(&Name::from_string(
            "Topology.HigherHomotopyGroup.contractible_trivial",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_contractible_trivial_not_available_without_init() {
    let mut env = Environment::new();
    // Only initialize higher homotopy (contractible not explicitly initialized before)
    env.init_topology_higher_homotopy().unwrap();

    // Without explicit contractible init, the constant should NOT be available
    // because init_topology_higher_homotopy does not transitively init contractible.
    assert!(
        env.get_const(&Name::from_string(
            "Topology.HigherHomotopyGroup.contractible_trivial",
        ))
        .is_none(),
        "contractible_trivial should NOT be available without explicit contractible init"
    );
}

#[test]
fn test_topology_higher_homotopy_equiv_iso_when_available() {
    let mut env = Environment::new();
    // First initialize homotopy_equivalence, then higher homotopy
    env.init_topology_homotopy_equivalence().unwrap();
    env.init_topology_higher_homotopy().unwrap();

    // Should exist when homotopy_equivalence is initialized first
    let c = env
        .get_const(&Name::from_string(
            "Topology.HigherHomotopyGroup.homotopy_equiv_iso",
        ))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_higher_homotopy_equiv_iso_not_available_without_init() {
    let mut env = Environment::new();
    // Only initialize higher homotopy
    env.init_topology_higher_homotopy().unwrap();

    // Without explicit homotopy_equivalence init, the constant should NOT be available
    // because init_topology_higher_homotopy does not transitively init homotopy_equivalence.
    assert!(
        env.get_const(&Name::from_string(
            "Topology.HigherHomotopyGroup.homotopy_equiv_iso",
        ))
        .is_none(),
        "homotopy_equiv_iso should NOT be available without explicit homotopy_equivalence init"
    );
}

#[test]
fn test_topology_higher_homotopy_all_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    let core_constants = vec![
        "Topology.Sphere",
        "Topology.Sphere.basepoint",
        "Topology.Sphere.topological_space",
        "Topology.BasedMap",
        "Topology.BasedMap.eval",
        "Topology.BasedMap.preserves_basepoint",
        "Topology.BasedHomotopy",
        "Topology.HigherHomotopyGroup",
        "Topology.HigherHomotopyGroup.class",
        "Topology.HigherHomotopyGroup.class_eq",
        "Topology.HigherHomotopyGroup.mul",
        "Topology.HigherHomotopyGroup.one",
        "Topology.HigherHomotopyGroup.inv",
        "Topology.HigherHomotopyGroup.mul_assoc",
        "Topology.HigherHomotopyGroup.one_mul",
        "Topology.HigherHomotopyGroup.mul_one",
        "Topology.HigherHomotopyGroup.mul_inv",
        "Topology.HigherHomotopyGroup.mul_comm",
    ];

    for name in core_constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_higher_homotopy_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_higher_homotopy().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_fundamental_group());
    assert!(env.has_topology_path_connected());
    assert!(env.has_nat());
    assert!(env.has_lt());
    assert!(env.has_eq());
    assert_const(&env, "Nat.lt");
}

// ================================================================
// TOPOLOGY.SUSPENSION TESTS
// ================================================================

#[test]
fn test_topology_suspension_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_suspension());
    env.init_topology_suspension().unwrap();
    assert!(env.has_topology_suspension());

    // Second initialization should be a no-op
    env.init_topology_suspension().unwrap();
    assert!(env.has_topology_suspension());
}

#[test]
fn test_topology_suspension_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension"))
        .unwrap();
    // Has universe param u
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_north_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.north"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_south_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.south"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_merid_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.merid"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_topological_space_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.topological_space"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_cone_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env.get_const(&Name::from_string("Topology.Cone")).unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_cone_apex_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.apex"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_cone_base_incl_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.base_incl"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_cone_path_to_apex_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.path_to_apex"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_cone_topological_space_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.topological_space"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_map_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map"))
        .unwrap();
    // Two universe params: u, v
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_suspension_map_north_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map_north"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_suspension_map_south_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map_south"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_suspension_map_continuous_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map_continuous"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_suspension_map_continuous_type_uses_suspension_instances() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let map_continuous = Expr::const_(
        Name::from_string("Topology.Suspension.map_continuous"),
        vec![Level::param(u), Level::param(v)],
    );

    let tc = TypeChecker::new(&env);
    let ty = tc
        .infer_type(&map_continuous)
        .expect("invariant: Suspension.map_continuous should type-check");

    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "Suspension.map_continuous should have 6 Pi binders (α, β, [TS α], [TS β], f, hf)"
    );

    assert!(
        !matches!(&t.kind, ExprKind::Sort(_)),
        "Suspension.map_continuous codomain must be Continuous (Suspension.map f), not a bare sort"
    );

    let continuous = Name::from_string("Topology.Continuous");
    assert!(
        expr_contains_const(&t, &continuous),
        "Suspension.map_continuous codomain must mention Topology.Continuous"
    );

    let suspension_top_space = Name::from_string("Topology.Suspension.topological_space");
    assert!(
        expr_contains_const(&t, &suspension_top_space),
        "Suspension.map_continuous codomain must use Suspension.topological_space instances"
    );
}

#[test]
fn test_topology_suspension_freudenthal_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.freudenthal"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_freudenthal_uses_suspension_topological_space_instance() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.freudenthal"))
        .unwrap();
    let susp_top_space = Name::from_string("Topology.Suspension.topological_space");
    assert!(
        expr_contains_const(&c.type_, &susp_top_space),
        "freudenthal type must build TopologicalSpace (Suspension α) via Suspension.topological_space"
    );
}

#[test]
fn test_topology_cone_contractible_uses_cone_topological_space_instance() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.contractible"))
        .unwrap();
    let cone_top_space = Name::from_string("Topology.Cone.topological_space");
    assert!(
        expr_contains_const(&c.type_, &cone_top_space),
        "Cone.contractible type must apply Contractible to Cone.topological_space instance"
    );
}

#[test]
fn test_topology_suspension_join_cones_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.join_cones"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_rec_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.rec"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_cone_rec_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Cone.rec"))
        .unwrap();
    assert_eq!(c.level_params.len(), 2);
}

#[test]
fn test_topology_suspension_map_id_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map_id"))
        .unwrap();
    assert_eq!(c.level_params.len(), 1);
}

#[test]
fn test_topology_suspension_map_comp_exists() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let c = env
        .get_const(&Name::from_string("Topology.Suspension.map_comp"))
        .unwrap();
    // Three universe params: u, v, w
    assert_eq!(c.level_params.len(), 3);
}

#[test]
fn test_topology_suspension_all_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    let core_constants = [
        "Topology.Suspension",
        "Topology.Suspension.north",
        "Topology.Suspension.south",
        "Topology.Suspension.merid",
        "Topology.Suspension.topological_space",
        "Topology.Cone",
        "Topology.Cone.apex",
        "Topology.Cone.base_incl",
        "Topology.Cone.path_to_apex",
        "Topology.Cone.topological_space",
        "Topology.Suspension.map",
        "Topology.Suspension.map_north",
        "Topology.Suspension.map_south",
        "Topology.Suspension.map_continuous",
        "Topology.Suspension.freudenthal",
        "Topology.Suspension.join_cones",
        "Topology.Suspension.rec",
        "Topology.Cone.rec",
        "Topology.Suspension.map_id",
        "Topology.Suspension.map_comp",
    ];

    for name in &core_constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_suspension_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_suspension().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_higher_homotopy());
    assert!(env.has_topology_continuous());
    assert!(env.has_eq());
}

// ============================================================
// Topology.VectorBundle tests
// ============================================================

#[test]
fn test_topology_vector_bundle_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_vector_bundle());
    env.init_topology_vector_bundle().unwrap();
    assert!(env.has_topology_vector_bundle());
}

#[test]
fn test_topology_vector_bundle_idempotent() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    env.init_topology_vector_bundle().unwrap();
    assert!(env.has_topology_vector_bundle());
}

#[test]
fn test_topology_vector_bundle_type() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle");
}

#[test]
fn test_topology_vector_bundle_to_fiber_bundle_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.toFiberBundle");
}

#[test]
fn test_topology_vector_bundle_zero_section_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.zero_section");
}

#[test]
fn test_topology_vector_bundle_zero_section_continuous_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.zero_section_continuous");
}

#[test]
fn test_topology_vector_bundle_section_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.section");
}

#[test]
fn test_topology_vector_bundle_rank_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.rank");
}

#[test]
fn test_topology_vector_bundle_direct_sum_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.direct_sum");
}

#[test]
fn test_topology_vector_bundle_tensor_product_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.tensor_product");
}

#[test]
fn test_topology_vector_bundle_dual_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.dual");
}

#[test]
fn test_topology_vector_bundle_pullback_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.pullback");
}

#[test]
fn test_topology_vector_bundle_tangent_bundle_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.tangent_bundle");
}

#[test]
fn test_topology_vector_bundle_cotangent_bundle_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.cotangent_bundle");
}

#[test]
fn test_topology_vector_bundle_section_zero_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.section_zero");
}

#[test]
fn test_topology_vector_bundle_isomorphism_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.isomorphism");
}

#[test]
fn test_topology_vector_bundle_hom_bundle_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.hom_bundle");
}

#[test]
fn test_topology_vector_bundle_exterior_power_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.exterior_power");
}

#[test]
fn test_topology_vector_bundle_proj_surjective_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.proj_is_surjective");
}

#[test]
fn test_topology_vector_bundle_fiber_nonempty_exists() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();
    assert_const(&env, "Topology.VectorBundle.fiber_nonempty");
}

#[test]
fn test_topology_vector_bundle_all_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();

    for name in [
        "Topology.VectorBundle",
        "Topology.VectorBundle.toFiberBundle",
        "Topology.VectorBundle.zero_section",
        "Topology.VectorBundle.zero_section_continuous",
        "Topology.VectorBundle.section",
        "Topology.VectorBundle.rank",
        "Topology.VectorBundle.direct_sum",
        "Topology.VectorBundle.tensor_product",
        "Topology.VectorBundle.dual",
        "Topology.VectorBundle.pullback",
        "Topology.VectorBundle.tangent_bundle",
        "Topology.VectorBundle.cotangent_bundle",
        "Topology.VectorBundle.section_zero",
        "Topology.VectorBundle.isomorphism",
        "Topology.VectorBundle.hom_bundle",
        "Topology.VectorBundle.exterior_power",
        "Topology.VectorBundle.proj_is_surjective",
        "Topology.VectorBundle.fiber_nonempty",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_vector_bundle_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_vector_bundle().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topology_fiber_bundle());
    assert!(env.has_topology_continuous());
    assert!(env.has_add_comm_group());
    assert!(env.has_semiring());
    assert!(env.has_eq());
}

// ============================================================
// Topology.CoproductTopology tests
// ============================================================

#[test]
fn test_topology_coproduct_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_coproduct());
    env.init_topology_coproduct().unwrap();
    assert!(env.has_topology_coproduct());
}

#[test]
fn test_topology_coproduct_idempotent() {
    let mut env = Environment::new();
    env.init_topology_coproduct().unwrap();
    env.init_topology_coproduct().unwrap();
    assert!(env.has_topology_coproduct());
}

#[test]
fn test_topology_coproduct_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_coproduct().unwrap();

    for s in [
        "Topology.CoproductTopology",
        "Topology.CoproductTopology.inl_continuous",
        "Topology.CoproductTopology.inr_continuous",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_coproduct_homeomorphism_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_coproduct().unwrap();

    for s in [
        "Topology.CoproductTopology.swap_homeomorphism",
        "Topology.CoproductTopology.assoc_homeomorphism",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_coproduct_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_coproduct().unwrap();

    let constants = [
        "Topology.CoproductTopology",
        "Topology.CoproductTopology.isOpen_iff",
        "Topology.CoproductTopology.isClosed_iff",
        "Topology.CoproductTopology.inl_continuous",
        "Topology.CoproductTopology.inr_continuous",
        "Topology.CoproductTopology.elim_continuous",
        "Topology.CoproductTopology.universal",
        "Topology.CoproductTopology.swap_homeomorphism",
        "Topology.CoproductTopology.assoc_homeomorphism",
        "Topology.CoproductTopology.connected_iff",
        "Topology.CoproductTopology.compact_iff",
        "Topology.CoproductTopology.sum_map_continuous",
        "Topology.CoproductTopology.cover_by_components",
        "Topology.CoproductTopology.disjoint_union_subspace",
    ];

    for name in &constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_coproduct_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_coproduct().unwrap();

    assert!(env.has_sum());
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_homeomorphism());
    assert!(env.has_topology_connected());
    assert!(env.has_topology_compact());
    assert!(env.has_eq());
}

// ============================================================
// Topology.CW tests
// ============================================================

#[test]
fn test_topology_cw_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_cw());
    env.init_topology_cw().unwrap();
    assert!(env.has_topology_cw());
}

#[test]
fn test_topology_cw_idempotent() {
    let mut env = Environment::new();
    env.init_topology_cw().unwrap();
    env.init_topology_cw().unwrap();
    assert!(env.has_topology_cw());
}

#[test]
fn test_topology_cw_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cw().unwrap();

    for s in [
        "Topology.CWComplex",
        "Topology.CWComplex.skeleton",
        "Topology.CWComplex.cell",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_cw_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cw().unwrap();

    let constants = [
        "Topology.CWComplex",
        "Topology.CWComplex.skeleton",
        "Topology.CWComplex.cell",
        "Topology.CWComplex.attach_cell",
        "Topology.CWComplex.characteristic_map",
        "Topology.CWComplex.closure_finite",
        "Topology.CWComplex.weak_topology",
        "Topology.CWComplex.homotopy_extension",
        "Topology.CWComplex.whitehead",
        "Topology.CWComplex.cellular_approximation",
        "Topology.CWComplex.subcomplex",
        "Topology.CWComplex.cw_on_subset",
        "Topology.CWComplex.connectivity",
        "Topology.CWComplex.cellular_homology",
        "Topology.CWComplex.attaching_map_continuous",
    ];

    for name in &constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_cw_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_cw().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_connected());
    assert!(env.has_topology_contractible());
    assert!(env.has_eq());
}

// ============================================================
// Topology.SimplicialComplex tests
// ============================================================

#[test]
fn test_topology_simplicial_complex_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_simplicial_complex());
    env.init_topology_simplicial_complex().unwrap();
    assert!(env.has_topology_simplicial_complex());
}

#[test]
fn test_topology_simplicial_complex_idempotent() {
    let mut env = Environment::new();
    env.init_topology_simplicial_complex().unwrap();
    env.init_topology_simplicial_complex().unwrap();
    assert!(env.has_topology_simplicial_complex());
}

#[test]
fn test_topology_simplicial_complex_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_simplicial_complex().unwrap();

    for s in [
        "Topology.SimplicialComplex",
        "Topology.SimplicialComplex.simplex",
        "Topology.SimplicialComplex.face",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_simplicial_complex_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_simplicial_complex().unwrap();

    let constants = [
        "Topology.SimplicialComplex",
        "Topology.SimplicialComplex.simplex",
        "Topology.SimplicialComplex.face",
        "Topology.SimplicialComplex.degeneracy",
        "Topology.SimplicialComplex.geometric_realization",
        "Topology.SimplicialComplex.realization_topology",
        "Topology.SimplicialComplex.realization_continuous",
        "Topology.SimplicialComplex.barycentric_subdivision",
        "Topology.SimplicialComplex.chain_complex",
        "Topology.SimplicialComplex.homology",
        "Topology.SimplicialComplex.cohomology",
        "Topology.SimplicialComplex.link",
        "Topology.SimplicialComplex.star",
        "Topology.SimplicialComplex.subcomplex",
        "Topology.SimplicialComplex.euler_characteristic",
        "Topology.SimplicialComplex.realization_to_cw",
    ];

    for name in &constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_simplicial_complex_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_simplicial_complex().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_homeomorphism());
    assert!(env.has_topology_cw());
    assert!(env.has_eq());
}

// ============================================================
// Topology.Homology tests
// ============================================================

#[test]
fn test_topology_homology_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_homology());
    env.init_topology_homology().unwrap();
    assert!(env.has_topology_homology());
}

#[test]
fn test_topology_homology_idempotent() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();
    env.init_topology_homology().unwrap();
    assert!(env.has_topology_homology());
}

#[test]
fn test_topology_homology_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.SingularChain",
        "Topology.Homology.H",
        "Topology.Homology.boundary",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_chain_complex_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.ChainComplex",
        "Topology.Homology.boundary_sq_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_group_structure_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.H_is_group",
        "Topology.Homology.induced",
        "Topology.Homology.functoriality",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_cohomology_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.Cohomology",
        "Topology.Homology.cup_product",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_exact_sequence_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.exact_sequence",
        "Topology.Homology.mayer_vietoris",
        "Topology.Homology.long_exact_pair",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_fundamental_theorems_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.homotopy_invariance",
        "Topology.Homology.excision",
        "Topology.Homology.dimension_axiom",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_hurewicz_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.hurewicz",
        "Topology.Homology.hurewicz_theorem",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_relative_and_betti_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    for s in [
        "Topology.Homology.relative",
        "Topology.Homology.betti",
        "Topology.Homology.euler_poincare",
        "Topology.Homology.H_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_homology_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    let constants = [
        "Topology.Homology.SingularChain",
        "Topology.Homology.ChainComplex",
        "Topology.Homology.boundary",
        "Topology.Homology.boundary_sq_zero",
        "Topology.Homology.H",
        "Topology.Homology.H_is_group",
        "Topology.Homology.induced",
        "Topology.Homology.functoriality",
        "Topology.Homology.Cohomology",
        "Topology.Homology.cup_product",
        "Topology.Homology.exact_sequence",
        "Topology.Homology.mayer_vietoris",
        "Topology.Homology.long_exact_pair",
        "Topology.Homology.homotopy_invariance",
        "Topology.Homology.excision",
        "Topology.Homology.dimension_axiom",
        "Topology.Homology.H_zero",
        "Topology.Homology.hurewicz",
        "Topology.Homology.hurewicz_theorem",
        "Topology.Homology.relative",
        "Topology.Homology.betti",
        "Topology.Homology.euler_poincare",
    ];

    for name in &constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_homology_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_homology().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_path_connected());
    assert!(env.has_topology_higher_homotopy());
    assert!(env.has_add_comm_group());
    assert!(env.has_ring());
    assert!(env.has_eq());
}

// ================================================================
// Topology.DeRham tests
// ================================================================

#[test]
fn test_topology_derham_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_derham());
    env.init_topology_derham().unwrap();
    assert!(env.has_topology_derham());
}

#[test]
fn test_topology_derham_idempotent() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();
    env.init_topology_derham().unwrap(); // Should not error
    assert!(env.has_topology_derham());
}

#[test]
fn test_topology_derham_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    // Core types
    for s in [
        "Topology.DeRham.SmoothManifold",
        "Topology.DeRham.DifferentialForm",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_exterior_derivative_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.exterior_derivative",
        "Topology.DeRham.d_squared_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_wedge_product_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.wedge",
        "Topology.DeRham.wedge_anticommutative",
        "Topology.DeRham.leibniz_rule",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_closed_exact_forms_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.ClosedForm",
        "Topology.DeRham.ExactForm",
        "Topology.DeRham.exact_is_closed",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_cohomology_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.H",
        "Topology.DeRham.H_is_add_comm_group",
        "Topology.DeRham.derham_theorem",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_poincare_and_stokes_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.poincare_lemma",
        "Topology.DeRham.integrate",
        "Topology.DeRham.stokes_theorem",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_pullback_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.pullback",
        "Topology.DeRham.pullback_commutes_d",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_hodge_theory_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in [
        "Topology.DeRham.HodgeStar",
        "Topology.DeRham.hodge_involution",
        "Topology.DeRham.codifferential",
        "Topology.DeRham.Laplacian",
        "Topology.DeRham.HarmonicForm",
        "Topology.DeRham.hodge_decomposition",
        "Topology.DeRham.harmonic_rep",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_betti_mayer_vietoris_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    for s in ["Topology.DeRham.betti", "Topology.DeRham.mayer_vietoris"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_topology_derham_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    let constants = [
        "Topology.DeRham.SmoothManifold",
        "Topology.DeRham.DifferentialForm",
        "Topology.DeRham.exterior_derivative",
        "Topology.DeRham.d_squared_zero",
        "Topology.DeRham.wedge",
        "Topology.DeRham.wedge_anticommutative",
        "Topology.DeRham.leibniz_rule",
        "Topology.DeRham.ClosedForm",
        "Topology.DeRham.ExactForm",
        "Topology.DeRham.exact_is_closed",
        "Topology.DeRham.H",
        "Topology.DeRham.H_is_add_comm_group",
        "Topology.DeRham.derham_theorem",
        "Topology.DeRham.poincare_lemma",
        "Topology.DeRham.integrate",
        "Topology.DeRham.stokes_theorem",
        "Topology.DeRham.pullback",
        "Topology.DeRham.pullback_commutes_d",
        "Topology.DeRham.HodgeStar",
        "Topology.DeRham.hodge_involution",
        "Topology.DeRham.codifferential",
        "Topology.DeRham.Laplacian",
        "Topology.DeRham.HarmonicForm",
        "Topology.DeRham.hodge_decomposition",
        "Topology.DeRham.harmonic_rep",
        "Topology.DeRham.betti",
        "Topology.DeRham.mayer_vietoris",
    ];

    for name in &constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_topology_derham_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_derham().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_homology());
    assert!(env.has_topology_contractible());
    assert!(env.has_eq());
    assert!(env.has_add_comm_group());
}

// ============================================================
// Topology.Morse tests
// ============================================================
