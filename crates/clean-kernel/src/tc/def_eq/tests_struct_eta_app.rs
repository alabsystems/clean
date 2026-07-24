// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the App-vs-App struct-eta fallback in `is_def_eq_structural`.
//!
//! When both sides of a def-eq check are `App` expressions and direct
//! component-wise comparison fails, clean must fall through to
//! `try_structure_eta_expansion` (matching Lean 4 type_checker.cpp:1117-1124).
//! Without this fallback, expressions like `(f x) =?= S.mk (f x).0 (f x).1`
//! would incorrectly return false.
//!
//! Part of #3134

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Build a simple non-parametric structure with `n` fields of type `field_ty`.
fn build_simple_struct(
    env: &mut Environment,
    name: &str,
    num_fields: u32,
    field_ty: Expr,
    result_sort: Expr,
) {
    let struct_name = Name::from_string(name);
    let ctor_name = Name::from_string(&format!("{name}.mk"));

    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, field_ty.clone(), ctor_type);
    }

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name,
            type_: result_sort,
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    })
    .expect("add_inductive");
}

/// Build `S.mk (Proj_0 e) (Proj_1 e) ... (Proj_n e)` for a zero-param struct.
fn build_eta_expanded(struct_name: &Name, ctor_name: &Name, num_fields: u32, e: &Expr) -> Expr {
    let mut result = Expr::const_(ctor_name.clone(), vec![]);
    for i in 0..num_fields {
        result = Expr::app(result, Expr::proj(struct_name.clone(), i, e.clone()));
    }
    result
}

// =========================================================================
// Core test: App-vs-App where direct comparison fails but struct-eta works
// =========================================================================

/// When comparing `(f x)` (an App) vs `S.mk (f x).0 (f x).1` (also an App),
/// the direct App comparison (f1==f2 && a1==a2) fails because the function
/// heads differ (f vs S.mk applied to a projection). The struct-eta fallback
/// must fire to prove these equal.
#[test]
fn test_app_vs_struct_eta_expanded_app() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Pt", 2, nat.clone(), Expr::type_());

    let pt_name = Name::from_string("Pt");
    let pt_ty = Expr::const_(pt_name.clone(), vec![]);

    // Declare f : Nat -> Pt and x : Nat
    let f_ty = Expr::pi(BinderInfo::Default, nat.clone(), pt_ty.clone());

    let tc = TypeChecker::new(&env);
    let f_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("f"), f_ty, BinderInfo::Default);
    let f = Expr::fvar(f_id);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat, BinderInfo::Default);
    let x = Expr::fvar(x_id);

    // lhs = f x (an App expression of type Pt)
    let lhs = Expr::app(f.clone(), x.clone());

    // rhs = Pt.mk (Proj_0 (f x)) (Proj_1 (f x)) -- struct-eta expansion of (f x)
    let rhs = build_eta_expanded(&pt_name, &Name::from_string("Pt.mk"), 2, &lhs);

    // Both lhs and rhs are App expressions. Direct App comparison fails because
    // lhs = App(f, x) while rhs = App(App(Pt.mk, Proj_0(fx)), Proj_1(fx)).
    // The struct-eta fallback should handle this.
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "f x =?= Pt.mk (f x).0 (f x).1 via struct-eta fallback on App-vs-App"
    );
    assert!(
        tc.is_def_eq(&rhs, &lhs),
        "symmetric: Pt.mk (f x).0 (f x).1 =?= f x"
    );
}

/// Single-field variant of the App-vs-App struct-eta fallback.
#[test]
fn test_app_vs_struct_eta_single_field() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Wrap", 1, nat.clone(), Expr::type_());

    let wrap_name = Name::from_string("Wrap");
    let wrap_ty = Expr::const_(wrap_name.clone(), vec![]);
    let f_ty = Expr::pi(BinderInfo::Default, nat.clone(), wrap_ty);

    let tc = TypeChecker::new(&env);
    let f_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("g"), f_ty, BinderInfo::Default);
    let f = Expr::fvar(f_id);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("y"), nat, BinderInfo::Default);
    let x = Expr::fvar(x_id);

    let lhs = Expr::app(f.clone(), x.clone());
    let rhs = build_eta_expanded(&wrap_name, &Name::from_string("Wrap.mk"), 1, &lhs);

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "g y =?= Wrap.mk (g y).0 via single-field struct-eta on App-vs-App"
    );
    assert!(tc.is_def_eq(&rhs, &lhs), "symmetric");
}

// =========================================================================
// Negative case: App-vs-App with non-structure type returns false
// =========================================================================

/// When the App result type is not structure-like (e.g., Nat, which is
/// recursive), the struct-eta fallback correctly returns false.
#[test]
fn test_app_vs_app_no_struct_eta_for_non_structure() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let f_ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());

    let tc = TypeChecker::new(&env);
    let f_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("f"), f_ty.clone(), BinderInfo::Default);
    let f = Expr::fvar(f_id);
    let g_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("g"), f_ty, BinderInfo::Default);
    let g = Expr::fvar(g_id);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat, BinderInfo::Default);
    let x = Expr::fvar(x_id);

    // f x vs g x — both App, different function heads, Nat result type (not structure)
    let lhs = Expr::app(f, x.clone());
    let rhs = Expr::app(g, x);

    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "f x =/= g x when result type is Nat (non-structure)"
    );
}

// =========================================================================
// Nested App: struct-eta on nested function application
// =========================================================================

/// Nested function application: `h (f x)` vs eta-expanded version, where
/// the outer App comparison must also exercise the fallback.
#[test]
fn test_app_vs_struct_eta_nested_app() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "S2", 2, nat.clone(), Expr::type_());

    let s2_name = Name::from_string("S2");
    let s2_ty = Expr::const_(s2_name.clone(), vec![]);

    // h : S2 -> S2, f : Nat -> S2, x : Nat
    let h_ty = Expr::pi(BinderInfo::Default, s2_ty.clone(), s2_ty.clone());
    let f_ty = Expr::pi(BinderInfo::Default, nat.clone(), s2_ty);

    let tc = TypeChecker::new(&env);
    let h_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("h"), h_ty, BinderInfo::Default);
    let h = Expr::fvar(h_id);
    let f_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("f"), f_ty, BinderInfo::Default);
    let f = Expr::fvar(f_id);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat, BinderInfo::Default);
    let x = Expr::fvar(x_id);

    // lhs = h (f x) -- type S2
    let lhs = Expr::app(h.clone(), Expr::app(f.clone(), x.clone()));

    // rhs = S2.mk (Proj_0 (h (f x))) (Proj_1 (h (f x)))
    let rhs = build_eta_expanded(&s2_name, &Name::from_string("S2.mk"), 2, &lhs);

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "h (f x) =?= S2.mk (h (f x)).0 (h (f x)).1 via struct-eta"
    );
    assert!(tc.is_def_eq(&rhs, &lhs), "symmetric");
}
