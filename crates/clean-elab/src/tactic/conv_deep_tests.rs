// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for deep conv-mode targeted rewriting (#3082)

use clean_kernel::{BinderInfo, Expr};

use super::conv::ConvPosition;
use super::conv_deep::{mk_app2, mk_app3, mk_eq_app, DeepConvState};
use super::TacticError;

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}
fn mk_var(name: &str) -> Expr {
    Expr::const_str(name)
}
fn mk_eq(lhs: Expr, rhs: Expr) -> Expr {
    mk_eq_app(nat_ty(), lhs, rhs)
}
fn mk_lam_nat(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat_ty(), body)
}
fn mk_pi_nat(body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat_ty(), body)
}
fn mk_proof() -> Expr {
    Expr::const_str("proof_placeholder")
}

// Construction

#[test]
fn test_deep_conv_new_from_equality() {
    let goal = mk_eq(mk_var("a"), mk_var("b"));
    let dcs = DeepConvState::new(&goal).expect("should create from equality");
    assert_eq!(dcs.depth(), 0);
    assert!(dcs.rewrites().is_empty());
    assert!(dcs.ext_vars().is_empty());
    assert_eq!(*dcs.current_expr(), goal);
}

#[test]
fn test_deep_conv_new_non_equality_fails() {
    assert!(DeepConvState::new(&mk_var("x")).is_err());
}

#[test]
fn test_deep_conv_new_unchecked() {
    let expr = mk_var("anything");
    let dcs = DeepConvState::new_unchecked(expr.clone());
    assert_eq!(dcs.depth(), 0);
    assert_eq!(*dcs.current_expr(), expr);
}

// LHS/RHS navigation

#[test]
fn test_deep_conv_enter_lhs() {
    let a = mk_var("a");
    let mut dcs = DeepConvState::new(&mk_eq(a.clone(), mk_var("b"))).unwrap();
    dcs.enter_lhs().expect("should navigate to LHS");
    assert_eq!(dcs.depth(), 1);
    assert_eq!(*dcs.current_expr(), a);
}

#[test]
fn test_deep_conv_enter_rhs() {
    let b = mk_var("b");
    let mut dcs = DeepConvState::new(&mk_eq(mk_var("a"), b.clone())).unwrap();
    dcs.enter_rhs().expect("should navigate to RHS");
    assert_eq!(dcs.depth(), 1);
    assert_eq!(*dcs.current_expr(), b);
}

#[test]
fn test_deep_conv_enter_lhs_on_non_equality_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.enter_lhs().is_err());
}

// Argument navigation

#[test]
fn test_deep_conv_enter_arg_binary_app() {
    let (f, a, b) = (mk_var("f"), mk_var("a"), mk_var("b"));
    let mut dcs = DeepConvState::new_unchecked(mk_app3(f, a.clone(), b));
    dcs.enter_arg(0).expect("should navigate to arg 0");
    assert_eq!(*dcs.current_expr(), a);
}

#[test]
fn test_deep_conv_enter_arg_last_arg() {
    let (f, a, b) = (mk_var("f"), mk_var("a"), mk_var("b"));
    let mut dcs = DeepConvState::new_unchecked(mk_app3(f, a, b.clone()));
    dcs.enter_arg(1).expect("should navigate to arg 1");
    assert_eq!(*dcs.current_expr(), b);
}

#[test]
fn test_deep_conv_enter_arg_single() {
    let (f, x) = (mk_var("f"), mk_var("x"));
    let mut dcs = DeepConvState::new_unchecked(mk_app2(f, x.clone()));
    dcs.enter_arg(0).expect("should navigate to arg 0");
    assert_eq!(*dcs.current_expr(), x);
}

#[test]
fn test_deep_conv_enter_arg_out_of_bounds() {
    let mut dcs = DeepConvState::new_unchecked(mk_app2(mk_var("f"), mk_var("x")));
    assert!(dcs.enter_arg(5).is_err());
}

#[test]
fn test_deep_conv_enter_arg_non_app_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.enter_arg(0).is_err());
}

// Function navigation

#[test]
fn test_deep_conv_enter_fun() {
    let f = mk_var("f");
    let mut dcs = DeepConvState::new_unchecked(mk_app2(f.clone(), mk_var("x")));
    dcs.enter_fun().expect("should navigate to function");
    assert_eq!(*dcs.current_expr(), f);
}

#[test]
fn test_deep_conv_enter_fun_non_app_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.enter_fun().is_err());
}

// Binder (ext) navigation

#[test]
fn test_deep_conv_ext_lambda() {
    let body = Expr::bvar(0);
    let mut dcs = DeepConvState::new_unchecked(mk_lam_nat(body.clone()));
    dcs.ext("x").expect("should enter lambda body");
    assert_eq!(dcs.depth(), 1);
    assert_eq!(*dcs.current_expr(), body);
    assert_eq!(dcs.ext_vars(), &["x"]);
}

#[test]
fn test_deep_conv_ext_pi() {
    let body = Expr::bvar(0);
    let mut dcs = DeepConvState::new_unchecked(mk_pi_nat(body.clone()));
    dcs.ext("x").expect("should enter pi body");
    assert_eq!(dcs.depth(), 1);
    assert_eq!(*dcs.current_expr(), body);
}

#[test]
fn test_deep_conv_ext_non_binder_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.ext("x").is_err());
}

// Rewrite tests

#[test]
fn test_deep_conv_apply_rewrite() {
    let (a, b, proof) = (mk_var("a"), mk_var("b"), mk_proof());
    let mut dcs = DeepConvState::new_unchecked(a.clone());
    dcs.apply_rewrite(b.clone(), proof.clone())
        .expect("should apply rewrite");
    assert_eq!(*dcs.current_expr(), b);
    assert_eq!(dcs.rewrites().len(), 1);
    assert_eq!(dcs.rewrites()[0].before, a);
    assert_eq!(dcs.rewrites()[0].after, b);
    assert_eq!(dcs.rewrites()[0].proof, proof);
}

#[test]
fn test_deep_conv_apply_rewrite_no_change_fails() {
    let a = mk_var("a");
    let mut dcs = DeepConvState::new_unchecked(a.clone());
    assert!(matches!(
        dcs.apply_rewrite(a, mk_proof()),
        Err(TacticError::NoProgress { .. })
    ));
}

#[test]
fn test_deep_conv_multiple_rewrites() {
    let (a, b, c) = (mk_var("a"), mk_var("b"), mk_var("c"));
    let mut dcs = DeepConvState::new_unchecked(a.clone());
    dcs.apply_rewrite(b.clone(), Expr::const_str("p1")).unwrap();
    dcs.apply_rewrite(c.clone(), Expr::const_str("p2")).unwrap();
    assert_eq!(dcs.rewrites().len(), 2);
    assert_eq!(dcs.rewrites()[0].before, a);
    assert_eq!(dcs.rewrites()[0].after, b);
    assert_eq!(dcs.rewrites()[1].before, b);
    assert_eq!(dcs.rewrites()[1].after, c);
    assert_eq!(*dcs.current_expr(), c);
}

// Close tests

#[test]
fn test_deep_conv_close_no_navigation() {
    let (a, b) = (mk_var("a"), mk_var("b"));
    let mut dcs = DeepConvState::new_unchecked(a);
    dcs.apply_rewrite(b.clone(), mk_proof()).unwrap();
    let (result, rewrites) = dcs.close();
    assert_eq!(result, b);
    assert_eq!(rewrites.len(), 1);
}

#[test]
fn test_deep_conv_close_with_navigation() {
    let (f, a, b) = (mk_var("f"), mk_var("a"), mk_var("b"));
    let mut dcs = DeepConvState::new_unchecked(mk_app2(f.clone(), a));
    dcs.enter_arg(0).unwrap();
    dcs.apply_rewrite(b.clone(), mk_proof()).unwrap();
    let (result, rewrites) = dcs.close();
    assert_eq!(result, mk_app2(f, b));
    assert_eq!(rewrites.len(), 1);
}

#[test]
fn test_deep_conv_close_no_rewrites() {
    let a = mk_var("a");
    let (result, rewrites) = DeepConvState::new_unchecked(a.clone()).close();
    assert_eq!(result, a);
    assert!(rewrites.is_empty());
}

// Position stack tracking

#[test]
fn test_deep_conv_position_stack_lhs_then_arg() {
    let (a, f) = (mk_var("a"), mk_var("f"));
    let goal = mk_eq(mk_app2(f.clone(), a.clone()), mk_var("b"));
    let mut dcs = DeepConvState::new(&goal).unwrap();
    assert_eq!(dcs.depth(), 0);

    dcs.enter_lhs().unwrap();
    assert_eq!(dcs.depth(), 1);
    assert_eq!(dcs.path(), &vec![ConvPosition::EqLhs]);
    assert_eq!(*dcs.current_expr(), mk_app2(f, a.clone()));

    dcs.enter_arg(0).unwrap();
    assert_eq!(dcs.depth(), 2);
    assert_eq!(*dcs.current_expr(), a);
}

#[test]
fn test_deep_conv_position_stack_rhs_then_fun() {
    let (a, g) = (mk_var("a"), mk_var("g"));
    let goal = mk_eq(a.clone(), mk_app2(g.clone(), a.clone()));
    let mut dcs = DeepConvState::new(&goal).unwrap();
    dcs.enter_rhs().unwrap();
    assert_eq!(*dcs.current_expr(), mk_app2(g.clone(), a));
    dcs.enter_fun().unwrap();
    assert_eq!(dcs.depth(), 2);
    assert_eq!(*dcs.current_expr(), g);
}

// Nested navigation and rewrite

#[test]
fn test_deep_conv_nested_lhs_arg_rewrite() {
    let (a, b, c, f) = (mk_var("a"), mk_var("b"), mk_var("c"), mk_var("f"));
    let goal = mk_eq(mk_app2(f.clone(), a.clone()), c.clone());
    let mut dcs = DeepConvState::new(&goal).unwrap();
    dcs.enter_lhs().unwrap();
    dcs.enter_arg(0).unwrap();
    assert_eq!(*dcs.current_expr(), a);
    dcs.apply_rewrite(b.clone(), mk_proof()).unwrap();
    let (result, rewrites) = dcs.close();
    assert_eq!(result, mk_eq(mk_app2(f, b), c));
    assert_eq!(rewrites.len(), 1);
}

#[test]
fn test_deep_conv_rewrite_inside_lambda() {
    let f = mk_var("f");
    let lam = mk_lam_nat(mk_app2(f.clone(), Expr::bvar(0)));
    let mut dcs = DeepConvState::new_unchecked(lam);
    dcs.ext("x").unwrap();
    dcs.enter_arg(0).unwrap();
    assert_eq!(*dcs.current_expr(), Expr::bvar(0));
    let y = mk_var("y");
    dcs.apply_rewrite(y.clone(), mk_proof()).unwrap();
    let (result, _) = dcs.close();
    assert_eq!(result, mk_lam_nat(mk_app2(f, y)));
}

// Binder type navigation

#[test]
fn test_deep_conv_enter_binder_type() {
    let mut dcs = DeepConvState::new_unchecked(mk_lam_nat(Expr::bvar(0)));
    dcs.enter_binder_type().expect("should enter binder type");
    assert_eq!(*dcs.current_expr(), nat_ty());
}

#[test]
fn test_deep_conv_enter_binder_type_non_binder_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.enter_binder_type().is_err());
}

// Let-binding navigation

#[test]
fn test_deep_conv_enter_let_value() {
    let a = mk_var("a");
    let let_expr = Expr::let_named(
        clean_kernel::Name::from_string("x"),
        nat_ty(),
        a.clone(),
        Expr::bvar(0),
        false,
    );
    let mut dcs = DeepConvState::new_unchecked(let_expr);
    dcs.enter_let_value().expect("should enter let value");
    assert_eq!(*dcs.current_expr(), a);
}

#[test]
fn test_deep_conv_enter_let_body() {
    let body = Expr::bvar(0);
    let let_expr = Expr::let_named(
        clean_kernel::Name::from_string("x"),
        nat_ty(),
        mk_var("a"),
        body.clone(),
        false,
    );
    let mut dcs = DeepConvState::new_unchecked(let_expr);
    dcs.enter_let_body().expect("should enter let body");
    assert_eq!(*dcs.current_expr(), body);
}

#[test]
fn test_deep_conv_enter_let_non_let_fails() {
    let mut dcs = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs.enter_let_value().is_err());
    let mut dcs2 = DeepConvState::new_unchecked(mk_var("x"));
    assert!(dcs2.enter_let_body().is_err());
}

// Preservation

#[test]
fn test_deep_conv_original_preserved_after_rewrite() {
    let a = mk_var("a");
    let mut dcs = DeepConvState::new_unchecked(a.clone());
    dcs.apply_rewrite(mk_var("b"), mk_proof()).unwrap();
    assert_eq!(*dcs.original(), a);
}

// Helper function structure

#[test]
fn test_mk_eq_app_structure() {
    let eq = mk_eq_app(nat_ty(), mk_var("a"), mk_var("b"));
    assert_eq!(eq.get_app_args().len(), 3);
}

#[test]
fn test_mk_app_structures() {
    assert_eq!(mk_app2(mk_var("f"), mk_var("x")).get_app_args().len(), 1);
    assert_eq!(
        mk_app3(mk_var("f"), mk_var("x"), mk_var("y"))
            .get_app_args()
            .len(),
        2
    );
}

// Edge cases: navigate beyond leaves

#[test]
fn test_deep_conv_navigate_leaf_fails() {
    let mut dcs1 = DeepConvState::new_unchecked(mk_var("leaf"));
    assert!(dcs1.enter_arg(0).is_err());
    let mut dcs2 = DeepConvState::new_unchecked(mk_var("leaf"));
    assert!(dcs2.enter_fun().is_err());
    let mut dcs3 = DeepConvState::new_unchecked(mk_var("leaf"));
    assert!(dcs3.ext("x").is_err());
}
