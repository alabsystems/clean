// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Expr};

use super::{check_defeq_spec, check_type_spec, DefeqAlgorithm, TypeCheckStep};
use crate::test_utils::build_spec_with_stack;

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}

fn nat_succ() -> Expr {
    Expr::const_str("Nat.succ")
}

fn beta_eta_nat() -> Expr {
    Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        nat(),
    )
}

#[test]
fn test_check_defeq_spec_structural_is_syntax_directed() {
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
        nat_zero(),
    );

    assert!(!check_defeq_spec(
        &redex,
        &nat_zero(),
        DefeqAlgorithm::StructuralEquality,
    ));
}

#[test]
fn test_check_defeq_spec_alpha_accepts_identical_binder_structure() {
    let lambda = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0));

    assert!(check_defeq_spec(
        &lambda,
        &lambda,
        DefeqAlgorithm::AlphaEquivalence,
    ));
}

#[test]
fn test_check_defeq_spec_beta_eta_reduces_beta_redex() {
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
        nat_zero(),
    );

    assert!(check_defeq_spec(
        &redex,
        &nat_zero(),
        DefeqAlgorithm::BetaEtaEquivalence,
    ));
}

#[test]
fn test_check_type_spec_sort_rule() {
    let spec = build_spec_with_stack();
    let witness = check_type_spec(spec.env(), &[], &Expr::prop(), &Expr::type_())
        .expect("sort should type-check");

    assert_eq!(witness.step, TypeCheckStep::Sort);
    assert!(witness.premises.is_empty());
}

#[test]
fn test_check_type_spec_bvar_rule() {
    let spec = build_spec_with_stack();
    let witness = check_type_spec(spec.env(), &[nat()], &Expr::bvar(0), &nat())
        .expect("bound variable should type-check");

    assert_eq!(witness.step, TypeCheckStep::BoundVariable);
    assert!(witness.premises.is_empty());
}

#[test]
fn test_check_type_spec_const_rule() {
    let spec = build_spec_with_stack();
    let witness =
        check_type_spec(spec.env(), &[], &nat_zero(), &nat()).expect("constant should type-check");

    assert_eq!(witness.step, TypeCheckStep::Constant);
    assert!(witness.premises.is_empty());
}

#[test]
fn test_check_type_spec_app_rule() {
    let spec = build_spec_with_stack();
    let expr = Expr::app(nat_succ(), nat_zero());
    let witness =
        check_type_spec(spec.env(), &[], &expr, &nat()).expect("application should type-check");

    assert_eq!(witness.step, TypeCheckStep::Application);
    assert_eq!(witness.premises.len(), 2);
    assert_eq!(witness.premises[0].step, TypeCheckStep::Constant);
    assert_eq!(witness.premises[1].step, TypeCheckStep::Constant);
}

#[test]
fn test_check_type_spec_lam_rule() {
    let spec = build_spec_with_stack();
    let expr = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0));
    let witness = check_type_spec(spec.env(), &[], &expr, &Expr::arrow(nat(), nat()))
        .expect("lambda should type-check");

    assert_eq!(witness.step, TypeCheckStep::Lambda);
    assert_eq!(witness.premises.len(), 2);
    assert_eq!(witness.premises[0].step, TypeCheckStep::Constant);
    assert_eq!(witness.premises[1].step, TypeCheckStep::BoundVariable);
}

#[test]
fn test_check_type_spec_pi_rule() {
    let spec = build_spec_with_stack();
    let expr = Expr::arrow(nat(), nat());
    let witness =
        check_type_spec(spec.env(), &[], &expr, &Expr::type_()).expect("pi should type-check");

    assert_eq!(witness.step, TypeCheckStep::Pi);
    assert_eq!(witness.premises.len(), 2);
    assert_eq!(witness.premises[0].step, TypeCheckStep::Constant);
    assert_eq!(witness.premises[1].step, TypeCheckStep::Constant);
}

#[test]
fn test_check_type_spec_conversion_rule() {
    let spec = build_spec_with_stack();
    let witness = check_type_spec(spec.env(), &[], &nat_zero(), &beta_eta_nat())
        .expect("conversion should type-check");

    assert_eq!(witness.step, TypeCheckStep::Conversion);
    assert_eq!(witness.premises.len(), 1);
    assert_eq!(witness.premises[0].step, TypeCheckStep::Constant);
    assert_eq!(witness.expected_type, beta_eta_nat());
}
