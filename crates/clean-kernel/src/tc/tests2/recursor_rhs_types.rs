// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #2170: recursor rule RHS actual domain types
//! and recOn infer_implicit post-processing.

use super::support::make_nat_env;
use super::*;

/// Extract lambda domain types from a lambda chain.
fn collect_lambda_domains(mut expr: &Expr) -> Vec<Expr> {
    let mut domains = Vec::new();
    while let ExprKind::Lam(_, domain, body) = &expr.kind {
        domains.push((**domain).clone());
        expr = body.as_ref();
    }
    domains
}

/// Create a List inductive environment (1 param α, 2 ctors: nil, cons).
fn make_list_env() -> Environment {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::level::Level;
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let list = Name::from_string("List");
    // Type u (= Sort (succ u)), matching Lean's `List : Type u → Type u` [R1]:
    // a Sort-u former is not provably nonzero and would be Prop-only-eliminating.
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
    let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    let nil_type = Expr::pi(BinderInfo::Default, type_u.clone(), list_a.clone());
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(BinderInfo::Default, type_u, cons_body);
    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list,
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("List add_inductive");
    env
}

/// #2170 F1: Nat.rec rule RHS has actual domain types, not Sort(0).
#[test]
fn test_nat_rec_rhs_domains_not_dummy() {
    let env = make_nat_env();
    let rec = env
        .get_recursor(&Name::from_string("Nat.rec"))
        .expect("Nat.rec");

    // Zero: λ motive. λ minor_zero. λ minor_succ. minor_zero
    let zero_doms = collect_lambda_domains(&rec.rules[0].rhs);
    assert_eq!(zero_doms.len(), 3);
    // Motive domain = Pi (Nat → Sort u)
    assert!(
        matches!(&zero_doms[0].kind, ExprKind::Pi(_, _, _)),
        "motive domain should be Pi, got {:?}",
        zero_doms[0].kind
    );
    // Minor domains are not Sort(0)
    for d in &zero_doms[1..] {
        assert!(
            !matches!(&d.kind, ExprKind::Sort(lvl) if *lvl == Level::zero()),
            "minor domain should not be Sort(0)"
        );
    }

    // Succ: λ motive. λ minor_zero. λ minor_succ. λ (n : Nat). body
    let succ_doms = collect_lambda_domains(&rec.rules[1].rhs);
    assert_eq!(succ_doms.len(), 4);
    assert!(
        matches!(&succ_doms[3].kind, ExprKind::Const(n, _) if n == &Name::from_string("Nat")),
        "field domain should be Const(Nat), got {:?}",
        succ_doms[3].kind
    );
}

/// #2170 F1: casesOn and recOn also use actual domain types.
#[test]
fn test_cases_on_rec_on_rhs_domains_not_dummy() {
    let env = make_nat_env();
    for name in ["Nat.casesOn", "Nat.recOn"] {
        let val = env
            .get_recursor(&Name::from_string(name))
            .expect("recursor should exist");
        let succ_doms = collect_lambda_domains(&val.rules[1].rhs);
        assert_eq!(succ_doms.len(), 4, "{name} succ rule should have 4 lambdas");
        assert!(
            matches!(&succ_doms[3].kind, ExprKind::Const(n, _) if n == &Name::from_string("Nat")),
            "{name} field domain should be Const(Nat), got {:?}",
            succ_doms[3].kind
        );
    }
}

/// #2170 F1: List.cons rule RHS field domains reference the type parameter.
#[test]
fn test_list_cons_rhs_field_types() {
    let env = make_list_env();
    let rec = env
        .get_recursor(&Name::from_string("List.rec"))
        .expect("List.rec");

    // cons: λ α. λ motive. λ minor_nil. λ minor_cons. λ head. λ tail. body
    let doms = collect_lambda_domains(&rec.rules[1].rhs);
    assert_eq!(doms.len(), 6, "cons RHS: 1p + 1m + 2min + 2f");

    // head : α → BVar ref to param (not Sort(0))
    assert!(
        matches!(&doms[4].kind, ExprKind::BVar(_)),
        "head domain should be BVar (ref α), got {:?}",
        doms[4].kind
    );
    // tail : List α → App (not Sort(0))
    assert!(
        matches!(&doms[5].kind, ExprKind::App(_, _)),
        "tail domain should be App (List α), got {:?}",
        doms[5].kind
    );
}

/// #2170 F2: List.recOn type has infer_implicit (α is Implicit).
#[test]
fn test_list_rec_on_infer_implicit() {
    let env = make_list_env();
    let rec_on = env
        .get_recursor(&Name::from_string("List.recOn"))
        .expect("List.recOn");
    let rec = env
        .get_recursor(&Name::from_string("List.rec"))
        .expect("List.rec");

    // Extract binder infos
    let rec_on_bis = recursor::collect_binder_infos(&rec_on.type_);
    let rec_bis = recursor::collect_binder_infos(&rec.type_);

    assert!(rec_on_bis.len() >= 2, "recOn needs ≥2 binders");
    // α should be Implicit (infer_implicit marks it because it appears in domains)
    assert_eq!(
        rec_on_bis[0],
        BinderInfo::Implicit,
        "α should be Implicit in recOn type"
    );
    assert_eq!(
        rec_on_bis[1],
        BinderInfo::Implicit,
        "motive should be Implicit in recOn type"
    );
    // rec and recOn agree on first 2 binder infos
    assert_eq!(rec_bis[0], rec_on_bis[0], "rec/recOn α binder info match");
    assert_eq!(
        rec_bis[1], rec_on_bis[1],
        "rec/recOn motive binder info match"
    );
}
