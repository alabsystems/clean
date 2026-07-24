// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::inductive_to_dt::{translate_inductive_to_dt, InductiveDTSpec};
use crate::smtlib_builder::SmtLibExpr;
use clean_kernel::{level::Level, name::Name, Environment, Expr};

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn app_ty(name: &str, arg: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        arg,
    )
}

fn option_nat_ty() -> Expr {
    app_ty("Option", nat_ty())
}

fn list_nat_ty() -> Expr {
    app_ty("List", nat_ty())
}

fn expr_text(exprs: Vec<SmtLibExpr>) -> Vec<String> {
    exprs.into_iter().map(|expr| expr.to_smtlib2()).collect()
}

fn recognizer_text(spec: &InductiveDTSpec) -> Vec<String> {
    spec.dt_constructor_recognizers()
        .into_iter()
        .map(|pred| pred.declaration().to_smtlib2())
        .collect()
}

fn accessor_text(spec: &InductiveDTSpec) -> Vec<String> {
    spec.dt_accessor_functions()
        .into_iter()
        .map(|acc| acc.declaration().to_smtlib2())
        .collect()
}

#[test]
fn test_option_nat_dt_spec_adds_testers_accessors_and_injectivity() {
    let mut env = Environment::new();
    env.init_option().expect("Option must initialize");
    let spec = translate_inductive_to_dt(&env, &option_nat_ty()).expect("Option Nat encoding");

    assert_eq!(spec.sort_name, "Option_Int");
    assert_eq!(
        spec.declaration_smtlib(),
        "(declare-datatype Option_Int ((Option_Int_none) (Option_Int_some (Option_Int_some_field0 Int))))"
    );
    assert_eq!(
        recognizer_text(&spec),
        vec![
            "(declare-fun is_Option_Int_none (Option_Int) Bool)".to_string(),
            "(declare-fun is_Option_Int_some (Option_Int) Bool)".to_string(),
        ]
    );
    assert_eq!(
        accessor_text(&spec),
        vec!["(declare-fun Option_Int_some_field0 (Option_Int) Int)".to_string()]
    );
    assert_eq!(
        spec.dt_accessor_functions()
            .into_iter()
            .map(|acc| acc.recursive)
            .collect::<Vec<_>>(),
        vec![false]
    );
    assert!(spec.dt_acyclicity_axiom().is_none());
    assert_eq!(
        expr_text(spec.clash_axioms()),
        vec!["(forall ((y0 Int)) (not (= Option_Int_none (Option_Int_some y0))))".to_string()]
    );
    assert_eq!(
        expr_text(spec.dt_injectivity_axioms()),
        vec![
            "(forall ((x0 Int) (y0 Int)) (=> (= (Option_Int_some x0) (Option_Int_some y0)) (= x0 y0)))"
                .to_string()
        ]
    );
    assert_eq!(
        expr_text(spec.selector_axioms()),
        vec![
            "(forall ((x0 Int)) (= (Option_Int_some_field0 (Option_Int_some x0)) x0))".to_string()
        ]
    );
}

#[test]
fn test_list_nat_dt_spec_marks_recursive_fields_and_adds_acyclicity() {
    let mut env = Environment::new();
    env.init_list().expect("List must initialize");
    let spec = translate_inductive_to_dt(&env, &list_nat_ty()).expect("List Nat encoding");

    assert_eq!(spec.sort_name, "List_Int");
    assert_eq!(
        recognizer_text(&spec),
        vec![
            "(declare-fun is_List_Int_nil (List_Int) Bool)".to_string(),
            "(declare-fun is_List_Int_cons (List_Int) Bool)".to_string(),
        ]
    );
    assert_eq!(
        accessor_text(&spec),
        vec![
            "(declare-fun List_Int_cons_field0 (List_Int) Int)".to_string(),
            "(declare-fun List_Int_cons_field1 (List_Int) List_Int)".to_string(),
        ]
    );
    assert_eq!(
        spec.dt_accessor_functions()
            .into_iter()
            .map(|acc| acc.recursive)
            .collect::<Vec<_>>(),
        vec![false, true]
    );

    let acyclicity = spec
        .dt_acyclicity_axiom()
        .expect("recursive list should produce a rank axiom");
    assert_eq!(
        acyclicity.rank_declaration.to_smtlib2(),
        "(declare-fun List_Int_dt_rank (List_Int) Int)"
    );
    assert_eq!(
        acyclicity.axiom.to_smtlib2(),
        "(forall ((x0 Int) (x1 List_Int)) (< (List_Int_dt_rank (List_Int_cons_field1 (List_Int_cons x0 x1))) (List_Int_dt_rank (List_Int_cons x0 x1))))"
    );
    assert_eq!(
        expr_text(spec.dt_injectivity_axioms()),
        vec![
            "(forall ((x0 Int) (x1 List_Int) (y0 Int) (y1 List_Int)) (=> (= (List_Int_cons x0 x1) (List_Int_cons y0 y1)) (and (= x0 y0) (= x1 y1))))"
                .to_string()
        ]
    );
}
