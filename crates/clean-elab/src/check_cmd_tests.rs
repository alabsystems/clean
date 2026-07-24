// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the enhanced `#check` command.

use super::*;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

#[test]
fn test_check_sort_prop() {
    let env = Environment::new();
    // Prop = Sort(0); type should be Type = Sort(1)
    let prop = Expr::sort(Level::zero());
    let result = check_expression(&prop, &env).expect("should check Prop");
    assert!(!result.display.is_empty());
    assert!(
        result.display.contains(':'),
        "display should contain colon: {}",
        result.display
    );
}

#[test]
fn test_check_sort_type() {
    let env = Environment::new();
    // Type 0 = Sort(1); type should be Sort(2)
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let result = check_expression(&type0, &env).expect("should check Type");
    assert!(!result.display.is_empty());
}

#[test]
fn test_check_nat_literal() {
    let env = Environment::new();
    let nat_42 = Expr::nat_lit(42u64);
    let result = check_expression(&nat_42, &env).expect("should check nat literal");
    // Nat literal should have type Nat
    assert!(
        result.display.contains(':'),
        "display should show type: {}",
        result.display
    );
}

#[test]
fn test_check_invalid_expr() {
    let env = Environment::new();
    let bad = Expr::const_(Name::from_string("nonexistent"), vec![]);
    let err = check_expression(&bad, &env);
    assert!(err.is_err(), "should fail for unknown constant");
}

#[test]
fn test_check_name_axiom() {
    let mut env = Environment::new();
    let decl = Declaration::Axiom {
        name: Name::from_string("myAxiom"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    };
    env.add_decl(decl).expect("should register axiom");

    let result = check_name("myAxiom", &env).expect("should find axiom");
    assert!(
        result.display.contains("myAxiom"),
        "display should contain name: {}",
        result.display
    );
    assert!(
        result.display.contains(':'),
        "display should show type: {}",
        result.display
    );
}

#[test]
fn test_check_name_with_universe_params() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let decl = Declaration::Axiom {
        name: Name::from_string("myPoly"),
        level_params: vec![u],
        type_: Expr::sort(Level::param(Name::from_string("u"))),
    };
    env.add_decl(decl)
        .expect("should register polymorphic axiom");

    let result = check_name("myPoly", &env).expect("should find polymorphic axiom");
    assert!(
        result.display.contains(".{"),
        "display should show universe params: {}",
        result.display
    );
    assert!(
        result.display.contains("u"),
        "display should contain universe name: {}",
        result.display
    );
}

#[test]
fn test_check_name_unknown() {
    let env = Environment::new();
    let err = check_name("nonexistent.name", &env);
    assert!(err.is_err(), "should fail for unknown name");
    match err {
        Err(ElabError::UnknownIdent(name)) => {
            assert_eq!(name, "nonexistent.name");
        }
        other => panic!("expected UnknownIdent, got {other:?}"),
    }
}

#[test]
fn test_check_result_display() {
    let cr = CheckResult {
        elaborated: Expr::sort(Level::zero()),
        type_: Expr::sort(Level::succ(Level::zero())),
        display: "Prop : Type".into(),
    };
    assert_eq!(format!("{cr}"), "Prop : Type");
}
