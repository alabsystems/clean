// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the enhanced `#print` command.

use super::*;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

#[test]
fn test_print_axiom_signature() {
    let mut env = Environment::new();
    let decl = Declaration::Axiom {
        name: Name::from_string("myAxiom"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    };
    env.add_decl(decl).expect("should register axiom");

    let result = print_declaration("myAxiom", &env).expect("should find axiom");
    assert_eq!(result.kind, DeclKind::Axiom);
    assert!(
        result.signature.contains("myAxiom"),
        "signature should contain name: {}",
        result.signature
    );
    assert!(result.body.is_none(), "axiom should have no body");
}

#[test]
fn test_print_definition_with_body() {
    let mut env = Environment::new();
    // def myDef : Type := Prop
    let decl = Declaration::Definition {
        name: Name::from_string("myDef"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())), // Type
        value: Expr::sort(Level::zero()),              // Prop
        is_reducible: true,
    };
    env.add_decl(decl).expect("should register definition");

    let result = print_declaration("myDef", &env).expect("should find definition");
    assert_eq!(result.kind, DeclKind::Definition);
    assert!(result.body.is_some(), "definition should have body");
    assert!(
        result.attributes.iter().any(|a| a.contains("reducible")),
        "should note reducibility: {:?}",
        result.attributes
    );
}

#[test]
fn test_print_theorem() {
    let mut env = Environment::new();
    // Register axiom `myProp : Prop` and axiom `myProof : myProp`.
    // Then theorem myThm : myProp := myProof is well-typed.
    let ax_prop = Declaration::Axiom {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // myProp : Prop
    };
    env.add_decl(ax_prop).expect("should register myProp axiom");

    let my_prop = Expr::const_(Name::from_string("myProp"), vec![]);
    let ax_proof = Declaration::Axiom {
        name: Name::from_string("myProof"),
        level_params: vec![],
        type_: my_prop.clone(), // myProof : myProp
    };
    env.add_decl(ax_proof)
        .expect("should register myProof axiom");

    let my_proof = Expr::const_(Name::from_string("myProof"), vec![]);
    let decl = Declaration::Theorem {
        name: Name::from_string("myThm"),
        level_params: vec![],
        type_: my_prop,  // myProp : Prop
        value: my_proof, // myProof : myProp
    };
    env.add_decl(decl).expect("should register theorem");

    let result = print_declaration("myThm", &env).expect("should find theorem");
    assert_eq!(result.kind, DeclKind::Theorem);
    assert!(result.body.is_some(), "theorem should have proof term");
}

#[test]
fn test_print_unknown_name() {
    let env = Environment::new();
    let err = print_declaration("nonexistent.name", &env);
    assert!(err.is_err(), "should fail for unknown name");
    match err {
        Err(ElabError::UnknownIdent(name)) => {
            assert_eq!(name, "nonexistent.name");
        }
        other => panic!("expected UnknownIdent, got {other:?}"),
    }
}

#[test]
fn test_print_with_universe_params() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let decl = Declaration::Axiom {
        name: Name::from_string("myPoly"),
        level_params: vec![u],
        type_: Expr::sort(Level::param(Name::from_string("u"))),
    };
    env.add_decl(decl)
        .expect("should register polymorphic axiom");

    let result = print_declaration("myPoly", &env).expect("should find");
    assert!(
        result.signature.contains(".{"),
        "signature should show universe params: {}",
        result.signature
    );
}

#[test]
fn test_print_result_display_def() {
    let pr = PrintResult {
        kind: DeclKind::Definition,
        signature: "myDef : Nat".into(),
        body: Some("0".into()),
        attributes: vec!["reducible".into()],
    };
    let display = format!("{pr}");
    assert!(display.contains("def myDef : Nat"));
    assert!(display.contains(":="));
    assert!(display.contains("0"));
    assert!(display.contains("-- reducible"));
}

#[test]
fn test_print_result_display_axiom() {
    let pr = PrintResult {
        kind: DeclKind::Axiom,
        signature: "myAxiom : Prop".into(),
        body: None,
        attributes: vec![],
    };
    let display = format!("{pr}");
    assert_eq!(display, "axiom myAxiom : Prop");
}

#[test]
fn test_decl_kind_display() {
    assert_eq!(format!("{}", DeclKind::Definition), "def");
    assert_eq!(format!("{}", DeclKind::Theorem), "theorem");
    assert_eq!(format!("{}", DeclKind::Axiom), "axiom");
    assert_eq!(format!("{}", DeclKind::Opaque), "opaque");
    assert_eq!(format!("{}", DeclKind::Inductive), "inductive");
    assert_eq!(format!("{}", DeclKind::Constructor), "constructor");
    assert_eq!(format!("{}", DeclKind::Recursor), "recursor");
}
