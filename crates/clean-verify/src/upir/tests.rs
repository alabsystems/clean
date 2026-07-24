// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    BinderStyle, LeanTranslationError, MatchStyle, SourceSystem, UpirBinder, UpirExpr,
    UpirForeignExpr, UpirLevel, UpirLiteral, UpirMatchArm, UpirName, UpirPattern, UpirProof,
    UpirSort, UpirValidationError,
};
use clean_kernel::Environment;
use clean_parser::{parse_decl, parse_expr};

fn type0() -> UpirExpr {
    UpirExpr::Sort(UpirSort::Type(UpirLevel::Zero))
}

fn explicit(name: &str) -> UpirBinder {
    UpirBinder {
        name: Some(name.to_string()),
        style: BinderStyle::Explicit,
    }
}

fn const_(name: &str) -> UpirExpr {
    UpirExpr::Const {
        name: UpirName::from_dotted(name),
        universes: vec![],
        source: SourceSystem::Clean,
    }
}

fn identity_expr() -> UpirExpr {
    UpirExpr::Lambda {
        binder: explicit("A"),
        domain: Box::new(type0()),
        body: Box::new(UpirExpr::Lambda {
            binder: explicit("x"),
            domain: Box::new(UpirExpr::Var(0)),
            body: Box::new(UpirExpr::Var(0)),
        }),
    }
}

#[test]
fn validate_rejects_unbound_var() {
    let err = UpirExpr::Var(0)
        .validate()
        .expect_err("Var 0 should be unbound");
    assert_eq!(err, UpirValidationError::UnboundVar { index: 0, depth: 0 });
}

#[test]
fn validate_rejects_duplicate_universe_params() {
    let proof = UpirProof::new(
        UpirName::from_dotted("Imported.id"),
        SourceSystem::Coq,
        vec!["u".to_string(), "u".to_string()],
        None,
        identity_expr(),
    );

    let err = proof
        .validate()
        .expect_err("duplicate universe params should fail");
    assert_eq!(
        err,
        UpirValidationError::DuplicateUniverseParam("u".to_string())
    );
}

#[test]
fn validate_rejects_duplicate_pattern_binders() {
    let expr = UpirExpr::Lambda {
        binder: explicit("n"),
        domain: Box::new(const_("Nat")),
        body: Box::new(UpirExpr::Match {
            scrutinee: Box::new(UpirExpr::Var(0)),
            motive: None,
            arms: vec![UpirMatchArm {
                pattern: UpirPattern::Ctor {
                    name: UpirName::from_dotted("Nat.succ"),
                    args: vec![
                        UpirPattern::Var(Some("k".to_string())),
                        UpirPattern::Var(Some("k".to_string())),
                    ],
                },
                body: Box::new(UpirExpr::Var(0)),
            }],
            style: MatchStyle::Pattern,
        }),
    };

    let err = expr
        .validate()
        .expect_err("duplicate pattern binders should fail");
    assert_eq!(
        err,
        UpirValidationError::DuplicatePatternBinder("k".to_string())
    );
}

#[test]
fn lean_translation_renders_identity_and_elaborates() {
    let expr = identity_expr();
    let source = expr.to_lean_source().expect("identity should render");
    assert_eq!(source, "fun (A : Type) => fun (x : A) => x");
    parse_expr(&source).expect("rendered identity should parse");

    let env = Environment::new();
    let _ = expr
        .elaborate_in(&env)
        .expect("rendered identity should elaborate");
}

#[test]
fn lean_translation_renders_match_with_pattern_bindings() {
    let expr = UpirExpr::Lambda {
        binder: explicit("n"),
        domain: Box::new(const_("Nat")),
        body: Box::new(UpirExpr::Match {
            scrutinee: Box::new(UpirExpr::Var(0)),
            motive: None,
            arms: vec![
                UpirMatchArm {
                    pattern: UpirPattern::Ctor {
                        name: UpirName::from_dotted("Nat.zero"),
                        args: vec![],
                    },
                    body: Box::new(UpirExpr::Literal(UpirLiteral::Nat(0))),
                },
                UpirMatchArm {
                    pattern: UpirPattern::Ctor {
                        name: UpirName::from_dotted("Nat.succ"),
                        args: vec![UpirPattern::Var(Some("k".to_string()))],
                    },
                    body: Box::new(UpirExpr::Var(0)),
                },
            ],
            style: MatchStyle::Pattern,
        }),
    };

    let source = expr.to_lean_source().expect("match should render");
    assert_eq!(
        source,
        "fun (n : Nat) => match n with | Nat.zero => 0 | Nat.succ k => k"
    );
    parse_expr(&source).expect("rendered match should parse");
}

#[test]
fn lean_translation_escapes_keyword_segments() {
    let expr = const_("Foo.match");
    let source = expr.to_lean_source().expect("escaped const should render");
    assert_eq!(source, "Foo.«match»");
    parse_expr(&source).expect("escaped const should parse");
}

#[test]
fn lean_translation_rejects_foreign_constructs() {
    let expr = UpirExpr::Foreign(UpirForeignExpr::MetamathExpr {
        symbols: vec!["wff".to_string(), "ph".to_string()],
    });

    let err = expr
        .to_lean_source()
        .expect_err("foreign constructs should be rejected");
    assert_eq!(
        err,
        LeanTranslationError::ForeignExpr("Metamath expression `wff ph`".to_string())
    );
}

#[test]
fn lean_theorem_declaration_renders_and_parses() {
    let statement = UpirExpr::Pi {
        binder: explicit("A"),
        domain: Box::new(type0()),
        body: Box::new(UpirExpr::Pi {
            binder: explicit("x"),
            domain: Box::new(UpirExpr::Var(0)),
            body: Box::new(UpirExpr::Var(1)),
        }),
    };
    let proof = identity_expr();
    let theorem = UpirProof::new(
        UpirName::from_dotted("Imported.match"),
        SourceSystem::Lean4,
        vec![],
        Some(statement),
        proof,
    );

    let source = theorem
        .to_lean_declaration()
        .expect("theorem should render");
    assert_eq!(
        source,
        "theorem Imported.«match» : forall (A : Type), forall (x : A), A := fun (A : Type) => fun (x : A) => x"
    );
    parse_decl(&source).expect("rendered theorem should parse");
}

#[test]
fn proof_validation_rejects_holes() {
    let proof = UpirProof::new(
        UpirName::from_dotted("Imported.hole"),
        SourceSystem::Agda,
        vec![],
        Some(type0()),
        UpirExpr::Hole {
            id: 7,
            type_: Some(Box::new(type0())),
        },
    );

    let err = proof.validate().expect_err("holes should be rejected");
    assert_eq!(err, UpirValidationError::HoleNotAllowed(7));
}
