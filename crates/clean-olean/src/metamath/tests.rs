// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    parse_database, parse_database_file, resolve_database, translate_database, Formula, Proof,
    ResolvedStatement, Statement,
};
use clean_kernel::{Declaration, Expr, ExprKind, Literal};
use tempfile::TempDir;

fn sample_syntax_db() -> &'static str {
    r#"
      $c wff -> ( ) $. 
      $v ph ps $. 
      wph $f wff ph $. 
      wps $f wff ps $. 
      wi $a wff ( ph -> ps ) $. 
      impSelf $p wff ( ph -> ph ) $= ( wi ) AAB $. 
      impNest $p wff ( ( ph -> ph ) -> ( ph -> ph ) ) $= ( wi ) AABZCB $.
    "#
}

#[test]
fn metamath_parse_basic_database() {
    let db = parse_database(sample_syntax_db()).expect("parse database");
    assert_eq!(db.statements.len(), 7);
    match &db.statements[4] {
        Statement::Axiom { label, formula } => {
            assert_eq!(label, "wi");
            assert_eq!(
                formula,
                &Formula {
                    typecode: "wff".to_string(),
                    tokens: vec![
                        "(".to_string(),
                        "ph".to_string(),
                        "->".to_string(),
                        "ps".to_string(),
                        ")".to_string()
                    ],
                }
            );
        }
        other => panic!("expected axiom, got {other:?}"),
    }
}

#[test]
fn metamath_parse_include_file() {
    let dir = TempDir::new().expect("tempdir");
    let inc = dir.path().join("inc.mm");
    let main = dir.path().join("main.mm");
    std::fs::write(&inc, "wph $f wff ph $.").unwrap();
    std::fs::write(
        &main,
        "$c wff $. $v ph $. $[ inc.mm $] th $p wff ph $= wph $.",
    )
    .unwrap();
    let db = parse_database_file(&main).expect("parse file");
    assert_eq!(db.statements.len(), 4);
}

#[test]
fn metamath_resolve_frames() {
    let db = parse_database(
        r#"
        $c wff |- $. 
        $v ph $. 
        wph $f wff ph $. 
        hph $e |- ph $. 
        id $a |- ph $. 
        th $p |- ph $= wph hph id $.
    "#,
    )
    .expect("parse");
    let resolved = resolve_database(&db).expect("resolve");
    let assertion = match resolved.get("id").expect("id") {
        ResolvedStatement::Assertion(assertion) => assertion,
        other => panic!("expected assertion, got {other:?}"),
    };
    assert_eq!(assertion.mandatory_floats.len(), 1);
    assert_eq!(assertion.essential_hyps.len(), 1);
}

#[test]
fn metamath_translate_compressed_proof() {
    let decls =
        translate_database(&parse_database(sample_syntax_db()).expect("parse")).expect("translate");
    let imp_self = decls
        .iter()
        .find(|decl| decl_name(decl) == "Metamath.impSelf")
        .expect("impSelf decl");
    let Declaration::Opaque { type_, value, .. } = imp_self else {
        panic!("expected opaque declaration");
    };
    assert_eq!(head_name(type_), Some("Metamath.Assertion.mk".to_string()));
    assert_eq!(head_name(value), Some("Metamath.Proof.apply".to_string()));
    let args = cloned_args(value);
    assert_eq!(expr_string(&args[0]).as_deref(), Some("wi"));
}

#[test]
fn metamath_translate_saved_step_proof() {
    let decls =
        translate_database(&parse_database(sample_syntax_db()).expect("parse")).expect("translate");
    let imp_nest = decls
        .iter()
        .find(|decl| decl_name(decl) == "Metamath.impNest")
        .expect("impNest decl");
    let Declaration::Opaque { value, .. } = imp_nest else {
        panic!("expected opaque declaration");
    };
    let args = cloned_args(value);
    assert_eq!(expr_string(&args[0]).as_deref(), Some("wi"));
}

#[test]
fn metamath_rejects_distinct_variable_violation() {
    let db = parse_database(
        r#"
        $c term combine $. 
        $v x y $. 
        vx $f term x $. 
        vy $f term y $. 
        $d x y $. 
        pair $a term combine x y $. 
        bad $p term combine x x $= vx vx pair $.
    "#,
    )
    .expect("parse");
    let err = translate_database(&db).expect_err("expected translation failure");
    let msg = err.to_string();
    assert!(msg.contains("distinct-variable"));
}

fn decl_name(decl: &Declaration) -> String {
    match decl {
        Declaration::Definition { name, .. }
        | Declaration::Axiom { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name.to_string(),
    }
}

fn head_name(expr: &Expr) -> Option<String> {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn cloned_args(expr: &Expr) -> Vec<Expr> {
    expr.get_app_args().into_iter().map(Clone::clone).collect()
}

fn expr_string(expr: &Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Lit(Literal::String(value)) => Some(value.to_string()),
        _ => None,
    }
}

#[test]
fn metamath_parse_uncompressed_proof() {
    let db = parse_database(
        r#"
        $c wff $. 
        $v ph $. 
        wph $f wff ph $. 
        id $p wff ph $= wph $.
    "#,
    )
    .expect("parse");
    let Statement::Provable { proof, .. } = &db.statements[3] else {
        panic!("expected provable statement");
    };
    assert_eq!(proof, &Proof::Uncompressed(vec!["wph".to_string()]));
}

#[test]
fn metamath_compressed_proof_numeric_overflow_is_rejected() {
    // Regression: a compressed proof whose numeric code is a long run of
    // 'U'..='Y' digits used to overflow the base-5 accumulator in
    // decode_compressed (translate.rs), aborting the process under
    // overflow-checks. 28 consecutive 'Y' chars overflow usize::MAX.
    // After the checked_mul/checked_add fix, this returns a structured
    // InvalidCompressedProof error instead of panicking.
    let ys = "Y".repeat(28);
    let src = format!(
        r#"
        $c wff $. 
        $v ph $. 
        wph $f wff ph $. 
        id $p wff ph $= ( wph ) {ys}A $.
    "#,
    );
    let db = parse_database(&src).expect("parse");
    let err = translate_database(&db).expect_err("expected overflow to be rejected, not panic");
    assert!(
        err.to_string().contains("overflow"),
        "unexpected error: {err}"
    );
}
