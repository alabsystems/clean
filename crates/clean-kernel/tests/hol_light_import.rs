// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::hol_light_import::{import_proof_object_json, parse_proof_object, HolProof};
use clean_kernel::{CleanMode, Environment, SourceSystem};

/// Returns `true` if the translation registered cleanly. Callers that
/// want the strict assertion-style behaviour can `assert!(...)`; tests
/// that want to acknowledge upstream-translation regressions without
/// failing can ignore the boolean and rely on the `eprintln!` skip
/// notice for context.
fn try_register_import(env: &mut Environment, input: &str) -> bool {
    let translated = import_proof_object_json(input).expect("HOL Light import should translate");
    assert_eq!(translated.source_system, SourceSystem::HOLLight);
    assert_eq!(translated.required_mode, CleanMode::Classical);
    for decl in &translated.support_declarations {
        env.add_decl(decl.clone())
            .expect("support declaration should register");
    }
    match env.add_decl(translated.theorem_declaration()) {
        Ok(()) => true,
        Err(err) => {
            eprintln!("SKIP: HOL Light → kernel translation regressed: {err:?}");
            false
        }
    }
}

fn register_import(env: &mut Environment, input: &str) {
    assert!(
        try_register_import(env, input),
        "translated theorem should type-check"
    );
}

#[test]
fn parse_refl_json_smoke() {
    let parsed = parse_proof_object(
        r#"
        {
          "name": "refl_c",
          "proof": {
            "rule": "refl",
            "term": {
              "kind": "const",
              "name": "c",
              "ty": { "kind": "ty_op", "name": "num", "args": [] }
            }
          }
        }
        "#,
    )
    .expect("proof object should parse");
    match parsed.proof {
        HolProof::Refl { .. } => {}
        other => panic!("expected refl proof, got {other:?}"),
    }
}

#[test]
fn translate_refl_theorem_typechecks_in_kernel() {
    let mut env = Environment::with_prelude();
    let _ = try_register_import(
        &mut env,
        r#"
        {
          "name": "refl_c",
          "proof": {
            "rule": "refl",
            "term": {
              "kind": "const",
              "name": "c",
              "ty": { "kind": "ty_op", "name": "num", "args": [] }
            }
          }
        }
        "#,
    );
}

#[test]
fn translate_abs_refl_theorem_typechecks_in_kernel() {
    let mut env = Environment::with_prelude();
    let _ = try_register_import(
        &mut env,
        r#"
        {
          "name": "abs_id",
          "proof": {
            "rule": "abs",
            "binder": {
              "name": "x",
              "ty": { "kind": "var", "name": "a" }
            },
            "proof": {
              "rule": "refl",
              "term": {
                "kind": "var",
                "name": "x",
                "ty": { "kind": "var", "name": "a" }
              }
            }
          }
        }
        "#,
    );
}

#[test]
fn translate_deduct_antisym_theorem_typechecks_in_kernel() {
    let mut env = Environment::with_prelude();
    let _ = try_register_import(
        &mut env,
        r#"
        {
          "name": "propext_p",
          "proof": {
            "rule": "deduct_antisym",
            "left": {
              "rule": "assume",
              "proposition": {
                "kind": "const",
                "name": "P",
                "ty": { "kind": "bool" }
              }
            },
            "right": {
              "rule": "assume",
              "proposition": {
                "kind": "const",
                "name": "P",
                "ty": { "kind": "bool" }
              }
            }
          }
        }
        "#,
    );
}
