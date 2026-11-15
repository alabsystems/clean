// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-registered computation checks for nested Nat literal patterns.
//! A count of generated casesOn nodes cannot detect substituting zero for four.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

fn computation(env: &mut Environment, call: &str, expected: &str, wrong: &str, id: usize) {
    let good = format!("correct{id}");
    register(env, &format!("theorem {good} : {call} = {expected} := rfl"))
        .unwrap_or_else(|error| panic!("{call} = {expected}: {error}"));
    let deps = env
        .axiom_deps(&Name::from_string(&good))
        .expect("registered theorem");
    assert!(
        deps.is_empty(),
        "computation proof depends on axioms: {deps:?}"
    );
    let bad = format!("incorrect{id}");
    let error = register(env, &format!("theorem {bad} : {call} = {wrong} := rfl"))
        .expect_err("the opposite computational result must be rejected");
    assert!(
        !error.contains("parse error"),
        "negative must parse: {error}"
    );
    assert!(
        !error.to_lowercase().contains("sorryax"),
        "no sorry fallback: {error}"
    );
    assert!(
        env.get_const(&Name::from_string(&bad)).is_none(),
        "false theorem registered"
    );
}

#[test]
fn nested_literal_matches_exact_value_and_rejects_the_original_false_theorem() {
    let mut env = Environment::with_prelude();
    // A single concrete arm reaches the nested planner directly; two some
    // arms can select the already-correct constructor-column splitter instead.
    register(
        &mut env,
        "def isSome4 : Option Nat → Bool\n  | some 4 => true\n  | _ => false",
    )
    .unwrap();
    for (id, (call, expected, wrong)) in [
        ("isSome4 (some 4)", "true", "false"),
        ("isSome4 (some 0)", "false", "true"),
        ("isSome4 (some 3)", "false", "true"),
        ("isSome4 (some 5)", "false", "true"),
        ("isSome4 none", "false", "true"),
    ]
    .into_iter()
    .enumerate()
    {
        computation(&mut env, call, expected, wrong, id);
    }
}

#[test]
fn multilevel_literals_and_numeral_add_keep_their_values() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def deep : Option (Option Nat) → Nat
  | some (some 4) => 7
  | _ => 0
def offset : Option Nat → Nat
  | some (n + 2) => n
  | _ => 99
"#,
    )
    .unwrap();
    for (id, (call, expected, wrong)) in [
        ("deep (some (some 4))", "7", "0"),
        ("deep (some (some 0))", "0", "7"),
        ("deep (some (some 3))", "0", "7"),
        ("deep (some (some 5))", "0", "7"),
        ("deep (some none)", "0", "7"),
        ("offset (some 5)", "3", "4"),
        ("offset (some 2)", "0", "99"),
        ("offset (some 1)", "99", "0"),
        ("offset (some 0)", "99", "0"),
    ]
    .into_iter()
    .enumerate()
    {
        computation(&mut env, call, expected, wrong, id);
    }
}

#[test]
fn nested_if_let_and_alias_patterns_match_the_same_literal() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def conditional (x : Option Nat) : Nat := if let some 4 := x then 7 else 0
def aliased : Option Nat → Nat
  | some (n@4) => n
  | _ => 99
"#,
    )
    .unwrap();
    for (id, (call, expected, wrong)) in [
        ("conditional (some 4)", "7", "0"),
        ("conditional (some 0)", "0", "7"),
        ("conditional (some 5)", "0", "7"),
        ("aliased (some 4)", "4", "99"),
        ("aliased (some 0)", "99", "0"),
        ("aliased (some 5)", "99", "5"),
    ]
    .into_iter()
    .enumerate()
    {
        computation(&mut env, call, expected, wrong, id);
    }
}

#[test]
fn literals_above_sixty_four_preserve_existing_literal_capability() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "def larger : Option Nat → Bool\n  | some 65 => true\n  | _ => false",
    )
    .unwrap();
    computation(&mut env, "larger (some 65)", "true", "false", 0);
    computation(&mut env, "larger (some 64)", "false", "true", 1);
    computation(&mut env, "larger (some 66)", "false", "true", 2);
}
