// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The source frontend must distinguish Lean's Euclidean Int notation from
//! explicit T-rounding heads, including after numeric tactic normalization.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elaborate(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|e| format!("parse: {e:?}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn assert_checked(env: &mut Environment, name: &str, proposition: &str, tactic: &str) {
    let source = format!("theorem {name} : {proposition} := by\n  {tactic}\n");
    elaborate(env, &source).unwrap_or_else(|e| panic!("{source}\n{e}"));
    assert!(env
        .axiom_deps(&Name::from_string(name))
        .expect("checked theorem")
        .is_empty());
}

#[test]
fn notation_and_explicit_heads_have_distinct_checked_semantics() {
    let mut env = Environment::with_prelude();
    for (index, proposition) in [
        "(-7 : Int) / 2 = -4",
        "(-1 : Int) % 256 = 255",
        "(-7 : Int) / (-2) = 4",
        "(7 : Int) / (-2) = -3",
        "(-6 : Int) % (-3) = 0",
        "(-7 : Int) % (-2) = 1",
        "(-7 : Int) / 0 = 0",
        "(-7 : Int) % 0 = -7",
        "(7 : Int) % 0 = 7",
        "(0 : Int) % 0 = 0",
        "Int.div (-7) 2 = -3",
        "Int.mod (-1) 256 = -1",
        "Int.div (-7) (-2) = 3",
        "Int.mod (-7) (-2) = -1",
        "Int.div (-7) 0 = 0",
        "Int.mod (-7) 0 = -7",
    ]
    .iter()
    .enumerate()
    {
        for tactic in ["rfl", "norm_num"] {
            assert_checked(
                &mut env,
                &format!("arithmetic_{index}_{tactic}"),
                proposition,
                tactic,
            );
        }
    }
}

#[test]
fn frontend_refuses_swapping_euclidean_and_truncating_results() {
    for proposition in [
        "(-7 : Int) / 2 = -3",
        "(-1 : Int) % 256 = -1",
        "Int.div (-7) 2 = -4",
        "Int.mod (-1) 256 = 255",
        "(-7 : Int) % 0 = 0",
    ] {
        for tactic in ["rfl", "norm_num"] {
            let mut env = Environment::with_prelude();
            let source = format!("theorem rejected : {proposition} := by\n  {tactic}\n");
            assert!(elaborate(&mut env, &source).is_err(), "accepted {source}");
            assert!(env.get_const(&Name::from_string("rejected")).is_none());
        }
    }
}

#[test]
fn custom_int_division_dictionaries_are_not_replaced_by_builtin_arithmetic() {
    for (class, projection, builtin_answer) in [("HDiv", "hDiv", "-4"), ("HMod", "hMod", "1")] {
        let expression = format!("@{class}.{projection} Int Int Int (@{class}.mk Int Int Int (fun _ _ => (42 : Int))) (-7) 2");
        for tactic in ["rfl", "norm_num"] {
            let mut env = Environment::with_prelude();
            assert_checked(&mut env, "custom", &format!("({expression}) = 42"), tactic);
            let source =
                format!("theorem rejected : ({expression}) = {builtin_answer} := by\n  {tactic}\n");
            assert!(elaborate(&mut env, &source).is_err(), "accepted {source}");
        }
    }
}
