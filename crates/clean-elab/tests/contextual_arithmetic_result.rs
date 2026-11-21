// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Context chooses polymorphic arithmetic carriers before arithmetic evaluates.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};

const FACTORY: &str = "def reviewFactory (n : Nat) : {α : Type} → α → α := fun {α} x => x\n";
const PICK: &str = "def reviewPick {α : Type} [Min α] (x y : α) : α := min x y\n";

fn elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    for declaration in clean_parser::parse_file(source).map_err(|e| e.to_string())? {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &declaration, &mut context)
            .map_err(|e| e.to_string())?;
        fn failures(result: &ElabResult) -> Result<(), String> {
            match result {
                ElabResult::Failed { error, .. } => Err(error.to_string()),
                ElabResult::Multiple(results) => results.iter().try_for_each(failures),
                _ => Ok(()),
            }
        }
        failures(&result)?;
    }
    Ok(env)
}

fn assert_computation(setup: &str, definition: &str, value: &str, false_value: &str) {
    let prefix = format!("{setup}{definition}\n");
    elaborate(&prefix).unwrap_or_else(|e| panic!("valid setup failed: {e}\n{prefix}"));
    let source = format!("{prefix}theorem correct : reviewValue = {value} := by rfl\n");
    let env = elaborate(&source).unwrap_or_else(|e| panic!("{e}\n{source}"));
    let name = Name::from_string("correct");
    let info = env.get_const(&name).expect("theorem registered");
    let proof = info.value.as_ref().expect("theorem has a value");
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .expect("proof independently type-checks");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());
    let false_source =
        format!("{prefix}theorem incorrect : reviewValue = {false_value} := by rfl\n");
    elaborate(&false_source).expect_err("the false computation must be refused after valid setup");
}

#[test]
fn declared_result_pins_an_ordinary_returned_function_carrier() {
    assert_computation(
        FACTORY,
        "def reviewValue : Int := reviewFactory 0 (1 - 7)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn declared_result_pins_a_named_prefix_returned_function_carrier() {
    assert_computation(
        FACTORY,
        "def reviewValue : Int := reviewFactory (n := 0) (1 - 7)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn ascribed_result_pins_a_named_prefix_returned_function_carrier() {
    assert_computation(
        FACTORY,
        "def reviewValue := (reviewFactory (n := 0) (1 - 7) : Int)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn declared_result_pins_fully_named_arithmetic() {
    assert_computation(
        PICK,
        "def reviewValue : Int := reviewPick (x := 1 - 7) (y := 9)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn ascribed_result_pins_fully_named_arithmetic() {
    assert_computation(
        PICK,
        "def reviewValue := (reviewPick (x := 1 - 7) (y := 9) : Int)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn reordered_named_arguments_keep_the_expected_carrier() {
    assert_computation(
        PICK,
        "def reviewValue : Int := reviewPick (y := 9) (x := 1 - 7)",
        "(-6 : Int)",
        "0",
    );
}

#[test]
fn an_explicit_nat_carrier_keeps_its_valid_result_coercion() {
    assert_computation(
        PICK,
        "def reviewValue : Int := reviewPick (α := Nat) (x := 1 - 7) (y := 9)",
        "0",
        "(-6 : Int)",
    );
}

#[test]
fn a_fixed_nat_domain_keeps_its_valid_result_coercion() {
    assert_computation(
        "def reviewNat (n : Nat) : Nat := n\n",
        "def reviewValue : Int := reviewNat (1 - 7)",
        "0",
        "(-6 : Int)",
    );
}
