// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regressions for multi-limb `BitVec.ofNat`/`BitVec.toNat`.
//!
//! These declarations run the same parse → elaborate → kernel-register path as
//! `clean check`. In particular, the first theorem forces `BitVec.ofNat` to
//! pre-WHNF an `Int.toNat (Int.ofNat ...)` operand and forces the elaborator to
//! keep the reduced BitVec payload inside kernel def-eq rather than storing the
//! bare `Nat` literal as a `BitVec`-typed metavariable solution.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_context = FileContext::new();
    let declarations = parse_file(source).map_err(|error| format!("parse error: {error}"))?;
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut file_context);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        collect_failures(&result)?;
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult) -> Result<(), String> {
    match result {
        ElabResult::Multiple(results) => {
            for result in results {
                collect_failures(result)?;
            }
            Ok(())
        }
        ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
        _ => Ok(()),
    }
}

fn assert_axiom_free(env: &Environment, theorem: &str) {
    let dependencies = env
        .axiom_deps(&Name::from_string(theorem))
        .unwrap_or_else(|| panic!("{theorem} must be registered"));
    assert!(
        dependencies.is_empty(),
        "{theorem} must be proved by computation, got {dependencies:?}"
    );
}

#[test]
fn composite_multilimb_operand_wraps_and_registers_by_rfl() {
    // (2^128 - 2^63) mod 2^64 = 2^63. The left operand is deliberately not a
    // literal: the scoped BitVec.ofNat operand pre-WHNF is load-bearing here.
    let source = "theorem bitvec_pipeline :\n\
        BitVec.ofNat 64 (Int.toNat (Int.ofNat 340282366920938463454151235394913435648)) =\n\
        BitVec.ofNat 64 9223372036854775808 := rfl";
    let env = elaborate_module(source).expect("the multi-limb composite pipeline must register");
    assert_axiom_free(&env, "bitvec_pipeline");
}

#[test]
fn tonat_preserves_a_two_limb_payload_by_rfl() {
    let source = "theorem bitvec_tonat_multilimb :\n\
        BitVec.toNat (BitVec.ofNat 128 170141183460469231731687303715884105728) =\n\
        170141183460469231731687303715884105728 := rfl";
    let env = elaborate_module(source).expect("BitVec.toNat must preserve the two-limb payload");
    assert_axiom_free(&env, "bitvec_tonat_multilimb");
}

#[test]
fn adjacent_false_multilimb_result_is_rejected() {
    let source = "theorem bitvec_pipeline_bad :\n\
        BitVec.ofNat 64 (Int.toNat (Int.ofNat 340282366920938463454151235394913435648)) =\n\
        BitVec.ofNat 64 9223372036854775809 := rfl";
    let error = elaborate_module(source)
        .expect_err("an adjacent but unequal wrapped payload must fail kernel registration");
    assert!(
        !error.to_lowercase().contains("sorryax"),
        "the false control must fail honestly, not through sorryAx: {error}"
    );
}
