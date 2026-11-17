// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Causal source controls for Lean's class outParam dependency restriction.
//! This complete file is retained unchanged on the test-only baseline and fix.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

const MEASURED: &str = include_str!(
    "../../../reports/false-accept-refresh-2026-11-12/fixtures/elab_fail/classBadOutParam.lean"
);

fn check(env: &mut Environment, context: &mut FileContext, source: &str) -> Result<(), ElabError> {
    fn failure(result: &ElabResult) -> Option<ElabError> {
        match result {
            ElabResult::Failed { error, .. } => Some(error.as_ref().clone()),
            ElabResult::Multiple(results) => results.iter().find_map(failure),
            _ => None,
        }
    }
    for decl in parse_file(source).expect("control source must parse") {
        let decl = preprocess_decl_with_context(&decl, context);
        let result = elaborate_decl_and_register_with_context(env, &decl, context)?;
        if let Some(error) = failure(&result) {
            return Err(error);
        }
    }
    Ok(())
}

fn accept(env: &mut Environment, context: &mut FileContext, source: &str) {
    check(env, context, source).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

fn refuse(
    env: &mut Environment,
    context: &mut FileContext,
    source: &str,
    name: &str,
    index: usize,
) {
    let error = check(env, context, source).expect_err("a regular parameter depends on an output");
    assert_eq!(
        error.to_string(),
        format!(
            "invalid class, parameter #{index} depends on `outParam`, but it is not an `outParam`"
        )
    );
    let name = Name::from_string(name);
    assert!(
        env.get_const(&name).is_none(),
        "invalid class is not published"
    );
    assert!(env.get_inductive(&name).is_none());
    assert!(!env.is_class(&name));
    assert!(env.get_constructor(&name.str("mk")).is_none());
}

fn metadata(env: &Environment, name: &str, outputs: &[usize], semis: &[usize]) {
    let info = env
        .get_class_info(&Name::from_string(name))
        .expect("valid class metadata must be registered");
    assert_eq!(info.out_params, outputs);
    assert_eq!(info.semi_out_params, semis);
}

#[test]
fn measured_original_c1_refuses_parameter_two_before_publication() {
    refuse(
        &mut Environment::with_prelude(),
        &mut FileContext::new(),
        MEASURED,
        "C1",
        2,
    );
}

#[test]
fn measured_original_c2_with_an_output_dependent_parameter_remains_valid() {
    // Elaborate the original fixture's second declaration without changing its
    // binders/assertions or allowing the intentionally invalid C1 to stop it.
    let mut decls = parse_file(MEASURED).expect("unchanged measured source parses");
    assert_eq!(decls.len(), 2);
    let good = decls.pop().expect("the original C2 declaration");
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let good = preprocess_decl_with_context(&good, &mut context);
    elaborate_decl_and_register_with_context(&mut env, &good, &mut context)
        .expect("original C2 remains valid");
    metadata(&env, "C2", &[0, 1], &[]);
    assert_eq!(
        env.get_class_info(&Name::from_string("C2"))
            .unwrap()
            .num_params,
        3
    );
}

#[test]
fn ordinary_dependent_parameter_is_refused() {
    refuse(
        &mut Environment::with_prelude(),
        &mut FileContext::new(),
        "class Bad (α : outParam Type) (x : α) where\n  val : Nat\n",
        "Bad",
        2,
    );
}

#[test]
fn implicit_regular_parameter_is_not_promoted_like_an_instance() {
    refuse(
        &mut Environment::with_prelude(),
        &mut FileContext::new(),
        "class Bad (α : outParam Type) {x : α} where\n  val : Nat\n",
        "Bad",
        2,
    );
}

#[test]
fn independent_input_after_output_remains_valid() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "class Good (α : outParam Type) (n : Nat) where\n  val : α\n",
    );
    metadata(&env, "Good", &[0], &[]);
}

#[test]
fn explicit_output_dependency_chain_remains_valid() {
    let mut env = Environment::with_prelude();
    accept(&mut env, &mut FileContext::new(),
        "class Good (α : outParam Type) (x : outParam α) (h : outParam (x = x)) where\n  val : Nat\n");
    metadata(&env, "Good", &[0, 1, 2], &[]);
}

#[test]
fn regular_parameter_after_an_output_chain_is_refused() {
    refuse(
        &mut Environment::with_prelude(),
        &mut FileContext::new(),
        "class Bad (α : outParam Type) (x : outParam α) (h : x = x) where\n  val : Nat\n",
        "Bad",
        3,
    );
}

#[test]
fn semi_output_does_not_create_the_full_output_restriction() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "class Good (α : semiOutParam Type) (x : α) where\n  val : Nat\n",
    );
    metadata(&env, "Good", &[], &[0]);
}

#[test]
fn semi_output_cannot_hide_a_dependency_on_a_full_output() {
    refuse(
        &mut Environment::with_prelude(),
        &mut FileContext::new(),
        "class Bad (α : outParam Type) (x : semiOutParam α) where\n  val : Nat\n",
        "Bad",
        2,
    );
}

const CARRIER: &str = "class Carrier (n : Nat) where\n  val : Nat\n";

#[test]
fn dependent_instance_parameter_is_promoted_to_an_output() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(&mut env, &mut context, CARRIER);
    accept(
        &mut env,
        &mut context,
        "class Good (n : outParam Nat) [inst : Carrier n] where\n  val : Nat\n",
    );
    metadata(&env, "Good", &[0, 1], &[]);
}

#[test]
fn regular_dependency_after_a_promoted_instance_is_refused() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(&mut env, &mut context, CARRIER);
    refuse(&mut env, &mut context,
        "class Bad (n : outParam Nat) [inst : Carrier n] (h : inst.val = inst.val) where\n  val : Nat\n", "Bad", 3);
}

#[test]
fn refused_namespaced_class_does_not_poison_a_valid_retry() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    refuse(
        &mut env,
        &mut context,
        "namespace Local\nclass Retry (α : outParam Type) (x : α) where\n  val : α\nend Local\n",
        "Local.Retry",
        2,
    );
    accept(
        &mut env,
        &mut context,
        // Each parser call owns a namespace block. Retry the same qualified
        // name in a new, independently balanced block after the refusal.
        "namespace Local\nclass Retry (α : outParam Type) (x : outParam α) where\n  val : α\nend Local\n",
    );
    metadata(&env, "Local.Retry", &[0, 1], &[]);
}

#[test]
fn valid_output_class_has_a_checked_useful_instance() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "class Value (α : outParam Type) (x : outParam α) where\n  val : α\n\
         instance valueNat : Value Nat 3 := ⟨7⟩\n\
         def readValue [v : Value Nat 3] : Nat := v.val\n\
         theorem selected : readValue = 7 := rfl\n",
    );
    metadata(&env, "Value", &[0, 1], &[]);
    assert!(env.is_instance(&Name::from_string("valueNat")));
    assert!(env
        .axiom_deps(&Name::from_string("selected"))
        .expect("checked theorem")
        .is_empty());
}

#[test]
fn local_outparam_name_is_an_input_not_a_global_marker() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "class LocalShadow (outParam : Type → Type) (x : outParam Nat) (h : x = x) where\n  val : Nat\n",
    );
    metadata(&env, "LocalShadow", &[], &[]);
    assert_eq!(
        env.get_class_info(&Name::from_string("LocalShadow"))
            .unwrap()
            .num_params,
        3
    );
}

#[test]
fn namespace_outparam_name_is_an_input_not_a_global_marker() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "universe u\nnamespace Shadow\ndef outParam (α : Sort u) : Sort u := α\nclass C (α : outParam Type) (x : α) where\n  val : Nat\nend Shadow\n",
    );
    metadata(&env, "Shadow.C", &[], &[]);
    assert_eq!(
        env.get_class_info(&Name::from_string("Shadow.C"))
            .unwrap()
            .num_params,
        2
    );
}
