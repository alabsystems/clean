// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual source use of canonical Nat modular identities, including zero modulus.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
theorem below_bound (a n : Nat) (h : a < n) : a % n = a := Nat.mod_eq_of_lt h
theorem repeated_modulus (a n : Nat) : (a % n) % n = a % n := Nat.mod_mod a n
theorem zero_modulus : (7 % 0) % 0 = 7 % 0 := Nat.mod_mod 7 0
theorem one_modulus (a : Nat) : (a % 1) % 1 = a % 1 := Nat.mod_mod a 1
";

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(xs) => xs.iter().any(failed),
        _ => false,
    }
}
fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut context = FileContext::new();
    for declaration in parse_file(source).map_err(|error| format!("{error:?}"))? {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        let result =
            elaborate_decl_and_register(env, &declaration).map_err(|error| error.to_string())?;
        if failed(&result) {
            return Err(format!("{result:?}"));
        }
    }
    Ok(())
}
fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    prepare_session_environment(&mut env);
    env
}

#[test]
fn actual_source_modular_identities_replay_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("canonical modular source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "below_bound",
        "repeated_modulus",
        "zero_modulus",
        "one_modulus",
    ] {
        let original = Name::from_string(name);
        let info = reference
            .environment()
            .get_const(&original)
            .expect("actual source theorem");
        assert!(info.level_params.is_empty());
        let type_ = info.type_.clone();
        let alias = Name::from_string(&format!("source_reference_{name}"));
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: vec![],
                type_,
                value: Expr::const_(original, vec![]),
            })
            .expect("replay actual source proof closure");
        assert!(reference
            .environment()
            .axiom_deps(&alias)
            .expect("closure")
            .is_empty());
    }
}

#[test]
fn source_refuses_a_changed_modular_result_with_the_original_proof() {
    for source in [
        "theorem bad_mod (a n : Nat) : (a % n) % n = Nat.succ (a % n) := Nat.mod_mod a n",
        "theorem bad_mod : 2 % 2 = 2 := Nat.mod_eq_of_lt (by decide)",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_mod")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}

#[test]
fn source_cannot_reverse_the_modulus_bound_hypothesis() {
    let mut env = environment();
    let before = (env.num_constants(), env.num_instances());
    let source = "theorem bad_mod (a n : Nat) (h : n < a) : a % n = a := Nat.mod_eq_of_lt h";
    assert!(register(&mut env, source).is_err());
    assert!(env.get_const(&Name::from_string("bad_mod")).is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}
