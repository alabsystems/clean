// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual source use of canonical Nat multiplication distributivity APIs.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
theorem distribute_left (a b c : Nat) : a * (b + c) = a * b + a * c := Nat.mul_add a b c
theorem distribute_right (a b c : Nat) : (a + b) * c = a * c + b * c := Nat.add_mul a b c
theorem distribute_zero (a b : Nat) : a * (b + 0) = a * b + a * 0 := Nat.mul_add a b 0
theorem distribute_unit (a b : Nat) : (a + b) * 1 = a * 1 + b * 1 := Nat.add_mul a b 1
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
fn actual_source_distributivity_replays_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("canonical distributivity source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "distribute_left",
        "distribute_right",
        "distribute_zero",
        "distribute_unit",
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
fn source_refuses_extra_units_with_the_original_distributivity_proofs() {
    for source in [
        "theorem bad_distrib (a b c : Nat) : a * (b + c) = Nat.succ (a * b + a * c) := Nat.mul_add a b c",
        "theorem bad_distrib (a b c : Nat) : (a + b) * c = Nat.succ (a * c + b * c) := Nat.add_mul a b c",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_distrib")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}

#[test]
fn source_cannot_drop_a_distributed_summand() {
    let mut env = environment();
    let before = (env.num_constants(), env.num_instances());
    let source = "theorem bad_distrib (a b c : Nat) : (a + b) * c = a * c := Nat.add_mul a b c";
    assert!(register(&mut env, source).is_err());
    assert!(env.get_const(&Name::from_string("bad_distrib")).is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}
