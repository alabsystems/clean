// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual source use of bounded-remainder uniqueness over the real Nat operations.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
theorem decomposition_remainder (a n q r : Nat) (hr : r < n) (he : q * n + r = a) : a % n = r := Nat.divmodAux.mod_eq_of_decomposition a n q r hr he
theorem unique_remainder (n q p r s : Nat) (hr : r < n) (hs : s < n) (he : q * n + r = p * n + s) : r = s := Nat.divmodAux.remainder_unique n q p r s hr hs he
theorem concrete_remainder : 14 % 5 = 4 := Nat.divmodAux.mod_eq_of_decomposition 14 5 2 4 (by decide) (by decide)
theorem remainder_of_sum (a b n : Nat) : (a + b) % n = (a % n + b % n) % n := Nat.add_mod a b n
theorem zero_modulus_sum (a b : Nat) : (a + b) % 0 = (a % 0 + b % 0) % 0 := Nat.add_mod a b 0
theorem remainder_of_product (a b n : Nat) : (a * b) % n = ((a % n) * (b % n)) % n := Nat.mul_mod a b n
theorem zero_modulus_product (a b : Nat) : (a * b) % 0 = ((a % 0) * (b % 0)) % 0 := Nat.mul_mod a b 0
theorem wraparound_product : (9 * 8) % 5 = ((9 % 5) * (8 % 5)) % 5 := Nat.mul_mod 9 8 5
theorem zero_quotient (r n : Nat) (hr : r < n) : r % n = r := Nat.mod_eq_of_lt hr
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
fn actual_source_remainder_uniqueness_replays_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("bounded remainder source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "decomposition_remainder",
        "unique_remainder",
        "concrete_remainder",
        "zero_quotient",
        "remainder_of_sum",
        "zero_modulus_sum",
        "remainder_of_product",
        "zero_modulus_product",
        "wraparound_product",
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
fn source_refuses_a_changed_remainder_with_the_original_proof() {
    let mut env = environment();
    let before = (env.num_constants(), env.num_instances());
    let source = "theorem bad_remainder (a n q r : Nat) (hr : r < n) (he : q * n + r = a) : a % n = Nat.succ r := Nat.divmodAux.mod_eq_of_decomposition a n q r hr he";
    assert!(register(&mut env, source).is_err());
    assert!(env.get_const(&Name::from_string("bad_remainder")).is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}

#[test]
fn source_requires_both_a_true_bound_and_a_true_decomposition() {
    for source in [
        "theorem bad_remainder : 14 % 5 = 9 := Nat.divmodAux.mod_eq_of_decomposition 14 5 1 9 (by decide) (by decide)",
        "theorem bad_remainder : 14 % 5 = 3 := Nat.divmodAux.mod_eq_of_decomposition 14 5 2 3 (by decide) (by decide)",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_remainder")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}

#[test]
fn source_refuses_changed_add_mod_conclusions() {
    for source in [
        "theorem bad_add_mod (a b n : Nat) : (a + b) % n = Nat.succ ((a % n + b % n) % n) := Nat.add_mod a b n",
        "theorem bad_add_mod : (1 + 1) % 2 = 1 % 2 + 1 % 2 := Nat.add_mod 1 1 2",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_add_mod")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}

#[test]
fn source_refuses_changed_mul_mod_conclusions() {
    for source in [
        "theorem bad_mul_mod (a b n : Nat) : (a * b) % n = Nat.succ (((a % n) * (b % n)) % n) := Nat.mul_mod a b n",
        "theorem bad_mul_mod : (4 * 4) % 5 = (4 % 5) * (4 % 5) := Nat.mul_mod 4 4 5",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_mul_mod")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}
