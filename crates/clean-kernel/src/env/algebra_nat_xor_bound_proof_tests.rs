// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantKind, ProofQuality};
use crate::tc::TypeChecker;
use std::collections::BTreeSet;

fn statement(operation: &str) -> Expr {
    // Independently spell the complete telescope: n, a, b, a-bound, b-bound.
    let result = lt(
        Expr::apps(k(operation), [Expr::bvar(3), Expr::bvar(2)]),
        pow2(Expr::bvar(4)),
    );
    let b_bound = lt(Expr::bvar(1), pow2(Expr::bvar(3)));
    let a_bound = lt(Expr::bvar(1), pow2(Expr::bvar(2)));
    let body = Expr::pi(
        BinderInfo::Default,
        a_bound,
        Expr::pi(BinderInfo::Default, b_bound, result),
    );
    (0..3).fold(body, |body, _| {
        Expr::pi(BinderInfo::Default, k("Nat"), body)
    })
}

fn axioms(env: &Environment) -> BTreeSet<Name> {
    env.constants()
        .filter(|info| info.kind == ConstantKind::Axiom)
        .map(|info| info.name.clone())
        .collect()
}

#[test]
fn test_native_prelude_retains_complete_xor_bound_and_constructive_proofs() {
    let env = Environment::with_prelude();
    for name in ["Nat.lt_two_pow_of_testBit_ge", "Nat.xor_lt_two_pow"] {
        let name = Name::from_string(name);
        let info = env.get_const(&name).expect("native arithmetic theorem");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("actual proof body");
        env.check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string(&format!("XorBoundReplay.{name}")),
            level_params: vec![],
            type_: info.type_.clone(),
            value,
        })
        .expect("complete closed proof must pass strict declaration replay");
        assert!(env
            .axiom_deps(&name)
            .expect("registered closure")
            .is_empty());
        assert_eq!(env.proof_quality(&name), Some(ProofQuality::Constructive));
    }
    assert_eq!(
        env.get_const(&Name::from_string("Nat.xor_lt_two_pow"))
            .expect("registered")
            .type_,
        statement("Nat.xor"),
        "the theorem must retain both arbitrary operands and their two bounds"
    );
}

#[test]
fn test_xor_bound_registration_adds_no_axioms_and_is_exactly_idempotent() {
    let mut env = Environment::new();
    env.register_nat_testbit_lt_pow_proof()
        .expect("bit foundation");
    env.register_nat_succ_add_proof()
        .expect("successor addition");
    env.register_nat_ble_le_lemmas().expect("zero bound");
    env.register_nat_pow_le_pow_right_proof()
        .expect("power monotonicity");
    env.init_nat_trans_lt_le_lt().expect("bound transitivity");
    let before = axioms(&env);
    env.register_nat_xor_bound_proof().expect("canonical bound");
    assert_eq!(
        axioms(&env),
        before,
        "registration must not enlarge the axiom census"
    );
    let first = env
        .get_const(&Name::from_string("Nat.xor_lt_two_pow"))
        .expect("registered")
        .clone();
    let count = env.num_constants();
    env.register_nat_xor_bound_proof()
        .expect("same exact registration");
    let second = env
        .get_const(&Name::from_string("Nat.xor_lt_two_pow"))
        .expect("retained");
    assert_eq!(second.type_, first.type_);
    assert_eq!(second.value, first.value);
    assert_eq!(env.num_constants(), count);
    assert_eq!(axioms(&env), before);
}

#[test]
fn test_xor_bound_cannot_prove_addition_or_omit_an_operand_bound() {
    let env = Environment::with_prelude();
    let proof = env
        .get_const(&Name::from_string("Nat.xor_lt_two_pow"))
        .expect("registered")
        .value
        .clone()
        .expect("proof body");
    // Addition is false at n=1, a=b=1. Removing b's bound is false at
    // n=0, a=0, b=1. Neither can reuse the checked XOR proof.
    let without_b_bound = (0..3).fold(
        Expr::pi(
            BinderInfo::Default,
            lt(Expr::bvar(1), pow2(Expr::bvar(2))),
            lt(xor(Expr::bvar(2), Expr::bvar(1)), pow2(Expr::bvar(3))),
        ),
        |body, _| Expr::pi(BinderInfo::Default, k("Nat"), body),
    );
    for (label, type_) in [
        ("addition", statement("Nat.add")),
        ("missing_b_bound", without_b_bound),
    ] {
        assert!(
            env.check_decl_readonly_strict(&Declaration::Theorem {
                name: Name::from_string(&format!("XorBoundMutant.{label}")),
                level_params: vec![],
                type_,
                value: proof.clone(),
            })
            .is_err(),
            "false {label} claim must not retain the original proof"
        );
    }
}

#[test]
fn test_xor_bound_uses_actual_xor_at_zero_and_word_boundaries() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (width, a, b) in [
        (0, 0, 0),
        (1, 1, 1),
        (32, u64::from(u32::MAX), 1),
        (64, u64::MAX, u64::MAX),
        (64, u64::MAX, 1u64 << 63),
        (64, 1u64 << 63, 1),
    ] {
        let limit = 1u128 << width;
        assert!(u128::from(a) < limit && u128::from(b) < limit);
        assert!(u128::from(a ^ b) < limit);
        assert!(
            tc.is_def_eq(
                &xor(Expr::nat_lit(a), Expr::nat_lit(b)),
                &Expr::nat_lit(a ^ b)
            ),
            "width={width} a={a} b={b}"
        );
    }
    assert_eq!(
        env.get_const(&Name::from_string("Nat.xor"))
            .expect("actual operation")
            .kind,
        ConstantKind::Definition
    );
    assert!(env
        .axiom_deps(&Name::from_string("Nat.xor"))
        .expect("operation closure")
        .is_empty());
}

#[test]
fn test_xor_bound_registration_refuses_name_squatting_without_discharge() {
    for name in ["Nat.lt_two_pow_of_testBit_ge", "Nat.xor_lt_two_pow"] {
        let mut env = Environment::new();
        let name = Name::from_string(name);
        env.add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("hostile pre-existing name");
        assert!(env.register_nat_xor_bound_proof().is_err());
        assert_eq!(
            env.get_const(&name).expect("not discharged").kind,
            ConstantKind::Axiom
        );
    }
}

#[test]
fn test_import_world_does_not_install_native_bit_bounds() {
    let mut env = Environment::new();
    env.suppress_lossy_structure_stubs = true;
    env.register_nat_xor_bound_proof()
        .expect("native overlay suppressed");
    for name in ["Nat.lt_two_pow_of_testBit_ge", "Nat.xor_lt_two_pow"] {
        assert!(env.get_const(&Name::from_string(name)).is_none());
    }
}
