// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantKind, ProofQuality};
use crate::tc::TypeChecker;
use std::collections::BTreeSet;

const THEOREM: &str = "Nat.bitwiseAux_xor_eq_of_lt_two_pow";

fn statement(operation: &str, zero_fuel: bool, with_b_bound: bool) -> Expr {
    // Spell the telescope independently of the proof builder.
    let offset = u32::from(with_b_bound);
    let width = Expr::bvar(3 + offset);
    let a = Expr::bvar(2 + offset);
    let b = Expr::bvar(1 + offset);
    let fuel = if zero_fuel { Expr::nat_lit(0) } else { width };
    let mut result = eq(
        k("Nat"),
        app("Nat.bitwiseAux", [k(operation), fuel, a.clone(), b.clone()]),
        app("Nat.xor", [a, b]),
    );
    if with_b_bound {
        result = Expr::pi(
            BinderInfo::Default,
            app("Nat.lt", [Expr::bvar(1), pow2(Expr::bvar(3))]),
            result,
        );
    }
    result = Expr::pi(
        BinderInfo::Default,
        app("Nat.lt", [Expr::bvar(1), pow2(Expr::bvar(2))]),
        result,
    );
    (0..3).fold(result, |body, _| {
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
fn test_native_xor_fuel_equality_has_complete_strict_constructive_proof() {
    let env = Environment::with_prelude();
    let name = Name::from_string(THEOREM);
    let info = env
        .get_const(&name)
        .expect("always-on native arithmetic theorem");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert_eq!(info.type_, statement("Bool.xor", false, true));
    let proof = info.value.clone().expect("actual complete proof");
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    env.check_decl_readonly_strict(&Declaration::Theorem {
        name: Name::from_string("XorFuelReplay.complete"),
        level_params: vec![],
        type_: info.type_.clone(),
        value: proof,
    })
    .expect("strict replay of every binder and both bit-index branches");
    assert!(env
        .axiom_deps(&name)
        .expect("transitive closure")
        .is_empty());
    assert!(env
        .trust_marker_deps(&name)
        .expect("marker closure")
        .is_empty());
    assert_eq!(env.proof_quality(&name), Some(ProofQuality::Constructive));
}

#[test]
fn test_xor_fuel_equality_refuses_wrong_operation_zero_fuel_and_missing_bound() {
    let env = Environment::with_prelude();
    let proof = env
        .get_const(&Name::from_string(THEOREM))
        .expect("registered")
        .value
        .clone()
        .expect("proof");
    // OR disagrees with XOR at width=1,a=b=1. Zero fuel disagrees at
    // width=1,a=1,b=0. Omitting b's bound fails at width=0,a=0,b=1.
    for (label, claim) in [
        ("or", statement("Bool.or", false, true)),
        ("zero_fuel", statement("Bool.xor", true, true)),
        ("missing_b_bound", statement("Bool.xor", false, false)),
    ] {
        assert!(
            env.check_decl_readonly_strict(&Declaration::Theorem {
                name: Name::from_string(&format!("XorFuelMutant.{label}")),
                level_params: vec![],
                type_: claim,
                value: proof.clone(),
            })
            .is_err(),
            "false {label} cannot retain the canonical proof"
        );
    }
}

#[test]
fn test_xor_fuel_equality_actual_recursors_cover_zero_and_word_boundaries() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (width, a, b) in [
        (0, 0, 0),
        (1, 1, 1),
        (32, u64::from(u32::MAX), 1),
        (64, u64::MAX, u64::MAX),
        (64, u64::MAX, 1u64 << 63),
    ] {
        assert!(
            tc.is_def_eq(
                &aux(Expr::nat_lit(width), Expr::nat_lit(a), Expr::nat_lit(b)),
                &Expr::nat_lit(a ^ b)
            ),
            "width={width}, a={a}, b={b}; heartbeat_spent={}, heartbeat_limit={}",
            tc.heartbeat_spent(),
            tc.heartbeat_limit()
        );
    }
    for name in ["Nat.bitwiseAux", "Nat.xor"] {
        let name = Name::from_string(name);
        assert_eq!(
            env.get_const(&name).expect("actual operation").kind,
            ConstantKind::Definition
        );
        assert!(env.axiom_deps(&name).expect("operation closure").is_empty());
    }
}

#[test]
fn test_xor_fuel_registration_is_exact_idempotent_and_adds_no_axioms() {
    let mut env = Environment::new();
    env.register_nat_xor_bound_proof()
        .expect("all prerequisites");
    let before = axioms(&env);
    env.register_nat_xor_fuel_proof()
        .expect("register equality");
    assert_eq!(axioms(&env), before);
    let first = env
        .get_const(&Name::from_string(THEOREM))
        .expect("registered")
        .clone();
    let count = env.num_constants();
    env.register_nat_xor_fuel_proof().expect("exact repeat");
    let second = env
        .get_const(&Name::from_string(THEOREM))
        .expect("retained");
    assert_eq!(second.type_, first.type_);
    assert_eq!(second.value, first.value);
    assert_eq!(env.num_constants(), count);
    assert_eq!(axioms(&env), before);
}

#[test]
fn test_xor_fuel_registration_preserves_import_world_and_refuses_name_squatting() {
    let mut imported = Environment::new();
    imported.suppress_lossy_structure_stubs = true;
    imported
        .register_nat_xor_fuel_proof()
        .expect("suppressed overlay");
    assert!(imported.get_const(&Name::from_string(THEOREM)).is_none());
    let mut hostile = Environment::new();
    hostile
        .register_nat_xor_bound_proof()
        .expect("all real prerequisites register before the hostile name");
    hostile
        .add_decl(Declaration::Axiom {
            name: Name::from_string(THEOREM),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("hostile name");
    assert!(hostile.register_nat_xor_fuel_proof().is_err());
    assert_eq!(
        hostile
            .get_const(&Name::from_string(THEOREM))
            .expect("not discharged")
            .kind,
        ConstantKind::Axiom
    );
}
