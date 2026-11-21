// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantKind, ProofQuality};
use crate::tc::TypeChecker;

#[test]
fn canonical_land_bound_and_fuel_are_closed_constructive_prelude_theorems() {
    let env = Environment::with_prelude();
    for name in [
        "Nat.land_lt_two_pow",
        "Nat.bitwiseAux_land_eq_of_lt_two_pow",
    ] {
        let name = Name::from_string(name);
        let info = env.get_const(&name).expect("always-on native AND theorem");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert_eq!(env.proof_quality(&name), Some(ProofQuality::Constructive));
        let value = info.value.clone().expect("constructive proof body");
        env.check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string(&format!("LandReplay.{name}")),
            level_params: vec![],
            type_: info.type_.clone(),
            value,
        })
        .expect("strict closed theorem replay");
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
}

fn expected_bound(operation: &str) -> Expr {
    let goal = lt(
        Expr::apps(k(operation), [Expr::bvar(3), Expr::bvar(2)]),
        pow2(Expr::bvar(4)),
    );
    let body = Expr::pi(
        BinderInfo::Default,
        lt(Expr::bvar(1), pow2(Expr::bvar(2))),
        Expr::pi(
            BinderInfo::Default,
            lt(Expr::bvar(1), pow2(Expr::bvar(3))),
            goal,
        ),
    );
    (0..3).fold(body, |body, _| {
        Expr::pi(BinderInfo::Default, k("Nat"), body)
    })
}

#[test]
fn canonical_land_bound_keeps_exact_operands_and_rejects_changed_operation() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("Nat.land_lt_two_pow"))
        .unwrap();
    assert_eq!(info.type_, expected_bound("Nat.land"));
    let error = env
        .check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string("LandMutant.add"),
            level_params: vec![],
            type_: expected_bound("Nat.add"),
            value: info.value.clone().unwrap(),
        })
        .expect_err("AND's proof cannot prove the false addition bound");
    assert!(
        matches!(
            error,
            EnvError::TypeCheckFailed {
                source: crate::tc::TypeError::TypeMismatch { .. },
                ..
            }
        ),
        "expected actual typed mismatch, got: {error}"
    );
    assert!(!crate::tc::declaration_budget_exhausted());
}

#[test]
fn canonical_land_actual_values_cover_zero_and_word_boundaries() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (width, a, b) in [
        (0, 0, 0),
        (1, 1, 1),
        (32, u64::from(u32::MAX), 1),
        (64, u64::MAX, u64::MAX),
        (64, u64::MAX, 1 << 63),
        (64, 1 << 63, 1),
        (64, u64::MAX, 4294967295),
    ] {
        assert!(u128::from(a) < 1_u128 << width);
        assert!(u128::from(b) < 1_u128 << width);
        let actual = land(Expr::nat_lit(a), Expr::nat_lit(b));
        assert!(tc.is_def_eq(&actual, &Expr::nat_lit(a & b)));
        let limited = Expr::apps(
            k("Nat.bitwiseAux"),
            [
                k("Bool.and"),
                Expr::nat_lit(width),
                Expr::nat_lit(a),
                Expr::nat_lit(b),
            ],
        );
        assert!(
            tc.is_def_eq(&limited, &actual),
            "width={width}, a={a}, b={b}; heartbeat_spent={}, heartbeat_limit={}",
            tc.heartbeat_spent(),
            tc.heartbeat_limit()
        );
    }
}

#[test]
fn canonical_land_registration_is_exact_and_rejects_a_hostile_existing_root() {
    let mut env = Environment::with_prelude();
    let count = env.num_constants();
    let before = env
        .get_const(&Name::from_string("Nat.land_lt_two_pow"))
        .unwrap()
        .clone();
    env.register_nat_land_fuel_proof()
        .expect("same exact proof registration");
    assert_eq!(env.num_constants(), count);
    let after = env
        .get_const(&Name::from_string("Nat.land_lt_two_pow"))
        .unwrap();
    assert_eq!(after.type_, before.type_);
    assert_eq!(after.value, before.value);
    let mut hostile = Environment::new();
    hostile.init_nat().expect("hostile declaration's Nat type");
    hostile
        .add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.land_lt_two_pow"),
            level_params: vec![],
            type_: k("Nat"),
        })
        .expect("independent hostile declaration");
    assert!(hostile.register_nat_land_bound_proof().is_err());
    assert_eq!(
        hostile
            .get_const(&Name::from_string("Nat.land_lt_two_pow"))
            .expect("hostile declaration retained")
            .kind,
        ConstantKind::Axiom
    );
}

#[test]
fn canonical_land_fuel_retains_its_exact_operation_and_import_world() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("Nat.bitwiseAux_land_eq_of_lt_two_pow"))
        .unwrap();
    let left = Expr::apps(
        k("Nat.bitwiseAux"),
        [k("Bool.and"), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)],
    );
    let right = land(Expr::bvar(3), Expr::bvar(2));
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), left.clone(), right],
    );
    let close = |body| {
        let body = Expr::pi(
            BinderInfo::Default,
            lt(Expr::bvar(1), pow2(Expr::bvar(2))),
            Expr::pi(
                BinderInfo::Default,
                lt(Expr::bvar(1), pow2(Expr::bvar(3))),
                body,
            ),
        );
        (0..3).fold(body, |body, _| {
            Expr::pi(BinderInfo::Default, k("Nat"), body)
        })
    };
    assert_eq!(info.type_, close(equality));
    let changed = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            k("Nat"),
            left,
            Expr::apps(k("Nat.xor"), [Expr::bvar(3), Expr::bvar(2)]),
        ],
    );
    let error = env
        .check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string("LandFuelMutant.xor"),
            level_params: vec![],
            type_: close(changed),
            value: info.value.clone().unwrap(),
        })
        .expect_err("AND fuel cannot prove canonical XOR");
    assert!(
        matches!(
            error,
            EnvError::TypeCheckFailed {
                source: crate::tc::TypeError::TypeMismatch { .. },
                ..
            }
        ),
        "expected actual typed mismatch, got: {error}"
    );
    assert!(!crate::tc::declaration_budget_exhausted());
    let mut imported = Environment::new();
    imported.suppress_lossy_structure_stubs = true;
    let count = imported.num_constants();
    imported
        .register_nat_land_fuel_proof()
        .expect("suppressed native overlay");
    assert_eq!(imported.num_constants(), count);
    assert!(imported
        .get_const(&Name::from_string("Nat.land_lt_two_pow"))
        .is_none());
    assert!(imported
        .get_const(&Name::from_string("Nat.bitwiseAux_land_eq_of_lt_two_pow"))
        .is_none());
}
