// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A bounded reduction witness from genuine Lean 4.35 UInt declarations.
//! This diagnostic prefix is not a full-Init or source-world qualification.

use clean_kernel::{Environment, Expr, Name, TypeChecker};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn genuine_uint_environment() -> Environment {
    let library = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.35.0")
        .expect("the exact official 4.35 library is required");
    let mut env = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut env, "v4.35.0").unwrap();
    clean_olean::load_module_with_deps(&mut env, "Init.Data.UInt.Basic", &[library])
        .expect("genuine UInt.Basic must load");
    assert_eq!(clean_olean::environment_world(&env), Some("v4.35.0"));
    env
}

#[test]
fn recent_uint16_nat_primitives_have_reviewed_fold_authority() {
    let env = genuine_uint_environment();
    // UInt16.neg uses BitVec.neg (2^width - value), and complement uses
    // BitVec.allOnes/xor. These are the actual Nat operations of that closure,
    // not permission to fold an arbitrary same-named declaration.
    let verdicts: Vec<_> = ["Nat.sub", "Nat.mod", "Nat.pow", "Nat.xor"]
        .map(|name| (name, env.native_fold_verdict(&Name::from_string(name))))
        .into_iter()
        .collect();
    for (name, verdict) in &verdicts {
        eprintln!("genuine435 {name} fold authority: {verdict:?}");
    }
    assert!(
        verdicts.iter().all(|(_, verdict)| verdict.is_ok()),
        "the genuine UInt witness needs reviewed Nat folds: {verdicts:?}"
    );
}

#[test]
fn recent_uint16_not_neg_one_reduces_with_a_bounded_kernel_check() {
    let env = genuine_uint_environment();
    for name in ["UInt16.ofNat", "UInt16.neg", "UInt16.complement"] {
        assert!(env
            .get_const(&Name::from_string(name))
            .unwrap()
            .level_params
            .is_empty());
    }
    let value = |n| Expr::app(constant("UInt16.ofNat"), Expr::nat_lit(n));
    let left = Expr::app(
        constant("UInt16.complement"),
        Expr::app(constant("UInt16.neg"), value(1)),
    );
    let right = value(0);
    let ty = constant("UInt16");
    let tc = TypeChecker::new(&env);
    tc.check_type(&left, &ty)
        .expect("native control's left expression is well typed");
    tc.check_type(&right, &ty)
        .expect("native control's right expression is well typed");

    // This is an extra diagnostic cost bound, not a production/default budget
    // change. Native 4.35 accepts the exact expression by rfl.
    let mut bounded = TypeChecker::new(&env);
    bounded.set_heartbeat_limit(1_000_000);
    bounded.enable_heartbeat_profiler();
    let equal = bounded.is_def_eq(&left, &right);
    eprintln!(
        "uint16 diagnostic equal={equal} spent={} profile={:?}",
        bounded.heartbeat_spent(),
        bounded.heartbeat_profile()
    );
    assert!(
        equal,
        "genuine 4.35 UInt16 rfl reduction must fit the diagnostic bound"
    );
}
