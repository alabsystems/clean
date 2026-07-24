// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::common::check_and_add_decl;
use clean_kernel::Environment;

fn env_with_my_nat() -> Environment {
    let mut env = Environment::with_prelude();
    check_and_add_decl(
        &mut env,
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    )
    .expect("MyNat should elaborate");
    env
}

#[test]
fn test_issue2013_structural_recursion_with_implicit_extra_param() {
    let mut env = env_with_my_nat();

    let result = check_and_add_decl(
        &mut env,
        r"def carryImplicit (n : MyNat) {inst : MyNat} (x : MyNat) : MyNat := match n with
| MyNat.zero => x
| MyNat.succ k => carryImplicit k x",
    );
    assert!(
        result.is_ok(),
        "Issue #2013: recursive calls with omitted implicit extra params should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_issue2013_structural_recursion_with_dependent_extra_params() {
    let mut env = env_with_my_nat();
    check_and_add_decl(&mut env, "axiom Payload : MyNat → Type")
        .expect("Payload family should elaborate");

    let result = check_and_add_decl(
        &mut env,
        r"def carryDependent (n m : MyNat) (payload : Payload m) : MyNat := match n with
| MyNat.zero => m
| MyNat.succ k => carryDependent k m payload",
    );
    assert!(
        result.is_ok(),
        "Issue #2013: dependent extra params should elaborate through structural recursion: {:?}",
        result.err()
    );
}
