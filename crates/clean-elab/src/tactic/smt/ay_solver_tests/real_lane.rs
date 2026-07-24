// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::create_smt_backend;
use super::super::*;
use super::real_support::{real_add, real_eq, real_lt, real_of_nat};
use clean_auto::bridge::ay_contract::AyLogic;
use serial_test::serial;

#[test]
#[serial]
fn test_verifiable_qf_lra_proves_concrete_real_constructor_inequality() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let proposition = real_lt(real_of_nat(0), real_of_nat(1));

    let mut solver = create_smt_backend(&config, AyLogic::QfLra);
    let outcome = solver
        .prove(&proposition)
        .expect("verifiable QF_LRA lane should accept concrete constructor-form Real bounds");

    assert!(
        outcome.proved,
        "constructor-form Real inequality should survive end-to-end translation to the solver"
    );
}

#[test]
#[serial]
fn test_verifiable_qf_lra_proves_direct_real_add_inequality() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let proposition = real_eq(real_add(real_of_nat(2), real_of_nat(3)), real_of_nat(5));

    let mut solver = create_smt_backend(&config, AyLogic::QfLra);
    let outcome = solver
        .prove(&proposition)
        .expect("verifiable QF_LRA lane should accept direct Real.add heads");

    assert!(
        outcome.proved,
        "direct Real.add equality should survive end-to-end translation with add-specific semantics"
    );
}
