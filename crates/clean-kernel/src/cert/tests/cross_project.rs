// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::cert::*;
use crate::{Declaration, Environment, Expr, Name};

fn prover() -> ProverInfo {
    ProverInfo::new(
        ProverSystem::Clean,
        "clean-kernel",
        Some(env!("CARGO_PKG_VERSION").to_string()),
    )
}

fn test_env() -> Environment {
    let mut env = Environment::with_prelude();
    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let dep_name = Name::from_string("Cross.dep");

    env.add_decl(Declaration::Theorem {
        name: dep_name.clone(),
        level_params: vec![],
        type_: true_ty.clone(),
        value: true_intro,
    })
    .expect("register dependency theorem");

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("Cross.main"),
        level_params: vec![],
        type_: true_ty,
        value: Expr::const_(dep_name, vec![]),
    })
    .expect("register main theorem");

    env
}

fn sample_cert(env: &Environment) -> CrossProjectCert {
    let dep = CrossProjectDependency::from_environment(env, "Cross.dep")
        .expect("build dependency from environment");
    CrossProjectCert::from_environment(env, "Cross.main", prover(), vec![dep])
        .expect("build cross-project cert from environment")
}

#[test]
fn test_cross_project_cert_json_roundtrip() {
    let env = test_env();
    let cert = sample_cert(&env);

    let json = cert
        .to_json()
        .expect("serialize cross-project cert to JSON");
    let restored =
        CrossProjectCert::from_json(&json).expect("deserialize cross-project cert from JSON");

    assert_eq!(cert, restored);
    restored
        .verify(&env)
        .expect("restored JSON cert should verify");
}

#[test]
fn test_cross_project_cert_bincode_roundtrip() {
    let env = test_env();
    let cert = sample_cert(&env);

    let bytes = cert
        .to_bincode()
        .expect("serialize cross-project cert to bincode");
    let restored = CrossProjectCert::from_bincode(&bytes)
        .expect("deserialize cross-project cert from bincode");

    assert_eq!(cert, restored);
    restored
        .verify(&env)
        .expect("restored bincode cert should verify");
}

#[test]
fn test_cross_project_verify_matches_environment() {
    let env = test_env();
    let cert = sample_cert(&env);

    cert.verify(&env)
        .expect("certificate should match theorem and dependency hashes");
    assert_eq!(cert.prover.system, ProverSystem::Clean);
    assert_eq!(cert.dependencies.len(), 1);
    assert_eq!(cert.dependencies[0].theorem_name, "Cross.dep");
}

#[test]
fn test_cross_project_verify_rejects_hash_mismatch() {
    let env = test_env();
    let mut cert = sample_cert(&env);
    cert.proof_hash = "00".repeat(32);

    let err = cert
        .verify(&env)
        .expect_err("proof hash mismatch should fail verification");

    assert!(matches!(
        err,
        CrossProjectVerifyError::HashMismatch {
            role: "theorem",
            name,
            field: "proof",
            ..
        } if name == "Cross.main"
    ));
}
