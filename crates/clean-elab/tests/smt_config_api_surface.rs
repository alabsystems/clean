// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_auto::bridge::ay_contract::AyLogic;
use clean_elab::tactic::drat::CnfFormula;
use clean_elab::tactic::smt::{AyConfig, AyProofConfig, InvalidAyLogicName, SmtVerifyPolicy};

#[test]
fn test_public_smt_config_builders_are_usable_from_external_crate() {
    let config = AyConfig::default()
        .with_timeout_ms(42)
        .verbose()
        .with_verify_policy(SmtVerifyPolicy::VerifyStrict)
        .try_with_logic_name("QF_LIA")
        .expect("public compatibility parser should accept supported logic names");

    assert_eq!(config.timeout_ms(), Some(42));
    assert!(
        config.is_verbose(),
        "verbose builder should be observable externally"
    );
    assert_eq!(config.logic_override(), Some(AyLogic::QfLia));
    assert_eq!(config.verify_policy(), SmtVerifyPolicy::VerifyStrict);
    assert!(
        config.produces_proofs(),
        "strict verification should keep the proof-production invariant"
    );

    let proof_config = AyProofConfig::new(config.clone(), AyLogic::QfLia, CnfFormula::new());
    assert_eq!(proof_config.logic(), AyLogic::QfLia);
    assert_eq!(proof_config.base().logic_override(), Some(AyLogic::QfLia));
    assert_eq!(
        proof_config.base().verify_policy(),
        SmtVerifyPolicy::VerifyStrict
    );
    assert!(
        proof_config.formula().clauses.is_empty(),
        "public constructor should accept an externally-created CNF formula"
    );
}

#[test]
fn test_public_logic_parser_returns_typed_error() {
    let err: InvalidAyLogicName = AyConfig::parse_logic_name("QF_UFX")
        .expect_err("invalid logic names must fail closed through the public API");
    assert_eq!(err.name(), "QF_UFX");
}
