// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

// ============================================================================
// AyConfig::from_env tests (Part of #2427)
// ============================================================================

#[test]
#[serial]
fn test_ay_config_from_env_default_is_extract_only() {
    // Unset the env var to ensure default behavior
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::unset("CLEAN_SMT_VERIFY");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::ExtractOnly,
        "unset CLEAN_SMT_VERIFY should yield ExtractOnly (proof reconstruction active)"
    );
    assert!(
        config.produces_proofs(),
        "ExtractOnly requires proof production"
    );
}

#[test]
#[serial]
fn test_ay_config_from_env_carcara() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_SMT_VERIFY", "carcara");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::VerifyCarcara,
        "CLEAN_SMT_VERIFY=carcara should yield VerifyCarcara"
    );
    assert!(
        config.produces_proofs(),
        "VerifyCarcara requires proof production"
    );
}

#[test]
#[serial]
fn test_ay_config_from_env_strict() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_SMT_VERIFY", "strict");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::VerifyStrict,
        "CLEAN_SMT_VERIFY=strict should yield VerifyStrict"
    );
    assert!(
        config.produces_proofs(),
        "VerifyStrict requires proof production"
    );
}

#[test]
#[serial]
fn test_ay_config_from_env_extract() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_SMT_VERIFY", "extract");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::ExtractOnly,
        "CLEAN_SMT_VERIFY=extract should yield ExtractOnly"
    );
    assert!(
        config.produces_proofs(),
        "ExtractOnly requires proof production"
    );
}

#[test]
#[serial]
fn test_ay_config_from_env_trust_explicit() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_SMT_VERIFY", "trust");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::TrustSolver,
        "CLEAN_SMT_VERIFY=trust should yield TrustSolver"
    );
    assert!(
        !config.produces_proofs(),
        "TrustSolver should not produce proofs"
    );
}

#[test]
#[serial]
fn test_ay_config_from_env_unknown_value_defaults() {
    let _env = crate::test_env::lock_env();
    let _guard = crate::test_env::ScopedEnvVar::set("CLEAN_SMT_VERIFY", "bogus");
    let config = AyConfig::from_env();
    assert_eq!(
        config.verify_policy(),
        SmtVerifyPolicy::ExtractOnly,
        "unknown value should fall through to ExtractOnly"
    );
    assert!(
        config.produces_proofs(),
        "ExtractOnly requires proof production"
    );
}

#[test]
fn test_ay_config_default_logic_remains_qf_uf_when_unset() {
    assert_eq!(
        AyConfig::default().effective_logic(),
        clean_auto::bridge::ay_contract::AyLogic::QfUf,
        "unset logic override should be the intentional QF_UF default"
    );
}

#[test]
fn test_ay_config_try_with_logic_name_accepts_supported_values() {
    use clean_auto::bridge::ay_contract::AyLogic;

    let cases = [
        ("ALL", AyLogic::All),
        ("QF_LIA", AyLogic::QfLia),
        ("QF_LRA", AyLogic::QfLra),
        ("QF_UF", AyLogic::QfUf),
        ("QF_UFLIA", AyLogic::QfUflia),
        ("QF_BV", AyLogic::QfBv),
        ("QF_AUFLIA", AyLogic::QfAuflia),
        ("UF", AyLogic::Uf),
        ("UFLIA", AyLogic::Uflia),
    ];

    for (name, logic) in cases {
        let config = AyConfig::default()
            .try_with_logic_name(name)
            .expect("supported logic name should parse");
        assert_eq!(
            config.logic_override(),
            Some(logic),
            "logic override should preserve the parsed enum for {name}"
        );
        assert_eq!(
            config.effective_logic(),
            logic,
            "effective logic should match the typed override for {name}"
        );
    }
}

#[test]
fn test_ay_config_try_with_invalid_logic_name_fails_closed() {
    let err = AyConfig::default()
        .try_with_logic_name("QF_UFX")
        .expect_err("invalid logic name must not silently default to QF_UF");
    assert_eq!(err.name(), "QF_UFX");
}

/// `with_verify_policy` must unconditionally synchronize `produce_proofs`
/// with the new policy. Previously, switching from a proof-producing policy
/// back to `TrustSolver` left `produce_proofs` stale at `true`, violating
/// the invariant documented on `from_env`.
#[test]
fn test_ay_config_with_verify_policy_resets_produce_proofs_for_trust_solver() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict);
    assert!(
        config.produces_proofs(),
        "VerifyStrict should enable proof production"
    );

    let config = config.with_verify_policy(SmtVerifyPolicy::TrustSolver);
    assert!(
        !config.produces_proofs(),
        "switching to TrustSolver must reset produce_proofs to false"
    );
    assert_eq!(config.verify_policy(), SmtVerifyPolicy::TrustSolver);
}

/// `enable_proofs` can still override `produce_proofs` independently, so
/// TrustSolver + proofs for debugging remains possible via explicit opt-in.
#[test]
fn test_ay_config_enable_proofs_overrides_trust_solver_default() {
    let config = AyConfig::default()
        .with_verify_policy(SmtVerifyPolicy::TrustSolver)
        .enable_proofs();
    assert!(
        config.produces_proofs(),
        "explicit enable_proofs after TrustSolver should opt into proof production"
    );
    assert_eq!(config.verify_policy(), SmtVerifyPolicy::TrustSolver);
}
