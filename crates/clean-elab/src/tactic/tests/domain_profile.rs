// Copyright 2026 Andrew Yates
// Author: dbx-clean-ai
// SPDX-License-Identifier: Apache-2.0

//! Tests for tactic-domain profile configuration.

use super::*;
use crate::tactic::cert_simp::cert_simp_lemma_names;
use crate::tactic::domain_profile::{
    cert_simp_config, project_mathverse_config, recommended_tactics, TacticDomainProfile,
};
use crate::tactic::project_mathverse::NatCoercionPolicy;

#[test]
fn test_sat_pb_profile_configures_pb_certificate_automation() {
    let profile = TacticDomainProfile::SatPb;
    let cert = cert_simp_config(profile);
    let mathverse = project_mathverse_config(profile);

    assert_eq!(profile.name(), "sat-pb");
    assert!(profile.semantic_heads().contains(&"PBConstraint"));
    assert!(profile.semantic_heads().contains(&"VeriPB"));
    assert!(profile.normalizers().contains(&"cert_simp"));
    assert!(profile.normalizers().contains(&"cert_mathverse"));
    assert!(cert.include_sat_pb);
    assert!(!cert.include_nn_verify);
    assert!(cert.simplify_hypotheses);
    assert!(cert.max_steps >= CertSimpConfig::default().max_steps);
    assert!(mathverse.normalize_cert_terms);
    assert_eq!(mathverse.coerce_nat, NatCoercionPolicy::LinearSafe);
    assert!(mathverse.cert_simp.include_sat_pb);
    assert_eq!(
        recommended_tactics(profile),
        &["cert_simp", "cert_mathverse", "simp", "omega"]
    );
}

#[test]
fn test_nn_verify_profile_configures_nn_certificate_automation() {
    let profile = TacticDomainProfile::NnVerify;
    let cert = profile.cert_simp_config();
    let mathverse = profile.project_mathverse_config();

    assert_eq!(TacticDomainProfile::from_name("nn-verify"), Some(profile));
    assert!(profile.semantic_heads().contains(&"CROWN"));
    assert!(profile.semantic_heads().contains(&"ExternalFarkasCert"));
    assert!(profile.normalizers().contains(&"nn_interval_nf"));
    assert!(!cert.include_sat_pb);
    assert!(cert.include_nn_verify);
    assert!(mathverse.normalize_cert_terms);
    assert!(!mathverse.cert_simp.include_sat_pb);
    assert!(mathverse.cert_simp.include_nn_verify);
    assert_eq!(
        profile.recommended_tactics(),
        &["cert_simp", "cert_mathverse", "linarith", "simp"]
    );
}

#[test]
fn test_proof_complexity_profile_reuses_sat_pb_pack_without_nn_pack() {
    let profile = TacticDomainProfile::ProofComplexity;
    let cert = cert_simp_config(profile);
    let mathverse = project_mathverse_config(profile);

    assert_eq!(
        TacticDomainProfile::from_name("proof-complexity"),
        Some(profile)
    );
    assert!(profile.semantic_heads().contains(&"Resolution"));
    assert!(profile.semantic_heads().contains(&"CuttingPlanes"));
    assert!(profile.semantic_heads().contains(&"PolynomialCalculus"));
    assert!(profile.normalizers().contains(&"proof_complexity_nf"));
    assert!(cert.include_sat_pb);
    assert!(!cert.include_nn_verify);
    assert!(mathverse.normalize_cert_terms);
    assert!(mathverse.cert_simp.include_sat_pb);
    assert_eq!(
        recommended_tactics(profile),
        &["cert_simp", "simp", "omega"]
    );
}

#[test]
fn test_general_profile_is_not_certificate_domain_by_default() {
    let profile = TacticDomainProfile::General;
    let cert = profile.cert_simp_config();
    let mathverse = profile.project_mathverse_config();

    assert_eq!(TacticDomainProfile::from_name("general"), Some(profile));
    assert_eq!(TacticDomainProfile::from_name("core"), Some(profile));
    assert_eq!(TacticDomainProfile::from_name("unknown"), None);
    assert!(!cert.include_sat_pb);
    assert!(!cert.include_nn_verify);
    assert!(cert.max_steps < CertSimpConfig::default().max_steps);
    assert!(!mathverse.normalize_cert_terms);
    assert!(!mathverse.cert_simp.include_sat_pb);
    assert!(!mathverse.cert_simp.include_nn_verify);
    assert_eq!(
        recommended_tactics(profile),
        &["exact", "apply", "rw", "simp", "omega"]
    );
}

#[test]
fn test_sat_pb_profile_loads_only_sat_pb_specific_cert_candidates() {
    let state = state_with_sat_pb_and_nn_candidate_defs();
    let cert_names = cert_simp_lemma_names(&state, &cert_simp_config(TacticDomainProfile::SatPb));
    let mathverse_names = cert_simp_lemma_names(
        &state,
        &project_mathverse_config(TacticDomainProfile::SatPb).cert_simp,
    );

    assert!(
        contains_name(&cert_names, "Cert.PB.checkBound"),
        "SAT/PB cert_simp config should load SAT/PB candidates, got {cert_names:?}"
    );
    assert!(
        !contains_name(&cert_names, "NNVerify.checkBound"),
        "SAT/PB cert_simp config must not load NN-only candidates, got {cert_names:?}"
    );
    assert_eq!(
        cert_names, mathverse_names,
        "SAT/PB cert_mathverse profile hook should pass through the same cert_simp candidate pack"
    );
}

#[test]
fn test_nn_verify_profile_loads_only_nn_specific_cert_candidates() {
    let state = state_with_sat_pb_and_nn_candidate_defs();
    let cert_names =
        cert_simp_lemma_names(&state, &cert_simp_config(TacticDomainProfile::NnVerify));
    let mathverse_names = cert_simp_lemma_names(
        &state,
        &project_mathverse_config(TacticDomainProfile::NnVerify).cert_simp,
    );

    assert!(
        contains_name(&cert_names, "NNVerify.checkBound"),
        "NN cert_simp config should load NN candidates, got {cert_names:?}"
    );
    assert!(
        !contains_name(&cert_names, "Cert.PB.checkBound"),
        "NN cert_simp config must not load SAT/PB-only candidates, got {cert_names:?}"
    );
    assert_eq!(
        cert_names, mathverse_names,
        "NN cert_mathverse profile hook should pass through the same cert_simp candidate pack"
    );
}

#[test]
fn test_legacy_default_cert_configs_still_load_both_domain_packs() {
    let state = state_with_sat_pb_and_nn_candidate_defs();
    let cert_names = cert_simp_lemma_names(&state, &CertSimpConfig::default());
    let mathverse_names =
        cert_simp_lemma_names(&state, &ProjectMathverseConfig::default().cert_simp);

    for names in [&cert_names, &mathverse_names] {
        assert!(
            contains_name(names, "Cert.PB.checkBound"),
            "legacy default config should still load SAT/PB candidates, got {names:?}"
        );
        assert!(
            contains_name(names, "NNVerify.checkBound"),
            "legacy default config should still load NN candidates, got {names:?}"
        );
    }
}

fn state_with_sat_pb_and_nn_candidate_defs() -> ProofState {
    let mut env = Environment::new();
    add_candidate_definition(&mut env, "Cert.PB.checkBound");
    add_candidate_definition(&mut env, "NNVerify.checkBound");
    ProofState::new(env, Expr::prop())
}

fn add_candidate_definition(env: &mut Environment, name: &str) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::prop(),
        is_reducible: true,
    })
    .unwrap();
}

fn contains_name(names: &[String], needle: &str) -> bool {
    names.iter().any(|name| name == needle)
}
