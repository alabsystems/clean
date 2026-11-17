// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical qualification of the already-held exact equality-header bridge.
//! Source registration earns no pass; actual calibration and default replay are owed.

#[path = "support/standalone_theory.rs"]
mod standalone_theory;
use standalone_theory::{Change, Mutation, Package};

#[test]
fn exact_eq_headers_recheck_all_owned_bodies_and_exact_controls() {
    standalone_theory::qualify(&Package {
        family: "kcheck_eq_headers",
        source_root: "KCheckEqHeaders",
        fixture_root: "EqHeadersQualification",
        theories: &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_labelled",
            "kcheck_rule_certificates",
            "kcheck_bool_island",
            "kcheck_bool_admission",
            "kcheck_eq_headers",
        ],
        fixture_modules: &[
            "KCheckEqHeaders",
            "EqHeaderContracts",
            "EqHeadersQualification",
        ],
        module_count: 5,
        lake_includes_root: true,
        root_imports_init: false,
        mint_env: "CLEAN_MINT_KCHECK_EQ_HEADERS_PINS",
        contract_pairs: include_str!("fixtures/lean/v4.30.0-rc2/kcheck_eq_headers/CONTRACTS.json"),
        contract_count: 12,
        data_pairs: &[],
        mutations: &[
            Mutation {
                proof: "KCheckEqHeaders.check_sound_with_eq_headers",
                literal: "EqHeaderContracts.omittedInitial",
                change: Change::DeleteBinder(8),
            },
            Mutation {
                proof: "KCheckEqHeaders.check_sound_with_eq_headers",
                literal: "EqHeaderContracts.omittedHeaders",
                change: Change::DeleteBinder(9),
            },
            Mutation {
                proof: "KCheckEqHeaders.check_sound_with_eq_headers",
                literal: "EqHeaderContracts.omittedIndexed",
                change: Change::DeleteBinder(3),
            },
        ],
        dependencies: &[
            "KCheckSpec.Env.find",
            "KCheckSpec.Base.familyEntry",
            "KCheckSpec.Base.eqType",
            "KCheckSpec.Base.eqReflType",
            "KCheckSpec.Base.eqRecType",
            "KCheckSpec.Base.oneLevelBound",
            "KCheckSpec.Base.twoLevelBound",
            "KCheckSpec.Env.assignment",
            "KCheckSpec.EntryValid",
            "KCheckSpec.Env.Valid",
            "KCheckSpec.RuleValid",
            "KCheckSpec.FamilyValid",
            "KCheckSpec.RootedAt",
            "KCheckSpec.CertificateEquality.inTele_apply_typed",
            "KCheckSpec.TypedEqualityReflection.valid_reflects",
            "KCheckBoolAdmission.check",
            "KCheckBoolAdmission.check_decomposition",
            "KCheckBoolAdmission.Runs.checked_valid",
            "KCheckBoolAdmission.checkedEnv",
            "KCheckBoolAdmission.install",
            "KCheckBoolAdmission.install_prefix",
            "KCheckBoolAdmission.packetFromOutputs",
            "KCheckRuleCertificates.TwoNullaryRules.rule_closed",
            "KCheckSpec.ModelSealing.sealEnv",
            "KCheckSpec.ModelSealing.env_valid",
            "KCheckSpec.ModelSealing.family_valid",
            "KCheckSpec.FamilyRegistration.env_valid",
        ],
    });
}
