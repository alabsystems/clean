// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full-ORDER qualification of the pure checked-rule bridge. Source registration
//! alone earns no pass; actual fenced calibration must mint the absent pins.

#[path = "support/standalone_theory.rs"]
mod standalone_theory;
use standalone_theory::{Change, Mutation, Package};

#[test]
fn checked_rule_certificates_recheck_all_owned_bodies_and_exact_controls() {
    standalone_theory::qualify(&Package {
        family: "kcheck_rule_certificates",
        source_root: "KCheckRuleCertificates",
        fixture_root: "RuleCertificateQualification",
        theories: &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_rule_certificates",
        ],
        fixture_modules: &[
            "KCheckRuleCertificates",
            "TwoNullaryLiteralContracts",
            "RuleCertificateQualification",
        ],
        module_count: 7,
        lake_includes_root: true,
        root_imports_init: false,
        mint_env: "CLEAN_MINT_KCHECK_RULE_CERTIFICATE_PINS",
        contract_pairs: include_str!(
            "fixtures/lean/v4.30.0-rc2/kcheck_rule_certificates/CONTRACTS.json"
        ),
        contract_count: 4,
        data_pairs: &[],
        mutations: &[
            Mutation {
                proof: "KCheckRuleCertificates.TwoNullaryRules.rule_valid",
                literal: "TwoNullaryLiteralContracts.omittedPriorValidity",
                change: Change::DeleteBinder(5),
            },
            Mutation {
                proof: "KCheckRuleCertificates.BudgetCases.missing_base_refused",
                literal: "TwoNullaryLiteralContracts.missing_base_forged",
                change: Change::ReplaceConstant("Bool.false", "Bool.true"),
            },
            Mutation {
                proof: "KCheckRuleCertificates.BudgetCases.wrong_index_refused",
                literal: "TwoNullaryLiteralContracts.wrong_index_forged",
                change: Change::ReplaceConstant("Bool.false", "Bool.true"),
            },
        ],
        dependencies: &[
            "KCheckSpec.Env.find",
            "KCheckSpec.Entry.define",
            "KCheckSpec.Env.assignment",
            "KCheckSpec.value",
            "KCheckSpec.Rooted",
            "KCheckSpec.RuleValid",
            "KCheckSpec.FamilyValid",
            "KCheckSpec.Env.Valid",
            "CICL.Model.RawEvaluation.eval",
            "CICL.Model.RawSet.Related",
        ],
    });
}
