// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full-ORDER qualification of the actual two-constructor Bool model island.
//! This retains the exact output mutation even though native attempt3 timed out.
//! A missing pin, replay refusal or timeout fails; source registration is no pass.

#[path = "support/standalone_theory.rs"]
mod standalone_theory;
use standalone_theory::{Change, Mutation, Package};

#[test]
fn bool_island_rechecks_all_owned_bodies_and_exact_controls() {
    standalone_theory::qualify(&Package {
        family: "kcheck_bool_island",
        source_root: "KCheckBoolIsland",
        fixture_root: "BoolIslandQualification",
        theories: &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_labelled",
            "kcheck_rule_certificates",
            "kcheck_bool_island",
        ],
        fixture_modules: &[
            "KCheckBoolIsland",
            "OperationalLiteralContracts",
            "BoolPacketContracts",
            "BoolMeaningContracts",
            "BoolIslandQualification",
        ],
        module_count: 12,
        lake_includes_root: false,
        root_imports_init: true,
        mint_env: "CLEAN_MINT_KCHECK_BOOL_ISLAND_PINS",
        contract_pairs: include_str!("fixtures/lean/v4.30.0-rc2/kcheck_bool_island/CONTRACTS.json"),
        contract_count: 57,
        data_pairs: &[
            (
                "KCheckBoolIsland.BoolCheckedPacket.packet",
                "BoolPacketContracts.Data.packet",
            ),
            (
                "KCheckBoolIsland.BoolFamily.nominal",
                "BoolPacketContracts.Data.nominal",
            ),
            (
                "KCheckBoolIsland.BoolFamily.suffix",
                "BoolPacketContracts.Data.suffix",
            ),
            (
                "KCheckBoolIsland.BoolFamily.sealed",
                "BoolPacketContracts.Data.sealed",
            ),
            (
                "KCheckBoolIsland.BoolFamily.registered",
                "BoolPacketContracts.Data.registered",
            ),
        ],
        mutations: &[
            Mutation {
                proof: "KCheckBoolIsland.BoolFamily.checked_prefix",
                literal: "BoolPacketContracts.omittedInitialValidity",
                change: Change::DeleteBinder(4),
            },
            Mutation {
                proof: "KCheckBoolIsland.BoolFamily.registered_valid",
                literal: "BoolPacketContracts.omittedIndexedClosure",
                change: Change::DeleteBinder(3),
            },
            Mutation {
                proof: "KCheckBoolIsland.BoolSemanticResults.program_result",
                literal: "BoolMeaningContracts.omittedWithin",
                change: Change::DeleteBinder(5),
            },
            Mutation {
                proof: "KCheckBoolIsland.BoolSemanticResults.constructors_distinct",
                literal: "BoolMeaningContracts.reflexiveConstructorMutation",
                change: Change::ReplaceConstant(
                    "KCheckBoolIsland.oneName",
                    "KCheckBoolIsland.zeroName",
                ),
            },
        ],
        dependencies: &[
            "KCheck.checkOrdinary",
            "KCheck.kcheck",
            "KCheck.kcheckRun",
            "KCheck.check",
            "KCheck.whnf",
            "KCheckSpec.Env.find",
            "KCheckSpec.Entry.define",
            "KCheckSpec.Env.assignment",
            "KCheckSpec.value",
            "KCheckSpec.Rooted",
            "KCheckSpec.RootedAt",
            "KCheckSpec.RuleValid",
            "KCheckSpec.FamilyValid",
            "KCheckSpec.Env.Valid",
            "KCheckSpec.ModelSealing.sealEnv",
            "KCheckSpec.FamilyRegistration.register",
            "KCheckSpec.PSigmaBase.base",
            "KCheckRuleCertificates.TwoNullaryRules.rule_valid",
            "KCheckRuleCertificates.TwoNullaryRules.family_valid",
            "CICL.Model.RawEvaluation.eval",
            "CICL.Model.RawSet.Related",
        ],
    });
}
