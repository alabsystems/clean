// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical source registration for the standalone atomic Bool transaction.
//! Native receipts do not qualify this path. Pins/default replay remain owed.

#[path = "support/standalone_theory.rs"]
mod standalone_theory;
use standalone_theory::{Change, Mutation, Package};

/// Count literal Const occurrences, preserving repeated structural appearances.
/// This matches the native probe's recursive exact-one-occurrence guard.
fn constant_occurrences(expression: &clean_olean::ParsedExpr, target: &str) -> usize {
    use clean_olean::ParsedExpr;
    let mut count = 0;
    let mut pending = vec![expression];
    while let Some(current) = pending.pop() {
        match current {
            ParsedExpr::Const(name, _) => count += usize::from(name == target),
            ParsedExpr::App(function, argument)
            | ParsedExpr::Lam(_, function, argument, _)
            | ParsedExpr::ForallE(_, function, argument, _) => {
                pending.push(function);
                pending.push(argument);
            }
            ParsedExpr::LetE(_, domain, value, body, _) => {
                pending.push(domain);
                pending.push(value);
                pending.push(body);
            }
            ParsedExpr::MData(_, inner) | ParsedExpr::Proj(_, _, inner) => pending.push(inner),
            ParsedExpr::BVar(_)
            | ParsedExpr::FVar(_)
            | ParsedExpr::MVar(_)
            | ParsedExpr::Sort(_)
            | ParsedExpr::Lit(_) => {}
            _ => panic!("unsupported expression in exact receipt-kind occurrence guard"),
        }
    }
    count
}

fn assert_single_receipt_kind_occurrence() {
    let compiled = clean_olean::test_support::compiled_fixture_dir("kcheck_bool_admission");
    let path = compiled.join("KCheckBoolAdmission/Cases.olean");
    let artifact = clean_olean::read_artifact(
        "KCheckBoolAdmission.Cases",
        &path,
        clean_olean::ArtifactDepth::Records,
    )
    .expect("complete actual Cases artifact for receipt-kind guard");
    // Cases currently uses the ordinary prelude module format. A future module
    // split needs an explicit authoritative-part update, never a partial read.
    assert!(
        !artifact.is_module,
        "receipt-kind guard requires the current ordinary module shape"
    );
    let parsed = clean_olean::parse_module(&std::fs::read(&path).expect("Cases bytes"))
        .expect("parse actual Cases declaration records");
    let receipts: Vec<_> = parsed
        .constants
        .iter()
        .filter(|constant| constant.name == "KCheckBoolAdmission.Cases.actual_receipt")
        .collect();
    assert_eq!(
        receipts.len(),
        1,
        "one exact original actual_receipt declaration"
    );
    let receipt = receipts[0];
    assert_eq!(
        receipt.kind,
        clean_olean::ConstantKind::Theorem,
        "receipt is a theorem"
    );
    assert!(
        receipt.value.is_some(),
        "receipt retains its original proof body"
    );
    assert_eq!(
        constant_occurrences(
            receipt
                .type_
                .as_ref()
                .expect("complete original receipt type"),
            "KCheckSpec.EntryKind.familyConstant"
        ),
        1,
        "output mutation changes exactly one literal receipt-kind occurrence",
    );
}

#[test]
fn atomic_bool_admission_rechecks_all_owned_bodies_and_exact_controls() {
    assert_single_receipt_kind_occurrence();
    standalone_theory::qualify(&Package {
        family: "kcheck_bool_admission",
        source_root: "KCheckBoolAdmission",
        fixture_root: "AtomicBoolQualification",
        module_count: 7,
        lake_includes_root: true,
        root_imports_init: true,
        mint_env: "CLEAN_MINT_KCHECK_BOOL_ADMISSION_PINS",
        theories: &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_labelled",
            "kcheck_rule_certificates",
            "kcheck_bool_island",
            "kcheck_bool_admission",
        ],
        fixture_modules: &[
            "KCheckBoolAdmission",
            "AtomicBoolContracts",
            "AtomicBoolQualification",
        ],
        contract_pairs: include_str!(
            "fixtures/lean/v4.30.0-rc2/kcheck_bool_admission/CONTRACTS.json"
        ),
        contract_count: 46,
        data_pairs: &[],
        mutations: &[
            Mutation {
                proof: "KCheckBoolAdmission.check_sound",
                literal: "AtomicBoolContracts.omittedInitialValidity",
                change: Change::DeleteBinder(8),
            },
            Mutation {
                proof: "KCheckBoolAdmission.install_valid",
                literal: "AtomicBoolContracts.omittedIndexedClosure",
                change: Change::DeleteBinder(3),
            },
            Mutation {
                proof: "KCheckBoolAdmission.install_eq",
                literal: "AtomicBoolContracts.omittedFreshness",
                change: Change::DeleteBinder(2),
            },
            Mutation {
                proof: "KCheckBoolAdmission.Cases.actual_receipt",
                literal: "AtomicBoolContracts.wrongReceiptKind",
                change: Change::ReplaceConstant(
                    "KCheckSpec.EntryKind.familyConstant",
                    "KCheckSpec.EntryKind.definition",
                ),
            },
        ],
        dependencies: &[
            "KCheck.ordinaryParts",
            "KCheck.checkOrdinary",
            "KCheck.Advice.start",
            "KCheck.splitFramesAux",
            "KCheck.checkOrdinary_sound",
            "KCheck.CompleteSound.block_sound",
            "KCheck.EnvTransport.append_valid",
            "KCheckSpec.Env.find",
            "KCheckSpec.Env.assignment",
            "KCheckSpec.Rooted",
            "KCheckSpec.RootedAt",
            "KCheckSpec.Env.Valid",
            "KCheckSpec.RuleValid",
            "KCheckSpec.FamilyValid",
            "KCheckSpec.FreshSealing.append_env",
            "KCheckSpec.ModelSealing.sealEnv",
            "KCheckSpec.FamilyRegistration.register",
            "KCheckSpec.PSigmaBase.base",
            "KCheckRuleCertificates.TwoNullaryRules.rule_valid",
            "KCheckRuleCertificates.TwoNullaryRules.family_valid",
        ],
    });
}
