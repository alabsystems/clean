// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit C5 (`theories/kcheck_init_slice`, `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! bounded 42-declaration `Init.Prelude` + `Init.Core` slice over `Env.base` (`PUnit`, `Eq`, `Nat`),
//! per-declaration `(usesIota, usesK)` token accounting, disjoint `kcheckOnlyLevelShape`
//! divergence class (`LevelGap.d1`, `LevelGap.Kd3`, `LevelGap.Kd4`), structure/unit-eta
//! refusals (`Unit.ext`, `Prod.eta`), and 12-case zero-acceptance forged corpus,
//! dual-kernel qualified through Lean's independent `leanchecker --fresh` and
//! Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `N`; the `Init` slice extractor is an
//!    unproved interim loader.
//! 2. No generation proves more consistency than its base theory (`Ax0`; all ground slice,
//!    divergence, refusal, and accounting theorems are verified choice-free).
//! 3. By design `KCheck.checker` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this test flips no authority and retains the independent quorum.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{
    ConstantKind, Expr, ExprKind, KernelEnvError, KernelTypeError, Name, ReferenceRefusal,
};
mod exec_kcheck_support;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth, ClosedRecheckOptions,
};
use sha2::{Digest, Sha256};

const MODULES: [&str; 6] = [
    "KCheckInitSlice.Accounting",
    "KCheckInitSlice.InitCorpus",
    "KCheckInitSlice.LevelDivergence",
    "KCheckInitSlice.RefusalCorpus",
    "KCheckInitSlice.Contracts",
    "KCheckInitSlice",
];

const EXECUTABLE_SLICE_DEFS: &[&str] = &[
    "KCheckInitSlice.isIotaToken",
    "KCheckInitSlice.isKToken",
    "KCheckInitSlice.tokensUseIota",
    "KCheckInitSlice.tokensUseK",
    "KCheckInitSlice.adviceBytesUseIotaK",
    "KCheckInitSlice.countVerdictClass",
    "KCheckInitSlice.countAcceptedUsingIota",
    "KCheckInitSlice.countAcceptedUsingK",
    "KCheckInitSlice.isAcceptedFrame",
    "KCheckInitSlice.countAcceptedInCorpus",
    "KCheckInitSlice.env_0",
    "KCheckInitSlice.env_42",
    "KCheckInitSlice.initSliceFrames",
    "KCheckInitSlice.initSliceByteFrames",
    "KCheckInitSlice.initAcceptedRows",
    "KCheckInitSlice.levelDivergenceRows",
    "KCheckInitSlice.structureEtaCorpus",
    "KCheckInitSlice.structureEtaRows",
    "KCheckInitSlice.forgedCorpus",
    "KCheckInitSlice.forgedAuditRows",
    "KCheckInitSlice.fullC5AuditRows",
];

const CHOICE_FREE_SLICE_DEFS: &[&str] = &[
    "KCheckInitSlice.tokensUseIota",
    "KCheckInitSlice.tokensUseK",
    "KCheckInitSlice.adviceBytesUseIotaK",
    "KCheckInitSlice.countVerdictClass",
    "KCheckInitSlice.countAcceptedUsingIota",
    "KCheckInitSlice.countAcceptedUsingK",
    "KCheckInitSlice.isAcceptedFrame",
    "KCheckInitSlice.countAcceptedInCorpus",
    "KCheckInitSlice.env_42",
    "KCheckInitSlice.initAcceptedRows",
    "KCheckInitSlice.levelDivergenceRows",
    "KCheckInitSlice.structureEtaRows",
    "KCheckInitSlice.forgedCorpus",
    "KCheckInitSlice.fullC5AuditRows",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckInitSlice.tokensUseIota_iff",
    "KCheckInitSlice.tokensUseK_iff",
    "KCheckInitSlice.adviceBytesUseIotaK_encode",
    "KCheckInitSlice.kcheckOnlyLevelShape_ne_acceptedBoth",
    "KCheckInitSlice.kcheckOnlyLevelShape_ne_structureEtaRefused",
    "KCheckInitSlice.kcheckOnlyLevelShape_ne_forgedRefused",
    "KCheckInitSlice.class_counts_partition",
    "KCheckInitSlice.countAcceptedInCorpus_eq_zero_iff",
    "KCheckInitSlice.step_1_ok",
    "KCheckInitSlice.step_2_ok",
    "KCheckInitSlice.step_3_ok",
    "KCheckInitSlice.step_4_ok",
    "KCheckInitSlice.step_11_ok",
    "KCheckInitSlice.step_20_ok",
    "KCheckInitSlice.step_21_ok",
    "KCheckInitSlice.step_29_ok",
    "KCheckInitSlice.step_30_ok",
    "KCheckInitSlice.step_42_ok",
    "KCheckInitSlice.initSlice_rooted_valid_N",
    "KCheckInitSlice.initSlice_rooted_valid_two",
    "KCheckInitSlice.initSlice_rooted_valid_three",
    "KCheckInitSlice.initSlice_byteFrames_rooted_valid",
    "KCheckInitSlice.initSlice_id_byte_ok",
    "KCheckInitSlice.initSlice_rfl_byte_ok",
    "KCheckInitSlice.initSlice_cast_eq_byte_ok",
    "KCheckInitSlice.initSlice_accepted_count",
    "KCheckInitSlice.initSlice_iota_count",
    "KCheckInitSlice.initSlice_k_count",
    "KCheckInitSlice.nat_noConfusion_usesIota",
    "KCheckInitSlice.cast_eq_usesK",
    "KCheckInitSlice.levelGap_d1_accepted",
    "KCheckInitSlice.levelGap_Kd3_accepted",
    "KCheckInitSlice.levelGap_Kd4_accepted",
    "KCheckInitSlice.levelGap_d1_byte_accepted",
    "KCheckInitSlice.levelGap_Kd3_byte_accepted",
    "KCheckInitSlice.levelGap_Kd4_byte_accepted",
    "KCheckInitSlice.levelGap_chain_sound_N",
    "KCheckInitSlice.levelDivergence_count",
    "KCheckInitSlice.levelDivergence_zero_merged_into_acceptedBoth",
    "KCheckInitSlice.levelDivergence_zero_merged_into_refused",
    "KCheckInitSlice.unit_ext_refl_refused",
    "KCheckInitSlice.unit_ext_irrel_refused",
    "KCheckInitSlice.unit_ext_etaL_refused",
    "KCheckInitSlice.prod_eta_proj_refused",
    "KCheckInitSlice.structureEtaCorpus_zero_acceptances",
    "KCheckInitSlice.structureEta_refused_count",
    "KCheckInitSlice.forged_1_refused",
    "KCheckInitSlice.forged_4_refused",
    "KCheckInitSlice.forged_10_refused",
    "KCheckInitSlice.forged_12_refused",
    "KCheckInitSlice.forgedCorpus_zero_acceptances",
    "KCheckInitSlice.forgedCorpus_every_member_refused",
    "KCheckInitSlice.fullC5Audit_class_counts",
    "KCheckInitSlice.fullC5Audit_partition",
    "KCheckInitSlice.not_forged_corpus_accepts_one",
    "KCheckInitSlice.not_forged_level_divergence_merged_into_accepted",
    "KCheckInitSlice.not_forged_unit_ext_accepted",
    "KCheckInitSlice.not_forged_cast_eq_no_k",
    "KCheckInitSlice.not_forged_nat_noConfusion_no_iota",
    "KCheckInitSlice.not_forged_type_in_type_accepted",
];

const CHOICE_FREE_THEOREMS: &[&str] = &[
    "KCheckInitSlice.adviceBytesUseIotaK_encode",
    "KCheckInitSlice.class_counts_partition",
    "KCheckInitSlice.countAcceptedInCorpus_eq_zero_iff",
    "KCheckInitSlice.step_4_ok",
    "KCheckInitSlice.step_21_ok",
    "KCheckInitSlice.step_29_ok",
    "KCheckInitSlice.step_42_ok",
    "KCheckInitSlice.initSlice_rooted_valid_N",
    "KCheckInitSlice.nat_noConfusion_usesIota",
    "KCheckInitSlice.cast_eq_usesK",
    "KCheckInitSlice.levelGap_d1_accepted",
    "KCheckInitSlice.levelGap_Kd3_accepted",
    "KCheckInitSlice.levelGap_Kd4_accepted",
    "KCheckInitSlice.levelGap_chain_sound_N",
    "KCheckInitSlice.unit_ext_refl_refused",
    "KCheckInitSlice.unit_ext_irrel_refused",
    "KCheckInitSlice.unit_ext_etaL_refused",
    "KCheckInitSlice.prod_eta_proj_refused",
    "KCheckInitSlice.forgedCorpus_zero_acceptances",
    "KCheckInitSlice.forgedCorpus_every_member_refused",
    "KCheckInitSlice.fullC5Audit_class_counts",
    "KCheckInitSlice.fullC5Audit_partition",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckInitSlice.Contracts.twin_accepted_both_count",
    "KCheckInitSlice.Contracts.twin_level_divergence_count",
    "KCheckInitSlice.Contracts.twin_structure_eta_refused_count",
    "KCheckInitSlice.Contracts.twin_forged_zero_acceptances",
    "KCheckInitSlice.Contracts.twin_iota_k_counts",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckInitSlice.Contracts.forged_corpus_accepts_one",
    "KCheckInitSlice.Contracts.forged_level_divergence_merged_into_accepted",
    "KCheckInitSlice.Contracts.forged_unit_ext_accepted",
    "KCheckInitSlice.Contracts.forged_cast_eq_no_k",
    "KCheckInitSlice.Contracts.forged_nat_noConfusion_no_iota",
    "KCheckInitSlice.Contracts.forged_type_in_type_accepted",
];

fn digest<T: serde::Serialize>(value: &T) -> String {
    Sha256::digest(
        bincode::serde::encode_to_vec(value, bincode::config::standard())
            .expect("canonical kernel bytes"),
    )
    .iter()
    .map(|byte| format!("{byte:02x}"))
    .collect()
}

fn verdict_refl(statement: &Expr) -> Expr {
    let ExprKind::Const(head, levels) = statement.get_app_fn().kind() else {
        panic!("contract statement must be an application of Eq: {statement:?}");
    };
    assert_eq!(
        head,
        &Name::from_string("Eq"),
        "contract statement must have head Eq"
    );
    let args = statement.get_app_args();
    assert_eq!(args.len(), 3, "Eq takes type, lhs, rhs");
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), levels.clone()),
            (*args[0]).clone(),
        ),
        (*args[2]).clone(),
    )
}

fn is_type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

#[test]
fn kcheck_init_slice_rechecks_through_two_kernels_with_c5_accounting_and_zero_forged_acceptances() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_init_slice");
    let descriptor: toml::Value = toml::from_str(
        &std::fs::read_to_string(package.join("lakefile.toml")).expect("package descriptor"),
    )
    .expect("descriptor TOML");
    let roots: Vec<&str> = descriptor["lean_lib"][0]["roots"]
        .as_array()
        .expect("library roots")
        .iter()
        .map(|root| root.as_str().expect("root name"))
        .collect();
    assert_eq!(
        roots, MODULES,
        "every actual module is an explicit library root"
    );
    let order: Vec<String> = std::fs::read_to_string(package.join("ORDER"))
        .expect("package order")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|stem| stem.replace('/', "."))
        .collect();
    assert_eq!(
        order, MODULES,
        "fixture compilation covers exactly the same modules"
    );

    let compiled = exec_kcheck_support::compiled_exec_kcheck_dir(
        "../../theories/kcheck_init_slice",
        &["../../theories/kcheck_loader"],
    );
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckInitSlice`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", MODULES[5]])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .env("PATH", std::env::join_paths(paths).expect("binary path"))
        .output()
        .expect("independent actual closure replay");
    assert!(
        replay.status.success(),
        "leanchecker --fresh {} failed:\n{}\n{}",
        MODULES[5],
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, MODULES[5], &[compiled.clone(), lib])
        .expect("compiled original input");
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();

    let mut raw_exports: BTreeMap<Name, &str> = BTreeMap::new();
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for module in MODULES {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .expect("actual module declarations, including private names");
        for name in artifact.names {
            let prev = raw_exports.insert(name.clone(), module);
            assert!(
                prev.is_none(),
                "duplicate exported structural name {name}: {prev:?} and {module}"
            );
            let text = name.to_string();
            if loaded.get_const(&name).is_none() {
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "{module} declares {name}, absent from loaded env without compiler ._unsafe_rec mark"
                );
                assert!(compiler_copies.insert(text), "{name} declared twice");
                continue;
            }
            assert!(
                !loaded.is_unsafe(&name) && !loaded.is_partial(&name),
                "{module} declares {name} unsafe or partial"
            );
            targets.insert(name);
        }
    }
    for copy in &compiler_copies {
        let def_name = copy
            .strip_suffix("._unsafe_rec")
            .expect("checked when collected");
        assert!(
            targets.contains(&Name::from_string(def_name)),
            "{copy} has no safe definition in targets"
        );
    }

    // Kernel 2: Clean's empty-base fenced ReferenceKernel (`reference_base_closed`).
    let base = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("fenced replay construction");
    assert!(
        base.report.passed() && base.entry_refusals.is_empty(),
        "{}\n{:?}",
        base.report.verdict_sentence(),
        base.entry_refusals
    );
    let mut kernel = base.into_kernel().expect("genuine successful completion");

    // Verify all executable C5 definitions are resident and within foundational Ax0,
    // and that accounting/corpus definitions are choice-free.
    for def_name in EXECUTABLE_SLICE_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "executable slice definition {def_name} missing from targets"
        );
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(&subject).expect("admitted definition");
        closure.extend(
            admitted
                .foundational_axiom_deps(&subject)
                .expect("foundational closure"),
        );
        assert!(
            closure.iter().all(clean_kernel::env::is_foundational_axiom),
            "executable slice definition {def_name} has non-foundational dependency: {closure:?}"
        );
    }
    for def_name in CHOICE_FREE_SLICE_DEFS {
        let subject = Name::from_string(def_name);
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(&subject).expect("admitted definition");
        closure.extend(
            admitted
                .foundational_axiom_deps(&subject)
                .expect("foundational closure"),
        );
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "slice definition {def_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify all ground slice/refusal/accounting theorems are choice-free.
    for thm_name in CHOICE_FREE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(&subject).expect("admitted theorem");
        closure.extend(
            admitted
                .foundational_axiom_deps(&subject)
                .expect("foundational closure"),
        );
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "slice theorem {thm_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify every headline C5 theorem is an admitted theorem of theories/kcheck_init_slice.
    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_init_slice"
        );
    }

    let mut statements = BTreeMap::new();
    let mut meanings = BTreeMap::new();
    let mut closures = BTreeMap::new();
    for name in &targets {
        let c = loaded.get_const(name).expect("target exists");
        let params: Vec<String> = c.level_params.iter().map(ToString::to_string).collect();
        if c.kind != ConstantKind::Theorem {
            meanings.insert(
                name.to_string(),
                digest(&(format!("{:?}", c.kind), &params, &c.type_, &c.value)),
            );
            continue;
        }
        statements.insert(name.to_string(), digest(&(&params, &c.type_)));
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(name).expect("admitted target");
        closure.extend(
            admitted
                .foundational_axiom_deps(name)
                .expect("foundational closure"),
        );
        assert!(
            closure.iter().all(clean_kernel::env::is_foundational_axiom),
            "{name} has a domain-specific or trust-marker dependency: {closure:?}"
        );
        closures.insert(
            name.to_string(),
            closure
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
        );
    }

    // Every headline C5 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckInitSlice.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckInitSlice.Controls.headline_false_{idx}")),
            level_params: c.level_params.clone(),
            type_: Expr::const_str("False"),
            value,
        });
        assert!(
            is_type_mismatch(&forged),
            "{thm_name}: wrong statement False must fail by type mismatch, got {forged:?}"
        );
    }

    // Honest twin evaluations pass `Eq.refl` in Clean's ReferenceKernel.
    for (idx, twin_name) in TWIN_CONTRACTS.iter().enumerate() {
        let twin_stmt = loaded
            .get_const(&Name::from_string(twin_name))
            .unwrap_or_else(|| panic!("missing twin contract {twin_name}"))
            .value
            .clone()
            .expect("twin contract proposition body");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckInitSlice.Controls.twin_refl_{idx}")),
                level_params: vec![],
                type_: twin_stmt.clone(),
                value: verdict_refl(&twin_stmt),
            })
            .unwrap_or_else(|e| panic!("Eq.refl failed at honest twin {twin_name}: {e:?}"));
    }

    // Forged acceptance/accounting claims fail `Eq.refl` by TypeMismatch in Clean's ReferenceKernel.
    for (idx, forged_name) in FORGED_CONTRACTS.iter().enumerate() {
        let forged_stmt = loaded
            .get_const(&Name::from_string(forged_name))
            .unwrap_or_else(|| panic!("missing forged contract {forged_name}"))
            .value
            .clone()
            .expect("forged contract proposition body");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckInitSlice.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_INIT_SLICE_PINS").is_some() {
        std::fs::write(
            package.join("statement_pins.json"),
            format!(
                "{}\n",
                serde_json::to_string_pretty(&statements).expect("json")
            ),
        )
        .expect("write statement_pins.json");
        std::fs::write(
            package.join("meaning_pins.json"),
            format!(
                "{}\n",
                serde_json::to_string_pretty(&meanings).expect("json")
            ),
        )
        .expect("write meaning_pins.json");
        std::fs::write(
            package.join("axiom_closures.json"),
            format!(
                "{}\n",
                serde_json::to_string_pretty(&closures).expect("json")
            ),
        )
        .expect("write axiom_closures.json");
    }

    let expected_statements: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("statement_pins.json"))
            .expect("reviewed statement_pins.json is required"),
    )
    .expect("statement_pins.json");
    let expected_meanings: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("meaning_pins.json"))
            .expect("reviewed meaning_pins.json is required"),
    )
    .expect("meaning_pins.json");
    let expected_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        &std::fs::read_to_string(package.join("axiom_closures.json"))
            .expect("reviewed axiom_closures.json is required"),
    )
    .expect("axiom_closures.json");

    assert_eq!(
        statements, expected_statements,
        "exact theorem statements and universe parameters"
    );
    assert_eq!(
        meanings, expected_meanings,
        "exact non-theorem kernel meanings"
    );
    assert_eq!(
        closures, expected_closures,
        "exact foundational axiom closures"
    );
}
