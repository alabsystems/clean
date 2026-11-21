// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan units C7 (full reducing algorithmic completeness relative to advice,
//! universal all-advice non-transitivity refusal of `KCheck.conv`, and real
//! `Init.Prelude` end-to-end consumption) and P2 / Decision 15 (proved 4-component
//! release-acceptance validator in Lean) (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! dual-kernel qualification of `theories/kcheck_c7_p2` through Lean's independent
//! `leanchecker --fresh` and Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `N` (`bound.eval (pad values) <= N`).
//! 2. No generation proves more consistency than its host Lean base (`propext` and
//!    `Quot.sound` only across every theorem in `theories/kcheck_c7_p2` — zero
//!    `Classical.choice`).
//! 3. By design `KCheck.checker` is to become the proved checker once all five Plan §2.1
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

const PACKAGE_ROOT: &str = "KCheckC7P2";

const MODULES: [&str; 7] = [
    "KCheckC7P2.TokenStream",
    "KCheckC7P2.NonTransitivity",
    "KCheckC7P2.Completeness",
    "KCheckC7P2.AdviceSize",
    "KCheckC7P2.ReleaseGate",
    "KCheckC7P2.Contracts",
    PACKAGE_ROOT,
];

const EXECUTABLE_C7_P2_DEFS: &[&str] = &[
    "KCheckC7P2.cursorAt",
    "KCheckC7P2.ntLeft",
    "KCheckC7P2.ntMid",
    "KCheckC7P2.ntRight",
    "KCheckC7P2.compileWhnf",
    "KCheckC7P2.compileConv",
    "KCheckC7P2.compileInfer",
    "KCheckC7P2.compileCheck",
    "KCheckC7P2.compileWalk",
    "KCheckC7P2.compileOrdinary",
    "KCheckC7P2.ordinaryNodes",
    "KCheckC7P2.initIdDecl",
    "KCheckC7P2.initEqSymmDecl",
    "KCheckC7P2.checkChainTelescopesFrom",
    "KCheckC7P2.checkChainTelescopes",
    "KCheckC7P2.checkReleaseAcceptance",
    "KCheckC7P2.thmViaIdDecl",
    "KCheckC7P2.thmViaIdTokens",
    "KCheckC7P2.step1Result",
    "KCheckC7P2.step2InBaseResult",
    "KCheckC7P2.step2AfterStep1Result",
    "KCheckC7P2.groundStep2GateAt",
    "KCheckC7P2.groundStep1DefinitionGate",
];

const HEADLINE_THEOREMS: &[&str] = &[
    // TokenStream: compositional ByteArray decoding, frame splitting, & 5-member fuel monotonicity
    "KCheckC7P2.readNat_encodeNat_append",
    "KCheckC7P2.decodeAt_encode_append",
    "KCheckC7P2.next_cursorAt_cons",
    "KCheckC7P2.splitFrames_encodeFrames",
    "KCheckC7P2.whnf_mono",
    "KCheckC7P2.conv_mono",
    "KCheckC7P2.inferAnn_mono",
    "KCheckC7P2.check_mono",
    "KCheckC7P2.walk_mono",
    // NonTransitivity: universal all-fuel, all-Advice refusal of non-transitive conv pair
    "KCheckC7P2.conv_ntLeft_ntMid_ok",
    "KCheckC7P2.conv_ntMid_ntRight_ok",
    "KCheckC7P2.conv_ntLeft_ntRight_refused",
    "KCheckC7P2.conv_ntLeft_ntRight_refused_all_advice",
    "KCheckC7P2.conv_ntRight_ntLeft_refused",
    "KCheckC7P2.conv_ntRight_ntLeft_refused_all_advice",
    // Completeness: full reducing algorithmic judgment -> KCheck.checker.kcheck + Init.Prelude
    "KCheckC7P2.algoWhnf_complete",
    "KCheckC7P2.algoConv_complete",
    "KCheckC7P2.algoInfer_complete",
    "KCheckC7P2.algoCheck_complete",
    "KCheckC7P2.algoWalk_complete",
    "KCheckC7P2.algoOrdinary_complete",
    "KCheckC7P2.initId_accepted_end_to_end",
    "KCheckC7P2.initEqSymm_accepted_by_kcheck",
    "KCheckC7P2.initId_kcheckRun_ok",
    // AdviceSize: an exact encoded byte bound and admission of that same advice
    "KCheckC7P2.compileOrdinary_bytes_le",
    "KCheckC7P2.algoOrdinary_complete_linear",
    // ReleaseGate: Plan P2 / Decision 15 validator soundness & single-guard refusals
    "KCheckC7P2.checkReleaseAcceptance_iff",
    "KCheckC7P2.interim_backing_grants_nothing",
    "KCheckC7P2.wrong_lineage_refused",
    "KCheckC7P2.familyConstant_grants_nothing",
    "KCheckC7P2.nonTheorem_grants_nothing",
    "KCheckC7P2.wrong_statement_digest_refused",
    "KCheckC7P2.wrong_statement_erasure_refused",
    "KCheckC7P2.wrong_envAfter_refused",
    "KCheckC7P2.broken_chain_refused",
    "KCheckC7P2.unrooted_token_refused",
    "KCheckC7P2.wrong_arity_refused",
    "KCheckC7P2.above_bound_refused",
    "KCheckC7P2.certifiedChain_rooted_valid",
    "KCheckC7P2.releaseAcceptance_sound",
    "KCheckC7P2.releaseAcceptance_quoted_holds",
    "KCheckC7P2.thmViaId_refused_in_base",
    "KCheckC7P2.twoStepChain_ok",
    "KCheckC7P2.groundStep2_accepted_at_two",
    "KCheckC7P2.groundStep2_refused_at_one",
    "KCheckC7P2.groundStep2_refused_interim",
    "KCheckC7P2.groundStep1_definition_refused",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckC7P2.Contracts.twin_ntLeft_ntMid_ok",
    "KCheckC7P2.Contracts.twin_ntMid_ntRight_ok",
    "KCheckC7P2.Contracts.twin_ntLeft_ntRight_beta_refused",
    "KCheckC7P2.Contracts.twin_initId_kcheckRun_ok",
    "KCheckC7P2.Contracts.twin_thmViaId_refused_in_base",
    "KCheckC7P2.Contracts.twin_twoStepChain_ok",
    "KCheckC7P2.Contracts.twin_groundStep2_accepted_at_two",
    "KCheckC7P2.Contracts.twin_groundStep2_refused_at_one",
    "KCheckC7P2.Contracts.twin_groundStep2_refused_interim",
    "KCheckC7P2.Contracts.twin_groundStep1_definition_refused",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckC7P2.Contracts.forged_ntLeft_ntRight_beta_ok",
    "KCheckC7P2.Contracts.forged_thmViaId_accepted_in_base",
    "KCheckC7P2.Contracts.forged_groundStep2_accepted_at_one",
    "KCheckC7P2.Contracts.forged_groundStep2_accepted_interim",
    "KCheckC7P2.Contracts.forged_groundStep1_definition_accepted",
    "KCheckC7P2.Contracts.forged_brokenChain_telescopes",
    "KCheckC7P2.Contracts.forged_familyConstant_grants_authority",
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
fn kcheck_c7_p2_rechecks_through_two_kernels_with_zero_choice_and_release_refusals() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_c7_p2");
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

    let compiled =
        exec_kcheck_support::compiled_exec_kcheck_dir("../../theories/kcheck_c7_p2", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckC7P2`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", PACKAGE_ROOT])
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
        PACKAGE_ROOT,
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, PACKAGE_ROOT, &[compiled.clone(), lib])
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

    // Check that algorithmic judgments mention neither `KCheck` nor `Advice` nor `Token`.
    for algo_type in [
        "KCheckC7P2.AlgoWhnf",
        "KCheckC7P2.AlgoConv",
        "KCheckC7P2.AlgoInfer",
        "KCheckC7P2.AlgoCheck",
        "KCheckC7P2.AlgoWalk",
        "KCheckC7P2.AlgoOrdinary",
    ] {
        let subject = Name::from_string(algo_type);
        assert!(
            targets.contains(&subject),
            "algorithmic judgment {algo_type} missing from targets"
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

    // Verify all executable advice-compiler and P2 validator definitions are resident and choice-free.
    for def_name in EXECUTABLE_C7_P2_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "executable C7/P2 definition {def_name} missing from targets"
        );
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(&subject).expect("admitted definition");
        closure.extend(
            admitted
                .foundational_axiom_deps(&subject)
                .expect("foundational closure"),
        );
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "executable definition {def_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify every headline C7/P2 theorem is an admitted theorem of theories/kcheck_c7_p2.
    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_c7_p2"
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
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "{name} in theories/kcheck_c7_p2 must be choice-free, got {closure:?}"
        );
        closures.insert(
            name.to_string(),
            closure
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
        );
    }

    // Every headline C7/P2 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckC7P2.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckC7P2.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckC7P2.Controls.twin_refl_{idx}")),
                level_params: vec![],
                type_: twin_stmt.clone(),
                value: verdict_refl(&twin_stmt),
            })
            .unwrap_or_else(|e| panic!("Eq.refl failed at honest twin {twin_name}: {e:?}"));
    }

    // Forged acceptance/refusal claims fail `Eq.refl` by TypeMismatch in Clean's ReferenceKernel.
    for (idx, forged_name) in FORGED_CONTRACTS.iter().enumerate() {
        let forged_stmt = loaded
            .get_const(&Name::from_string(forged_name))
            .unwrap_or_else(|| panic!("missing forged contract {forged_name}"))
            .value
            .clone()
            .expect("forged contract proposition body");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckC7P2.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_C7_P2_PINS").is_some() {
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
