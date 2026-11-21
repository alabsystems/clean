// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit S2 (`theories/kcheck_s2_bool_prod`,
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` §5 Lane S row S2;
//! `docs/plans/SELF_PROOF_COMPLETION_MAP_2026-11-15.md` row S2, amended by D4):
//! 100% choice-free (`0` `Classical.choice`) certificate-slot synthesis, `PSigma.{u, v}`
//! set-model basis, generic certificate-island semantic transport (`certifiedFamily_valid`),
//! end-to-end `Prod.{u, v}` & `Bool` certificate admission + `KCheck.kcheck` + native
//! `Token.iota` + set-model validity, forged/missing/axiom slot refutations, and unconditional
//! `Or` `Prop → Type` large-elimination impossibility:
//! 1. Algorithmic expected-slot builder (`buildExpectedSlots`, `verifyCertificateSlots`,
//!    `stepLicensedByIotaSlot`) checking model formers (`I._model`), constructors (`c._model`),
//!    recursors (`I.rec._model`), iota equations (`I.rec._model.iota_i`), and optional K slots,
//!    deterministically refusing duplicate names, missing slots, axiom/opaque/quotient/unsafe
//!    entries, universe-parameter arity mismatches, and expression mismatches;
//! 2. Constructive `PSigma.{u, v}` set-model carrier (`psigmaCarrier`, `psigmaRecBody`,
//!    `psigmaPrime_basis_laws`) and environment validity (`basePSigma_valid`) extending
//!    `KCheck.base` (`Eq`, `PUnit`, `Nat`) with `PSigma`, `PSigma.mk`, and `PSigma.rec`;
//! 3. Generic certificate-island replay (`kcheckIsland`, `CertAdmissibleBlock`) and semantic
//!    validity transport (`certifiedFamily_valid`) rebinding an `Env.Valid` model of `E_island`
//!    along `blockRenameMap` to an `Env.Valid` model of the installed inductive environment `E'`;
//! 4. End-to-end `Prod.{u, v}` & `Bool` admission (`prodCertSlots_ok`, `kcheckIsland_prod_ok`,
//!    `kcheck_prodBlock_ok`, `whnf_prodRec_mk_ok`, `prodInstalled_valid`; `boolCertSlots_ok`,
//!    `kcheckIsland_bool_ok`, `kcheck_boolBlock_ok`, `whnf_boolRec_false_ok`,
//!    `whnf_boolRec_true_ok`, `boolInstalled_valid`);
//! 5. Forged/missing/axiom slot refutations (`verifyCertificateSlots_refuses_forged_bool_iota0`,
//!    `kcheck_refuses_forgedBoolConcreteIota`, `forgedBoolConcreteIotaTerm_uninhabited`,
//!    `verifyCertificateSlots_refuses_missing_bool_iota1`,
//!    `verifyCertificateSlots_refuses_missing_prod_rec`,
//!    `verifyCertificateSlots_refuses_axiom_bool_iota1`) and unconditional choice-free refutation
//!    of `Or` `Prop → Type` large elimination (`orLargeElimEnv_not_valid`), dual-kernel qualified
//!    through pinned Lean's `leanchecker --fresh` and Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`{propext, Quot.sound}`;
//!    `Classical.choice` is verified absent from every declaration in `KCheckS2BoolProd`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this standalone S2 package flips no authority and retains
//!    the independent re-checker quorum.

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
use exec_kcheck_support::compiled_exec_kcheck_dir;
use sha2::{Digest, Sha256};

const MODULES: [&str; 8] = [
    "KCheckS2BoolProd.SlotBuilder",
    "KCheckS2BoolProd.PSigmaBasis",
    "KCheckS2BoolProd.CertTransport",
    "KCheckS2BoolProd.ProdCert",
    "KCheckS2BoolProd.BoolCert",
    "KCheckS2BoolProd.Refutations",
    "KCheckS2BoolProd.Contracts",
    "KCheckS2BoolProd",
];

const EXECUTABLE_S2_DEFS: &[&str] = &[
    "KCheckS2BoolProd.buildExpectedSlots",
    "KCheckS2BoolProd.verifyCertificateSlots",
    "KCheckS2BoolProd.stepLicensedByIotaSlot",
    "KCheckS2BoolProd.basePSigma",
    "KCheckS2BoolProd.kcheckIsland",
    "KCheckS2BoolProd.blockMatchesSpec",
    "KCheckS2BoolProd.prodSpec",
    "KCheckS2BoolProd.prodBlock",
    "KCheckS2BoolProd.prodCertIsland",
    "KCheckS2BoolProd.prodCertFrames",
    "KCheckS2BoolProd.prodIslandEnv",
    "KCheckS2BoolProd.prodInstalledEnv",
    "KCheckS2BoolProd.prodIotaProbeOk",
    "KCheckS2BoolProd.boolSpec",
    "KCheckS2BoolProd.boolBlock",
    "KCheckS2BoolProd.boolCertIsland",
    "KCheckS2BoolProd.boolCertFrames",
    "KCheckS2BoolProd.boolIslandEnv",
    "KCheckS2BoolProd.boolInstalledEnv",
    "KCheckS2BoolProd.boolProbeFalseOk",
    "KCheckS2BoolProd.boolProbeTrueOk",
    "KCheckS2BoolProd.forgedBoolCertIsland",
    "KCheckS2BoolProd.forgedBoolConcreteIotaDecl",
    "KCheckS2BoolProd.forgedBoolConcreteAdvice",
    "KCheckS2BoolProd.forgedBoolConcreteIotaTerm",
    "KCheckS2BoolProd.boolIslandMissingIota1",
    "KCheckS2BoolProd.prodIslandMissingRec",
    "KCheckS2BoolProd.boolIslandAxiomIota1",
    "KCheckS2BoolProd.orLargeElimSpec",
    "KCheckS2BoolProd.orLargeElimEnv",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckS2BoolProd.stripped_renameConsts",
    "KCheckS2BoolProd.checkUniqueDeclNames_dup",
    "KCheckS2BoolProd.checkOneSlot_missing",
    "KCheckS2BoolProd.checkOneSlot_refuses_axiom",
    "KCheckS2BoolProd.checkOneSlot_refuses_typeMismatch",
    "KCheckS2BoolProd.stepLicensedByIotaSlot_refuses_missing",
    "KCheckS2BoolProd.psigmaCarrier_mem_sort",
    "KCheckS2BoolProd.psigmaRecBody_mk",
    "KCheckS2BoolProd.psigmaRecBody_typed",
    "KCheckS2BoolProd.psigmaPrime_basis_laws",
    "KCheckS2BoolProd.extendValid_valueless_nominal",
    "KCheckS2BoolProd.basePSigma_valid",
    "KCheckS2BoolProd.basePSigma_valid_two",
    "KCheckS2BoolProd.basePSigma_valid_three",
    "KCheckS2BoolProd.certifiedFamily_valid",
    "KCheckS2BoolProd.prodCertSlots_ok",
    "KCheckS2BoolProd.kcheckIsland_prod_ok",
    "KCheckS2BoolProd.prodBlock_certAdmissible",
    "KCheckS2BoolProd.kcheck_prodBlock_ok",
    "KCheckS2BoolProd.whnf_prodRec_mk_ok",
    "KCheckS2BoolProd.prodInstalled_valid",
    "KCheckS2BoolProd.prodInstalled_valid_two",
    "KCheckS2BoolProd.prodInstalled_valid_three",
    "KCheckS2BoolProd.boolCertSlots_ok",
    "KCheckS2BoolProd.kcheckIsland_bool_ok",
    "KCheckS2BoolProd.boolBlock_certAdmissible",
    "KCheckS2BoolProd.kcheck_boolBlock_ok",
    "KCheckS2BoolProd.whnf_boolRec_false_ok",
    "KCheckS2BoolProd.whnf_boolRec_true_ok",
    "KCheckS2BoolProd.boolInstalled_valid",
    "KCheckS2BoolProd.boolInstalled_valid_two",
    "KCheckS2BoolProd.boolInstalled_valid_three",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_forged_bool_iota0",
    "KCheckS2BoolProd.stepLicensedByIotaSlot_refuses_forged_bool_iota0",
    "KCheckS2BoolProd.not_certAdmissible_forged_bool_iota0",
    "KCheckS2BoolProd.kcheck_refuses_forgedBoolConcreteIota",
    "KCheckS2BoolProd.forgedBoolConcreteIotaTerm_uninhabited",
    "KCheckS2BoolProd.forgedBoolConcreteIotaTerm_uninhabited_two",
    "KCheckS2BoolProd.forgedBoolConcreteIotaTerm_uninhabited_three",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_missing_bool_iota1",
    "KCheckS2BoolProd.stepLicensedByIotaSlot_refuses_missing_bool_iota1",
    "KCheckS2BoolProd.not_certAdmissible_missing_bool_iota1",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_missing_prod_rec",
    "KCheckS2BoolProd.not_certAdmissible_missing_prod_rec",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_axiom_bool_iota1",
    "KCheckS2BoolProd.not_certAdmissible_axiom_bool_iota1",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_psigma_or_model",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_missing_or_rec",
    "KCheckS2BoolProd.verifyCertificateSlots_refuses_axiom_or_rec",
    "KCheckS2BoolProd.orLargeElimEnv_not_valid",
    "KCheckS2BoolProd.orLargeElimEnv_not_valid_two",
    "KCheckS2BoolProd.orLargeElimEnv_not_valid_three",
    "KCheckS2BoolProd.Contracts.ground_s2_prod_admission_and_valid",
    "KCheckS2BoolProd.Contracts.ground_s2_bool_admission_and_valid",
    "KCheckS2BoolProd.Contracts.ground_s2_forged_bool_iota_refuted",
    "KCheckS2BoolProd.Contracts.ground_s2_or_large_elim_refuted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_bool_iota0_slots_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_bool_concrete_iota_kcheck_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_missing_bool_iota1_licensed",
    "KCheckS2BoolProd.Contracts.not_forged_s2_missing_prod_rec_slots_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_axiom_bool_iota1_slots_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_psigma_or_model_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_missing_or_rec_accepted",
    "KCheckS2BoolProd.Contracts.not_forged_s2_axiom_or_rec_accepted",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckS2BoolProd.Contracts.twin_s2_prod_cert_slots_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_bool_cert_slots_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_prod_block_kcheck_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_bool_block_kcheck_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_bool_whnf_false_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_bool_whnf_true_ok",
    "KCheckS2BoolProd.Contracts.twin_s2_forged_bool_iota0_refused",
    "KCheckS2BoolProd.Contracts.twin_s2_missing_bool_iota1_refused",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckS2BoolProd.Contracts.forged_s2_bool_iota0_slots_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_bool_concrete_iota_kcheck_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_missing_bool_iota1_licensed",
    "KCheckS2BoolProd.Contracts.forged_s2_missing_prod_rec_slots_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_axiom_bool_iota1_slots_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_psigma_or_model_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_missing_or_rec_accepted",
    "KCheckS2BoolProd.Contracts.forged_s2_axiom_or_rec_accepted",
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
fn kcheck_s2_bool_prod_rechecks_through_two_kernels_choice_free_with_cert_admission_and_refutations(
) {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_s2_bool_prod");
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

    let compiled = compiled_exec_kcheck_dir("../../theories/kcheck_s2_bool_prod", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    let root_module = MODULES[MODULES.len() - 1];

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckS2BoolProd`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", root_module])
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
        "leanchecker --fresh {root_module} failed:\n{}\n{}",
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, root_module, &[compiled.clone(), lib])
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

    for def_name in EXECUTABLE_S2_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "missing executable S2 definition {def_name}"
        );
        let closure = kernel
            .environment()
            .foundational_axiom_deps(&subject)
            .expect("admitted executable S2 definition");
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "S2 definition {def_name} unexpectedly depends on Classical.choice: {closure:?}"
        );
    }

    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_s2_bool_prod"
        );
    }

    let mut statements = BTreeMap::new();
    let mut meanings = BTreeMap::new();
    let mut closures = BTreeMap::new();
    for name in &targets {
        let c = loaded.get_const(name).expect("target exists");
        let params: Vec<String> = c.level_params.iter().map(ToString::to_string).collect();
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
            "100% of KCheckS2BoolProd must be choice-free, but {name} depends on Classical.choice: {closure:?}"
        );
        if c.kind != ConstantKind::Theorem {
            meanings.insert(
                name.to_string(),
                digest(&(format!("{:?}", c.kind), &params, &c.type_, &c.value)),
            );
            continue;
        }
        statements.insert(name.to_string(), digest(&(&params, &c.type_)));
        closures.insert(
            name.to_string(),
            closure
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
        );
    }

    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckS2BoolProd.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS2BoolProd.Controls.headline_false_{idx}")),
            level_params: c.level_params.clone(),
            type_: Expr::const_str("False"),
            value,
        });
        assert!(
            is_type_mismatch(&forged),
            "{thm_name}: wrong statement False must fail by type mismatch, got {forged:?}"
        );
    }

    for (idx, twin_name) in TWIN_CONTRACTS.iter().enumerate() {
        let twin_stmt = loaded
            .get_const(&Name::from_string(twin_name))
            .unwrap_or_else(|| panic!("missing twin contract {twin_name}"))
            .value
            .clone()
            .expect("twin contract proposition body");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckS2BoolProd.Controls.twin_refl_{idx}")),
                level_params: vec![],
                type_: twin_stmt.clone(),
                value: verdict_refl(&twin_stmt),
            })
            .unwrap_or_else(|e| panic!("Eq.refl failed at honest twin {twin_name}: {e:?}"));
    }

    for (idx, forged_name) in FORGED_CONTRACTS.iter().enumerate() {
        let forged_stmt = loaded
            .get_const(&Name::from_string(forged_name))
            .unwrap_or_else(|| panic!("missing forged contract {forged_name}"))
            .value
            .clone()
            .expect("forged contract proposition body");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS2BoolProd.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_S2_BOOL_PROD_PINS").is_some() {
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
