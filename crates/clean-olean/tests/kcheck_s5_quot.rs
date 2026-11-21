// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit S5 (`theories/kcheck_s5_quot`,
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` §5 Lane S row S5;
//! `docs/plans/SELF_PROOF_COMPLETION_MAP_2026-11-15.md` row S5):
//! 100% choice-free (`0` `Classical.choice`, `0` `IndexedUnionClosed` hypotheses)
//! raw-set equivalence-class interpretation of `Quot`, `Quot.mk`, `Quot.lift`,
//! `Quot.ind`, and `Quot.sound` (`baseQuot_valid`), S5 `.quotient` checker admission
//! with the mandatory `Eq` precondition guard (`checkQuotAdmission`,
//! `checkQuotAdmission_valid`), guarded labelled `Quot.lift` head reduction
//! (`quotLiftStep`, `quotLiftStep_sound`, `quotLiftStep_sound_baseQuot`), end-to-end
//! `KCheck.kcheck` & `KCheck.whnf` execution probes, and semantic/checker refutations:
//! 1. Constructive raw-set equivalence classes (`QuotEqvStep`, `eqvClass`,
//!    `quotCarrierPos`, `quotLiftUnion`) bounded via `tower.power` at `uVal > 0`
//!    and canonical truth values at `uVal = 0`, proving `quotCarrierRaw_mem_sort`,
//!    `quotLiftRaw_beta`, `quotLiftRaw_typed`, `quotIndRaw_typed`, `quotSoundRaw_typed`,
//!    `extendValid_valueless_entries`, `baseQuot_valid`, `baseQuot_valid_two`, and
//!    `baseQuot_valid_three` with zero `Classical.choice` and zero `IndexedUnionClosed`;
//! 2. Explicit `Eq` precondition admission checker (`checkQuotAdmission`) and general
//!    semantic extension theorem (`checkQuotAdmission_valid`), paired with proof that
//!    unextended `KCheck.kcheck` refuses `.quotient` (`kcheck_refuses_quot`);
//! 3. Guarded labelled `Quot.lift` head reduction (`quotLiftStep`) verifying `Eq` and
//!    quotient primitives, level tie `uL ≈ uL'`, parameter ties `αT =ₑ αT'` and
//!    `rT =ₑ rT'`, closedness `Scoped depth 0`, and domain labels (`Dh =ₑ ∀ a b, r a b →
//!    Eq β (f a) (f b)`), with semantic & annotation preservation (`quotLiftStep_sound`,
//!    `quotLiftStep_sound_baseQuot`), plus `KCheck.kcheck` (`quotCarrierAcceptOk_true`)
//!    and `quotLiftStep` + `KCheck.whnf` beta reduction (`quotLiftWhnfBetaOk_true`);
//! 4. Constructive syntactic & semantic refutations (`checkQuotAdmission_refuses_without_eq`,
//!    `checkQuotAdmission_refuses_forged_eq`, `checkQuotAdmission_refuses_duplicate_quot`,
//!    `envWithoutEqQuot_not_valid`, `quotMk_zero_one_related`,
//!    `nat_zero_eq_one_uninhabited_two`, `unguardedQuotLift_unsound`, and
//!    `quotLiftStep_refuses_{forged_resp_domain,mismatched_rel,mismatched_alpha,mismatched_level}`),
//!    dual-kernel qualified through pinned Lean's `leanchecker --fresh` and Clean's
//!    empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`{propext, Quot.sound}`;
//!    `Classical.choice` is verified absent from every declaration in `KCheckS5Quot`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this standalone S5 package flips no authority and retains
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

const MODULES: [&str; 5] = [
    "KCheckS5Quot.QuotBasis",
    "KCheckS5Quot.QuotChecker",
    "KCheckS5Quot.Refutations",
    "KCheckS5Quot.Contracts",
    "KCheckS5Quot",
];

const EXECUTABLE_S5_DEFS: &[&str] = &[
    "KCheckS5Quot.quotEntry",
    "KCheckS5Quot.quotMkEntry",
    "KCheckS5Quot.quotLiftEntry",
    "KCheckS5Quot.quotIndEntry",
    "KCheckS5Quot.quotSoundEntry",
    "KCheckS5Quot.quotNewEntries",
    "KCheckS5Quot.baseQuot",
    "KCheckS5Quot.pinnedEqEntry",
    "KCheckS5Quot.termExactEq",
    "KCheckS5Quot.entryExactEq",
    "KCheckS5Quot.checkQuotAdmission",
    "KCheckS5Quot.quotLiftStep",
    "KCheckS5Quot.quotCarrierDecl",
    "KCheckS5Quot.quotCarrierAdvice",
    "KCheckS5Quot.quotCarrierAcceptOk",
    "KCheckS5Quot.quotLiftProbeRedex",
    "KCheckS5Quot.quotLiftProbeAfterStep",
    "KCheckS5Quot.quotLiftWhnfBetaOk",
    "KCheckS5Quot.emptyEnv",
    "KCheckS5Quot.envForgedEq",
    "KCheckS5Quot.envWithoutEqQuot",
    "KCheckS5Quot.forgedRespDomainRedex",
    "KCheckS5Quot.mismatchedRelRedex",
    "KCheckS5Quot.mismatchedAlphaRedex",
    "KCheckS5Quot.mismatchedLevelRedex",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckS5Quot.step_of_eqvClass_related",
    "KCheckS5Quot.quotCarrierRaw_mem_sort",
    "KCheckS5Quot.quotLiftRaw_beta",
    "KCheckS5Quot.quotLiftRaw_typed",
    "KCheckS5Quot.quotIndRaw_typed",
    "KCheckS5Quot.quotSoundRaw_typed",
    "KCheckS5Quot.extendValid_valueless_entries",
    "KCheckS5Quot.baseQuot_valid",
    "KCheckS5Quot.baseQuot_valid_two",
    "KCheckS5Quot.baseQuot_valid_three",
    "KCheckS5Quot.kcheck_refuses_quot",
    "KCheckS5Quot.termExactEq_eq",
    "KCheckS5Quot.entryExactEq_eq",
    "KCheckS5Quot.sameErasure_value",
    "KCheckS5Quot.value_push_of_scoped0",
    "KCheckS5Quot.checkQuotAdmission_base_ok",
    "KCheckS5Quot.checkQuotAdmission_valid",
    "KCheckS5Quot.quotLiftStep_sound",
    "KCheckS5Quot.quotLiftStep_sound_baseQuot",
    "KCheckS5Quot.quotCarrierAcceptOk_true",
    "KCheckS5Quot.quotLiftStep_probe_ok",
    "KCheckS5Quot.quotLiftWhnfBetaOk_true",
    "KCheckS5Quot.checkQuotAdmission_refuses_without_eq",
    "KCheckS5Quot.checkQuotAdmission_refuses_forged_eq",
    "KCheckS5Quot.checkQuotAdmission_refuses_duplicate_quot",
    "KCheckS5Quot.checkQuotAdmission_refuses_trailing_advice",
    "KCheckS5Quot.envWithoutEqQuot_not_valid",
    "KCheckS5Quot.quotMk_zero_one_related",
    "KCheckS5Quot.nat_zero_eq_one_uninhabited",
    "KCheckS5Quot.nat_zero_eq_one_uninhabited_two",
    "KCheckS5Quot.unguardedQuotLift_unsound",
    "KCheckS5Quot.quotLiftStep_refuses_forged_resp_domain",
    "KCheckS5Quot.quotLiftStep_refuses_mismatched_rel",
    "KCheckS5Quot.quotLiftStep_refuses_mismatched_alpha",
    "KCheckS5Quot.quotLiftStep_refuses_mismatched_level",
    "KCheckS5Quot.Contracts.ground_s5_quot_admission_and_valid",
    "KCheckS5Quot.Contracts.ground_s5_quot_lift_step_and_beta",
    "KCheckS5Quot.Contracts.ground_s5_eq_guard_refuted",
    "KCheckS5Quot.Contracts.ground_s5_unguarded_quot_lift_refuted",
    "KCheckS5Quot.Contracts.not_forged_s5_missing_eq_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_forged_eq_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_duplicate_quot_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_trailing_advice_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_resp_domain_step_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_mismatched_rel_step_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_mismatched_alpha_step_accepted",
    "KCheckS5Quot.Contracts.not_forged_s5_mismatched_level_step_accepted",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckS5Quot.Contracts.twin_s5_quot_admission_base_ok",
    "KCheckS5Quot.Contracts.twin_s5_kcheck_raw_quotient_refused",
    "KCheckS5Quot.Contracts.twin_s5_quot_carrier_kcheck_ok",
    "KCheckS5Quot.Contracts.twin_s5_quot_lift_step_probe_ok",
    "KCheckS5Quot.Contracts.twin_s5_quot_lift_whnf_beta_ok",
    "KCheckS5Quot.Contracts.twin_s5_missing_eq_refused",
    "KCheckS5Quot.Contracts.twin_s5_forged_resp_domain_refused",
    "KCheckS5Quot.Contracts.twin_s5_mismatched_rel_refused",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckS5Quot.Contracts.forged_s5_missing_eq_accepted",
    "KCheckS5Quot.Contracts.forged_s5_forged_eq_accepted",
    "KCheckS5Quot.Contracts.forged_s5_duplicate_quot_accepted",
    "KCheckS5Quot.Contracts.forged_s5_trailing_advice_accepted",
    "KCheckS5Quot.Contracts.forged_s5_resp_domain_step_accepted",
    "KCheckS5Quot.Contracts.forged_s5_mismatched_rel_step_accepted",
    "KCheckS5Quot.Contracts.forged_s5_mismatched_alpha_step_accepted",
    "KCheckS5Quot.Contracts.forged_s5_mismatched_level_step_accepted",
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
fn kcheck_s5_quot_rechecks_through_two_kernels_choice_free_with_quot_admission_lift_and_refutations(
) {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_s5_quot");
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

    let compiled = compiled_exec_kcheck_dir("../../theories/kcheck_s5_quot", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    let root_module = MODULES[MODULES.len() - 1];

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckS5Quot`).
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

    for def_name in EXECUTABLE_S5_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "missing executable S5 definition {def_name}"
        );
        let closure = kernel
            .environment()
            .foundational_axiom_deps(&subject)
            .expect("admitted executable S5 definition");
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "S5 definition {def_name} unexpectedly depends on Classical.choice: {closure:?}"
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
            "{thm_name} must be an admitted theorem of theories/kcheck_s5_quot"
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
            "100% of KCheckS5Quot must be choice-free, but {name} depends on Classical.choice: {closure:?}"
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
                name: Name::from_string(&format!("KCheckS5Quot.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS5Quot.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckS5Quot.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckS5Quot.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_S5_QUOT_PINS").is_some() {
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
