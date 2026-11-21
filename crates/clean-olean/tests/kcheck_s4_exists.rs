// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit S4 / D4 (`theories/kcheck_s4_exists`, `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! choice-free proof-dependent `Exists.{u}` projection typing, beta reduction, and
//! `Prop`-structure eta semantics at `u.eval levels = 0`, paired with universal
//! semantic refutations at `u > 0` (both `reduceProj0` and `inferProj0` + `inferProj1`
//! dependent typing alone on parameter-erased `CICL.Expr.proj`), dual-kernel qualified
//! through pinned Lean's `leanchecker --fresh` and Clean's empty-base fenced
//! `ReferenceKernel` with zero `Classical.choice` across 100% of declarations.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`{propext, Quot.sound}`;
//!    `Classical.choice` is verified absent from every declaration in `KCheckS4Exists`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this standalone S4 package flips no authority and retains
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
    "KCheckS4Exists.Syntax",
    "KCheckS4Exists.Semantics",
    "KCheckS4Exists.Refutations",
    "KCheckS4Exists.Contracts",
    "KCheckS4Exists",
];

const EXECUTABLE_S4_DEFS: &[&str] = &[
    "KCheckS4Exists.existsName",
    "KCheckS4Exists.existsIntroName",
    "KCheckS4Exists.existsRecName",
    "KCheckS4Exists.existsType",
    "KCheckS4Exists.existsIntroType",
    "KCheckS4Exists.existsRecType",
    "KCheckS4Exists.existsRecRule",
    "KCheckS4Exists.existsDecl",
    "KCheckS4Exists.existsIntroDecl",
    "KCheckS4Exists.existsRecDecl",
    "KCheckS4Exists.existsBound",
    "KCheckS4Exists.existsProj0Expr",
    "KCheckS4Exists.existsProj1Expr",
    "KCheckS4Exists.existsProjValidIdx",
    "KCheckS4Exists.existsProjCheckB",
    "KCheckS4Exists.Contracts.existsRecKFlag",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckS4Exists.existsProjCheckB_iff",
    "KCheckS4Exists.existsProjAdmissible_of_alwaysZero",
    "KCheckS4Exists.existsDecl_safe",
    "KCheckS4Exists.existsIntroDecl_safe",
    "KCheckS4Exists.existsRecDecl_safe",
    "KCheckS4Exists.existsType_closed",
    "KCheckS4Exists.existsIntroType_closed",
    "KCheckS4Exists.existsRecType_closed",
    "KCheckS4Exists.existsType_levelScoped",
    "KCheckS4Exists.existsIntroType_levelScoped",
    "KCheckS4Exists.existsRecType_levelScoped",
    "KCheckS4Exists.existsType_typed",
    "KCheckS4Exists.existsDen_typed",
    "KCheckS4Exists.existsIntroDen_typed",
    "KCheckS4Exists.existsRecDen_typed",
    "KCheckS4Exists.existsAssignment_compatible",
    "KCheckS4Exists.inferProj0_meaning",
    "KCheckS4Exists.inferProj1_meaning",
    "KCheckS4Exists.reduceProj0_meaning",
    "KCheckS4Exists.reduceProj1_meaning",
    "KCheckS4Exists.etaStruct_meaning",
    "KCheckS4Exists.validatedExistsProjRule_to_rule",
    "KCheckS4Exists.validatedExistsProjRule_sound",
    "KCheckS4Exists.existsProj0_data_reduction_refuted",
    "KCheckS4Exists.existsProj0_nat_witness_unsound",
    "KCheckS4Exists.existsProj1_dependent_typing_refuted",
    "KCheckS4Exists.Contracts.ground_inferProj0_holds",
    "KCheckS4Exists.Contracts.ground_inferProj1_holds",
    "KCheckS4Exists.Contracts.ground_reduceProj0_holds",
    "KCheckS4Exists.Contracts.ground_reduceProj1_holds",
    "KCheckS4Exists.Contracts.ground_etaStruct_holds",
    "KCheckS4Exists.Contracts.ground_proj0_nat_unsound",
    "KCheckS4Exists.Contracts.ground_proj1_nat_unsound",
    "KCheckS4Exists.not_forged_data_level_admissible",
    "KCheckS4Exists.not_forged_succ_zero_admissible",
    "KCheckS4Exists.not_forged_field_two_valid",
    "KCheckS4Exists.not_forged_exists_bound_zero",
    "KCheckS4Exists.not_forged_exists_rec_k_enabled",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckS4Exists.Contracts.twin_admissible_prop_zero",
    "KCheckS4Exists.Contracts.twin_inadmissible_data_succ",
    "KCheckS4Exists.Contracts.twin_valid_field_indices",
    "KCheckS4Exists.Contracts.twin_exists_bound_at_zero",
    "KCheckS4Exists.Contracts.twin_exists_rec_k_disabled",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckS4Exists.Contracts.forged_data_level_admissible",
    "KCheckS4Exists.Contracts.forged_succ_zero_admissible",
    "KCheckS4Exists.Contracts.forged_field_two_valid",
    "KCheckS4Exists.Contracts.forged_exists_bound_zero",
    "KCheckS4Exists.Contracts.forged_exists_rec_k_enabled",
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
fn kcheck_s4_exists_rechecks_through_two_kernels_choice_free_with_refutation_controls() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_s4_exists");
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

    let compiled = compiled_exec_kcheck_dir("../../theories/kcheck_s4_exists", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckS4Exists`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", MODULES[4]])
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
        MODULES[4],
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, MODULES[4], &[compiled.clone(), lib])
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

    for def_name in EXECUTABLE_S4_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "missing executable S4 definition {def_name}"
        );
        let closure = kernel
            .environment()
            .foundational_axiom_deps(&subject)
            .expect("admitted executable S4 definition");
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "S4 definition {def_name} unexpectedly depends on Classical.choice: {closure:?}"
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
            "{thm_name} must be an admitted theorem of theories/kcheck_s4_exists"
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
            "100% of KCheckS4Exists must be choice-free, but {name} depends on Classical.choice: {closure:?}"
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

    // Every headline S4 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckS4Exists.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS4Exists.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckS4Exists.Controls.twin_refl_{idx}")),
                level_params: vec![],
                type_: twin_stmt.clone(),
                value: verdict_refl(&twin_stmt),
            })
            .unwrap_or_else(|e| panic!("Eq.refl failed at honest twin {twin_name}: {e:?}"));
    }

    // Forged acceptance claims fail `Eq.refl` by TypeMismatch in Clean's ReferenceKernel.
    for (idx, forged_name) in FORGED_CONTRACTS.iter().enumerate() {
        let forged_stmt = loaded
            .get_const(&Name::from_string(forged_name))
            .unwrap_or_else(|| panic!("missing forged contract {forged_name}"))
            .value
            .clone()
            .expect("forged contract proposition body");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS4Exists.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_S4_EXISTS_PINS").is_some() {
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
