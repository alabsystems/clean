// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit S1 (`theories/kcheck_s1_interface`,
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` §5 Lane S row S1;
//! `docs/plans/SELF_PROOF_COMPLETION_MAP_2026-11-15.md` row S1):
//! 100% choice-free (`0` `Classical.choice`) core interface alignment between `KCheck`,
//! `CICL`, and `CICL.Model`:
//! 1. Exact Boolean-to-proposition `WF uvars` decision equivalences (`levelWithin_iff_scoped`,
//!    `exprLevelsWithin_iff_scoped`, `termLevelsWithin_iff_scoped`, `termLevelsScoped_toExpr`)
//!    and global preservation across `whnf`, `inferAnn`, `check`, `checkOrdinary`, `kcheck`,
//!    and `kcheckRun`;
//! 2. Bidirectional (`↔`) `levelsEqv`, `Token.sort` (`sortDF`), and `Token.const` (`constDF`)
//!    decision theorems, `conv_const_to_statementMeaning`, and height-3 semantic refutation
//!    when `levelsEqv` is omitted;
//! 3. De Bruijn index (`bvar`) ↔ context level (`Term.local`) duality, `openAt` / `closeAt`
//!    roundtrip and `closeAt_toExpr` erasure duality, deterministic `.freeVariable`,
//!    `.looseBound`, and `.unknownLocal` refusals, and the exact locally-nameless variable
//!    bridge to `CICL.LocalContextRules` (`NamedContext` / `inferFVar`);
//! 4. Explicit `envToSignature : Env → CICL.Signature Unit` projection, `envToSignature_base`,
//!    `kcheck_ordinary_envToSignature`, `kcheckRun_extends_baseSignature`, set-model assignment
//!    alignment, and a 4-declaration universe-polymorphic `kcheckRun` + semantic soundness
//!    theorem, dual-kernel qualified through pinned Lean's `leanchecker --fresh` and Clean's
//!    empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`{propext, Quot.sound}`;
//!    `Classical.choice` is verified absent from every declaration in `KCheckS1Interface`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this standalone S1 package flips no authority and retains
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
    "KCheckS1Interface.LevelScopeAndConstDF",
    "KCheckS1Interface.DepthAndFreeVars",
    "KCheckS1Interface.EnvSignatureLink",
    "KCheckS1Interface.Contracts",
    "KCheckS1Interface",
];

const EXECUTABLE_S1_DEFS: &[&str] = &[
    "KCheckS1Interface.termLevelsWithin",
    "KCheckS1Interface.outOfScopeTypeDecl",
    "KCheckS1Interface.outOfScopeValueDecl",
    "KCheckS1Interface.upRenN",
    "KCheckS1Interface.entryToConstantDecl",
    "KCheckS1Interface.envToSignature",
    "KCheckS1Interface.s1PolyIdType",
    "KCheckS1Interface.s1PolyIdVal",
    "KCheckS1Interface.s1PolyIdDecl",
    "KCheckS1Interface.s1PolyIdAdvice",
    "KCheckS1Interface.s1PolyUnitType",
    "KCheckS1Interface.s1PolyUnitVal",
    "KCheckS1Interface.s1PolyUnitDecl",
    "KCheckS1Interface.s1PolyUnitAdvice",
    "KCheckS1Interface.s1PolySortSwapType",
    "KCheckS1Interface.s1PolySortSwapVal",
    "KCheckS1Interface.s1PolySortSwapDecl",
    "KCheckS1Interface.s1PolySortSwapAdvice",
    "KCheckS1Interface.s1PolyUnitSwapEqType",
    "KCheckS1Interface.s1PolyUnitSwapEqVal",
    "KCheckS1Interface.s1PolyUnitSwapEqDecl",
    "KCheckS1Interface.s1PolyUnitSwapEqAdvice",
    "KCheckS1Interface.s1PolyDecls",
    "KCheckS1Interface.s1PolyAdviceBytes",
    "KCheckS1Interface.Contracts.groundNamedCtx",
    "KCheckS1Interface.Contracts.groundKCheckCtx",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckS1Interface.levelWithin_iff_scoped",
    "KCheckS1Interface.exprLevelsWithin_iff_scoped",
    "KCheckS1Interface.termLevelsWithin_iff_scoped",
    "KCheckS1Interface.termLevelsScoped_toExpr",
    "KCheckS1Interface.termLevelsScoped_instLevels",
    "KCheckS1Interface.envLevelsScoped_base",
    "KCheckS1Interface.whnf_preserves_levelsScoped",
    "KCheckS1Interface.inferAnn_preserves_levelsScoped",
    "KCheckS1Interface.check_preserves_levelsScoped",
    "KCheckS1Interface.checkOrdinary_preserves_levelsScoped",
    "KCheckS1Interface.kcheck_preserves_envLevelsScoped",
    "KCheckS1Interface.kcheckRun_envLevelsScoped",
    "KCheckS1Interface.kcheck_refuses_outOfScope_typeLevel",
    "KCheckS1Interface.kcheck_refuses_outOfScope_valueLevel",
    "KCheckS1Interface.check_refuses_wrong_levelArity",
    "KCheckS1Interface.levelsEqv_iff_levelsSemEq",
    "KCheckS1Interface.conv_sort_iff_semEq",
    "KCheckS1Interface.conv_sort_refuses_nonSemEq",
    "KCheckS1Interface.conv_const_iff_constDF",
    "KCheckS1Interface.conv_const_refuses_mismatch",
    "KCheckS1Interface.conv_const_to_statementMeaning",
    "KCheckS1Interface.constDF_without_levelEqv_refuted_s1",
    "KCheckS1Interface.lookupLocal_index_level_duality",
    "KCheckS1Interface.lookupLocal_out_of_range",
    "KCheckS1Interface.toExpr_local_roundtrip",
    "KCheckS1Interface.openAt_preserves_scoped",
    "KCheckS1Interface.closeAt_preserves_scoped",
    "KCheckS1Interface.closeAt_openAt_id",
    "KCheckS1Interface.openAt_closeAt_id",
    "KCheckS1Interface.closeAt_toExpr",
    "KCheckS1Interface.toExpr_depth_succ_eq_rename",
    "KCheckS1Interface.check_refuses_raw_fvar",
    "KCheckS1Interface.check_refuses_loose_bvar",
    "KCheckS1Interface.inferAnn_refuses_loose_bvar",
    "KCheckS1Interface.inferAnn_refuses_unknown_local",
    "KCheckS1Interface.ctxErases_cons_assumption",
    "KCheckS1Interface.ctxErases_cons_definition",
    "KCheckS1Interface.check_closed_fvar_matches_namedContext",
    "KCheckS1Interface.envToSignature_base",
    "KCheckS1Interface.kcheck_ordinary_envToSignature",
    "KCheckS1Interface.kcheck_inductiveBlock_envToSignature",
    "KCheckS1Interface.kcheckRun_extends_baseSignature",
    "KCheckS1Interface.base_assignment_eq_baseInterpretation",
    "KCheckS1Interface.kcheck_ordinary_assignment_step",
    "KCheckS1Interface.s1PolyDecls_kcheckRun_accepts",
    "KCheckS1Interface.s1PolySortSwap_refl_refused",
    "KCheckS1Interface.s1PolyId_const_refl_refused",
    "KCheckS1Interface.s1PolyUnitSwapEq_model_sound",
    "KCheckS1Interface.Contracts.ground_s1_polyRun_accepts_and_extends_baseSignature",
    "KCheckS1Interface.Contracts.ground_s1_sortDF_conv_and_refl_refused",
    "KCheckS1Interface.Contracts.ground_s1_constDF_conv_and_semantic_refutation",
    "KCheckS1Interface.Contracts.ground_s1_namedContext_closed_fvar_roundtrip",
    "KCheckS1Interface.Contracts.not_forged_s1_outOfScope_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_wrong_levelArity_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_sortDF_distinct_levels_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_constDF_distinct_levels_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_raw_fvar_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_loose_bvar_accepted",
    "KCheckS1Interface.Contracts.not_forged_s1_unknown_local_accepted",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckS1Interface.Contracts.twin_s1_polyRun_receipt_names",
    "KCheckS1Interface.Contracts.twin_s1_levelScope_outOfBounds_refusal",
    "KCheckS1Interface.Contracts.twin_s1_sortDF_accepts_max_comm",
    "KCheckS1Interface.Contracts.twin_s1_constDF_accepts_poly_levels",
    "KCheckS1Interface.Contracts.twin_s1_raw_fvar_refused",
    "KCheckS1Interface.Contracts.twin_s1_closed_fvar_checks_to_local",
    "KCheckS1Interface.Contracts.twin_s1_envToSignature_base_eq",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckS1Interface.Contracts.forged_s1_outOfScope_accepted",
    "KCheckS1Interface.Contracts.forged_s1_wrong_levelArity_accepted",
    "KCheckS1Interface.Contracts.forged_s1_sortDF_distinct_levels_accepted",
    "KCheckS1Interface.Contracts.forged_s1_constDF_distinct_levels_accepted",
    "KCheckS1Interface.Contracts.forged_s1_raw_fvar_accepted",
    "KCheckS1Interface.Contracts.forged_s1_loose_bvar_accepted",
    "KCheckS1Interface.Contracts.forged_s1_unknown_local_accepted",
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
fn kcheck_s1_interface_rechecks_through_two_kernels_choice_free_with_core_interface_bridges() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_s1_interface");
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

    let compiled = compiled_exec_kcheck_dir("../../theories/kcheck_s1_interface", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    let root_module = MODULES[MODULES.len() - 1];

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckS1Interface`).
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

    for def_name in EXECUTABLE_S1_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "missing executable S1 definition {def_name}"
        );
        let closure = kernel
            .environment()
            .foundational_axiom_deps(&subject)
            .expect("admitted executable S1 definition");
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "S1 definition {def_name} unexpectedly depends on Classical.choice: {closure:?}"
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
            "{thm_name} must be an admitted theorem of theories/kcheck_s1_interface"
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
            "100% of KCheckS1Interface must be choice-free, but {name} depends on Classical.choice: {closure:?}"
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
                name: Name::from_string(&format!("KCheckS1Interface.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS1Interface.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckS1Interface.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckS1Interface.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_S1_INTERFACE_PINS").is_some() {
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
