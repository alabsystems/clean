// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit C8 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! dual-kernel qualification of `theories/kcheck_eval` (the verified first-order
//! `Nat` evaluator derived rule `0xE0` and successor checker `KCheckEval.checker :
//! KCheckSpec.Checker` inhabiting the **unchanged** pinned `KCheckSpec.C3Owes`
//! obligation of `theories/kcheck_spec`, Decision 8 successor rule).
//!
//! Standing limits:
//! 1. Soundness is per universe bound `height` (and `2 <= height` for `natBound`).
//! 2. No generation proves more consistency than its base theory (`propext`,
//!    `Quot.sound`, `Classical.choice` inherited from `KCheck.CompleteSound`;
//!    zero `Classical.choice` in all executable `KCheckEval` definitions and in
//!    `FOExpr.toTerm_semantics` / `evalEq_definitionEvidence`).
//! 3. By design `KCheckEval.checker` demonstrates the proved-derived-rule successor
//!    extension discipline over `kcheck_spec` without modifying `kcheck_spec`, while
//!    the quorum of independent re-checkers stays; authority does not flip until all
//!    five Plan §2.1 gates hold in fact.

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
    "KCheckEval.Syntax",
    "KCheckEval.Codec",
    "KCheckEval.Semantics",
    "KCheckEval.Checker",
    "KCheckEval.Contracts",
    "KCheckEval",
];

const EXECUTABLE_EVAL_DEFS: &[&str] = &[
    "KCheckEval.termExact",
    "KCheckEval.entryExact",
    "KCheckEval.familyExact",
    "KCheckEval.hasCanonicalBase",
    "KCheckEval.numeralTerm",
    "KCheckEval.natAddTerm",
    "KCheckEval.natPredTerm",
    "KCheckEval.natSubTerm",
    "KCheckEval.natMulTerm",
    "KCheckEval.natPowTerm",
    "KCheckEval.FOExpr.eval",
    "KCheckEval.FOExpr.toTerm",
    "KCheckEval.encodeFOExpr",
    "KCheckEval.encodeEvalFrame",
    "KCheckEval.decodeFOExprAux",
    "KCheckEval.isEvalAdvice",
    "KCheckEval.decodeEvalFrame",
    "KCheckEval.convEvalNat",
    "KCheckEval.checkEvalOrdinary",
    "KCheckEval.kcheck",
    "KCheckEval.kcheckBytes",
    "KCheckEval.kcheckRun",
    "KCheckEval.checker",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckEval.termExact_eq",
    "KCheckEval.entryExact_eq",
    "KCheckEval.familyExact_eq",
    "KCheckEval.hasCanonicalBase_base",
    "KCheckEval.hasCanonicalBase_unpack",
    "KCheckEval.FOExpr.toTerm_citesWithin",
    "KCheckEval.decodeEvalFrame_encodeEvalFrame",
    "KCheckEval.FOExpr.toTerm_semantics",
    "KCheckEval.convEvalNat_sound",
    "KCheckEval.evalEq_definitionEvidence",
    "KCheckEval.checker_startsAtSeed",
    "KCheckEval.isEvalAdvice_encode_false",
    "KCheckEval.kcheck_encode_eq_base",
    "KCheckEval.checkEvalOrdinary_sound",
    "KCheckEval.kcheck_sound_N",
    "KCheckEval.kcheck_sound",
    "KCheckEval.block_sound",
    "KCheckEval.report_upper_bound",
    "KCheckEval.c3Owes",
    "KCheckEval.Contracts.framePowAdd_size",
    "KCheckEval.Contracts.eval_powAdd_accepted",
    "KCheckEval.Contracts.frameSubMul_size",
    "KCheckEval.Contracts.eval_subMul_accepted",
    "KCheckEval.Contracts.framePredSucc_size",
    "KCheckEval.Contracts.eval_predSucc_def_accepted",
    "KCheckEval.Contracts.eval_underflow_accepted",
    "KCheckEval.Contracts.mixed_stream_accepted",
    "KCheckEval.Contracts.infer_admitted_eval_const_ok",
    "KCheckEval.Contracts.refuse_false_equality",
    "KCheckEval.Contracts.refuse_axiom_with_eval_frame",
    "KCheckEval.Contracts.refuse_mismatched_refl_body",
    "KCheckEval.Contracts.refuse_trailing_bytes",
    "KCheckEval.Contracts.refuse_truncated_frame",
    "KCheckEval.Contracts.refuse_nonminimal_leb128",
    "KCheckEval.Contracts.refuse_missing_canonical_base",
    "KCheckEval.Contracts.refuse_duplicate_name",
];

const CHOICE_FREE_THEOREMS: &[&str] = &[
    "KCheckEval.decodeEvalFrame_encodeEvalFrame",
    "KCheckEval.FOExpr.toTerm_semantics",
    "KCheckEval.convEvalNat_sound",
    "KCheckEval.evalEq_definitionEvidence",
    "KCheckEval.checker_startsAtSeed",
    "KCheckEval.isEvalAdvice_encode_false",
    "KCheckEval.kcheck_encode_eq_base",
    "KCheckEval.checkEvalOrdinary_sound",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckEval.Contracts.twin_checker_startsAtSeed",
    "KCheckEval.Contracts.twin_eval_powAdd_accepted",
    "KCheckEval.Contracts.twin_mixed_stream_accepted",
    "KCheckEval.Contracts.twin_refuse_false_equality",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckEval.Contracts.forged_eval_powAdd_refused",
    "KCheckEval.Contracts.forged_false_equality_accepted",
    "KCheckEval.Contracts.forged_axiom_accepted",
    "KCheckEval.Contracts.forged_trailing_accepted",
    "KCheckEval.Contracts.forged_nonminimal_accepted",
    "KCheckEval.Contracts.forged_missing_base_accepted",
    "KCheckEval.Contracts.forged_token_is_eval_advice",
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
fn kcheck_eval_rechecks_through_two_kernels_with_unchanged_c3_owes_and_forged_controls() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_eval");
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

    let compiled = exec_kcheck_support::compiled_exec_kcheck_dir("../../theories/kcheck_eval", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckEval`).
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

    // Verify Decision 8 successor invariant directly on kernel AST:
    // `KCheckEval.c3Owes` has exact Pi type
    // `KCheckSpec.C3Owes.{u} KCheck.checker -> KCheckSpec.C3Owes.{u} KCheckEval.checker`
    // over the unchanged pinned obligation from `theories/kcheck_spec`.
    let c3_owes_info = loaded
        .get_const(&Name::from_string("KCheckEval.c3Owes"))
        .expect("KCheckEval.c3Owes must exist");
    assert_eq!(c3_owes_info.kind, ConstantKind::Theorem);
    assert_eq!(
        c3_owes_info.level_params.len(),
        1,
        "KCheckEval.c3Owes must be universe-polymorphic in u"
    );
    let u_param = clean_kernel::Level::param(c3_owes_info.level_params[0].clone());
    let expected_c3_head = Expr::const_(Name::from_string("KCheckSpec.C3Owes"), vec![u_param]);
    let ExprKind::Pi(_, c3_dom, c3_body) = c3_owes_info.type_.kind() else {
        panic!(
            "KCheckEval.c3Owes type must be `KCheckSpec.C3Owes KCheck.checker -> KCheckSpec.C3Owes KCheckEval.checker`, got {:?}",
            c3_owes_info.type_
        );
    };
    let ExprKind::App(dom_head, dom_arg) = c3_dom.kind() else {
        panic!("KCheckEval.c3Owes domain must be an application, got {c3_dom:?}");
    };
    assert_eq!(
        dom_head.get_app_fn(),
        &expected_c3_head,
        "KCheckEval.c3Owes premise must be KCheckSpec.C3Owes"
    );
    assert_eq!(
        dom_arg.as_ref(),
        &Expr::const_str("KCheck.checker"),
        "KCheckEval.c3Owes premise argument must be KCheck.checker"
    );
    let ExprKind::App(c3_head, c3_arg) = c3_body.kind() else {
        panic!(
            "KCheckEval.c3Owes conclusion must be an application `KCheckSpec.C3Owes KCheckEval.checker`, got {c3_body:?}"
        );
    };
    assert_eq!(
        c3_head.get_app_fn(),
        &expected_c3_head,
        "KCheckEval.c3Owes must inhabit the unchanged KCheckSpec.C3Owes obligation"
    );
    assert_eq!(
        c3_arg.as_ref(),
        &Expr::const_str("KCheckEval.checker"),
        "KCheckEval.c3Owes argument must be KCheckEval.checker"
    );

    // Verify all executable evaluator/checker definitions are resident and choice-free.
    for def_name in EXECUTABLE_EVAL_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "executable evaluator definition {def_name} missing from targets"
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

    // Verify the new evaluator soundness proofs themselves are choice-free.
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
            "evaluator theorem {thm_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify every headline C8 theorem is an admitted theorem of theories/kcheck_eval.
    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_eval"
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

    // Every headline C8 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckEval.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckEval.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckEval.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckEval.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_EVAL_PINS").is_some() {
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
