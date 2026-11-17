// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan units M5 (widened labelled quotation bridge) and M6 (proved receipt
//! level-bound consumer gate) (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! dual-kernel qualification of `theories/kcheck_m5_m6` through Lean's independent
//! `leanchecker --fresh` and Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `N` (`receipt.bound.eval (pad values) <= N`).
//! 2. No generation proves more consistency than its base theory (`propext` and `Quot.sound`
//!    for all generic M5/M6 theorems; `Classical.choice` enters only in the concrete
//!    `TowerRealizer.two` / `three` wrappers via `UniverseTower.indexedUnionClosed_two`/`three`).
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

const MODULES: [&str; 4] = [
    "KCheckM5M6.Quotation",
    "KCheckM5M6.BoundGate",
    "KCheckM5M6.Contracts",
    "KCheckM5M6",
];

const EXECUTABLE_M5_M6_DEFS: &[&str] = &[
    "KCheckM5M6.natTerm",
    "KCheckM5M6.natZeroTerm",
    "KCheckM5M6.natSuccTerm",
    "KCheckM5M6.addFnTerm",
    "KCheckM5M6.mulFnTerm",
    "KCheckM5M6.arithWeaken",
    "KCheckM5M6.arithQuoteTerm",
    "KCheckM5M6.hostQuoteTermAt",
    "KCheckM5M6.WidenedFormulaAt.toHost",
    "KCheckM5M6.WidenedFormula.quote",
    "KCheckM5M6.checkReportWithinBound",
    "KCheckM5M6.checkReceiptWithinBound",
    "KCheckM5M6.checkArityReceiptWithinBound",
    "KCheckM5M6.eqzOrdinary",
    "KCheckM5M6.eqzRunResult",
    "KCheckM5M6.eqzGateAt",
    "KCheckM5M6.oneParamOffsetReceipt",
    "KCheckM5M6.idNatGateAtTwo",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckM5M6.arithWeaken_meaning",
    "KCheckM5M6.arithQuoteTerm_toExpr",
    "KCheckM5M6.arithQuoteTerm_scoped",
    "KCheckM5M6.arithQuoteTerm_baseNames",
    "KCheckM5M6.hostQuoteTermAt_toExpr",
    "KCheckM5M6.hostQuoteTermAt_scoped",
    "KCheckM5M6.hostQuoteTermAt_baseNames",
    "KCheckM5M6.WidenedFormulaAt.toHost_holdsAt",
    "KCheckM5M6.WidenedFormulaAt.ofHostFormulaAt_toHost",
    "KCheckM5M6.WidenedFormulaAt.ofFormulaAt_holdsAt",
    "KCheckM5M6.WidenedFormula.quote_toExpr",
    "KCheckM5M6.widenedQuote_closed",
    "KCheckM5M6.widenedQuote_baseNames",
    "KCheckM5M6.widenedQuote_correct",
    "KCheckM5M6.widenedQuote_sound",
    "KCheckM5M6.badLeZeroOne_refuted",
    "KCheckM5M6.widenedOrderArithFormula_holds_in_model",
    "KCheckM5M6.checkReportWithinBound_iff",
    "KCheckM5M6.checkReceiptWithinBound_iff",
    "KCheckM5M6.checkArityReceiptWithinBound_iff",
    "KCheckM5M6.checkReceiptWithinBound_mono",
    "KCheckM5M6.checkReceiptWithinBound_refuses_above",
    "KCheckM5M6.checkReceiptWithinBound_refuses_nonTheorem",
    "KCheckM5M6.checkArityReceiptWithinBound_refuses_arity",
    "KCheckM5M6.consumer_gate_receipt_sound",
    "KCheckM5M6.consumer_gate_widened_holds",
    "KCheckM5M6.consumer_gate_widened_holds_two",
    "KCheckM5M6.consumer_gate_widened_holds_three",
    "KCheckM5M6.run_consumer_gate_widened_holds",
    "KCheckM5M6.eqz_accepted_at_two",
    "KCheckM5M6.eqz_refused_at_one",
    "KCheckM5M6.eqz_holds_end_to_end",
    "KCheckM5M6.polyReceipt_accepted_at_two",
    "KCheckM5M6.polyReceipt_refused_above_two",
    "KCheckM5M6.polyReceipt_refused_wrong_arity",
    "KCheckM5M6.idNat_definition_refused",
];

const CHOICE_FREE_THEOREMS: &[&str] = &[
    "KCheckM5M6.WidenedFormulaAt.toHost_holdsAt",
    "KCheckM5M6.widenedQuote_closed",
    "KCheckM5M6.widenedQuote_baseNames",
    "KCheckM5M6.widenedQuote_correct",
    "KCheckM5M6.widenedQuote_sound",
    "KCheckM5M6.badLeZeroOne_refuted",
    "KCheckM5M6.widenedOrderArithFormula_holds_in_model",
    "KCheckM5M6.checkReceiptWithinBound_iff",
    "KCheckM5M6.checkArityReceiptWithinBound_iff",
    "KCheckM5M6.checkReceiptWithinBound_refuses_above",
    "KCheckM5M6.checkReceiptWithinBound_refuses_nonTheorem",
    "KCheckM5M6.checkArityReceiptWithinBound_refuses_arity",
    "KCheckM5M6.consumer_gate_receipt_sound",
    "KCheckM5M6.consumer_gate_widened_holds",
    "KCheckM5M6.run_consumer_gate_widened_holds",
    "KCheckM5M6.eqz_accepted_at_two",
    "KCheckM5M6.eqz_refused_at_one",
    "KCheckM5M6.polyReceipt_accepted_at_two",
    "KCheckM5M6.polyReceipt_refused_above_two",
    "KCheckM5M6.polyReceipt_refused_wrong_arity",
    "KCheckM5M6.idNat_definition_refused",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckM5M6.Contracts.twin_eqz_accepted_at_two",
    "KCheckM5M6.Contracts.twin_eqz_refused_at_one",
    "KCheckM5M6.Contracts.twin_poly_accepted_at_two",
    "KCheckM5M6.Contracts.twin_poly_refused_above_two",
    "KCheckM5M6.Contracts.twin_poly_refused_wrong_arity",
    "KCheckM5M6.Contracts.twin_idNat_definition_refused",
    "KCheckM5M6.Contracts.twin_widenedOrderFormula_baseNames",
    "KCheckM5M6.Contracts.twin_widenedOrderFormula_scopedB",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckM5M6.Contracts.forged_eqz_accepted_at_one",
    "KCheckM5M6.Contracts.forged_poly_accepted_above_two",
    "KCheckM5M6.Contracts.forged_poly_accepted_wrong_arity",
    "KCheckM5M6.Contracts.forged_idNat_definition_accepted",
    "KCheckM5M6.Contracts.forged_sortFour_accepted_at_three",
    "KCheckM5M6.Contracts.forged_widenedOrderFormula_unscoped",
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
fn kcheck_m5_m6_rechecks_through_two_kernels_with_choice_free_bridge_and_bound_refusals() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_m5_m6");
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
        exec_kcheck_support::compiled_exec_kcheck_dir("../../theories/kcheck_m5_m6", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckM5M6`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", MODULES[3]])
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
        MODULES[3],
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, MODULES[3], &[compiled.clone(), lib])
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

    // Verify `widenedQuote_sound` inhabits the exact `KCheckSpec.Base.QuoteSound` schema.
    let quote_sound_info = loaded
        .get_const(&Name::from_string("KCheckM5M6.widenedQuote_sound"))
        .expect("KCheckM5M6.widenedQuote_sound must exist");
    assert_eq!(quote_sound_info.kind, ConstantKind::Theorem);
    assert_eq!(
        quote_sound_info.level_params.len(),
        1,
        "KCheckM5M6.widenedQuote_sound must be universe-polymorphic in u"
    );
    assert_eq!(
        quote_sound_info.type_.get_app_fn(),
        &Expr::const_(
            Name::from_string("KCheckSpec.Base.QuoteSound"),
            vec![clean_kernel::Level::param(
                quote_sound_info.level_params[0].clone()
            )]
        ),
        "KCheckM5M6.widenedQuote_sound head must be KCheckSpec.Base.QuoteSound"
    );

    // Verify all executable quotation and bound-gate definitions are resident and choice-free.
    for def_name in EXECUTABLE_M5_M6_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "executable M5/M6 definition {def_name} missing from targets"
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

    // Verify all generic M5/M6 theorems and ground evaluations are choice-free.
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
            "M5/M6 theorem {thm_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify every headline M5/M6 theorem is an admitted theorem of theories/kcheck_m5_m6.
    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_m5_m6"
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

    // Exact choice-exception ratchet inside theories/kcheck_m5_m6: only the three
    // concrete `TowerRealizer.two`/`three` wrappers may depend on `Classical.choice`.
    let choice_users: BTreeSet<String> = closures
        .iter()
        .filter(|(_, deps)| deps.contains("Classical.choice"))
        .map(|(name, _)| name.clone())
        .collect();
    let expected_choice_users: BTreeSet<String> = [
        "KCheckM5M6.consumer_gate_widened_holds_three",
        "KCheckM5M6.consumer_gate_widened_holds_two",
        "KCheckM5M6.eqz_holds_end_to_end",
    ]
    .into_iter()
    .map(ToString::to_string)
    .collect();
    assert_eq!(
        choice_users, expected_choice_users,
        "unexpected Classical.choice user in theories/kcheck_m5_m6"
    );

    // Every headline M5/M6 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckM5M6.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckM5M6.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckM5M6.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckM5M6.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_M5_M6_PINS").is_some() {
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
