// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit S6 / F1 / Decision 8 (`theories/kcheck_s6_full_binops`,
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! 100% computable, choice-free (`0` `Classical.choice`) 29-declaration
//! `KCheck.kcheckRun` admission (`Nat.pred`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`,
//! `Lean.reduceNat` `.opaqueDecl`, `Bool`, `Bool.false`, `Bool.true`, `Nat.isZero`,
//! `Nat.ble`, `Nat.beq`, `Lean.reduceBool` `.opaqueDecl`, `Nat.ifZero`, `Nat.divFuel`,
//! `Nat.div`, `Nat.mod`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.gcdFuel`, `Nat.gcd`,
//! `Nat.bitOr`, `Nat.bitXor`, `Nat.landFuel`, `Nat.land`, `Nat.lorFuel`, `Nat.lor`,
//! `Nat.xorFuel`, `Nat.xor`), 5-judgment environment extension monotonicity, universal
//! all-`(a, b)` defining-equation `KCheck.conv` reductions across **all 11 `NatBinOp`s**
//! (`add`, `sub`, `mul`, `div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`,
//! `shiftRight`) and both `NatBinPred`s (`ble`, `beq`), `Lean.reduceBool` &
//! `Lean.reduceNat` `deltaOpaque` refusals, and unified choice-free `stdLiteralAssignment`
//! semantic soundness + negative controls, dual-kernel qualified through pinned Lean's
//! `leanchecker --fresh` and Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`{propext, Quot.sound}`;
//!    `Classical.choice` is verified absent from every declaration in `KCheckS6FullBinOps`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six Plan §2.1
//!    conditions hold in fact; this standalone S6/F1 package flips no authority and retains
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

const MODULES: [&str; 6] = [
    "KCheckS6FullBinOps.EnvAndCombinators",
    "KCheckS6FullBinOps.DivModShiftGcdConv",
    "KCheckS6FullBinOps.BitwiseAndAllOpsConv",
    "KCheckS6FullBinOps.Semantics",
    "KCheckS6FullBinOps.Contracts",
    "KCheckS6FullBinOps",
];

const EXECUTABLE_S6_FULL_BINOP_DEFS: &[&str] = &[
    "KCheckS6FullBinOps.natIfZeroDecl",
    "KCheckS6FullBinOps.natDivFuelDecl",
    "KCheckS6FullBinOps.natDivDecl",
    "KCheckS6FullBinOps.natModDecl",
    "KCheckS6FullBinOps.natShiftLeftDecl",
    "KCheckS6FullBinOps.natShiftRightDecl",
    "KCheckS6FullBinOps.natGcdFuelDecl",
    "KCheckS6FullBinOps.natGcdDecl",
    "KCheckS6FullBinOps.natBitOrDecl",
    "KCheckS6FullBinOps.natBitXorDecl",
    "KCheckS6FullBinOps.natLandFuelDecl",
    "KCheckS6FullBinOps.natLandDecl",
    "KCheckS6FullBinOps.natLorFuelDecl",
    "KCheckS6FullBinOps.natLorDecl",
    "KCheckS6FullBinOps.natXorFuelDecl",
    "KCheckS6FullBinOps.natXorDecl",
    "KCheckS6FullBinOps.natFullBinOpEnv",
    "KCheckS6FullBinOps.allFullBinOpDecls",
    "KCheckS6FullBinOps.natFullBinOpRunAdvice",
    "KCheckS6FullBinOps.labelledNatDiv",
    "KCheckS6FullBinOps.labelledNatMod",
    "KCheckS6FullBinOps.labelledNatShiftLeft",
    "KCheckS6FullBinOps.labelledNatShiftRight",
    "KCheckS6FullBinOps.labelledNatGcd",
    "KCheckS6FullBinOps.labelledNatLand",
    "KCheckS6FullBinOps.labelledNatLor",
    "KCheckS6FullBinOps.labelledNatXor",
    "KCheckS6FullBinOps.labelledNatBinOp",
    "KCheckS6FullBinOps.natBinOpConvFuel",
    "KCheckS6FullBinOps.natBinOpConvScript",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckS6FullBinOps.kcheckRun_fullBinOps29_ok",
    "KCheckS6FullBinOps.whnf_env_mono",
    "KCheckS6FullBinOps.conv_env_mono",
    "KCheckS6FullBinOps.inferAnn_env_mono",
    "KCheckS6FullBinOps.check_env_mono",
    "KCheckS6FullBinOps.walk_env_mono",
    "KCheckS6FullBinOps.whnfNatFull_to_conv",
    "KCheckS6FullBinOps.whnf_natRecBinOp_zero",
    "KCheckS6FullBinOps.whnf_natRecBinOp_succ",
    "KCheckS6FullBinOps.conv_natDiv_numerals",
    "KCheckS6FullBinOps.conv_natMod_numerals",
    "KCheckS6FullBinOps.conv_natShiftLeft_numerals",
    "KCheckS6FullBinOps.conv_natShiftRight_numerals",
    "KCheckS6FullBinOps.conv_natGcd_numerals",
    "KCheckS6FullBinOps.conv_natLand_numerals",
    "KCheckS6FullBinOps.conv_natLor_numerals",
    "KCheckS6FullBinOps.conv_natXor_numerals",
    "KCheckS6FullBinOps.conv_all_natBinOp_numerals",
    "KCheckS6FullBinOps.conv_all_natBinPred_numerals",
    "KCheckS6FullBinOps.conv_deltaL_reduceBool_fullBinOp_refused",
    "KCheckS6FullBinOps.conv_deltaL_reduceNat_fullBinOp_refused",
    "KCheckS6FullBinOps.labelledNatBinOp_toExpr",
    "KCheckS6FullBinOps.reduceBinNatOp_lit",
    "KCheckS6FullBinOps.kcheck_all_natBinOp_conv_and_sound",
    "KCheckS6FullBinOps.kcheck_all_natBinPred_fullBinOp_conv_and_sound",
    "KCheckS6FullBinOps.natBinOp_wrongVal_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natDiv_7_2_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natMod_7_3_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natShiftLeft_3_2_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natShiftRight_6_1_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natGcd_6_4_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natLand_5_3_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natLor_5_3_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natXor_5_3_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natBle_fullBinOp_2_3_conv_and_sound",
    "KCheckS6FullBinOps.Contracts.ground_natDiv_7_2_ne_4_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natMod_7_3_ne_2_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natGcd_6_4_ne_3_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natLand_5_3_ne_2_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natLor_5_3_ne_5_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natXor_5_3_ne_7_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natShiftLeft_3_2_ne_10_refuted",
    "KCheckS6FullBinOps.Contracts.ground_natShiftRight_6_1_ne_2_refuted",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natShiftLeft_1_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natShiftRight_1_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natDiv_0_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natGcd_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natLand_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_conv_natXor_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.not_forged_deltaL_reduceNat_fullBinOp_accepted",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckS6FullBinOps.Contracts.twin_kcheck_natDiv_decl_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natShiftLeft_1_0_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natShiftRight_1_0_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natDiv_0_0_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natGcd_0_1_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natLand_0_1_ok",
    "KCheckS6FullBinOps.Contracts.twin_conv_natXor_0_1_ok",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckS6FullBinOps.Contracts.forged_conv_natShiftLeft_1_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_conv_natShiftRight_1_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_conv_natDiv_0_0_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_conv_natGcd_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_conv_natLand_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_conv_natXor_0_1_wrong_val",
    "KCheckS6FullBinOps.Contracts.forged_deltaL_reduceNat_fullBinOp_accepted",
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
fn kcheck_s6_full_binops_rechecks_through_two_kernels_choice_free_across_all_11_nat_binops() {
    let package =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_s6_full_binops");
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

    let compiled = compiled_exec_kcheck_dir(
        "../../theories/kcheck_s6_full_binops",
        &[
            "../../theories/kcheck_s6_string_accel",
            "../../theories/kcheck_s6_nat_arith",
        ],
    );
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    let root_module = MODULES[MODULES.len() - 1];

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckS6FullBinOps`).
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

    for def_name in EXECUTABLE_S6_FULL_BINOP_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "missing executable S6 full-binop definition {def_name}"
        );
        let closure = kernel
            .environment()
            .foundational_axiom_deps(&subject)
            .expect("admitted executable S6 full-binop definition");
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "S6 full-binop definition {def_name} unexpectedly depends on Classical.choice: {closure:?}"
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
            "{thm_name} must be an admitted theorem of theories/kcheck_s6_full_binops"
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
            "100% of KCheckS6FullBinOps must be choice-free, but {name} depends on Classical.choice: {closure:?}"
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

    // Every headline S6 full-binop theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckS6FullBinOps.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckS6FullBinOps.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckS6FullBinOps.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckS6FullBinOps.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    if std::env::var_os("MINT_KCHECK_S6_FULL_BINOPS_PINS").is_some() {
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
