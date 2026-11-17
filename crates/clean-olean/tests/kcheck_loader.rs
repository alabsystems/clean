// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit C6 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! dual-kernel qualification of `theories/kcheck_loader` (the proved pure-Lean
//! NDJSON 3.1.0 declaration export codec, LEB128 advice decoder, `KCheckSpec.Loader
//! KCheck.checker` instantiation, and byte-level `step_sound_N` / `run_rooted_valid`
//! / `step_rooted_receipt_holds` theorems), plus live cross-producer byte-stream
//! interoperability from Q1's Rust `clean_olean::ndjson::write_export` directly into
//! `KCheckLoader.loadDeclaration` inside Clean's empty-base fenced `ReferenceKernel`.
//!
//! Standing limits:
//! 1. Soundness is per universe bound `height`.
//! 2. No generation proves more consistency than its base theory (`propext`,
//!    `Quot.sound`, `Classical.choice` within `Ax0`; binary UTF-8, NDJSON, and
//!    advice token parsers are verified choice-free).
//! 3. By design `kcheck` + `KCheckLoader` are to replace `clean-kernel` as the
//!    compiled checker front-end, while the quorum of independent re-checkers
//!    stays; authority does not flip until all five Plan §2.1 gates hold in fact.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{
    ConstantKind, Expr, ExprKind, KernelEnvError, KernelTypeError, Level, Name, ReferenceRefusal,
};
mod exec_kcheck_support;

use clean_olean::ndjson::{write_export, ExportWriteMeta};
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth, ClosedRecheckOptions,
};
use sha2::{Digest, Sha256};

const MODULES: [&str; 8] = [
    "KCheckLoader.Json",
    "KCheckLoader.Tables",
    "KCheckLoader.Print",
    "KCheckLoader.RoundTrip",
    "KCheckLoader.Refusals",
    "KCheckLoader.Soundness",
    "KCheckLoader.Contracts",
    "KCheckLoader",
];

const EXECUTABLE_LOADER_DEFS: &[&str] = &[
    "KCheckLoader.encUTF8Char",
    "KCheckLoader.decUTF8Char",
    "KCheckLoader.parseNdjson",
    "KCheckLoader.renderNdjson",
    "KCheckLoader.decodeExport",
    "KCheckLoader.printDeclaration",
    "KCheckLoader.loadDeclaration",
    "KCheckLoader.loadDeclarationWithArities",
    "KCheckLoader.decodeAdviceTokens",
    "KCheckLoader.loadAdviceBytes",
    "KCheckLoader.loader",
];

const CHOICE_FREE_LOADER_DEFS: &[&str] = &[
    "KCheckLoader.encUTF8Char",
    "KCheckLoader.decUTF8Char",
    "KCheckLoader.parseNdjson",
    "KCheckLoader.decodeAdviceTokens",
    "KCheckLoader.loadAdviceBytes",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "KCheckLoader.parseNdjson_renderNdjson",
    "KCheckLoader.loadDeclaration_printDeclaration",
    "KCheckLoader.loadDeclaration_printDeclaration_eqBlock",
    "KCheckLoader.loadDeclaration_printDeclaration_punitBlock",
    "KCheckLoader.loadDeclaration_printDeclaration_natBlock",
    "KCheckLoader.loadDeclaration_post",
    "KCheckLoader.decodeAdviceTokens_encode",
    "KCheckLoader.loadAdviceBytes_encode",
    "KCheckLoader.loader_declaration_roundTrip",
    "KCheckLoader.loader_advice_roundTrip",
    "KCheckLoader.loader_declaration_post",
    "KCheckLoader.step_printDeclaration",
    "KCheckLoader.step_sound_N",
    "KCheckLoader.run_rooted_valid",
    "KCheckLoader.run_rooted_valid_two",
    "KCheckLoader.run_rooted_valid_three",
    "KCheckLoader.step_rooted_receipt_holds",
    "KCheckLoader.step_idNat_bytes_ok",
    "KCheckLoader.step_eqz_bytes_ok",
    "KCheckLoader.step_natBlock_bytes_ok",
    "KCheckLoader.step_looseBVar_bytes_refused",
    "KCheckLoader.step_truncatedAdvice_bytes_refused",
    "KCheckLoader.refuse_level_mvar",
    "KCheckLoader.refuse_expr_mvar",
    "KCheckLoader.refuse_fvar",
    "KCheckLoader.refuse_loose_bvar",
    "KCheckLoader.refuse_duplicate_level_param",
    "KCheckLoader.refuse_undeclared_level_param",
    "KCheckLoader.refuse_level_max_arity",
    "KCheckLoader.refuse_level_imax_arity",
    "KCheckLoader.refuse_inductive_pi_arity",
    "KCheckLoader.refuse_inductive_non_sort_target",
    "KCheckLoader.refuse_ctor_pi_arity",
    "KCheckLoader.refuse_ctor_target_spine",
    "KCheckLoader.refuse_bad_constant_arity",
    "KCheckLoader.refuse_duplicate_json_key",
    "KCheckLoader.refuse_leading_zero_json_nat",
    "KCheckLoader.refuse_malformed_natVal_lit",
    "KCheckLoader.refuse_rebound_name_zero",
    "KCheckLoader.refuse_rebound_level_zero",
    "KCheckLoader.refuse_unbound_expr_index",
    "KCheckLoader.refuse_bad_meta_version",
    "KCheckLoader.refuse_duplicate_declaration",
    "KCheckLoader.refuse_missing_declaration",
    "KCheckLoader.refuse_empty_export",
    "KCheckLoader.refuse_advice_unknown_tag",
    "KCheckLoader.refuse_advice_truncated_operand",
    "KCheckLoader.refuse_advice_truncated_leb128",
    "KCheckLoader.refuse_advice_nonminimal_leb128",
    "KCheckLoader.not_wrongLooseBVarAccepted",
    "KCheckLoader.not_wrongLevelMVarAccepted",
    "KCheckLoader.not_wrongDupLevelParamAccepted",
    "KCheckLoader.not_wrongDuplicateKeyAccepted",
    "KCheckLoader.not_wrongTruncatedAdviceAccepted",
];

const TWIN_CONTRACTS: &[&str] = &[
    "KCheckLoader.Contracts.twin_prop_axiom_decoded",
    "KCheckLoader.Contracts.twin_advice_refl_loaded",
    "KCheckLoader.Contracts.twin_duplicate_key_refused",
    "KCheckLoader.Contracts.twin_leading_zero_refused",
];

const FORGED_CONTRACTS: &[&str] = &[
    "KCheckLoader.Contracts.forged_loose_bvar_decoded",
    "KCheckLoader.Contracts.forged_level_mvar_decoded",
    "KCheckLoader.Contracts.forged_dup_level_param_decoded",
    "KCheckLoader.Contracts.forged_undeclared_level_param_decoded",
    "KCheckLoader.Contracts.forged_inductive_arity_decoded",
    "KCheckLoader.Contracts.forged_duplicate_json_key_loaded",
    "KCheckLoader.Contracts.forged_leading_zero_nat_loaded",
    "KCheckLoader.Contracts.forged_rebound_name_zero_decoded",
    "KCheckLoader.Contracts.forged_truncated_advice_decoded",
    "KCheckLoader.Contracts.forged_nonminimal_advice_decoded",
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
fn kcheck_loader_rechecks_through_two_kernels_with_forged_and_rust_export_controls() {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_loader");
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
        exec_kcheck_support::compiled_exec_kcheck_dir("../../theories/kcheck_loader", &[]);
    let lib = require_pinned_lean_lib_path().expect("exact Lean pin");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("toolchain bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel 1: Lean's independent fresh kernel replay (`leanchecker --fresh KCheckLoader`).
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", MODULES[7]])
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
        MODULES[7],
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, MODULES[7], &[compiled.clone(), lib])
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

    // Verify all executable loader definitions are resident and within foundational Ax0,
    // and that the binary UTF-8/NDJSON/advice parser definitions are choice-free.
    for def_name in EXECUTABLE_LOADER_DEFS {
        let subject = Name::from_string(def_name);
        assert!(
            targets.contains(&subject),
            "executable loader definition {def_name} missing from targets"
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
            "executable loader definition {def_name} has non-foundational dependency: {closure:?}"
        );
    }
    for def_name in CHOICE_FREE_LOADER_DEFS {
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
            "binary loader definition {def_name} must be choice-free, got {closure:?}"
        );
    }

    // Verify every headline C6 soundness, round-trip, and refusal theorem is an admitted theorem.
    for thm_name in HEADLINE_THEOREMS {
        let subject = Name::from_string(thm_name);
        let info = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing headline theorem {thm_name}"));
        assert!(
            targets.contains(&subject)
                && info.kind == ConstantKind::Theorem
                && info.value.is_some(),
            "{thm_name} must be an admitted theorem of theories/kcheck_loader"
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

    // Every headline C6 theorem proof re-enters at its own statement and is rejected at False.
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let subject = Name::from_string(thm_name);
        let c = loaded.get_const(&subject).expect("headline theorem");
        let value = c.value.clone().expect("theorem carries proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("KCheckLoader.Controls.headline_ok_{idx}")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|e| panic!("{thm_name} failed at own statement: {e:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("KCheckLoader.Controls.headline_false_{idx}")),
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
                name: Name::from_string(&format!("KCheckLoader.Controls.twin_refl_{idx}")),
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
            name: Name::from_string(&format!("KCheckLoader.Controls.forged_refl_{idx}")),
            level_params: vec![],
            type_: forged_stmt.clone(),
            value: verdict_refl(&forged_stmt),
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl at forged contract {forged_name} must fail by type mismatch, got {bad:?}"
        );
    }

    // Live cross-producer interop: emit NDJSON 3.1.0 bytes from Q1's Rust `write_export`
    // for `axiom P : Prop` and evaluate `KCheckLoader.loadDeclaration (utf8Bytes <rust_ndjson>)`
    // directly inside Clean's empty-base fenced ReferenceKernel via `Eq.refl`!
    let mut export_env = Environment::new();
    export_env
        .add_decl(Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("register axiom P : Prop in fresh export env");
    let export_meta = ExportWriteMeta {
        lean_version: "4.30.0-rc2".to_owned(),
        lean_githash: "0000000000000000000000000000000000000000".to_owned(),
    };
    let mut rust_ndjson_bytes = Vec::new();
    let export_summary = write_export(
        &export_env,
        &BTreeSet::from([Name::from_string("P")]),
        &export_meta,
        &mut rust_ndjson_bytes,
    )
    .expect("write NDJSON 3.1.0 export from Rust writer");
    assert_eq!(export_summary.records, 1);
    let rust_ndjson_str =
        String::from_utf8(rust_ndjson_bytes).expect("write_export emits valid UTF-8");

    let template_stmt = loaded
        .get_const(&Name::from_string(
            "KCheckLoader.Contracts.forged_duplicate_json_key_loaded",
        ))
        .expect("template loadDeclaration equality")
        .value
        .clone()
        .expect("template body");
    let eq_head = template_stmt.get_app_fn().clone();
    let eq_args = template_stmt.get_app_args();
    let load_decl_fn = eq_args[1].get_app_fn().clone();
    let mk_load_eq = |ndjson: &str| -> Expr {
        let bytes_expr = Expr::app(
            Expr::const_str("KCheckLoader.utf8Bytes"),
            Expr::str_lit(ndjson),
        );
        let lhs = Expr::app(load_decl_fn.clone(), bytes_expr);
        Expr::app(
            Expr::app(Expr::app(eq_head.clone(), (*eq_args[0]).clone()), lhs),
            (*eq_args[2]).clone(),
        )
    };

    let rust_interop_stmt = mk_load_eq(&rust_ndjson_str);
    kernel
        .add_checked(Declaration::Theorem {
            name: Name::from_string("KCheckLoader.Controls.rust_write_export_interop_ok"),
            level_params: vec![],
            type_: rust_interop_stmt.clone(),
            value: verdict_refl(&rust_interop_stmt),
        })
        .expect(
            "KCheckLoader.loadDeclaration must decode Q1 Rust write_export bytes to propAxiomDecl",
        );

    let mutated_rust_ndjson = rust_ndjson_str.replacen(
        "\"isUnsafe\":false",
        "\"isUnsafe\":false,\"isUnsafe\":false",
        1,
    );
    assert_ne!(mutated_rust_ndjson, rust_ndjson_str);
    let mutated_interop_stmt = mk_load_eq(&mutated_rust_ndjson);
    let mutated_res = kernel.add_checked(Declaration::Theorem {
        name: Name::from_string("KCheckLoader.Controls.rust_write_export_duplicate_key_forged"),
        level_params: vec![],
        type_: mutated_interop_stmt.clone(),
        value: verdict_refl(&mutated_interop_stmt),
    });
    assert!(
        is_type_mismatch(&mutated_res),
        "duplicate JSON key in Rust export stream must be refused by KCheckLoader: {mutated_res:?}"
    );

    if std::env::var_os("MINT_KCHECK_LOADER_PINS").is_some() {
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
