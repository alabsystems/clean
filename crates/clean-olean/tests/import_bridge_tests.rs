// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge tests: compare .olean-loaded Init declarations against handwritten env init.
//!
//! Phase 0 of the .olean-based env init design (designs/2026-02-13-1488-olean-based-env-init.md).
//! Validates that handwritten init_nat/init_bool/init_list/init_option produce declarations
//! with the same universe level parameters as the canonical Lean 4 .olean files.
//!
//! Part of #1488

use clean_kernel::env::{ConstantInfo, Environment, TrustedEnvExt};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::{default_search_paths, load_module_with_deps, load_olean_file, OleanExporter};
use std::path::PathBuf;
use tempfile::tempdir;

fn get_lean_lib_path() -> Option<PathBuf> {
    default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Prelude.olean").exists())
}

/// Gate this file's integration tests behind `CLEAN_OLEAN_INTEGRATION=1`.
/// They load real `.olean` files against the installed Lean toolchain; on
/// machines with a non-matching toolchain they surface compiler-name and
/// inductive-flag differences that reflect Lean version drift rather than
/// real bugs in the import pipeline. Opt in via the env var when running
/// the dedicated integration lane.
fn require_olean_lean() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean integration test skipped \u{2014} set \
             CLEAN_OLEAN_INTEGRATION=1 to run against the installed \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

fn load_olean_prelude(lib_path: &PathBuf) -> Environment {
    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", std::slice::from_ref(lib_path))
        .expect("Failed to load Init.Prelude from .olean");
    env
}

fn load_handwritten_core() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_bool().expect("init_bool");
    env.init_nat().expect("init_nat");
    env.init_list().expect("init_list");
    env.init_option().expect("init_option");
    env
}

/// Load multiple Init .olean modules into a single environment.
fn load_olean_init_extended(lib_path: &PathBuf) -> Environment {
    load_olean_init_extended_strict(lib_path)
}

/// Load multiple Init .olean modules and fail immediately on any load error.
fn load_olean_init_extended_strict(lib_path: &PathBuf) -> Environment {
    let mut env = Environment::default();
    for module in INIT_MODULES_EXTENDED {
        load_module_with_deps(&mut env, module, std::slice::from_ref(lib_path))
            .unwrap_or_else(|e| panic!("Failed to load {module}: {e}"));
    }
    env
}

/// Load comprehensive Init .olean modules into a single environment.
/// Tolerant: skips modules that fail to load (some may have unsupported features).
fn load_olean_init_comprehensive(lib_path: &PathBuf) -> (Environment, usize, usize) {
    let mut env = Environment::default();
    let mut loaded = 0usize;
    let mut failed = 0usize;
    for module in INIT_MODULES_COMPREHENSIVE {
        match load_module_with_deps(&mut env, module, std::slice::from_ref(lib_path)) {
            Ok(_) => loaded += 1,
            Err(e) => {
                println!("  SKIP {module}: {e}");
                failed += 1;
            }
        }
    }
    (env, loaded, failed)
}

/// Load all handwritten data type init functions (data_types.rs + core.rs).
fn load_handwritten_extended() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_heq().expect("init_heq");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_bool().expect("init_bool");
    env.init_nat().expect("init_nat");
    env.init_list().expect("init_list");
    env.init_option().expect("init_option");
    env.init_prod().expect("init_prod");
    env.init_pprod().expect("init_pprod");
    env.init_sigma().expect("init_sigma");
    env.init_subtype().expect("init_subtype");
    env.init_sum().expect("init_sum");
    env.init_psum().expect("init_psum");
    env.init_psigma().expect("init_psigma");
    env.init_empty().expect("init_empty");
    env.init_pempty().expect("init_pempty");
    env.init_ulift().expect("init_ulift");
    env.init_char().expect("init_char");
    env.init_string().expect("init_string");
    env.init_int().expect("init_int");
    env.init_float().expect("init_float");
    // UInt types skipped: init_uint_types depends on Fin which has its own init chain.
    // The 22 init functions above cover the core data_types.rs + core.rs surface area.
    env
}

fn load_handwritten_prelude() -> Environment {
    Environment::try_with_prelude().expect("with_prelude")
}

fn level_param_names(params: &[Name]) -> Vec<String> {
    params.iter().map(|n| n.to_string()).collect()
}

fn canonical_level_param_name(index: usize) -> Name {
    Name::from_string(&format!("u_{index}"))
}

fn canonicalize_level_param_names(ty: &Expr, params: &[Name]) -> Expr {
    let subst: Vec<(Name, Level)> = params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.clone(), Level::param(canonical_level_param_name(i))))
        .collect();
    ty.instantiate_level_params(&subst)
}

fn erase_binder_info(e: &Expr) -> Expr {
    use clean_kernel::expr::{BinderInfo, ExprKind};

    match e.kind() {
        ExprKind::Pi(_, ty, body) => Expr::pi(
            BinderInfo::Default,
            erase_binder_info(ty),
            erase_binder_info(body),
        ),
        ExprKind::Lam(_, ty, body) => Expr::lam(
            BinderInfo::Default,
            erase_binder_info(ty),
            erase_binder_info(body),
        ),
        ExprKind::App(f, a) => Expr::app(erase_binder_info(f), erase_binder_info(a)),
        ExprKind::Let(let_name, ty, val, body, nondep) => Expr::let_named(
            let_name.clone(),
            erase_binder_info(ty),
            erase_binder_info(val),
            erase_binder_info(body),
            *nondep,
        ),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, erase_binder_info(inner))
        }
        _ => e.clone(),
    }
}

const TOPOLOGY_BRIDGE_NAMESPACES: &[&str] = &["Topology.Manifold", "Topology.LieGroup"];
const TOPOLOGY_BRIDGE_SENTINELS: &[&str] = &[
    "Topology.Manifold.Chart",
    "Topology.Manifold.Chart.domain",
    "Topology.Manifold.Chart.toFun",
    "Topology.LieGroup.LieGroup",
    "Topology.LieGroup.LieAlgebraHom",
];

fn is_in_namespace(name: &str, namespace: &str) -> bool {
    name == namespace
        || name
            .strip_prefix(namespace)
            .is_some_and(|suffix| suffix.starts_with('.'))
}

fn is_in_any_namespace(name: &str, namespaces: &[&str]) -> bool {
    namespaces.iter().any(|ns| is_in_namespace(name, ns))
}

fn collect_namespace_constants(env: &Environment, namespaces: &[&str]) -> Vec<ConstantInfo> {
    let mut constants: Vec<ConstantInfo> = env
        .constants()
        .filter(|info| is_in_any_namespace(&info.name.to_string(), namespaces))
        .cloned()
        .collect();
    constants.sort_by_key(|info| info.name.to_string());
    constants
}

fn canonicalized_type_for_compare(type_: &Expr, level_params: &[Name]) -> Expr {
    erase_binder_info(&canonicalize_level_param_names(type_, level_params))
}

fn collect_pi_binders(mut ty: Expr) -> (Vec<Expr>, Expr) {
    let mut binders = Vec::new();
    while let ExprKind::Pi(_, domain, body) = ty.kind() {
        binders.push(domain.as_ref().clone());
        ty = body.as_ref().clone();
    }
    (binders, ty)
}

fn app_head_and_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = expr;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

fn head_const_name(expr: &Expr) -> Option<&Name> {
    let (head, _) = app_head_and_args(expr);
    match head.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    }
}

/// Compare a single constant's level params between two environments.
/// Returns: (matched, mismatched, missing_a, missing_b)
fn compare_const_levels(
    env_a: &Environment,
    env_b: &Environment,
    name_str: &str,
) -> (bool, bool, bool, bool) {
    let name = Name::from_string(name_str);
    match (env_a.get_const(&name), env_b.get_const(&name)) {
        (Some(a), Some(b)) => {
            let matched = a.level_params.len() == b.level_params.len();
            if matched {
                if a.level_params != b.level_params {
                    println!(
                        "    NOTE: {name_str} names differ: a={:?} b={:?}",
                        level_param_names(&a.level_params),
                        level_param_names(&b.level_params),
                    );
                }
            } else {
                println!(
                    "  MISMATCH {name_str}: a={} params, b={} params",
                    a.level_params.len(),
                    b.level_params.len(),
                );
            }
            (matched, !matched, false, false)
        }
        (Some(_), None) => (false, false, false, true),
        (None, Some(_)) => (false, false, true, false),
        (None, None) => (false, false, true, true),
    }
}

/// Compare named constants between environments, returning (matches, mismatches).
fn compare_named_constants(
    env_olean: &Environment,
    env_hw: &Environment,
    constants: &[(&str, usize)],
) -> (u32, u32) {
    let (mut matches, mut mismatches) = (0u32, 0u32);
    for (name_str, expected) in constants {
        let (m, mm, _, _) = compare_const_levels(env_olean, env_hw, name_str);
        if m {
            let actual = env_olean
                .get_const(&Name::from_string(name_str))
                .map(|c| c.level_params.len())
                .unwrap_or(0);
            println!("  MATCH {name_str}: {actual} level params (expected {expected})");
            matches += 1;
        } else if mm {
            mismatches += 1;
        }
    }
    (matches, mismatches)
}

/// Count universe-level overlap between two environments over all hw constants.
/// Returns: (overlap, matches, mismatches, hw_only, mismatched_names)
fn count_full_overlap(
    env_olean: &Environment,
    env_hw: &Environment,
) -> (u32, u32, u32, u32, Vec<String>) {
    let (mut overlap, mut level_match, mut level_mismatch, mut hw_only) = (0u32, 0u32, 0u32, 0u32);
    let mut mismatched_names = Vec::new();
    for ci in env_hw.constants() {
        if let Some(oc) = env_olean.get_const(&ci.name) {
            overlap += 1;
            if ci.level_params.len() == oc.level_params.len() {
                level_match += 1;
            } else {
                level_mismatch += 1;
                mismatched_names.push(format!(
                    "{}: hw={}, olean={}",
                    ci.name,
                    ci.level_params.len(),
                    oc.level_params.len()
                ));
                println!(
                    "  MISMATCH {}: hw={}, olean={}",
                    ci.name,
                    ci.level_params.len(),
                    oc.level_params.len()
                );
            }
        } else {
            hw_only += 1;
        }
    }
    (
        overlap,
        level_match,
        level_mismatch,
        hw_only,
        mismatched_names,
    )
}

/// Core Init types to test: (name, expected_level_param_count)
const CORE_INIT_CONSTANTS: &[(&str, usize)] = &[
    ("Nat", 0),
    ("Nat.succ", 0),
    ("Nat.zero", 0),
    ("Nat.rec", 1),
    ("Bool", 0),
    ("Bool.true", 0),
    ("Bool.false", 0),
    ("Bool.rec", 1),
    ("List", 1),
    ("List.nil", 1),
    ("List.cons", 1),
    ("Option", 1),
    ("Option.none", 1),
    ("Option.some", 1),
    ("Eq", 1),
    ("Eq.refl", 1),
];

/// Extended constants from data_types.rs + core.rs: (name, expected_level_param_count)
const EXTENDED_INIT_CONSTANTS: &[(&str, usize)] = &[
    ("Eq", 1),
    ("Eq.refl", 1),
    ("HEq", 1),
    ("Prod", 2),
    ("Prod.mk", 2),
    ("PProd", 2),
    ("PProd.mk", 2),
    ("Sigma", 2),
    ("Subtype", 1),
    ("Sum", 2),
    ("Sum.inl", 2),
    ("Sum.inr", 2),
    ("PSum", 2),
    ("PSum.inl", 2),
    ("PSum.inr", 2),
    ("PSigma", 2),
    ("PSigma.mk", 2),
    ("Empty", 0),
    ("PEmpty", 1),
    ("ULift", 2),
    ("Bool", 0),
    ("Nat", 0),
    ("List", 1),
    ("Option", 1),
    ("Char", 0),
    ("String", 0),
    ("String.mk", 0),
    ("Int", 0),
    ("Int.ofNat", 0),
    ("Int.negSucc", 0),
    ("Float", 0),
];

/// Init .olean modules to load for extended testing.
const INIT_MODULES_EXTENDED: &[&str] = &[
    "Init.Prelude",
    "Init.Core",
    "Init.Data.Nat.Basic",
    "Init.Data.Int.Basic",
    "Init.Data.Char.Basic",
    "Init.Data.String.Basic",
    "Init.Data.Array.Basic",
    "Init.Data.Option.Basic",
    "Init.Data.List.Basic",
    "Init.Data.Float",
    "Init.Data.UInt.Basic",
];

/// Comprehensive Init .olean modules — maximizes overlap with `try_with_prelude()`.
///
/// Covers: data types, algebra (via Nat/Int arithmetic), classical logic,
/// control structures (State, Id), decidability, ordering, and more.
/// This targets the full 66 init_* functions called by `try_with_prelude()`.
const INIT_MODULES_COMPREHENSIVE: &[&str] = &[
    // Core
    "Init.Prelude",
    "Init.Core",
    // Data types
    "Init.Data.Nat.Basic",
    "Init.Data.Nat.Lemmas",
    "Init.Data.Int.Basic",
    "Init.Data.Int.Lemmas",
    "Init.Data.Char.Basic",
    "Init.Data.String.Basic",
    "Init.Data.Array.Basic",
    "Init.Data.Option.Basic",
    "Init.Data.List.Basic",
    "Init.Data.List.Lemmas",
    "Init.Data.Float",
    "Init.Data.UInt.Basic",
    "Init.Data.Fin.Basic",
    "Init.Data.Sum",
    "Init.Data.Prod",
    "Init.Data.Subtype",
    "Init.Data.ULift",
    "Init.Data.PLift",
    "Init.Data.BEq",
    "Init.Data.Hashable",
    "Init.Data.Zero",
    "Init.Data.OfScientific",
    "Init.Data.Ord",
    "Init.Data.Order",
    // Classical logic and decidability
    "Init.Classical",
    "Init.PropLemmas",
    "Init.ByCases",
    "Init.SizeOf",
    // Control / monadic
    "Init.Control.Basic",
    "Init.Control.State",
    "Init.Control.Id",
    "Init.Control.Reader",
    "Init.Control.Option",
    "Init.Control.Except",
    // Well-founded recursion
    "Init.WF",
    // Coe and notation
    "Init.Coe",
    "Init.Notation",
];

/// Init constants expected to have stable universe-level parameter counts
/// between .olean-loaded declarations and `Environment::with_prelude()`.
const PRELUDE_BRIDGE_CONSTANTS: &[&str] = &[
    "Eq",
    "Eq.refl",
    "HEq",
    "Bool",
    "Bool.true",
    "Bool.false",
    "Nat",
    "Nat.succ",
    "Nat.zero",
    "Nat.rec",
    "List",
    "List.nil",
    "List.cons",
    "Option",
    "Option.none",
    "Option.some",
    "Prod",
    "Prod.mk",
    "Sigma",
    "Subtype",
    "Sum",
    "Sum.inl",
    "Sum.inr",
    "Empty",
    "PEmpty",
    "Char",
    "String",
    "String.mk",
    "Int",
    "Int.ofNat",
    "Int.negSucc",
    "Float",
];

/// Phase 0 bridge requirement for #1488:
/// compare `.olean` Init constants against handwritten prelude init.
#[test]
fn test_bridge_init_vs_with_prelude_level_params() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_init_extended_strict(&lib_path);
    let env_hw = load_handwritten_prelude();
    let mut missing_in_olean = Vec::new();
    let mut missing_in_hw = Vec::new();
    let mut level_mismatches = Vec::new();
    let mut compared = 0u32;

    for name_str in PRELUDE_BRIDGE_CONSTANTS {
        let name = Name::from_string(name_str);
        match (env_olean.get_const(&name), env_hw.get_const(&name)) {
            (Some(oc), Some(hc)) => {
                compared += 1;
                if oc.level_params.len() != hc.level_params.len() {
                    level_mismatches.push(format!(
                        "{name_str}: olean={}, hw={}",
                        oc.level_params.len(),
                        hc.level_params.len()
                    ));
                }
            }
            (Some(_), None) => missing_in_hw.push((*name_str).to_string()),
            (None, Some(_)) => missing_in_olean.push((*name_str).to_string()),
            (None, None) => {
                missing_in_olean.push((*name_str).to_string());
                missing_in_hw.push((*name_str).to_string());
            }
        }
    }

    println!(
        "=== Prelude Bridge: compared={compared}, missing_in_olean={}, missing_in_hw={}, level_mismatches={} ===",
        missing_in_olean.len(),
        missing_in_hw.len(),
        level_mismatches.len(),
    );
    assert!(
        missing_in_olean.is_empty(),
        "Expected all bridge constants in .olean env: {missing_in_olean:?}"
    );
    assert!(
        missing_in_hw.is_empty(),
        "Expected all bridge constants in handwritten prelude env: {missing_in_hw:?}"
    );
    assert!(
        level_mismatches.is_empty(),
        "Universe-level parameter count mismatches: {level_mismatches:?}"
    );
    assert_eq!(
        compared as usize,
        PRELUDE_BRIDGE_CONSTANTS.len(),
        "Expected to compare all bridge constants"
    );
}

/// Phase 0 core test: compare universe level params between .olean-loaded
/// and handwritten Init declarations for Nat, Bool, List, Option.
#[test]
fn test_bridge_init_level_params() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_prelude(&lib_path);
    let env_hw = load_handwritten_core();
    let (matches, mismatches) = compare_named_constants(&env_olean, &env_hw, CORE_INIT_CONSTANTS);

    println!("\n=== Bridge: {matches} match, {mismatches} mismatch ===");
    assert!(
        matches >= 8,
        "Expected >=8 matching constants, got {matches} (mismatches: {mismatches})"
    );
}

/// Extended comparison: check all handwritten constants that also exist in .olean.
#[test]
fn test_bridge_init_overlap_analysis() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_prelude(&lib_path);
    let mut env_hw = Environment::new();
    env_hw.init_eq().expect("init_eq");
    env_hw.init_true_false().expect("init_true_false");
    env_hw.init_and().expect("init_and");
    env_hw.init_bool().expect("init_bool");
    env_hw.init_nat().expect("init_nat");
    env_hw.init_list().expect("init_list");
    env_hw.init_option().expect("init_option");

    let (overlap, level_match, level_mismatch, hw_only, _) =
        count_full_overlap(&env_olean, &env_hw);

    println!("=== Overlap: {overlap} shared, {level_match} match, {level_mismatch} mismatch, {hw_only} hw-only ===");
    assert!(overlap > 0, "Expected overlap > 0");
}

/// Compare type expressions for key constants using TypeChecker.
#[test]
fn test_bridge_init_typecheck_comparison() {
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_prelude(&lib_path);
    let env_hw = load_handwritten_core();
    let key_names: Vec<&str> = CORE_INIT_CONSTANTS.iter().map(|(n, _)| *n).collect();

    let (mut o_ok, mut o_fail, mut h_ok, mut h_fail) = (0u32, 0u32, 0u32, 0u32);
    for name_str in &key_names {
        let name = Name::from_string(name_str);
        if let Some(info) = env_olean.get_const(&name) {
            let tc = TypeChecker::new(&env_olean);
            match tc.infer_type(&info.type_) {
                Ok(_) => o_ok += 1,
                Err(e) => {
                    println!("  .olean TC FAIL {name_str}: {e:?}");
                    o_fail += 1;
                }
            }
        }
        if let Some(info) = env_hw.get_const(&name) {
            let tc = TypeChecker::new(&env_hw);
            match tc.infer_type(&info.type_) {
                Ok(_) => h_ok += 1,
                Err(e) => {
                    println!("  HW TC FAIL {name_str}: {e:?}");
                    h_fail += 1;
                }
            }
        }
    }

    println!("=== TC: olean {o_ok} ok/{o_fail} fail, hw {h_ok} ok/{h_fail} fail ===");
    assert_eq!(o_fail, 0, ".olean constants should all type-check");
}

/// Load Init.Data.Nat.Basic and compare extended Nat operations.
#[test]
fn test_bridge_nat_basic_extended() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env_olean = Environment::default();
    let summaries = load_module_with_deps(
        &mut env_olean,
        "Init.Data.Nat.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Init.Data.Nat.Basic");

    let total: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Init.Data.Nat.Basic: {total} constants ({} modules)",
        summaries.len()
    );

    let mut env_hw = Environment::new();
    env_hw.init_nat().expect("init_nat");

    let nat_consts = [
        "Nat", "Nat.succ", "Nat.zero", "Nat.rec", "Nat.add", "Nat.sub", "Nat.mul",
    ];
    let mut found_both = 0;
    for name_str in &nat_consts {
        let (m, _, _, _) = compare_const_levels(&env_olean, &env_hw, name_str);
        if m {
            found_both += 1;
            println!("  OK {name_str}");
        }
    }

    assert!(
        found_both >= 4,
        "Expected >=4 Nat constants in both envs, got {found_both}"
    );
}

/// Extended Init bridge: compare 31 data_types.rs + core.rs constants against .olean.
///
/// Covers: Int, Char, String, PSigma, Sum, PSum, Empty, PEmpty, ULift,
/// Prod, PProd, Sigma, Subtype, HEq, Float — beyond the core 5.
#[test]
fn test_bridge_init_extended_data_types() {
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_init_extended(&lib_path);
    let env_hw = load_handwritten_extended();

    let (mut matches, mut mismatches) = (0u32, 0u32);
    let (mut tc_ok, mut tc_fail) = (0u32, 0u32);
    for (name_str, expected) in EXTENDED_INIT_CONSTANTS {
        let name = Name::from_string(name_str);
        let hw = env_hw.get_const(&name);
        let ol = env_olean.get_const(&name);
        match (hw, ol) {
            (Some(h), Some(o)) => {
                if h.level_params.len() == o.level_params.len() {
                    matches += 1;
                    println!(
                        "  MATCH {name_str}: {} params (expected {expected})",
                        h.level_params.len()
                    );
                } else {
                    mismatches += 1;
                    println!(
                        "  MISMATCH {name_str}: hw={}, olean={}",
                        h.level_params.len(),
                        o.level_params.len()
                    );
                }
                let tc = TypeChecker::new(&env_hw);
                match tc.infer_type(&h.type_) {
                    Ok(_) => tc_ok += 1,
                    Err(e) => {
                        println!("  HW TC FAIL {name_str}: {e:?}");
                        tc_fail += 1;
                    }
                }
            }
            (Some(_), None) => println!("  HW-ONLY {name_str}"),
            (None, Some(_)) => println!("  OLEAN-ONLY {name_str}"),
            (None, None) => println!("  MISSING {name_str}"),
        }
    }

    println!(
        "\n=== Extended: {matches} match, {mismatches} mismatch, TC: {tc_ok} ok/{tc_fail} fail ==="
    );
    assert_eq!(mismatches, 0, "Expected 0 universe-level mismatches");
    assert!(
        matches >= 20,
        "Expected >=20 matching constants, got {matches}"
    );
}

/// Full overlap: verify 0 universe-level mismatches across ALL handwritten constants.
#[test]
fn test_bridge_init_full_overlap_zero_mismatches() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_init_extended(&lib_path);
    let env_hw = load_handwritten_extended();
    let (overlap, level_match, level_mismatch, hw_only, mismatched_names) =
        count_full_overlap(&env_olean, &env_hw);

    println!("=== Full Overlap: {overlap} shared, {level_match} match, {level_mismatch} mismatch, {hw_only} hw-only ===");
    assert_eq!(
        level_mismatch, 0,
        "Expected 0 universe-level mismatches but found {level_mismatch}: {mismatched_names:?}"
    );
    assert!(
        overlap >= 50,
        "Expected >=50 overlapping constants, got {overlap}"
    );
}

/// Count Pi binders in a type expression, returning the depth.
fn count_pi_binders(ty: &Expr) -> u32 {
    use clean_kernel::expr::ExprKind;
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = t.kind() {
        count += 1;
        t = body.as_ref().clone();
    }
    count
}

/// Collect Sort level from the return type (innermost non-Pi expression).
fn return_sort_display(ty: &Expr) -> String {
    use clean_kernel::expr::ExprKind;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = t.kind() {
        t = body.as_ref().clone();
    }
    format!("{t}")
}

/// Compare type structure for one constant, returning (binder_match, structural_match, def_eq).
fn compare_type_structure(
    name_str: &str,
    env_hw: &Environment,
    env_olean: &Environment,
) -> (bool, bool, Option<bool>) {
    use clean_kernel::tc::TypeChecker;
    let name = Name::from_string(name_str);
    let (Some(hw), Some(ol)) = (env_hw.get_const(&name), env_olean.get_const(&name)) else {
        return (true, false, None);
    };
    let hw_b = count_pi_binders(&hw.type_);
    let ol_b = count_pi_binders(&ol.type_);
    let binder_ok = hw_b == ol_b;
    if !binder_ok {
        println!("  BINDER MISMATCH {name_str}: hw={hw_b}, olean={ol_b}");
    }
    let hw_ret = return_sort_display(&hw.type_);
    let ol_ret = return_sort_display(&ol.type_);
    if hw_ret != ol_ret {
        println!("  RETURN SORT {name_str}: hw={hw_ret}, olean={ol_ret}");
    }
    let structural = hw.type_ == ol.type_;
    if structural {
        println!("  STRUCTURAL MATCH {name_str}");
    } else {
        println!(
            "  STRUCTURAL DIFF {name_str}:\n    hw:    {}\n    olean: {}",
            hw.type_, ol.type_
        );
    }
    let tc = TypeChecker::new(env_hw);
    let def_eq = if tc.infer_type(&hw.type_).is_ok() {
        let eq = tc.is_def_eq(&hw.type_, &ol.type_);
        if !eq {
            println!("  DEF_EQ FAIL {name_str}");
        }
        Some(eq)
    } else {
        None
    };
    (binder_ok, structural, def_eq)
}

/// Phase 0 type-structure bridge: compare Pi binder count, return sort,
/// structural equality, and def_eq between .olean and handwritten Init
/// constants. Catches #1488 Bug Class 1/2.
#[test]
fn test_bridge_init_type_structure_comparison() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let env_olean = load_olean_init_extended(&lib_path);
    let env_hw = load_handwritten_extended();
    let (mut binder_ok, mut structural_ok, mut def_eq_ok, mut def_eq_fail) =
        (0u32, 0u32, 0u32, 0u32);
    let mut failures: Vec<String> = Vec::new();

    for (name_str, _) in EXTENDED_INIT_CONSTANTS {
        let (b, s, d) = compare_type_structure(name_str, &env_hw, &env_olean);
        if b {
            binder_ok += 1;
        } else {
            failures.push(format!("{name_str}: binder mismatch"));
        }
        if s {
            structural_ok += 1;
        }
        match d {
            Some(true) => def_eq_ok += 1,
            Some(false) => def_eq_fail += 1,
            None => {}
        }
    }

    println!("\n=== Type Structure Bridge ===");
    println!("  Binder match: {binder_ok}, structural: {structural_ok}, def_eq: {def_eq_ok} ok/{def_eq_fail} fail");
    assert_eq!(failures.len(), 0, "Binder mismatches: {failures:?}");
}

/// Verify that Eq/Eq.refl bridge diffs are only universe-parameter naming
/// differences (`u` vs `u_1`), not semantic type-shape mismatches.
#[test]
fn test_bridge_eq_level_param_name_diffs_are_alpha_equivalent() {
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_init_extended(&lib_path);
    let env_hw = load_handwritten_extended();

    for const_name in ["Eq", "Eq.refl"] {
        let name = Name::from_string(const_name);
        let hw = env_hw
            .get_const(&name)
            .unwrap_or_else(|| panic!("Missing handwritten constant: {const_name}"));
        let ol = env_olean
            .get_const(&name)
            .unwrap_or_else(|| panic!("Missing .olean constant: {const_name}"));

        assert_eq!(
            hw.level_params.len(),
            ol.level_params.len(),
            "{const_name}: expected matching universe parameter arity"
        );
        assert_ne!(
            hw.level_params, ol.level_params,
            "{const_name}: expected a naming difference to validate"
        );

        let hw_alpha =
            erase_binder_info(&canonicalize_level_param_names(&hw.type_, &hw.level_params));
        let ol_alpha =
            erase_binder_info(&canonicalize_level_param_names(&ol.type_, &ol.level_params));
        assert_eq!(
            hw_alpha, ol_alpha,
            "{const_name}: types should match after canonical level-param renaming and binder-info erasure"
        );

        let hw_inst = hw.type_.instantiate_level_params(
            &hw.level_params
                .iter()
                .cloned()
                .map(|p| (p, Level::zero()))
                .collect::<Vec<_>>(),
        );
        let ol_inst = ol.type_.instantiate_level_params(
            &ol.level_params
                .iter()
                .cloned()
                .map(|p| (p, Level::zero()))
                .collect::<Vec<_>>(),
        );
        let tc = TypeChecker::new(&env_hw);
        assert!(
            tc.is_def_eq(&hw_inst, &ol_inst),
            "{const_name}: concrete instantiation should erase naming-only diffs"
        );
    }
}

/// Phase 0 cross-TypeChecker validation: verify handwritten types type-check
/// in the .olean environment and vice versa.
///
/// If a handwritten type fails to type-check in the .olean env, it contains
/// a structural error (wrong universe, missing argument, etc.) that the
/// .olean env's richer context catches.
#[test]
fn test_bridge_init_cross_env_typecheck() {
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let env_olean = load_olean_init_extended(&lib_path);
    let env_hw = load_handwritten_extended();

    let (mut hw_in_olean_ok, mut hw_in_olean_fail) = (0u32, 0u32);
    let (mut olean_in_hw_ok, mut olean_in_hw_fail) = (0u32, 0u32);
    let mut cross_failures: Vec<String> = Vec::new();

    for (name_str, _) in EXTENDED_INIT_CONSTANTS {
        let name = Name::from_string(name_str);
        let (Some(hw), Some(ol)) = (env_hw.get_const(&name), env_olean.get_const(&name)) else {
            continue;
        };

        // Test: does the handwritten type type-check in the .olean environment?
        let tc_olean = TypeChecker::new(&env_olean);
        match tc_olean.infer_type(&hw.type_) {
            Ok(_) => hw_in_olean_ok += 1,
            Err(e) => {
                hw_in_olean_fail += 1;
                cross_failures.push(format!("{name_str} (hw in olean): {e:?}"));
                println!("  HW-IN-OLEAN FAIL {name_str}: {e:?}");
            }
        }

        // Test: does the .olean type type-check in the handwritten environment?
        let tc_hw = TypeChecker::new(&env_hw);
        match tc_hw.infer_type(&ol.type_) {
            Ok(_) => olean_in_hw_ok += 1,
            Err(e) => {
                olean_in_hw_fail += 1;
                cross_failures.push(format!("{name_str} (olean in hw): {e:?}"));
                println!("  OLEAN-IN-HW FAIL {name_str}: {e:?}");
            }
        }
    }

    println!("\n=== Cross-Env TypeCheck Bridge ===");
    println!("  HW types in .olean env: {hw_in_olean_ok} ok, {hw_in_olean_fail} fail");
    println!("  .olean types in HW env: {olean_in_hw_ok} ok, {olean_in_hw_fail} fail");
    if !cross_failures.is_empty() {
        println!("  Cross-failures: {cross_failures:?}");
    }

    // The .olean environment is the ground truth (type-checked by Lean 4's
    // elaborator). If handwritten types fail in .olean env, they are wrong.
    assert_eq!(
        hw_in_olean_fail, 0,
        "Handwritten types must type-check in .olean env: {cross_failures:?}"
    );
}

/// Full prelude bridge: compare ALL constants from `Environment::try_with_prelude()`
/// against comprehensive Init .olean loading.
///
/// Unlike the extended tests (22 init_* functions, 31 named constants), this test
/// covers the entire prelude surface area (66 init_* functions, including algebra,
/// logic, classical, decidable, control, etc.) against the broadest possible Init
/// .olean module set.
///
/// Part of #1488 Phase 0: validates that the full prelude's universe-level params
/// match the canonical Lean 4 .olean declarations.
#[test]
fn test_bridge_full_prelude_overlap_zero_mismatches() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let (env_olean, loaded, failed) = load_olean_init_comprehensive(&lib_path);
    let env_hw = load_handwritten_prelude();

    println!("=== Full Prelude Bridge ===");
    println!("  Comprehensive .olean modules: {loaded} loaded, {failed} failed");

    let olean_count = env_olean.num_constants();
    let hw_count = env_hw.num_constants();
    println!("  .olean constants: {olean_count}, handwritten prelude constants: {hw_count}");

    let (overlap, level_match, level_mismatch, hw_only, mismatched_names) =
        count_full_overlap(&env_olean, &env_hw);

    println!("  Overlap: {overlap} shared, {level_match} match, {level_mismatch} mismatch, {hw_only} hw-only");

    if !mismatched_names.is_empty() {
        println!("  First mismatches (max 20):");
        for name in mismatched_names.iter().take(20) {
            println!("    {name}");
        }
    }

    assert_eq!(
        level_mismatch, 0,
        "Full prelude: expected 0 universe-level mismatches but found {level_mismatch}: {mismatched_names:?}"
    );
    // The full prelude should have significantly more overlap than the extended test (>=50)
    assert!(
        overlap >= 100,
        "Expected >=100 overlapping constants with full prelude, got {overlap}"
    );
}

/// Cross-env type-check results for bridge tests.
struct CrossEnvResults {
    tested: u32,
    hw_only: u32,
    hw_in_olean_ok: u32,
    hw_in_olean_fail: u32,
    olean_in_hw_ok: u32,
    olean_in_hw_fail: u32,
    failures: Vec<String>,
}

/// Run cross-env type-checking: for each overlapping constant, check that the
/// handwritten type type-checks in the .olean env and vice versa.
fn run_cross_env_typecheck(env_hw: &Environment, env_olean: &Environment) -> CrossEnvResults {
    use clean_kernel::tc::TypeChecker;
    let mut r = CrossEnvResults {
        tested: 0,
        hw_only: 0,
        hw_in_olean_ok: 0,
        hw_in_olean_fail: 0,
        olean_in_hw_ok: 0,
        olean_in_hw_fail: 0,
        failures: Vec::new(),
    };
    for ci in env_hw.constants() {
        let name = &ci.name;
        let Some(oc) = env_olean.get_const(name) else {
            r.hw_only += 1;
            continue;
        };
        r.tested += 1;
        let tc_o = TypeChecker::new(env_olean);
        match tc_o.infer_type(&ci.type_) {
            Ok(_) => r.hw_in_olean_ok += 1,
            Err(e) => {
                r.hw_in_olean_fail += 1;
                let msg = format!("{name} (hw in olean): {e:?}");
                if r.failures.len() < 30 {
                    r.failures.push(msg.clone());
                }
                println!("  HW-IN-OLEAN FAIL {msg}");
            }
        }
        let tc_h = TypeChecker::new(env_hw);
        match tc_h.infer_type(&oc.type_) {
            Ok(_) => r.olean_in_hw_ok += 1,
            Err(e) => {
                r.olean_in_hw_fail += 1;
                let msg = format!("{name} (olean in hw): {e:?}");
                if r.failures.len() < 30 {
                    r.failures.push(msg.clone());
                }
                println!("  OLEAN-IN-HW FAIL {msg}");
            }
        }
    }
    r
}

/// Full prelude cross-env type-checking: verify that handwritten types from
/// `try_with_prelude()` type-check in the comprehensive .olean environment.
///
/// Part of #1488 Phase 0.
#[test]
fn test_bridge_full_prelude_cross_env_typecheck() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let (env_olean, loaded, _) = load_olean_init_comprehensive(&lib_path);
    let env_hw = load_handwritten_prelude();

    println!("=== Full Prelude Cross-Env TypeCheck ===");
    println!("  Comprehensive modules loaded: {loaded}");

    let r = run_cross_env_typecheck(&env_hw, &env_olean);

    println!("\n  Tested: {}, hw-only: {}", r.tested, r.hw_only);
    println!(
        "  HW in .olean: {} ok, {} fail",
        r.hw_in_olean_ok, r.hw_in_olean_fail
    );
    println!(
        "  .olean in HW: {} ok, {} fail",
        r.olean_in_hw_ok, r.olean_in_hw_fail
    );

    if r.hw_in_olean_fail > 0 {
        println!(
            "\n  WARNING: {} handwritten types fail in .olean env.",
            r.hw_in_olean_fail
        );
        for f in r
            .failures
            .iter()
            .filter(|f| f.contains("hw in olean"))
            .take(10)
        {
            println!("    {f}");
        }
    }

    assert!(
        r.tested >= 50,
        "Expected >=50 cross-env tested constants, got {}",
        r.tested
    );

    // Regression guard: this test intentionally allows known mismatches while #1488
    // is in progress, but should fail if the mismatch count gets worse.
    const MAX_HW_IN_OLEAN_FAIL: u32 = 51;
    const MAX_OLEAN_IN_HW_FAIL: u32 = 70;
    assert!(
        r.hw_in_olean_fail <= MAX_HW_IN_OLEAN_FAIL,
        "Regression: hw_in_olean_fail {} > baseline {}",
        r.hw_in_olean_fail,
        MAX_HW_IN_OLEAN_FAIL
    );
    assert!(
        r.olean_in_hw_fail <= MAX_OLEAN_IN_HW_FAIL,
        "Regression: olean_in_hw_fail {} > baseline {}",
        r.olean_in_hw_fail,
        MAX_OLEAN_IN_HW_FAIL
    );
}

/// Topology overlay bridge gate for #1736 / #1444.
///
/// Provenance source for this check is a namespace-scoped snapshot from the
/// initialized kernel environment (Topology.Manifold + Topology.LieGroup),
/// exported into a temporary .olean payload and immediately re-imported.
/// This validates that import bridge semantics preserve migrated overlay
/// declaration signatures for the active topology namespaces.
///
/// Semantic shape assertions for canary declarations ensure this test fails on
/// topology signature drift, not only on round-trip plumbing failures.
fn build_topology_snapshot_constants() -> Vec<ConstantInfo> {
    let mut source_env = Environment::new();
    source_env
        .init_topology_lie_group()
        .expect("init_topology_lie_group should succeed");

    let constants = collect_namespace_constants(&source_env, TOPOLOGY_BRIDGE_NAMESPACES);
    assert!(
        !constants.is_empty(),
        "expected topology namespace snapshot to contain declarations"
    );
    constants
}

fn assert_topology_snapshot_scoped(constants: &[ConstantInfo]) {
    let mut manifold_count = 0usize;
    let mut lie_group_count = 0usize;
    for info in constants {
        let name_str = info.name.to_string();
        if is_in_namespace(&name_str, "Topology.Manifold") {
            manifold_count += 1;
        } else if is_in_namespace(&name_str, "Topology.LieGroup") {
            lie_group_count += 1;
        } else {
            panic!("unexpected namespace in topology snapshot: {}", info.name);
        }
    }
    assert!(
        manifold_count > 0 && lie_group_count > 0,
        "expected both Topology.Manifold and Topology.LieGroup declarations in snapshot"
    );
}

fn assert_topology_snapshot_contains_sentinels(constants: &[ConstantInfo]) {
    let names: Vec<String> = constants.iter().map(|info| info.name.to_string()).collect();
    let missing: Vec<String> = TOPOLOGY_BRIDGE_SENTINELS
        .iter()
        .filter(|name| !names.iter().any(|existing| existing == **name))
        .map(|name| (*name).to_owned())
        .collect();
    assert!(
        missing.is_empty(),
        "topology snapshot missing sentinel declarations: {missing:?}"
    );
}

fn load_roundtripped_topology_payload(constants: &[ConstantInfo]) -> Environment {
    let mut snapshot_env = Environment::default();
    snapshot_env.extend_constants_unchecked(constants.iter().cloned());

    let bytes = OleanExporter::export_with_env(
        &snapshot_env,
        &[],
        &[],
        "1736000000000000000000000000000000000000",
    )
    .expect("topology overlay export should succeed");

    let tmp = tempdir().expect("tempdir");
    let olean_path = tmp.path().join("TopologyOverlayBridge.olean");
    std::fs::write(&olean_path, &bytes).expect("write temp topology overlay bridge .olean");

    let mut imported_env = Environment::default();
    let summary = load_olean_file(&mut imported_env, &olean_path)
        .expect("load_olean_file for topology overlay bridge should succeed");
    assert_eq!(
        summary.added_constants,
        constants.len(),
        "imported constant count should match topology snapshot"
    );
    assert_eq!(
        summary.duplicate_constants, 0,
        "topology bridge import should not report duplicates"
    );
    imported_env
}

fn assert_topology_semantic_equivalence(constants: &[ConstantInfo], imported_env: &Environment) {
    let mut missing = Vec::new();
    let mut level_mismatches = Vec::new();
    let mut type_mismatches = Vec::new();

    for source in constants {
        match imported_env.get_const(&source.name) {
            Some(imported) => {
                if source.level_params.len() != imported.level_params.len() {
                    level_mismatches.push(format!(
                        "{}: source={} imported={}",
                        source.name,
                        source.level_params.len(),
                        imported.level_params.len()
                    ));
                    continue;
                }

                let source_ty = canonicalized_type_for_compare(&source.type_, &source.level_params);
                let imported_ty =
                    canonicalized_type_for_compare(&imported.type_, &imported.level_params);
                if source_ty != imported_ty {
                    type_mismatches.push(format!(
                        "{}:\n  source={}\n  imported={}",
                        source.name, source_ty, imported_ty
                    ));
                }
            }
            None => missing.push(source.name.to_string()),
        }
    }
    assert!(
        missing.is_empty(),
        "topology bridge missing imported declarations: {missing:?}"
    );
    assert!(
        level_mismatches.is_empty(),
        "topology bridge level-arity mismatches: {level_mismatches:?}"
    );
    assert!(
        type_mismatches.is_empty(),
        "topology bridge type mismatches: {type_mismatches:?}"
    );
}

fn assert_chart_to_fun_roundtrip_shape(imported_env: &Environment) {
    use clean_kernel::tc::TypeChecker;

    let tc = TypeChecker::new(imported_env);
    let chart_const = Expr::const_(
        Name::from_string("Topology.Manifold.Chart.toFun"),
        vec![Level::param(Name::from_string("u"))],
    );
    let chart_ty = tc
        .infer_type(&chart_const)
        .expect("Chart.toFun should type-check after topology bridge round-trip");
    let (chart_binders, chart_codomain) = collect_pi_binders(chart_ty);
    assert!(
        chart_binders.len() >= 5,
        "Chart.toFun should have at least 5 Pi binders; got {}",
        chart_binders.len()
    );
    assert!(
        chart_binders.iter().any(|domain| matches!(
            head_const_name(domain),
            Some(name) if name == &Name::from_string("Topology.Manifold.Chart")
        )),
        "Chart.toFun should include a Chart binder domain"
    );
    let has_fin_binder = chart_binders.iter().any(|domain| {
        matches!(
            head_const_name(domain),
            Some(name) if name == &Name::from_string("Fin")
        )
    });
    match chart_codomain.kind() {
        ExprKind::Pi(_, fin_domain, rat_codomain) => {
            assert!(
                matches!(
                    head_const_name(fin_domain),
                    Some(name) if name == &Name::from_string("Fin")
                ),
                "Chart.toFun codomain domain should be Fin n"
            );
            assert!(
                matches!(
                    rat_codomain.kind(),
                    ExprKind::Const(name, _) if name == &Name::from_string("Rat")
                ),
                "Chart.toFun codomain should be Rat"
            );
        }
        ExprKind::Const(name, _) if name == &Name::from_string("Rat") => {
            assert!(
                has_fin_binder,
                "Chart.toFun ending in Rat should have a Fin binder in Pi domains"
            );
        }
        _ => panic!("Chart.toFun codomain should be Fin n -> Rat"),
    }
}

fn assert_lie_algebra_hom_roundtrip_shape(imported_env: &Environment) {
    use clean_kernel::tc::TypeChecker;

    let tc = TypeChecker::new(imported_env);
    let lie_algebra = Name::from_string("Topology.LieGroup.LieAlgebra");
    let lie_hom_const = Expr::const_(
        Name::from_string("Topology.LieGroup.LieAlgebraHom"),
        vec![
            Level::param(Name::from_string("u")),
            Level::param(Name::from_string("v")),
        ],
    );
    let lie_hom_ty = tc
        .infer_type(&lie_hom_const)
        .expect("LieAlgebraHom should type-check after topology bridge round-trip");
    let (lie_hom_binders, lie_hom_codomain) = collect_pi_binders(lie_hom_ty);
    assert_eq!(
        lie_hom_binders.len(),
        11,
        "LieAlgebraHom should have 11 Pi binders"
    );
    let phi_ty = lie_hom_binders
        .last()
        .expect("LieAlgebraHom should have a final phi binder");
    match phi_ty.kind() {
        ExprKind::Pi(_, phi_domain, phi_codomain) => {
            assert!(
                matches!(head_const_name(phi_domain), Some(name) if name == &lie_algebra),
                "LieAlgebraHom phi domain should be LieAlgebra"
            );
            assert!(
                matches!(head_const_name(phi_codomain), Some(name) if name == &lie_algebra),
                "LieAlgebraHom phi codomain should be LieAlgebra"
            );
        }
        _ => panic!("LieAlgebraHom final binder should be an arrow type"),
    }
    assert!(
        matches!(lie_hom_codomain.kind(), ExprKind::Sort(level) if level.is_zero()),
        "LieAlgebraHom codomain should be Prop"
    );
}

fn assert_topology_roundtrip_type_shapes(imported_env: &Environment) {
    assert_chart_to_fun_roundtrip_shape(imported_env);
    assert_lie_algebra_hom_roundtrip_shape(imported_env);
}

#[test]
fn test_bridge_topology_overlay_namespace_semantic_equivalence() {
    let constants = build_topology_snapshot_constants();
    assert_topology_snapshot_scoped(&constants);
    assert_topology_snapshot_contains_sentinels(&constants);
    let imported_env = load_roundtripped_topology_payload(&constants);
    assert_topology_semantic_equivalence(&constants, &imported_env);
    assert_topology_roundtrip_type_shapes(&imported_env);
}

/// Regression test: export_with_env must write ConstantVal.levelParams as List Name,
/// not List Level. Prior to this fix, write_level_params wrapped each name in a
/// Level.param constructor, causing InvalidObjectTag { tag: 4 } on reimport.
#[test]
fn test_bridge_level_params_roundtrip_as_names() {
    let mut env = Environment::default();
    let info = ConstantInfo {
        name: Name::from_string("TestPoly.myAxiom"),
        level_params: vec![Name::from_string("u"), Name::from_string("v")],
        type_: Expr::sort(Level::param(Name::from_string("u"))),
        value: None,
        is_reducible: false,
        reducibility: clean_kernel::env::Reducibility::Opaque,
        kind: clean_kernel::env::ConstantKind::Axiom,
    };
    env.extend_constants_unchecked(std::iter::once(info));

    let bytes =
        OleanExporter::export_with_env(&env, &[], &[], "c0de000000000000000000000000000000000003")
            .expect("export_with_env should succeed");

    let tmp = tempdir().expect("tempdir");
    let olean_path = tmp.path().join("TestPoly.olean");
    std::fs::write(&olean_path, &bytes).expect("write temp .olean");

    let mut imported_env = Environment::default();
    let summary =
        load_olean_file(&mut imported_env, &olean_path).expect("load_olean_file should succeed");
    assert_eq!(summary.added_constants, 1);

    let imported = imported_env
        .get_const(&Name::from_string("TestPoly.myAxiom"))
        .expect("imported constant should exist");
    assert_eq!(imported.level_params.len(), 2, "should have 2 level params");
    assert_eq!(imported.level_params[0].to_string(), "u");
    assert_eq!(imported.level_params[1].to_string(), "v");
}
