// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for loading Rat (rational numbers) via .olean import (#3154).
//!
//! Validates that the .olean parser correctly reads Init.Data.Rat.Basic from
//! Lean 4 v4.27+ toolchains, extracting the `Rat` type, operations, instance
//! constants, and extension entries needed for linarith over rationals.
//!
//! clean's `linarith` works by direct pattern matching on LE.le/HAdd.hAdd, not
//! via LinearOrderedField typeclass synthesis (see arith_linarith/parse.rs).
//!
//! Tests use `parse_module_file` (direct .olean parsing, <10ms) rather than
//! `load_module_with_deps` which takes >20min for v4.28 Init dependency trees.
//!
//! Requires Lean 4 v4.27+ via elan (Rat was moved to Init in v4.27).

use clean_olean::default_search_paths;
use clean_olean::module::ParsedModule;
use std::path::PathBuf;

/// Get the first search path that contains a v4.27+ Init with Rat support.
fn get_v4_27_plus_lib_path() -> Option<PathBuf> {
    default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Data/Rat/Basic.olean").exists())
}

/// Count extension entries across all extensions in a parsed module.
fn count_extension_entries(module: &ParsedModule) -> (usize, usize) {
    let mut total_entries = 0;
    let mut nonempty_extensions = 0;
    for ext in &module.entries {
        let count = ext.entries.len();
        total_entries += count;
        if count > 0 {
            nonempty_extensions += 1;
        }
    }
    (total_entries, nonempty_extensions)
}

// =============================================================================
// Rat.Basic: type, operations, and critical instances
// =============================================================================

#[test]
fn test_rat_basic_type_and_operations() {
    let Some(lib_path) = get_v4_27_plus_lib_path() else {
        eprintln!("Skipping test: Lean 4 v4.27+ not found (Init/Data/Rat/Basic.olean missing)");
        return;
    };

    let rat_path = lib_path.join("Init/Data/Rat/Basic.olean");
    let module =
        clean_olean::parse_module_file(&rat_path).expect("should parse Init.Data.Rat.Basic");

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    println!(
        "Init.Data.Rat.Basic: {} constants, {} imports, {} extensions",
        module.constants.len(),
        module.imports.len(),
        module.entries.len(),
    );

    // Rat type must exist
    assert!(
        const_names.contains(&"Rat"),
        "Rat type must be in Init.Data.Rat.Basic constants"
    );

    // Rat-prefixed operations
    let rat_count = const_names.iter().filter(|n| n.starts_with("Rat.")).count();
    assert!(
        rat_count > 30,
        "Expected > 30 Rat.* constants, got {rat_count}"
    );

    // Critical fields for linarith
    for op in ["Rat.num", "Rat.den"] {
        assert!(const_names.contains(&op), "Critical {op} missing");
    }

    // Module size
    assert!(module.constants.len() > 50, "Expected > 50 total constants");
    println!("  [PASS] Rat type + {rat_count} operations + Rat.num/Rat.den");
}

#[test]
fn test_rat_basic_linarith_instances() {
    let Some(lib_path) = get_v4_27_plus_lib_path() else {
        eprintln!("Skipping test: Lean 4 v4.27+ not found");
        return;
    };

    let rat_path = lib_path.join("Init/Data/Rat/Basic.olean");
    let module =
        clean_olean::parse_module_file(&rat_path).expect("should parse Init.Data.Rat.Basic");

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();

    // Instance constants critical for linarith constraint extraction
    let inst_consts: Vec<&&str> = const_names
        .iter()
        .filter(|n| n.contains("inst") && (n.contains("Rat") || n.contains("rat")))
        .collect();
    println!("  Rat instance constants: {}", inst_consts.len());

    let has_add = inst_consts.iter().any(|n| n.contains("Add"));
    let has_le = inst_consts
        .iter()
        .any(|n| n.contains("LE") || n.contains("Le"));
    let has_lt = inst_consts
        .iter()
        .any(|n| n.contains("LT") || n.contains("Lt"));
    let has_mul = inst_consts.iter().any(|n| n.contains("Mul"));
    let has_decidable_eq = inst_consts
        .iter()
        .any(|n| n.contains("DecidableEq") || n.contains("decEq"));

    println!("    Add:{has_add} LE:{has_le} LT:{has_lt} Mul:{has_mul} DecEq:{has_decidable_eq}");

    // Hard requirements for linarith
    assert!(has_add, "Rat must have Add instance");
    assert!(has_le, "Rat must have LE instance");
    assert!(has_lt, "Rat must have LT instance");
    println!("  [PASS] Critical instances (Add/LE/LT) present");
}

#[test]
fn test_rat_basic_extension_entries() {
    let Some(lib_path) = get_v4_27_plus_lib_path() else {
        eprintln!("Skipping test: Lean 4 v4.27+ not found");
        return;
    };

    let rat_path = lib_path.join("Init/Data/Rat/Basic.olean");
    let module =
        clean_olean::parse_module_file(&rat_path).expect("should parse Init.Data.Rat.Basic");

    let (total_entries, ext_count) = count_extension_entries(&module);
    println!("  Extension entries: {total_entries} across {ext_count} extensions");

    // Extension entries confirm v2 .olean parsing pipeline works
    assert!(
        total_entries > 0,
        "Expected extension entries in Rat.Basic (v2 .olean parsing may be broken)"
    );
    println!("  [PASS] {total_entries} extension entries parsed");
}

// =============================================================================
// Rat.Lemmas: proof constants for proof reconstruction
// =============================================================================

#[test]
fn test_parse_rat_lemmas_olean_structure() {
    let Some(lib_path) = get_v4_27_plus_lib_path() else {
        eprintln!("Skipping test: Lean 4 v4.27+ not found");
        return;
    };

    let lemmas_path = lib_path.join("Init/Data/Rat/Lemmas.olean");
    if !lemmas_path.exists() {
        eprintln!("Skipping test: Init/Data/Rat/Lemmas.olean not found");
        return;
    }

    let module =
        clean_olean::parse_module_file(&lemmas_path).expect("should parse Init.Data.Rat.Lemmas");

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    let rat_consts: Vec<&&str> = const_names
        .iter()
        .filter(|n| n.starts_with("Rat."))
        .collect();

    println!(
        "Init.Data.Rat.Lemmas: {} constants ({} Rat.*)",
        module.constants.len(),
        rat_consts.len(),
    );

    let le_count = rat_consts.iter().filter(|n| n.contains("le")).count();
    let lt_count = rat_consts.iter().filter(|n| n.contains("lt")).count();
    let add_count = rat_consts.iter().filter(|n| n.contains("add")).count();
    let mul_count = rat_consts.iter().filter(|n| n.contains("mul")).count();

    println!("  le:{le_count} lt:{lt_count} add:{add_count} mul:{mul_count}");

    assert!(
        module.constants.len() > 100,
        "Expected > 100 constants in Rat.Lemmas"
    );
    println!("  [PASS] {} total constants", module.constants.len());
}

// =============================================================================
// Grind/Ordered/Rat: LinearOrder instance probe
// =============================================================================

#[test]
fn test_parse_ordered_rat_olean_if_present() {
    let Some(lib_path) = get_v4_27_plus_lib_path() else {
        eprintln!("Skipping test: Lean 4 v4.27+ not found");
        return;
    };

    let ordered_rat_path = lib_path.join("Init/Grind/Ordered/Rat.olean");
    if !ordered_rat_path.exists() {
        println!("Init/Grind/Ordered/Rat.olean not present in this Lean version");
        return;
    }

    let module = clean_olean::parse_module_file(&ordered_rat_path)
        .expect("should parse Init.Grind.Ordered.Rat");

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    println!(
        "Init.Grind.Ordered.Rat: {} constants",
        module.constants.len()
    );

    let linear_ordered: Vec<&&str> = const_names
        .iter()
        .filter(|n| n.contains("LinearOrder") || n.contains("linearOrder"))
        .collect();
    println!("  LinearOrder-related: {:?}", linear_ordered);

    let rat_instances: Vec<&&str> = const_names
        .iter()
        .filter(|n| n.contains("Rat") && n.contains("inst"))
        .collect();
    println!("  Rat instances: {:?}", rat_instances);
}
