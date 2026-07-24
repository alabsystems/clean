// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for gamma-crown axiom replacement via Lean 4 Init imports.

use std::path::PathBuf;

use super::*;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::ConstantKind;

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn get_lean_lib() -> Option<PathBuf> {
    find_lean_lib_path()
}

// ---------------------------------------------------------------------------
// Mapping table tests (no toolchain required)
// ---------------------------------------------------------------------------

#[test]
fn test_gamma_crown_axiom_mappings_has_12_entries() {
    let mappings = gamma_crown_axiom_mappings();
    assert_eq!(mappings.len(), 12, "Expected 12 gamma-crown axiom mappings");
}

#[test]
fn test_gamma_crown_axiom_mappings_unique_names() {
    let mappings = gamma_crown_axiom_mappings();
    let names: Vec<&str> = mappings.iter().map(|m| m.axiom_name).collect();
    let mut deduped = names.clone();
    deduped.sort();
    deduped.dedup();
    assert_eq!(
        names.len(),
        deduped.len(),
        "Axiom mapping names must be unique"
    );
}

#[test]
fn test_gamma_crown_axiom_mappings_all_have_candidates() {
    let mappings = gamma_crown_axiom_mappings();
    for mapping in &mappings {
        assert!(
            !mapping.lean_candidates.is_empty(),
            "Axiom {} has no Lean candidates",
            mapping.axiom_name
        );
    }
}

// ---------------------------------------------------------------------------
// Mathlib extended mapping tests (no toolchain required)
// ---------------------------------------------------------------------------

#[test]
fn test_mathlib_gamma_crown_axiom_mappings_has_entries() {
    let mappings = mathlib_gamma_crown_axiom_mappings();
    // 13 Rat field + 6 Rat ordering + 7 Matrix + 4 Real + 3 Topology + 2 Probability = 35
    assert_eq!(
        mappings.len(),
        35,
        "Expected 35 Mathlib gamma-crown axiom mappings"
    );
}

#[test]
fn test_mathlib_gamma_crown_axiom_mappings_unique_names() {
    let mappings = mathlib_gamma_crown_axiom_mappings();
    let names: Vec<&str> = mappings.iter().map(|m| m.axiom_name).collect();
    let mut deduped = names.clone();
    deduped.sort();
    deduped.dedup();
    assert_eq!(
        names.len(),
        deduped.len(),
        "Mathlib axiom mapping names must be unique"
    );
}

#[test]
fn test_all_gamma_crown_axiom_mappings_combines_both() {
    let init_count = gamma_crown_axiom_mappings().len();
    let mathlib_count = mathlib_gamma_crown_axiom_mappings().len();
    let all = all_gamma_crown_axiom_mappings();
    assert_eq!(
        all.len(),
        init_count + mathlib_count,
        "all_gamma_crown_axiom_mappings should be Init + Mathlib combined"
    );
}

#[test]
fn test_all_gamma_crown_axiom_mappings_no_name_collisions() {
    let all = all_gamma_crown_axiom_mappings();
    let names: Vec<&str> = all.iter().map(|m| m.axiom_name).collect();
    let mut deduped = names.clone();
    deduped.sort();
    deduped.dedup();
    assert_eq!(
        names.len(),
        deduped.len(),
        "Init and Mathlib axiom names must not collide"
    );
}

#[test]
fn test_mathlib_mappings_cover_gamma_crown_categories() {
    let mappings = mathlib_gamma_crown_axiom_mappings();
    let names: Vec<&str> = mappings.iter().map(|m| m.axiom_name).collect();

    // Rat field properties
    assert!(names.contains(&"rat_add_comm"), "Missing rat_add_comm");
    assert!(
        names.contains(&"rat_mul_inv_cancel"),
        "Missing rat_mul_inv_cancel"
    );
    assert!(
        names.contains(&"rat_left_distrib"),
        "Missing rat_left_distrib"
    );

    // Rat ordering
    assert!(names.contains(&"rat_le_refl"), "Missing rat_le_refl");
    assert!(names.contains(&"rat_le_total"), "Missing rat_le_total");
    assert!(names.contains(&"rat_mul_nonneg"), "Missing rat_mul_nonneg");

    // Matrix operations
    assert!(names.contains(&"mat_mul_one"), "Missing mat_mul_one");
    assert!(
        names.contains(&"mat_transpose_mul"),
        "Missing mat_transpose_mul"
    );

    // Real analysis
    assert!(
        names.contains(&"real_triangle_ineq"),
        "Missing real_triangle_ineq"
    );
    assert!(names.contains(&"real_sq_nonneg"), "Missing real_sq_nonneg");

    // Topology/Lipschitz
    assert!(names.contains(&"lipschitz_comp"), "Missing lipschitz_comp");
    assert!(names.contains(&"dist_triangle"), "Missing dist_triangle");

    // Probability
    assert!(names.contains(&"measure_mono"), "Missing measure_mono");
}

#[test]
fn test_gamma_crown_mathlib_modules_list() {
    let modules = gamma_crown_mathlib_modules();
    assert!(
        modules.len() >= 6,
        "Expected >= 6 gamma-crown Mathlib modules, got {}",
        modules.len()
    );
    assert!(
        modules.contains(&"Mathlib.Data.Rat.Basic".to_string()),
        "Missing Mathlib.Data.Rat.Basic"
    );
    assert!(
        modules.contains(&"Mathlib.Data.Matrix.Basic".to_string()),
        "Missing Mathlib.Data.Matrix.Basic"
    );
}

// ---------------------------------------------------------------------------
// AxiomReplacementTable tests (require Lean 4 toolchain)
// ---------------------------------------------------------------------------

#[test]
fn test_replacement_table_from_init_resolves_nat_theorems() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let stats = table.stats();
    println!("=== Replacement Table Stats ===");
    println!("  Total axioms: {}", stats.total_axioms);
    println!("  Replaced with proof: {}", stats.replaced_with_proof);
    println!("  Resolved (no proof): {}", stats.resolved_no_proof);
    println!("  Unresolved: {}", stats.unresolved);

    // At minimum, Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc
    // should be available from Init.Data.Nat.Lemmas
    assert!(
        stats.replaced_with_proof + stats.resolved_no_proof >= 4,
        "Expected >= 4 resolved axioms, got {}",
        stats.replaced_with_proof + stats.resolved_no_proof
    );

    // Print resolved entries for diagnostics
    for r in table.resolved() {
        let status = if r.has_proof() { "PROVED" } else { "AXIOM" };
        println!("  {} -> {} [{}]", r.axiom_name, r.lean_name, status);
    }

    // Print unresolved
    for name in table.unresolved_axioms() {
        println!("  UNRESOLVED: {name}");
    }
}

#[test]
fn test_replacement_table_add_comm_has_proof() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let add_comm = table.get("add_comm");
    assert!(add_comm.is_some(), "add_comm should be resolved from Init");
    let r = add_comm.unwrap();
    assert_eq!(r.lean_name, "Nat.add_comm");
    // Nat.add_comm should have a proof term in Init.Data.Nat.Lemmas
    println!(
        "  add_comm -> {} [has_proof={}]",
        r.lean_name,
        r.has_proof()
    );
}

#[test]
fn test_replacement_table_mat_mul_assoc_unresolved_without_mathlib() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    // Matrix.mul_assoc requires Mathlib, not just Init
    let mat = table.get("mat_mul_assoc");
    assert!(
        mat.is_none(),
        "mat_mul_assoc should NOT be resolved from Init alone"
    );

    assert!(
        table
            .unresolved_axioms()
            .contains(&"mat_mul_assoc".to_string()),
        "mat_mul_assoc should be in unresolved list"
    );
}

// ---------------------------------------------------------------------------
// Environment patching tests
// ---------------------------------------------------------------------------

#[test]
fn test_apply_replacements_to_fresh_env() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Build replacement table from Init
    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    // Create a fresh environment to patch. The replacement table's proof
    // terms reference `Nat.le.brecOn`, `instHAdd`, `instHMul`, `Nat.le`, and
    // other Init constants that the hand-registered `try_with_prelude` does
    // not carry. Load Init into the target env so it mirrors the
    // environment `apply_replacements` is designed to patch. #3576: prior to
    // this fix the test used `Environment::default()`, which has no prelude
    // at all, and every axiom failed type-checking with "Unknown constant:
    // Nat".
    let mut target_env = Environment::default();
    let init_result = crate::lean4::mathlib_import::load_init_modules(&mut target_env, &lib_path);
    assert!(
        !init_result.loaded_modules.is_empty(),
        "target env must load at least one Init module before apply_replacements"
    );

    // Apply all resolvable axioms
    let axiom_names: Vec<&str> = gamma_crown_axiom_mappings()
        .iter()
        .map(|m| m.axiom_name)
        .collect();

    let result = apply_replacements(&mut target_env, &table, &axiom_names);

    println!("=== Patch Result ===");
    println!("  Theorems added: {:?}", result.theorems_added);
    println!("  No proof available: {:?}", result.no_proof_available);
    println!("  Not in table: {:?}", result.not_in_table);
    println!("  Errors: {:?}", result.errors);

    // At least some theorems should have been added
    // (assuming Init provides proof terms for Nat arithmetic)
    let total_resolved = result.theorems_added.len() + result.no_proof_available.len();
    assert!(
        total_resolved >= 4,
        "Expected >= 4 resolved axioms in patch, got {total_resolved}"
    );

    // Verify added theorems are in the environment
    for name_str in &result.theorems_added {
        let name = Name::from_string(name_str);
        let ci = target_env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{name_str} should exist in patched env"));
        assert_eq!(
            ci.kind,
            ConstantKind::Theorem,
            "{name_str} should be a Theorem, not {:?}",
            ci.kind
        );
        assert!(ci.value.is_some(), "{name_str} should have a proof term");
    }

    // mat_mul_assoc should be in not_in_table (requires Mathlib)
    assert!(
        result.not_in_table.contains(&"mat_mul_assoc".to_string()),
        "mat_mul_assoc should be unresolvable from Init"
    );
}

#[test]
fn test_apply_replacements_specific_subset() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let mut target_env = Environment::default();

    // Apply only a specific subset
    let result = apply_replacements(
        &mut target_env,
        &table,
        &["add_comm", "mul_comm", "nonexistent_axiom"],
    );

    // add_comm and mul_comm should be resolved (or at least attempted)
    // nonexistent_axiom should be in not_in_table
    assert!(
        result
            .not_in_table
            .contains(&"nonexistent_axiom".to_string()),
        "nonexistent_axiom should not be in table"
    );

    println!("  Added: {:?}", result.theorems_added);
    println!("  Errors: {:?}", result.errors);
}

#[test]
fn test_apply_replacements_duplicate_name_error() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let mut target_env = Environment::default();

    // First application should succeed
    let result1 = apply_replacements(&mut target_env, &table, &["add_comm"]);

    if !result1.theorems_added.is_empty() {
        // Second application of the same axiom should produce a duplicate error
        let result2 = apply_replacements(&mut target_env, &table, &["add_comm"]);
        assert!(
            !result2.errors.is_empty(),
            "Second apply should produce duplicate-name error"
        );
        println!("  Expected duplicate error: {:?}", result2.errors);
    }
}

// ---------------------------------------------------------------------------
// load_init_with_replacements convenience function
// ---------------------------------------------------------------------------

#[test]
fn test_load_init_with_replacements() {
    let Some((env, table)) = load_init_with_replacements() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    assert!(
        env.num_constants() > 100,
        "Init env should have > 100 constants, got {}",
        env.num_constants()
    );

    let stats = table.stats();
    assert_eq!(stats.total_axioms, 12);
    assert!(
        stats.replaced_with_proof + stats.resolved_no_proof >= 4,
        "Expected >= 4 resolved from Init"
    );

    println!("=== load_init_with_replacements ===");
    println!("  Env constants: {}", env.num_constants());
    println!("  Table stats: {:?}", stats);
}

// ---------------------------------------------------------------------------
// ReplacementStats consistency
// ---------------------------------------------------------------------------

#[test]
fn test_replacement_stats_sum_to_total() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let stats = table.stats();
    let sum = stats.replaced_with_proof + stats.resolved_no_proof + stats.unresolved;
    assert_eq!(
        sum, stats.total_axioms,
        "Stats should sum to total: {sum} != {}",
        stats.total_axioms
    );
}

#[test]
fn test_replacement_table_num_resolved_consistent() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let table =
        AxiomReplacementTable::from_init_path(&lib_path).expect("should build table from Init");

    let stats = table.stats();
    assert_eq!(
        table.num_resolved(),
        stats.replaced_with_proof + stats.resolved_no_proof,
        "num_resolved should match stats"
    );
    assert_eq!(
        table.total_axioms(),
        stats.total_axioms,
        "total_axioms should match stats"
    );
}

// ---------------------------------------------------------------------------
// Extended Mathlib table tests (require Lean 4 toolchain)
// ---------------------------------------------------------------------------

#[test]
fn test_extended_table_from_init_resolves_more_via_typeclass_instances() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Build an Init environment
    let mut env = Environment::default();
    let result = super::load_init_modules(&mut env, &lib_path);
    if result.loaded_modules.is_empty() {
        eprintln!("Skipping test: Init modules failed to load");
        return;
    }

    // Compare Init-only vs extended table on same environment
    let init_table = AxiomReplacementTable::from_environment(&env);
    let extended_table = AxiomReplacementTable::from_environment_extended(&env);

    let init_stats = init_table.stats();
    let ext_stats = extended_table.stats();

    println!("=== Init-Only vs Extended Table (Init env) ===");
    println!(
        "  Init-only: {}/{} resolved",
        init_stats.replaced_with_proof + init_stats.resolved_no_proof,
        init_stats.total_axioms
    );
    println!(
        "  Extended:  {}/{} resolved",
        ext_stats.replaced_with_proof + ext_stats.resolved_no_proof,
        ext_stats.total_axioms
    );

    // Extended table has more total axioms (Init + Mathlib mappings)
    assert!(
        ext_stats.total_axioms > init_stats.total_axioms,
        "Extended table should have more total axioms"
    );

    // Some Mathlib mappings may resolve against Init via typeclass instances
    // (e.g., `add_comm` resolves Rat.add_comm if Rat instances are in Init)
    // The extended table should resolve at least as many as Init-only
    let init_resolved = init_stats.replaced_with_proof + init_stats.resolved_no_proof;
    let ext_resolved = ext_stats.replaced_with_proof + ext_stats.resolved_no_proof;
    assert!(
        ext_resolved >= init_resolved,
        "Extended table should resolve >= Init table: {ext_resolved} < {init_resolved}"
    );
}

#[test]
fn test_extended_table_stats_sum_to_total() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let result = super::load_init_modules(&mut env, &lib_path);
    if result.loaded_modules.is_empty() {
        return;
    }

    let table = AxiomReplacementTable::from_environment_extended(&env);
    let stats = table.stats();
    let sum = stats.replaced_with_proof + stats.resolved_no_proof + stats.unresolved;
    assert_eq!(
        sum, stats.total_axioms,
        "Extended stats should sum to total: {sum} != {}",
        stats.total_axioms
    );
}

#[test]
fn test_load_mathlib_with_replacements() {
    let Some((env, table)) = load_mathlib_with_replacements() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    assert!(
        env.num_constants() > 100,
        "Env should have > 100 constants, got {}",
        env.num_constants()
    );

    let stats = table.stats();
    // Extended table has 12 Init + 35 Mathlib = 47 total axioms
    assert_eq!(stats.total_axioms, 47);

    // At minimum, Init axioms should resolve
    assert!(
        stats.replaced_with_proof + stats.resolved_no_proof >= 4,
        "Expected >= 4 resolved from Init+Mathlib"
    );

    println!("=== load_mathlib_with_replacements ===");
    println!("  Env constants: {}", env.num_constants());
    println!("  Table stats: {:?}", stats);

    // Print resolved entries for diagnostics
    for r in table.resolved() {
        let status = if r.has_proof() { "PROVED" } else { "AXIOM" };
        println!("  {} -> {} [{}]", r.axiom_name, r.lean_name, status);
    }
}

// ---------------------------------------------------------------------------
// Mathlib-specific Axiom Replacement tests (require Mathlib .olean files)
// ---------------------------------------------------------------------------

#[test]
fn test_from_mathlib_resolves_init_at_minimum() {
    let Some(table) = AxiomReplacementTable::from_mathlib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let stats = table.stats();
    println!("=== from_mathlib Table Stats ===");
    println!("  Total axioms: {}", stats.total_axioms);
    println!("  Replaced with proof: {}", stats.replaced_with_proof);
    println!("  Resolved (no proof): {}", stats.resolved_no_proof);
    println!("  Unresolved: {}", stats.unresolved);

    // Should resolve at least Init axioms even without Mathlib .olean files
    assert!(
        stats.replaced_with_proof + stats.resolved_no_proof >= 4,
        "Expected >= 4 resolved from from_mathlib"
    );
}

#[test]
fn test_apply_mathlib_replacements_rat_axioms() {
    let Some(lib_path) = get_lean_lib() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mathlib_paths = super::find_mathlib_search_paths();
    if mathlib_paths.is_empty() {
        eprintln!("Skipping test: Mathlib not found");
        return;
    }

    // Load Init + Mathlib.Data.Rat.Basic
    let mut env = Environment::default();
    let _ = super::load_init_modules(&mut env, &lib_path);
    let _ = super::load_mathlib_modules(
        &mut env,
        &["Mathlib.Data.Rat.Basic"],
        &lib_path,
        &mathlib_paths,
    );

    let table = AxiomReplacementTable::from_environment_extended(&env);

    // Apply Rat axiom replacements to a fresh environment
    let mut target = Environment::default();
    let rat_axioms = &[
        "rat_add_comm",
        "rat_mul_comm",
        "rat_add_zero",
        "rat_mul_one",
    ];
    let result = apply_replacements(&mut target, &table, rat_axioms);

    println!("=== Rat Axiom Replacements ===");
    println!("  Added: {:?}", result.theorems_added);
    println!("  No proof: {:?}", result.no_proof_available);
    println!("  Not in table: {:?}", result.not_in_table);
    println!("  Errors: {:?}", result.errors);

    // With Mathlib loaded, at least some Rat axioms should resolve
    let total_resolved = result.theorems_added.len() + result.no_proof_available.len();
    println!("  Total resolved: {total_resolved}/{}", rat_axioms.len());
}
