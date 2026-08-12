// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental environment kernel TC measurement for Mathverse Library constants.
//!
//! Unlike `verify_measurement` which creates a fresh `Environment::new()` per
//! constant (causing 99.67% failure from missing dependencies), this module
//! loads constants incrementally into a SHARED environment. Constants that
//! pass type-checking populate the environment for later constants, matching
//! how Lean 4 actually loads its Init module.

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::path::PathBuf;

    use crate::build_library::{build_lean4_library, BuildConfig};
    use crate::shard::ShardReader;
    use crate::shard_reconstruct::{
        reconstruct_from_shard_with_level_lists, reconstruct_level_params,
    };
    use crate::types::{MathverseConstantHeader, NO_VALUE};

    use clean_kernel::{Declaration, Environment, Name};

    /// Find the first available Lean 4 toolchain library directory.
    fn find_lean4_lib() -> Option<PathBuf> {
        let home = std::env::var("HOME").ok()?;
        let toolchains = PathBuf::from(&home).join(".elan/toolchains");
        if !toolchains.is_dir() {
            return None;
        }
        let mut candidates: Vec<PathBuf> = Vec::new();
        if let Ok(entries) = std::fs::read_dir(&toolchains) {
            for entry in entries.filter_map(|e| e.ok()) {
                let lib_lean = entry.path().join("lib/lean");
                if lib_lean.join("Init.olean").exists() {
                    candidates.push(lib_lean);
                }
            }
        }
        candidates.sort();
        candidates.pop()
    }

    /// Collect .mathverse shard files from output directory (base/ and delta/).
    fn collect_shard_files(output_dir: &PathBuf) -> Vec<PathBuf> {
        let mut shard_files: Vec<PathBuf> = Vec::new();
        for subdir in &["base", "delta"] {
            let dir = output_dir.join(subdir);
            if dir.is_dir() {
                if let Ok(entries) = std::fs::read_dir(&dir) {
                    for entry in entries.filter_map(|e| e.ok()) {
                        let path = entry.path();
                        if path.extension().is_some_and(|ext| ext == "mathverse") {
                            shard_files.push(path);
                        }
                    }
                }
            }
        }
        shard_files.sort();
        shard_files
    }

    /// Classify a failure reason into a short bucket name.
    fn classify_failure(reason: &str) -> String {
        if reason.contains("unknown constant") || reason.contains("Unknown constant") {
            "unknown constant reference".to_string()
        } else if reason.contains("universe") || reason.contains("Universe") {
            "universe level error".to_string()
        } else if reason.contains("type mismatch") {
            "type mismatch".to_string()
        } else if reason.contains("function expected") {
            "function expected".to_string()
        } else if reason.contains("unsupported") {
            "unsupported expression tag".to_string()
        } else if reason.contains("out of bounds") {
            "expr/level index out of bounds".to_string()
        } else if reason.contains("deep recursion") || reason.contains("stack") {
            "stack/recursion limit".to_string()
        } else if reason.len() > 80 {
            format!("{}...", &reason[..80])
        } else {
            reason.to_string()
        }
    }

    /// A reconstructed constant ready for incremental loading.
    struct ReconstructedConstant {
        name: String,
        type_expr: clean_kernel::Expr,
        value_expr: Option<clean_kernel::Expr>,
        level_params: Vec<clean_kernel::Name>,
    }

    /// Load and reconstruct all constants from shard files.
    fn load_all_constants(shard_files: &[PathBuf]) -> Vec<ReconstructedConstant> {
        let mut constants = Vec::new();
        for shard_path in shard_files {
            let reader = match ShardReader::from_file(shard_path) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("  WARN: failed to load shard {}: {e}", shard_path.display());
                    continue;
                }
            };
            for header in &reader.constants {
                let name = reader
                    .strings
                    .get(header.name_idx as usize)
                    .cloned()
                    .unwrap_or_default();
                let type_expr = match reconstruct_from_shard_with_level_lists(
                    &reader.exprs,
                    &reader.levels,
                    &reader.strings,
                    &reader.level_lists,
                    header.type_idx,
                ) {
                    Ok(e) => e,
                    Err(_) => continue, // skip reconstruction failures
                };
                let value_expr = if header.value_idx != NO_VALUE {
                    reconstruct_from_shard_with_level_lists(
                        &reader.exprs,
                        &reader.levels,
                        &reader.strings,
                        &reader.level_lists,
                        header.value_idx,
                    )
                    .ok()
                } else {
                    None
                };
                let level_params = reconstruct_level_params(
                    &reader.strings,
                    header.level_params_start,
                    header.level_params_count,
                )
                .unwrap_or_default();
                constants.push(ReconstructedConstant {
                    name,
                    type_expr,
                    value_expr,
                    level_params,
                });
            }
        }
        constants
    }

    /// Incremental verification result.
    struct IncrementalResult {
        total: usize,
        axiom_pass: usize,
        axiom_fail: usize,
        theorem_pass: usize,
        definition_pass: usize,
        value_fail: usize,
        skipped_reconstruct: usize,
        axiom_failure_reasons: HashMap<String, usize>,
        value_failure_reasons: HashMap<String, usize>,
    }

    /// Run incremental verification: axiom pass, then value pass.
    fn run_incremental(shard_files: &[PathBuf]) -> IncrementalResult {
        let shard_files = shard_files.to_vec();
        std::thread::Builder::new()
            .name("mathverse-incr-verify".to_string())
            .stack_size(256 * 1024 * 1024)
            .spawn(move || run_incremental_inner(&shard_files))
            .expect("spawn verify thread")
            .join()
            .expect("verify thread panicked")
    }

    /// Count raw (pre-reconstruction) constants across all shard files.
    fn count_raw_constants(shard_files: &[PathBuf]) -> usize {
        let mut count = 0usize;
        for shard_path in shard_files {
            if let Ok(reader) = ShardReader::from_file(shard_path) {
                count += reader.constants.len();
            }
        }
        count
    }

    /// Pass 1: Add each constant as Axiom (type-only) to a shared env.
    /// Returns (axiom_accepted flags, pass count, fail count, failure reasons).
    fn axiom_pass(
        env: &mut Environment,
        constants: &[ReconstructedConstant],
    ) -> (Vec<bool>, usize, usize, HashMap<String, usize>) {
        let total = constants.len();
        let mut pass = 0usize;
        let mut fail = 0usize;
        let mut reasons: HashMap<String, usize> = HashMap::new();
        let mut accepted = vec![false; total];

        eprintln!("  Pass 1: Loading {total} constants as axioms...");
        for (i, c) in constants.iter().enumerate() {
            let decl = Declaration::Axiom {
                name: Name::from_string(&c.name),
                level_params: c.level_params.clone(),
                type_: c.type_expr.clone(),
            };
            match env.add_decl(decl) {
                Ok(()) => {
                    pass += 1;
                    accepted[i] = true;
                }
                Err(e) => {
                    fail += 1;
                    *reasons.entry(classify_failure(&e.to_string())).or_insert(0) += 1;
                }
            }
            if (i + 1) % 5000 == 0 {
                eprintln!("    progress: {}/{total} ({pass} pass, {fail} fail)", i + 1);
            }
        }
        (accepted, pass, fail, reasons)
    }

    /// Pass 2: Try Theorem/Definition for constants with values.
    /// Returns (theorem_pass, def_pass, fail, failure reasons).
    fn value_pass(
        env: &mut Environment,
        constants: &[ReconstructedConstant],
        axiom_accepted: &[bool],
    ) -> (usize, usize, usize, HashMap<String, usize>) {
        let mut thm_pass = 0usize;
        let mut def_pass = 0usize;
        let mut fail = 0usize;
        let mut reasons: HashMap<String, usize> = HashMap::new();
        let with_values: usize = constants
            .iter()
            .enumerate()
            .filter(|(i, c)| axiom_accepted[*i] && c.value_expr.is_some())
            .count();

        eprintln!("  Pass 2: Checking {with_values} constants with values...");
        let mut checked = 0usize;
        for (i, c) in constants.iter().enumerate() {
            if !axiom_accepted[i] || c.value_expr.is_none() {
                continue;
            }
            let value = c.value_expr.as_ref().unwrap();
            // Use suffixed names to avoid collisions with axiom-pass entries.
            let thm_decl = Declaration::Theorem {
                name: Name::from_string(&format!("{}.thm_check", c.name)),
                level_params: c.level_params.clone(),
                type_: c.type_expr.clone(),
                value: value.clone(),
            };
            match env.add_decl(thm_decl) {
                Ok(()) => thm_pass += 1,
                Err(_) => {
                    let def_decl = Declaration::Definition {
                        name: Name::from_string(&format!("{}.def_check", c.name)),
                        level_params: c.level_params.clone(),
                        type_: c.type_expr.clone(),
                        value: value.clone(),
                        is_reducible: false,
                    };
                    match env.add_decl(def_decl) {
                        Ok(()) => def_pass += 1,
                        Err(e) => {
                            fail += 1;
                            *reasons.entry(classify_failure(&e.to_string())).or_insert(0) += 1;
                        }
                    }
                }
            }
            checked += 1;
            if checked % 5000 == 0 {
                eprintln!(
                    "    progress: {checked}/{with_values} ({thm_pass} thm, {def_pass} def, {fail} fail)"
                );
            }
        }
        (thm_pass, def_pass, fail, reasons)
    }

    fn run_incremental_inner(shard_files: &[PathBuf]) -> IncrementalResult {
        let constants = load_all_constants(shard_files);
        let total = constants.len();
        let raw_count = count_raw_constants(shard_files);
        let skipped_reconstruct = raw_count.saturating_sub(total);

        let mut env = Environment::new();
        let (accepted, axiom_pass, axiom_fail, axiom_failure_reasons) =
            axiom_pass(&mut env, &constants);
        let (theorem_pass, definition_pass, value_fail, value_failure_reasons) =
            value_pass(&mut env, &constants, &accepted);

        IncrementalResult {
            total,
            axiom_pass,
            axiom_fail,
            theorem_pass,
            definition_pass,
            value_fail,
            skipped_reconstruct,
            axiom_failure_reasons,
            value_failure_reasons,
        }
    }

    fn print_incremental_report(toolchain: &str, r: &IncrementalResult) {
        eprintln!("\n========================================");
        eprintln!("  INCREMENTAL ENV TC - INIT MODULE");
        eprintln!("========================================");
        eprintln!("Toolchain: {toolchain}");
        eprintln!();
        eprintln!("--- Pass 1: Axiom Loading (type-only) ---");
        eprintln!("  Total reconstructed:  {}", r.total);
        eprintln!("  Skipped (reconstruct): {}", r.skipped_reconstruct);
        eprintln!("  Axiom accepted:        {}", r.axiom_pass);
        eprintln!("  Axiom rejected:        {}", r.axiom_fail);
        if r.total > 0 {
            let pct = 100.0 * r.axiom_pass as f64 / r.total as f64;
            eprintln!("  Axiom pass rate:       {pct:.2}%");
        }
        if !r.axiom_failure_reasons.is_empty() {
            let mut sorted: Vec<_> = r.axiom_failure_reasons.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            eprintln!("  Axiom failure breakdown:");
            for (reason, count) in &sorted {
                eprintln!("    {count:>6}  {reason}");
            }
        }
        eprintln!();
        eprintln!("--- Pass 2: Value Verification ---");
        let with_values = r.theorem_pass + r.definition_pass + r.value_fail;
        eprintln!("  Constants with values: {with_values}");
        eprintln!("  Theorem verified:      {}", r.theorem_pass);
        eprintln!("  Definition verified:   {}", r.definition_pass);
        eprintln!("  Value rejected:        {}", r.value_fail);
        if with_values > 0 {
            let pct = 100.0 * (r.theorem_pass + r.definition_pass) as f64 / with_values as f64;
            eprintln!("  Value pass rate:       {pct:.2}%");
        }
        if !r.value_failure_reasons.is_empty() {
            let mut sorted: Vec<_> = r.value_failure_reasons.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            eprintln!("  Value failure breakdown:");
            for (reason, count) in &sorted {
                eprintln!("    {count:>6}  {reason}");
            }
        }
        eprintln!();
        eprintln!("--- Summary ---");
        let total_with_reconstruct = r.total + r.skipped_reconstruct;
        eprintln!("  Raw constants from shards: {total_with_reconstruct}");
        eprintln!("  Reconstructed:             {}", r.total);
        eprintln!("  Axioms in env:             {}", r.axiom_pass);
        let verified = r.theorem_pass + r.definition_pass;
        eprintln!("  Values verified:           {verified}");
        eprintln!();
        eprintln!("NOTE: Using reconstructed level_params from shard headers.");
    }

    #[test]
    fn test_measure_init_kernel_tc_incremental() {
        let lean4_lib = match find_lean4_lib() {
            Some(p) => p,
            None => {
                eprintln!("SKIP: No Lean 4 toolchain found under ~/.elan/toolchains/");
                return;
            }
        };
        eprintln!("Using toolchain: {}", lean4_lib.display());

        let tmp = tempfile::tempdir().expect("tempdir");
        let config = BuildConfig {
            lean_lib_dir: lean4_lib.clone(),
            output_dir: tmp.path().join("mathverse"),
            modules: vec!["Init".to_string()],
            shard_size_limit: 5000,
            max_file_size: 2_500_000,
            verbose: true,
            ..BuildConfig::default()
        };

        let build_result = build_lean4_library(&config).expect("build should succeed");
        eprintln!("=== Build Phase (Init) ===");
        eprintln!("  files_parsed:    {}", build_result.files_parsed);
        eprintln!("  total_constants: {}", build_result.total_constants);
        eprintln!("  shards_written:  {}", build_result.shards_written);

        let shard_files = collect_shard_files(&config.output_dir);
        eprintln!("  shard files found: {}", shard_files.len());

        let result = run_incremental(&shard_files);
        print_incremental_report(&lean4_lib.display().to_string(), &result);

        assert!(
            result.total > 1000,
            "expected >1000 constants, got {}",
            result.total
        );
        // The incremental approach should accept significantly more axioms
        // than the per-constant approach (which got 0.33%).
        assert!(
            result.axiom_pass > result.axiom_fail / 10,
            "expected meaningful axiom acceptance, got {}/{}",
            result.axiom_pass,
            result.total
        );
    }
}
