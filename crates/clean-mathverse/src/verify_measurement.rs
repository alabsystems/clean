// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check pass rate measurement for Mathverse Library constants.
//!
//! Builds an Mathverse Library from Lean 4 `.olean` files, loads the built shards,
//! and runs kernel type-checking on every constant via `reconstruct_from_shard`
//! + `Environment::add_decl()`. Reports pass/fail rates for updating
//! `data/MATHVERSE_KERNEL_COMPATIBILITY.md`.

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
    /// Searches `~/.elan/toolchains/*/lib/lean/` for directories containing
    /// `Init.olean`.
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
        // Sort and take the latest (by directory name, which is version-sortable).
        candidates.sort();
        candidates.pop()
    }

    /// Outcome of verifying a single constant.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Outcome {
        /// Kernel accepted as theorem (type + value).
        KernelVerifiedTheorem,
        /// Kernel accepted as definition (type + value, not Prop).
        KernelVerifiedDefinition,
        /// Kernel accepted type as axiom (no value, or value failed).
        AxiomAccepted,
        /// FlatExpr reconstruction failed.
        ReconstructFailed(String),
        /// Kernel type-check rejected the declaration.
        TypeCheckFailed(String),
    }

    /// Verify a single constant from a shard's arenas.
    fn verify_constant(
        reader: &ShardReader,
        ci: usize,
        header: &MathverseConstantHeader,
    ) -> Outcome {
        // Reconstruct the type expression.
        let type_expr = match reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            header.type_idx,
        ) {
            Ok(e) => e,
            Err(e) => return Outcome::ReconstructFailed(format!("type: {e}")),
        };

        // Reconstruct the value expression (if present).
        let value_expr = if header.value_idx != NO_VALUE {
            match reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.value_idx,
            ) {
                Ok(e) => Some(e),
                Err(e) => return Outcome::ReconstructFailed(format!("value: {e}")),
            }
        } else {
            None
        };

        // Reconstruct declaration-level universe parameter names.
        let level_params = reconstruct_level_params(
            &reader.strings,
            header.level_params_start,
            header.level_params_count,
        )
        .unwrap_or_default();

        let name_str = reader
            .strings
            .get(header.name_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or("<unknown>");

        // Try as theorem first if we have a value.
        if let Some(ref value) = value_expr {
            let theorem_name = Name::from_string(&format!("measure.{ci}.{name_str}"));
            let theorem_decl = Declaration::Theorem {
                name: theorem_name,
                level_params: level_params.clone(),
                type_: type_expr.clone(),
                value: value.clone(),
            };
            let mut env = Environment::new();
            if env.add_decl(theorem_decl).is_ok() {
                return Outcome::KernelVerifiedTheorem;
            }

            // Theorem failed -- try as definition.
            let def_name = Name::from_string(&format!("measure.{ci}.{name_str}.def"));
            let def_decl = Declaration::Definition {
                name: def_name,
                level_params: level_params.clone(),
                type_: type_expr.clone(),
                value: value.clone(),
                is_reducible: false,
            };
            let mut env2 = Environment::new();
            if env2.add_decl(def_decl).is_ok() {
                return Outcome::KernelVerifiedDefinition;
            }
        }

        // Fall back to axiom (type-only verification).
        let axiom_name = Name::from_string(&format!("measure.{ci}.{name_str}.axiom"));
        let axiom_decl = Declaration::Axiom {
            name: axiom_name,
            level_params,
            type_: type_expr,
        };
        let mut env3 = Environment::new();
        match env3.add_decl(axiom_decl) {
            Ok(()) => Outcome::AxiomAccepted,
            Err(e) => Outcome::TypeCheckFailed(e.to_string()),
        }
    }

    /// Classify a failure reason into a short bucket name for grouping.
    fn classify_failure(reason: &str) -> String {
        if reason.contains("out of bounds") {
            "expr/level index out of bounds".to_string()
        } else if reason.contains("unsupported") {
            "unsupported expression tag".to_string()
        } else if reason.contains("invalid FlatExpr tag")
            || reason.contains("invalid FlatLevel tag")
        {
            "invalid flat tag".to_string()
        } else if reason.contains("binder info") {
            "invalid binder info".to_string()
        } else if reason.contains("unknown constant") || reason.contains("Unknown constant") {
            "unknown constant reference".to_string()
        } else if reason.contains("type mismatch") {
            "type mismatch".to_string()
        } else if reason.contains("universe") || reason.contains("Universe") {
            "universe level error".to_string()
        } else if reason.contains("function expected") {
            "function expected".to_string()
        } else if reason.contains("deep recursion") || reason.contains("stack") {
            "stack/recursion limit".to_string()
        } else if reason.len() > 80 {
            format!("{}...", &reason[..80])
        } else {
            reason.to_string()
        }
    }

    /// Collect .mathverse shard files from the output directory.
    /// LibraryLoader writes base shards to `output_dir/base/` and deltas to
    /// `output_dir/delta/`.
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

    /// Verification result tuple.
    type VerifyResult = (
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        HashMap<String, usize>,
        Vec<(String, String)>,
    );

    /// Run kernel TC verification on all constants across all shard files.
    /// Returns (total, theorem_verified, def_verified, axiom_accepted,
    ///          reconstruct_failed, tc_failed, failure_reasons, sample_failures).
    fn run_verification(shard_files: &[PathBuf]) -> VerifyResult {
        // Spawn a thread with 256MB stack to handle deeply recursive expressions.
        let shard_files = shard_files.to_vec();
        std::thread::Builder::new()
            .name("mathverse-verify".to_string())
            .stack_size(256 * 1024 * 1024)
            .spawn(move || run_verification_inner(&shard_files))
            .expect("spawn verify thread")
            .join()
            .expect("verify thread panicked")
    }

    fn run_verification_inner(shard_files: &[PathBuf]) -> VerifyResult {
        let mut total_constants = 0usize;
        let mut kernel_verified_theorem = 0usize;
        let mut kernel_verified_def = 0usize;
        let mut axiom_accepted = 0usize;
        let mut reconstruct_failed = 0usize;
        let mut type_check_failed = 0usize;
        let mut failure_reasons: HashMap<String, usize> = HashMap::new();
        let mut sample_failures: Vec<(String, String)> = Vec::new();

        for shard_path in shard_files {
            let reader = match ShardReader::from_file(shard_path) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("  WARN: failed to load shard {}: {e}", shard_path.display());
                    continue;
                }
            };

            for (ci, header) in reader.constants.iter().enumerate() {
                total_constants += 1;
                let outcome = verify_constant(&reader, ci, header);

                match &outcome {
                    Outcome::KernelVerifiedTheorem => kernel_verified_theorem += 1,
                    Outcome::KernelVerifiedDefinition => kernel_verified_def += 1,
                    Outcome::AxiomAccepted => axiom_accepted += 1,
                    Outcome::ReconstructFailed(reason) => {
                        reconstruct_failed += 1;
                        let bucket = classify_failure(reason);
                        *failure_reasons.entry(bucket).or_insert(0) += 1;
                        if sample_failures.len() < 30 {
                            let name = reader
                                .strings
                                .get(header.name_idx as usize)
                                .cloned()
                                .unwrap_or_default();
                            sample_failures.push((name, reason.clone()));
                        }
                    }
                    Outcome::TypeCheckFailed(reason) => {
                        type_check_failed += 1;
                        let bucket = classify_failure(reason);
                        *failure_reasons.entry(bucket).or_insert(0) += 1;
                        if sample_failures.len() < 30 {
                            let name = reader
                                .strings
                                .get(header.name_idx as usize)
                                .cloned()
                                .unwrap_or_default();
                            sample_failures.push((name, reason.clone()));
                        }
                    }
                }

                if total_constants % 5000 == 0 {
                    eprintln!("  progress: {total_constants} constants verified...");
                }
            }
        }

        (
            total_constants,
            kernel_verified_theorem,
            kernel_verified_def,
            axiom_accepted,
            reconstruct_failed,
            type_check_failed,
            failure_reasons,
            sample_failures,
        )
    }

    /// Print a formatted report.
    fn print_report(
        title: &str,
        toolchain: &str,
        total_constants: usize,
        kernel_verified_theorem: usize,
        kernel_verified_def: usize,
        axiom_accepted: usize,
        reconstruct_failed: usize,
        type_check_failed: usize,
        failure_reasons: &HashMap<String, usize>,
        sample_failures: &[(String, String)],
    ) {
        let kernel_verified_total = kernel_verified_theorem + kernel_verified_def;
        let total_accepted = kernel_verified_total + axiom_accepted;
        let total_failed = reconstruct_failed + type_check_failed;

        eprintln!("\n========================================");
        eprintln!("  {title}");
        eprintln!("========================================");
        eprintln!("Toolchain: {toolchain}");
        eprintln!("Max file size: 2.5MB");
        eprintln!();
        eprintln!("--- Totals ---");
        eprintln!("  Total constants:          {total_constants}");
        eprintln!("  Kernel verified (theorem): {kernel_verified_theorem}");
        eprintln!("  Kernel verified (defn):    {kernel_verified_def}");
        eprintln!("  Kernel verified (total):   {kernel_verified_total}");
        eprintln!("  Axiom accepted:            {axiom_accepted}");
        eprintln!("  Total accepted:            {total_accepted}");
        eprintln!("  Reconstruct failed:        {reconstruct_failed}");
        eprintln!("  Type-check failed:         {type_check_failed}");
        eprintln!("  Total failed:              {total_failed}");

        if total_constants > 0 {
            let verified_pct = 100.0 * kernel_verified_total as f64 / total_constants as f64;
            let accepted_pct = 100.0 * total_accepted as f64 / total_constants as f64;
            let failed_pct = 100.0 * total_failed as f64 / total_constants as f64;
            eprintln!();
            eprintln!("--- Rates ---");
            eprintln!("  Kernel verified rate: {verified_pct:.2}%");
            eprintln!("  Total accepted rate:  {accepted_pct:.2}%");
            eprintln!("  Failure rate:         {failed_pct:.2}%");
        }

        if !failure_reasons.is_empty() {
            let mut sorted: Vec<_> = failure_reasons.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            eprintln!();
            eprintln!("--- Failure Breakdown ---");
            for (reason, count) in &sorted {
                eprintln!("  {count:>6}  {reason}");
            }
        }

        if !sample_failures.is_empty() {
            eprintln!();
            eprintln!("--- Sample Failures (first {}) ---", sample_failures.len());
            for (name, reason) in sample_failures {
                let short = if reason.len() > 120 {
                    format!("{}...", &reason[..120])
                } else {
                    reason.clone()
                };
                eprintln!("  {name}: {short}");
            }
        }
    }

    #[test]
    fn test_measure_init_kernel_tc_pass_rates() {
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
        };

        let build_result = build_lean4_library(&config).expect("build should succeed");
        eprintln!("=== Build Phase (Init) ===");
        eprintln!("  files_parsed:    {}", build_result.files_parsed);
        eprintln!("  files_failed:    {}", build_result.files_failed);
        eprintln!("  total_constants: {}", build_result.total_constants);
        eprintln!("  shards_written:  {}", build_result.shards_written);

        let shard_files = collect_shard_files(&config.output_dir);
        eprintln!("  shard files found: {}", shard_files.len());

        let (total, thm, def, axiom, recon_fail, tc_fail, reasons, samples) =
            run_verification(&shard_files);

        print_report(
            "KERNEL TC PASS RATE - INIT MODULE",
            &lean4_lib.display().to_string(),
            total,
            thm,
            def,
            axiom,
            recon_fail,
            tc_fail,
            &reasons,
            &samples,
        );

        assert!(total > 1000, "expected >1000 constants, got {total}");
    }

    #[test]
    fn test_measure_all_modules_kernel_tc_pass_rates() {
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
            modules: vec![], // all modules
            shard_size_limit: 10_000,
            max_file_size: 2_500_000,
            verbose: true,
        };

        let build_result = build_lean4_library(&config).expect("build should succeed");
        eprintln!("=== Build Phase (All Modules) ===");
        eprintln!("  files_parsed:    {}", build_result.files_parsed);
        eprintln!("  files_failed:    {}", build_result.files_failed);
        eprintln!("  total_constants: {}", build_result.total_constants);
        eprintln!("  shards_written:  {}", build_result.shards_written);

        let shard_files = collect_shard_files(&config.output_dir);

        let (total, thm, def, axiom, recon_fail, tc_fail, reasons, samples) =
            run_verification(&shard_files);

        print_report(
            "KERNEL TC PASS RATE - ALL MODULES",
            &lean4_lib.display().to_string(),
            total,
            thm,
            def,
            axiom,
            recon_fail,
            tc_fail,
            &reasons,
            &samples,
        );

        assert!(
            total > 10_000,
            "expected >10K constants for all modules, got {total}"
        );
    }
}
