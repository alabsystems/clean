// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_shard build-native` implementation — thin CLI wrapper around
//! [`clean_mathverse::build_library_native::build_clean_native_library`].
//!
//! Kept in its own file so the top-level `main.rs` stays under the
//! project-wide 500-line cap.

use std::fs;
use std::path::PathBuf;

use clean_kernel::Environment;
use clean_mathverse::build_library_native::{
    build_native_shard_with_config, seed_native_environment, NativeBuildConfig,
};

pub fn cmd_build_native(args: &[String]) {
    // `--gate-clean` produces a shard that passes `shard_verify::native_gate`
    // (NN-content excluded, prelude constants skipped). Default keeps the
    // historical whole-environment export.
    let gate_clean = args.iter().any(|a| a == "--gate-clean");
    let output_dir = match args.iter().find(|a| !a.starts_with("--")) {
        Some(p) => PathBuf::from(p),
        None => {
            eprintln!("Usage: mathverse_shard build-native <output-dir> [--gate-clean]");
            std::process::exit(1);
        }
    };
    fs::create_dir_all(&output_dir).unwrap_or_else(|e| {
        eprintln!(
            "Error: failed to create output dir {}: {e}",
            output_dir.display()
        );
        std::process::exit(1);
    });

    println!("=== Building clean-Native Mathverse Shard ===");
    println!("  Output dir: {}", output_dir.display());
    println!("  Gate-clean: {gate_clean}");

    let mut env = Environment::new();
    seed_native_environment(&mut env);

    let config = NativeBuildConfig {
        gate_clean,
        ..Default::default()
    };
    match build_native_shard_with_config(&env, &output_dir, &config) {
        Ok(result) => {
            println!();
            println!("=== Build Complete ===");
            println!("  Shard:                  {}", result.shard_path.display());
            println!(
                "  Sidecar:                {}",
                result.sidecar_path.display()
            );
            println!("  Total declarations:     {}", result.total_declarations);
            println!("  Constructive theorems:  {}", result.constructive_theorems);
            println!(
                "  Axiom-dependent reject: {}",
                result.axiom_dependent_rejected
            );
            println!("  Unchecked reject:       {}", result.unchecked_rejected);
            println!("  Non-foundational axiom: {}", result.axioms_rejected);
            println!(
                "  Foundational axioms:    {}",
                result.foundational_axioms_skipped
            );
            println!("  Definitions skipped:    {}", result.definitions_skipped);
            println!(
                "  Content-profiled (NN):  {}",
                result.content_profiled_rejected
            );
            println!("  In-prelude skipped:     {}", result.prelude_skipped);
            println!(
                "  Flatten failures:       {}",
                result.flatten_failures.len()
            );
            println!("  Elapsed:                {} ms", result.elapsed_ms);

            // Optional: dump per-reject classification for triage
            // (#3551 Tier D axiom-reject whitelisting work).
            if std::env::var("MATHVERSE_DUMP_REJECTS").is_ok() {
                println!();
                println!("=== Rejected declarations (by reason) ===");
                for d in &result.decisions {
                    if d.accepted {
                        continue;
                    }
                    if let Some(reason) = &d.exclude_reason {
                        println!("  {} | {:?}", d.name, reason);
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("Build failed: {e}");
            std::process::exit(1);
        }
    }
}
