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

            // Optional: dump the FULL axiom closure of every ACCEPTED
            // declaration, so a `ProofQuality::Constructive` verdict can be
            // adjudicated on the trust it actually consumes rather than on
            // its name. Symmetric with `MATHVERSE_DUMP_REJECTS` below, and
            // like it, off unless explicitly requested — the default build
            // path is byte-identical without the variable.
            if let Ok(path) = std::env::var("MATHVERSE_DUMP_ACCEPTED_CLOSURE") {
                dump_accepted_closure(&env, &result, &PathBuf::from(path));
            }

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

/// Write `{name -> closure evidence}` for every ACCEPTED declaration.
///
/// The evidence per name is deliberately the four facts a reviewer needs to
/// either ratify or reject the shard's `Constructive` label, and no summary
/// on top of them:
///
/// * `kind` / `has_value` — a `Theorem` carrying a proof term. `proof_quality`
///   classifies a value-less theorem `Unchecked`, so both are load-bearing.
/// * `domain_axiom_closure` — MUST be empty; this is the predicate the shard
///   actually filters on.
/// * `foundational_axiom_closure` — the half `axiom_deps` throws away. This is
///   where `Classical.choice` shows up, and it is the difference between
///   "reaches nothing" and "reaches classical choice" — two very different
///   theorems that an empty `domain_axiom_closure` reports identically.
/// * `declaration_verification` — `FullKernelCheck` vs `StructuralOnly`.
///   `Environment::proof_quality` documents that it CANNOT see this
///   distinction: a structurally-added theorem still carries its value and is
///   labelled `Constructive` by its axiom closure exactly like a checked one.
///   `None` is recorded verbatim as unknown and never read as a pass.
fn dump_accepted_closure(
    env: &Environment,
    result: &clean_mathverse::build_library_native::CleanNativeBuildResult,
    path: &PathBuf,
) {
    use clean_kernel::Name;

    let mut rows = Vec::new();
    for d in &result.decisions {
        if !d.accepted {
            continue;
        }
        let name = Name::from_string(&d.name);
        let info = env.get_const(&name);
        let mut foundational: Vec<String> = env
            .foundational_axiom_deps(&name)
            .map(|s| s.into_iter().map(|n| n.to_string()).collect())
            .unwrap_or_default();
        foundational.sort();
        let mut domain: Vec<String> = env
            .axiom_deps(&name)
            .map(|s| s.into_iter().map(|n| n.to_string()).collect())
            .unwrap_or_default();
        domain.sort();
        rows.push(serde_json::json!({
            "name": d.name,
            "kind": info.map(|i| format!("{:?}", i.kind)),
            "has_value": info.map(|i| i.value.is_some()),
            "domain_axiom_closure": domain,
            "foundational_axiom_closure": foundational,
            "declaration_verification": env
                .declaration_verification(&name)
                .map(|v| format!("{v:?}")),
        }));
    }

    let payload = serde_json::json!({
        "accepted_count": rows.len(),
        "declarations": rows,
    });
    match serde_json::to_string_pretty(&payload) {
        Ok(text) => {
            if let Err(e) = fs::write(path, text + "\n") {
                eprintln!("Warning: accepted-closure dump failed: {e}");
            } else {
                println!("  Accepted-closure dump: {}", path.display());
            }
        }
        Err(e) => eprintln!("Warning: accepted-closure dump serialize failed: {e}"),
    }
}
