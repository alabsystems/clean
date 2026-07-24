// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI for verifying and inspecting `.cleancert` proof certificate bundles.
//!
//! Subcommands:
//!   verify  <path.cleancert>   Verify all theorems in the bundle
//!   inspect <path.cleancert>   List theorems with types and proof status
//!   stats   <path.cleancert>   Show bundle summary statistics
//!
//! Options:
//!   --json   Output machine-readable JSON instead of human text

use std::collections::HashMap;
use std::path::Path;
use std::process;
use std::time::Instant;

use clean_kernel::cert::bundle::CertBundle;
use clean_kernel::cert::{BundleInspectEntry, TrustLevel};
use clean_kernel::Name;

// ────────────────────────────────────────────────────────────────────────────
// Color helpers (only when stderr/stdout is a tty)
// ────────────────────────────────────────────────────────────────────────────

fn is_tty() -> bool {
    // `IsTerminal` (stable since Rust 1.70) replaces the former libc `isatty`
    // FFI, keeping every clean-kernel target free of `unsafe` in normal builds.
    std::io::IsTerminal::is_terminal(&std::io::stdout())
}

fn green(s: &str) -> String {
    if is_tty() {
        format!("\x1b[32m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}

fn red(s: &str) -> String {
    if is_tty() {
        format!("\x1b[31m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}

fn bold(s: &str) -> String {
    if is_tty() {
        format!("\x1b[1m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Trust level display
// ────────────────────────────────────────────────────────────────────────────

fn trust_level_str(t: TrustLevel) -> &'static str {
    match t {
        TrustLevel::KernelVerified => "kernel-verified",
        TrustLevel::SmtBacked => "smt-backed",
        TrustLevel::Axiom => "axiom",
        TrustLevel::Unverified => "unverified",
    }
}

fn inspect_status_str(entry: &BundleInspectEntry) -> &'static str {
    if entry.is_ready() {
        "ready"
    } else {
        "incomplete"
    }
}

fn inspect_issue_labels(entry: &BundleInspectEntry) -> Vec<&'static str> {
    entry.issues.iter().map(|issue| issue.as_str()).collect()
}

fn inspect_issue_summary(entry: &BundleInspectEntry) -> String {
    if entry.is_ready() {
        "ready".to_string()
    } else {
        inspect_issue_labels(entry).join(", ")
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Entry point
// ────────────────────────────────────────────────────────────────────────────

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let json_mode = args.iter().any(|a| a == "--json");
    // Filter out flags for positional parsing.
    let positional: Vec<&str> = args[1..]
        .iter()
        .filter(|a| !a.starts_with("--"))
        .map(|s| s.as_str())
        .collect();

    if positional.is_empty() {
        print_usage();
        process::exit(1);
    }

    let command = positional[0];
    let path = positional.get(1).copied();

    match command {
        "verify" => {
            let path = require_path(path, "verify <path.cleancert>");
            cmd_verify(path, json_mode);
        }
        "inspect" => {
            let path = require_path(path, "inspect <path.cleancert>");
            cmd_inspect(path, json_mode);
        }
        "stats" => {
            let path = require_path(path, "stats <path.cleancert>");
            cmd_stats(path, json_mode);
        }
        "help" | "--help" | "-h" => {
            print_usage();
        }
        other => {
            eprintln!("Unknown command: {other}");
            print_usage();
            process::exit(1);
        }
    }
}

fn print_usage() {
    eprintln!("clean_cert — verify and inspect .cleancert proof bundles");
    eprintln!();
    eprintln!("Usage: clean_cert <command> [options] <path.cleancert>");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  verify   Verify all theorems in the bundle (exit 0 = all pass)");
    eprintln!("  inspect  List theorems with proof status and trust levels");
    eprintln!("  stats    Show bundle summary statistics");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --json   Output machine-readable JSON");
}

fn require_path<'a>(path: Option<&'a str>, usage: &str) -> &'a Path {
    match path {
        Some(p) => Path::new(p),
        None => {
            eprintln!("Usage: clean_cert {usage}");
            process::exit(1);
        }
    }
}

fn load_bundle(path: &Path) -> CertBundle {
    match CertBundle::load(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Error loading bundle {}: {e}", path.display());
            process::exit(2);
        }
    }
}

/// Print a JSON value to stdout, exiting with the standard error code (2)
/// if serialization fails instead of panicking.
fn print_json(output: &serde_json::Value) {
    match serde_json::to_string_pretty(output) {
        Ok(rendered) => println!("{rendered}"),
        Err(e) => {
            eprintln!("Error serializing JSON output: {e}");
            process::exit(2);
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// verify
// ────────────────────────────────────────────────────────────────────────────

fn cmd_verify(path: &Path, json_mode: bool) {
    let start = Instant::now();
    let bundle = load_bundle(path);
    let inspect = bundle.inspect();
    let load_time = start.elapsed();

    let verify_start = Instant::now();
    let result = match bundle.verify_all() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Verification error: {e}");
            process::exit(2);
        }
    };
    let verify_time = verify_start.elapsed();

    if json_mode {
        let output = build_verify_json(path, &result, &inspect, load_time, verify_time);
        print_json(&output);
    } else {
        print!(
            "{}",
            render_verify_human(path, &bundle, &result, &inspect, load_time, verify_time)
        );
    }

    if !result.all_passed() {
        process::exit(1);
    }
}

fn build_verify_json(
    path: &Path,
    result: &clean_kernel::cert::bundle::BundleVerifyResult,
    inspect: &clean_kernel::cert::BundleInspectReport,
    load_time: std::time::Duration,
    verify_time: std::time::Duration,
) -> serde_json::Value {
    let failures: Vec<serde_json::Value> = result
        .failures
        .iter()
        .map(|(name, reason)| {
            let inspect_entry = inspect.entries.iter().find(|entry| entry.name == *name);
            serde_json::json!({
                "theorem": name,
                "reason": reason,
                "declaration_kind": inspect_entry.and_then(|entry| entry.declaration_kind),
                "theorem_type": inspect_entry.and_then(|entry| entry.theorem_type.clone()),
                "status": inspect_entry.map(inspect_status_str),
                "issues": inspect_entry.map(inspect_issue_labels).unwrap_or_default(),
            })
        })
        .collect();

    serde_json::json!({
        "path": path.display().to_string(),
        "passed": result.passed,
        "failed": result.failed,
        "all_passed": result.all_passed(),
        "trust_level": trust_level_str(result.trust_level),
        "ready_count": inspect.ready_count,
        "incomplete_count": inspect.incomplete_count,
        "failures": failures,
        "load_time_ms": load_time.as_millis(),
        "verify_time_ms": verify_time.as_millis(),
    })
}

fn render_verify_human(
    path: &Path,
    bundle: &CertBundle,
    result: &clean_kernel::cert::bundle::BundleVerifyResult,
    inspect: &clean_kernel::cert::BundleInspectReport,
    load_time: std::time::Duration,
    verify_time: std::time::Duration,
) -> String {
    let mut out = String::new();
    out.push_str(&format!("{} {}\n", bold("Bundle:"), path.display()));
    out.push_str(&format!(
        "{} {}\n",
        bold("Project:"),
        bundle.manifest().project
    ));
    out.push_str(&format!(
        "{} {} ready, {} incomplete\n",
        bold("Coverage:"),
        inspect.ready_count,
        inspect.incomplete_count
    ));
    out.push('\n');

    for entry in &bundle.manifest().theorems {
        let is_failure = result.failures.iter().any(|(n, _)| n == &entry.name);
        let status = if is_failure {
            red("FAIL")
        } else {
            green("PASS")
        };
        out.push_str(&format!("  [{status}] {}\n", entry.name));
        if is_failure {
            if let Some((_, reason)) = result.failures.iter().find(|(n, _)| n == &entry.name) {
                out.push_str(&format!("         {}\n", red(reason)));
            }
            if let Some(inspect_entry) = inspect.entries.iter().find(|item| item.name == entry.name)
            {
                out.push_str(&format!(
                    "         bundle state: {}\n",
                    inspect_issue_summary(inspect_entry)
                ));
            }
        }
    }

    out.push('\n');
    out.push_str(&format!(
        "Result: {} passed, {} failed ({})\n",
        result.passed,
        result.failed,
        if result.all_passed() {
            green("ALL PASSED")
        } else {
            red("FAILURES DETECTED")
        }
    ));
    out.push_str(&format!(
        "Trust level: {}\n",
        trust_level_str(result.trust_level)
    ));
    out.push_str(&format!(
        "Timing: load {:.1}ms, verify {:.1}ms\n",
        load_time.as_secs_f64() * 1000.0,
        verify_time.as_secs_f64() * 1000.0,
    ));
    out
}

// ────────────────────────────────────────────────────────────────────────────
// inspect
// ────────────────────────────────────────────────────────────────────────────

fn cmd_inspect(path: &Path, json_mode: bool) {
    let bundle = load_bundle(path);
    let manifest = bundle.manifest();
    let report = bundle.inspect();

    if json_mode {
        let theorems: Vec<serde_json::Value> = report
            .entries
            .iter()
            .map(|entry| {
                let mut obj = serde_json::json!({
                    "name": entry.name,
                    "trust_level": trust_level_str(entry.trust_level),
                    "sorry_free": entry.sorry_free,
                    "status": inspect_status_str(entry),
                    "issues": inspect_issue_labels(entry),
                    "has_certificate": entry.has_certificate,
                    "has_environment_declaration": entry.has_environment_declaration,
                    "has_proof_term": entry.has_proof_term,
                    "has_cross_project_certificate": entry.has_cross_project_certificate,
                });
                if let Some(theorem_type) = &entry.theorem_type {
                    obj["theorem_type"] = serde_json::Value::String(theorem_type.clone());
                }
                if let Some(kind) = entry.declaration_kind {
                    obj["declaration_kind"] = serde_json::Value::String(kind.to_string());
                }
                if let Some(type_hash) = &entry.type_hash {
                    obj["type_hash"] = serde_json::Value::String(type_hash.clone());
                }
                if let Some(proof_hash) = &entry.proof_hash {
                    obj["proof_hash"] = serde_json::Value::String(proof_hash.clone());
                }
                let name = Name::from_string(&entry.name);
                if let Some(xproj) = bundle.cross_project_cert(&name) {
                    obj["cross_project"] = serde_json::json!({
                        "theorem_name": xproj.theorem_name,
                        "dependencies": xproj.dependencies.len(),
                    });
                }
                obj
            })
            .collect();

        let output = serde_json::json!({
            "path": path.display().to_string(),
            "project": manifest.project,
            "clean_version": manifest.clean_version,
            "bundle_version": manifest.version,
            "theorem_count": manifest.theorems.len(),
            "ready_count": report.ready_count,
            "incomplete_count": report.incomplete_count,
            "trust_level": trust_level_str(manifest.trust_level),
            "theorems": theorems,
        });
        print_json(&output);
    } else {
        println!("{} {}", bold("Bundle:"), path.display());
        println!("{} {}", bold("Project:"), manifest.project);
        println!("{} {}", bold("clean version:"), manifest.clean_version);
        println!(
            "{} {}",
            bold("Trust level:"),
            trust_level_str(manifest.trust_level)
        );
        println!("{} {}", bold("Theorems:"), manifest.theorems.len());
        println!(
            "{} {} ready, {} incomplete",
            bold("Readiness:"),
            report.ready_count,
            report.incomplete_count
        );
        println!();

        for entry in &report.entries {
            let trust = trust_level_str(entry.trust_level);
            let sorry = if entry.sorry_free { "" } else { " [SORRY]" };
            println!(
                "  {} [{}]{} ({})",
                entry.name,
                trust,
                sorry,
                inspect_issue_summary(entry)
            );
            if let Some(theorem_type) = &entry.theorem_type {
                println!("    type:       {theorem_type}");
            }
            if let Some(kind) = entry.declaration_kind {
                println!("    decl_kind:  {kind}");
            }
            if let Some(type_hash) = &entry.type_hash {
                println!(
                    "    type_hash:  {}...",
                    &type_hash[..16.min(type_hash.len())]
                );
            }
            if let Some(proof_hash) = &entry.proof_hash {
                println!(
                    "    proof_hash: {}...",
                    &proof_hash[..16.min(proof_hash.len())]
                );
            }
            println!(
                "    cert:       {}, env: {}, proof: {}",
                if entry.has_certificate {
                    "present"
                } else {
                    "missing"
                },
                if entry.has_environment_declaration {
                    "present"
                } else {
                    "missing"
                },
                if entry.has_proof_term {
                    "present"
                } else {
                    "missing"
                }
            );
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// stats
// ────────────────────────────────────────────────────────────────────────────

fn cmd_stats(path: &Path, json_mode: bool) {
    let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);

    let bundle = load_bundle(path);
    let manifest = bundle.manifest();

    // Trust level breakdown.
    let mut trust_counts: HashMap<&'static str, usize> = HashMap::new();
    let mut sorry_count = 0usize;
    for entry in &manifest.theorems {
        *trust_counts
            .entry(trust_level_str(entry.trust_level))
            .or_insert(0) += 1;
        if !entry.sorry_free {
            sorry_count += 1;
        }
    }

    // Count axioms in environment (declarations without values).
    let axiom_names: Vec<String> = manifest
        .theorems
        .iter()
        .filter(|e| e.trust_level == TrustLevel::Axiom)
        .map(|e| e.name.clone())
        .collect();

    if json_mode {
        let output = serde_json::json!({
            "path": path.display().to_string(),
            "project": manifest.project,
            "clean_version": manifest.clean_version,
            "bundle_version": manifest.version,
            "theorem_count": manifest.theorems.len(),
            "axiom_count": axiom_names.len(),
            "sorry_count": sorry_count,
            "trust_level": trust_level_str(manifest.trust_level),
            "trust_breakdown": trust_counts,
            "env_hash": manifest.env_hash,
            "bundle_size_bytes": file_size,
            "has_trust_chain": bundle.trust_chain().is_some(),
        });
        print_json(&output);
    } else {
        println!("{} {}", bold("Bundle:"), path.display());
        println!("{} {}", bold("Project:"), manifest.project);
        println!("{} {}", bold("clean version:"), manifest.clean_version);
        println!("{} v{}", bold("Bundle format:"), manifest.version);
        println!();

        println!("{}", bold("Summary:"));
        println!("  Theorems:      {}", manifest.theorems.len());
        println!("  Axioms:        {}", axiom_names.len());
        if sorry_count > 0 {
            println!("  Sorry:         {}", red(&sorry_count.to_string()));
        }
        println!("  Trust level:   {}", trust_level_str(manifest.trust_level));
        println!(
            "  Trust chain:   {}",
            if bundle.trust_chain().is_some() {
                "present"
            } else {
                "absent"
            }
        );
        println!();

        println!("{}", bold("Trust Breakdown:"));
        for (level, count) in &trust_counts {
            println!("  {level:<20} {count}");
        }
        println!();

        println!("{}", bold("Hashes:"));
        println!("  env_hash: {}", manifest.env_hash);
        println!();

        println!("{}", bold("Size:"));
        println!(
            "  Bundle: {} bytes ({:.1} KB)",
            file_size,
            file_size as f64 / 1024.0
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::cert::ProofCert;
    use clean_kernel::{Declaration, Environment, Expr};

    fn axiom_bundle() -> CertBundle {
        let mut env = Environment::with_prelude();
        let theorem_name = Name::from_string("Test.assumed");
        env.add_decl(Declaration::Axiom {
            name: theorem_name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register axiom");

        let mut certs = HashMap::new();
        certs.insert(
            theorem_name,
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
            },
        );

        CertBundle::build("test-project", "0.1.0", env, certs, HashMap::new(), None)
            .expect("build bundle")
    }

    #[test]
    fn verify_renderers_report_bundle_readiness_for_failures() {
        let bundle = axiom_bundle();
        let inspect = bundle.inspect();
        let result = bundle
            .verify_all()
            .expect("verify_all should return a result");
        let json = build_verify_json(
            Path::new("fixture.cleancert"),
            &result,
            &inspect,
            std::time::Duration::ZERO,
            std::time::Duration::ZERO,
        );
        let failure = &json["failures"][0];

        assert_eq!(json["passed"], 0);
        assert_eq!(json["failed"], 1);
        assert_eq!(json["all_passed"], false);
        assert_eq!(json["ready_count"], 0);
        assert_eq!(json["incomplete_count"], 1);
        assert_eq!(failure["theorem"], "Test.assumed");
        assert_eq!(failure["status"], "incomplete");
        assert_eq!(failure["issues"], serde_json::json!(["missing-proof-term"]));
        assert_eq!(failure["declaration_kind"], "axiom");
        assert_eq!(failure["theorem_type"], "True");
        assert_eq!(
            failure["reason"],
            "verification failed for theorem 'Test.assumed': declaration has no proof term"
        );

        let human = render_verify_human(
            Path::new("fixture.cleancert"),
            &bundle,
            &result,
            &inspect,
            std::time::Duration::ZERO,
            std::time::Duration::ZERO,
        );
        assert!(human.contains("Coverage: 0 ready, 1 incomplete"));
        assert!(human.contains("[FAIL] Test.assumed"));
        assert!(human.contains("declaration has no proof term"));
        assert!(human.contains("bundle state: missing-proof-term"));
        assert!(human.contains("Result: 0 passed, 1 failed (FAILURES DETECTED)"));
    }
}
