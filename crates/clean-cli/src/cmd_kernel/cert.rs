// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel cert verify|inspect|stats` handlers (#3447).
//!
//! In-process. Uses `clean_kernel::cert::bundle::CertBundle` directly. These
//! verbs operate on `.cleancert` bundles; the top-level `clean cert verify`
//! verb (Phase 2) still handles the single `ProofCert` + `Expr` JSON pair
//! shape.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;
use std::time::Instant;

use anyhow::{anyhow, bail};
use clean_kernel::cert::bundle::CertBundle;
use clean_kernel::cert::{BundleInspectEntry, TrustLevel};
use clean_kernel::cli::KernelCertCommands;
use clean_kernel::Name;

pub(super) fn dispatch(command: KernelCertCommands) -> anyhow::Result<()> {
    match command {
        KernelCertCommands::Verify { path, json } => verify(&path, json),
        KernelCertCommands::Inspect { path, json } => inspect(&path, json),
        KernelCertCommands::Stats { path, json } => stats(&path, json),
    }
}

fn trust_level_str(t: TrustLevel) -> &'static str {
    match t {
        TrustLevel::KernelVerified => "kernel-verified",
        TrustLevel::SmtBacked => "smt-backed",
        TrustLevel::Axiom => "axiom",
        TrustLevel::Unverified => "unverified",
    }
}

fn load_bundle(path: &Path) -> anyhow::Result<CertBundle> {
    CertBundle::load(path).map_err(|e| anyhow!("loading bundle {}: {e}", path.display()))
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

// ─── verify ─────────────────────────────────────────────────────────────────

fn verify(path: &Path, json: bool) -> anyhow::Result<()> {
    let start = Instant::now();
    let bundle = load_bundle(path)?;
    let inspect = bundle.inspect();
    let load_time = start.elapsed();

    let verify_start = Instant::now();
    let result = bundle
        .verify_all()
        .map_err(|e| anyhow!("verification error: {e}"))?;
    let verify_time = verify_start.elapsed();

    if json {
        emit_verify_json(path, &result, &inspect, load_time, verify_time)?;
    } else {
        emit_verify_human(path, &bundle, &result, &inspect, load_time, verify_time);
    }

    if !result.all_passed() {
        bail!("kernel cert verify: one or more theorems failed");
    }
    Ok(())
}

fn emit_verify_json(
    path: &Path,
    result: &clean_kernel::cert::bundle::BundleVerifyResult,
    inspect: &clean_kernel::cert::BundleInspectReport,
    load_time: std::time::Duration,
    verify_time: std::time::Duration,
) -> anyhow::Result<()> {
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
    let output = serde_json::json!({
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
    });
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

fn emit_verify_human(
    path: &Path,
    bundle: &CertBundle,
    result: &clean_kernel::cert::bundle::BundleVerifyResult,
    inspect: &clean_kernel::cert::BundleInspectReport,
    load_time: std::time::Duration,
    verify_time: std::time::Duration,
) {
    println!("Bundle: {}", path.display());
    println!("Project: {}", bundle.manifest().project);
    println!(
        "Coverage: {} ready, {} incomplete",
        inspect.ready_count, inspect.incomplete_count
    );
    println!();
    for entry in &bundle.manifest().theorems {
        let is_failure = result.failures.iter().any(|(n, _)| n == &entry.name);
        let status = if is_failure { "FAIL" } else { "PASS" };
        println!("  [{status}] {}", entry.name);
        if is_failure {
            if let Some((_, reason)) = result.failures.iter().find(|(n, _)| n == &entry.name) {
                println!("         {reason}");
            }
            if let Some(inspect_entry) = inspect.entries.iter().find(|item| item.name == entry.name)
            {
                println!(
                    "         bundle state: {}",
                    inspect_issue_summary(inspect_entry)
                );
            }
        }
    }
    println!();
    println!(
        "Result: {} passed, {} failed ({})",
        result.passed,
        result.failed,
        if result.all_passed() {
            "ALL PASSED"
        } else {
            "FAILURES DETECTED"
        }
    );
    println!("Trust level: {}", trust_level_str(result.trust_level));
    println!(
        "Timing: load {:.1}ms, verify {:.1}ms",
        load_time.as_secs_f64() * 1000.0,
        verify_time.as_secs_f64() * 1000.0,
    );
}

// ─── inspect ────────────────────────────────────────────────────────────────

fn inspect(path: &Path, json: bool) -> anyhow::Result<()> {
    // `verify` is the trust verb and fails closed. `inspect` is the *diagnostic*
    // verb: when the trust loader refuses a bundle, the user still needs to be
    // told WHAT is not ready (e.g. "theorem X has no proof term") rather than
    // only that something is. The quarantined read pins every recorded trust
    // claim to `unverified`, and the command still exits non-zero, so no gate
    // is loosened by producing the report.
    let strict_error = match CertBundle::load(path) {
        Ok(bundle) => {
            let report = bundle.inspect();
            if json {
                emit_inspect_json(path, &bundle, &report)?;
            } else {
                emit_inspect_human(path, &bundle, &report);
            }
            return Ok(());
        }
        Err(error) => error,
    };

    let bundle = CertBundle::load_for_inspection(path).map_err(|diagnostic_error| {
        anyhow!(
            "loading bundle {}: {strict_error} \
             (quarantined read also failed: {diagnostic_error})",
            path.display()
        )
    })?;
    let report = bundle.inspect();

    if json {
        let mut output = build_inspect_json(path, &bundle, &report);
        output["rejected"] = serde_json::Value::Bool(true);
        output["rejection_reason"] = serde_json::Value::String(strict_error.to_string());
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("REJECTED by the trust loader: {strict_error}");
        println!("Quarantined readiness diagnostics follow; nothing in this bundle is verified.");
        println!();
        emit_inspect_human(path, &bundle, &report);
    }
    bail!("loading bundle {}: {strict_error}", path.display())
}

fn emit_inspect_json(
    path: &Path,
    bundle: &CertBundle,
    report: &clean_kernel::cert::BundleInspectReport,
) -> anyhow::Result<()> {
    let output = build_inspect_json(path, bundle, report);
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

fn build_inspect_json(
    path: &Path,
    bundle: &CertBundle,
    report: &clean_kernel::cert::BundleInspectReport,
) -> serde_json::Value {
    let manifest = bundle.manifest();
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
    output
}

fn emit_inspect_human(
    path: &Path,
    bundle: &CertBundle,
    report: &clean_kernel::cert::BundleInspectReport,
) {
    print!("{}", render_inspect_human(path, bundle, report));
}

fn render_inspect_human(
    path: &Path,
    bundle: &CertBundle,
    report: &clean_kernel::cert::BundleInspectReport,
) -> String {
    let manifest = bundle.manifest();
    let mut out = String::new();
    writeln!(&mut out, "Bundle: {}", path.display()).expect("write to string");
    writeln!(&mut out, "Project: {}", manifest.project).expect("write to string");
    writeln!(&mut out, "clean version: {}", manifest.clean_version).expect("write to string");
    writeln!(
        &mut out,
        "Trust level: {}",
        trust_level_str(manifest.trust_level)
    )
    .expect("write to string");
    writeln!(&mut out, "Theorems: {}", manifest.theorems.len()).expect("write to string");
    writeln!(
        &mut out,
        "Readiness: {} ready, {} incomplete",
        report.ready_count, report.incomplete_count
    )
    .expect("write to string");
    writeln!(&mut out).expect("write to string");
    for entry in &report.entries {
        let trust = trust_level_str(entry.trust_level);
        let sorry = if entry.sorry_free { "" } else { " [SORRY]" };
        writeln!(
            &mut out,
            "  {} [{}]{} ({})",
            entry.name,
            trust,
            sorry,
            inspect_issue_summary(entry)
        )
        .expect("write to string");
        if let Some(theorem_type) = &entry.theorem_type {
            writeln!(&mut out, "    type:       {theorem_type}").expect("write to string");
        }
        if let Some(kind) = entry.declaration_kind {
            writeln!(&mut out, "    decl_kind:  {kind}").expect("write to string");
        }
        if let Some(type_hash) = &entry.type_hash {
            let preview = &type_hash[..16.min(type_hash.len())];
            writeln!(&mut out, "    type_hash:  {preview}...").expect("write to string");
        }
        if let Some(proof_hash) = &entry.proof_hash {
            let preview = &proof_hash[..16.min(proof_hash.len())];
            writeln!(&mut out, "    proof_hash: {preview}...").expect("write to string");
        }
        writeln!(
            &mut out,
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
        )
        .expect("write to string");
    }
    out
}

// ─── stats ──────────────────────────────────────────────────────────────────

struct StatsSummary {
    trust_counts: HashMap<&'static str, usize>,
    sorry_count: usize,
    axiom_names: Vec<String>,
    file_size: u64,
}

fn collect_stats(path: &Path, bundle: &CertBundle) -> StatsSummary {
    let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    let manifest = bundle.manifest();
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
    let axiom_names: Vec<String> = manifest
        .theorems
        .iter()
        .filter(|e| e.trust_level == TrustLevel::Axiom)
        .map(|e| e.name.clone())
        .collect();
    StatsSummary {
        trust_counts,
        sorry_count,
        axiom_names,
        file_size,
    }
}

fn stats(path: &Path, json: bool) -> anyhow::Result<()> {
    let bundle = load_bundle(path)?;
    let summary = collect_stats(path, &bundle);

    if json {
        emit_stats_json(path, &bundle, &summary)?;
    } else {
        emit_stats_human(path, &bundle, &summary);
    }
    Ok(())
}

fn emit_stats_json(path: &Path, bundle: &CertBundle, s: &StatsSummary) -> anyhow::Result<()> {
    let manifest = bundle.manifest();
    let output = serde_json::json!({
        "path": path.display().to_string(),
        "project": manifest.project,
        "clean_version": manifest.clean_version,
        "bundle_version": manifest.version,
        "theorem_count": manifest.theorems.len(),
        "axiom_count": s.axiom_names.len(),
        "sorry_count": s.sorry_count,
        "trust_level": trust_level_str(manifest.trust_level),
        "trust_breakdown": s.trust_counts,
        "env_hash": manifest.env_hash,
        "bundle_size_bytes": s.file_size,
        "has_trust_chain": bundle.trust_chain().is_some(),
    });
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

fn emit_stats_human(path: &Path, bundle: &CertBundle, s: &StatsSummary) {
    let manifest = bundle.manifest();
    println!("Bundle: {}", path.display());
    println!("Project: {}", manifest.project);
    println!("Clean version: {}", manifest.clean_version);
    println!("Bundle format: v{}", manifest.version);
    println!();
    println!("Summary:");
    println!("  Theorems:      {}", manifest.theorems.len());
    println!("  Axioms:        {}", s.axiom_names.len());
    if s.sorry_count > 0 {
        println!("  Sorry:         {}", s.sorry_count);
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
    println!("Trust Breakdown:");
    for (level, count) in &s.trust_counts {
        println!("  {level:<20} {count}");
    }
    println!();
    println!("Hashes:");
    println!("  env_hash: {}", manifest.env_hash);
    println!();
    println!("Size:");
    println!(
        "  Bundle: {} bytes ({:.1} KB)",
        s.file_size,
        s.file_size as f64 / 1024.0
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::cert::{ProofCert, TrustLevel};
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

        // `CertBundle::build` deliberately refuses this fixture: a manifest
        // entry is a claim of proof authority and `Test.assumed` has none.
        // `for_inspection` is the quarantined view that lets the readiness
        // renderers describe exactly that deficiency.
        CertBundle::for_inspection("test-project", "0.1.0", env, certs, HashMap::new())
            .expect("assemble diagnostics view")
    }

    #[test]
    fn inspect_renderers_report_readiness_diagnostics() {
        let bundle = axiom_bundle();
        let report = bundle.inspect();
        let json = build_inspect_json(Path::new("fixture.cleancert"), &bundle, &report);
        let theorem = &json["theorems"][0];

        assert_eq!(json["ready_count"], 0);
        assert_eq!(json["incomplete_count"], 1);
        assert_eq!(theorem["name"], "Test.assumed");
        assert_eq!(theorem["status"], "incomplete");
        assert_eq!(theorem["issues"], serde_json::json!(["missing-proof-term"]));
        assert_eq!(theorem["declaration_kind"], "axiom");
        assert_eq!(theorem["theorem_type"], "True");
        assert_eq!(theorem["has_certificate"], true);
        assert_eq!(theorem["has_environment_declaration"], true);
        assert_eq!(theorem["has_proof_term"], false);
        assert_eq!(
            theorem["trust_level"],
            trust_level_str(TrustLevel::Unverified)
        );

        let human = render_inspect_human(Path::new("fixture.cleancert"), &bundle, &report);
        assert!(human.contains("Readiness: 0 ready, 1 incomplete"));
        assert!(human.contains("Test.assumed [unverified] (missing-proof-term)"));
        assert!(human.contains("type:       True"));
        assert!(human.contains("decl_kind:  axiom"));
        assert!(human.contains("cert:       present, env: present, proof: missing"));
    }

    /// The readiness renderers exist to say what is *not* ready; they must
    /// never launder an assumed theorem into a proved or certified one.
    #[test]
    fn inspect_renderers_never_present_an_assumed_theorem_as_proved() {
        let bundle = axiom_bundle();
        let report = bundle.inspect();
        let json = build_inspect_json(Path::new("fixture.cleancert"), &bundle, &report);

        assert_eq!(json["trust_level"], trust_level_str(TrustLevel::Unverified));
        assert_eq!(
            json["theorems"][0]["trust_level"],
            trust_level_str(TrustLevel::Unverified)
        );
        // No proof term exists, so no proof hash may be published for it.
        assert!(json["theorems"][0].get("proof_hash").is_none());

        let human = render_inspect_human(Path::new("fixture.cleancert"), &bundle, &report);
        for forbidden in ["kernel-verified", "smt-backed", "proof: present"] {
            assert!(
                !human.contains(forbidden),
                "quarantined diagnostics leaked `{forbidden}`:\n{human}"
            );
        }

        // And the diagnostics view is not a route to a trust verdict: the
        // verify path still refuses it outright.
        assert!(
            bundle.verify_all().is_err(),
            "an assumed theorem must never reach a verification verdict"
        );
    }
}
