// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean export-cert <FILE.lean> --out <PATH.cleancert>` handler.
//!
//! Closes audit item 6 from `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md`:
//! drives parser → elaborator → kernel on a single Lean source file and
//! serializes the accepted theorems as a [`CertBundle`]. Downstream the
//! bundle is consumed by `clean kernel cert verify` (`cmd_kernel/cert.rs`).
//!
//! This is the in-tree pipeline that lets Clean operate as a
//! soundness-grounded verifier:
//!
//! ```text
//! .lean source --[export-cert]--> .cleancert bundle --[cert verify]--> PASS/FAIL
//! ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::{anyhow, bail};
use clean_elab::register::reset_kernel_check_counter;
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, kernel_check_failure_count,
    preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::cert::bundle::CertBundle;
use clean_kernel::cert::{CrossProjectCert, ProofCert, ProverInfo, ProverSystem};
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use clean_kernel::verify_api::verify_expr;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_tactics;
use serde::Serialize;

use crate::cli::ExportCertArgs;

/// Top-level dispatch for `clean export-cert`.
pub(crate) fn handle_export_cert_command(args: ExportCertArgs) -> anyhow::Result<()> {
    reset_sorry_counter();
    reset_kernel_check_counter();
    let result = run_export(&args)?;

    if let Some(json_path) = &args.json_report {
        write_json_report(json_path, &result)?;
    }

    print_summary(&result);
    if result.exported == 0 && !args.allow_empty {
        bail!(
            "export-cert: no theorems exported from {} (use --allow-empty to suppress)",
            args.file.display()
        );
    }
    Ok(())
}

#[derive(Debug, Serialize)]
struct ExportReport {
    schema_version: &'static str,
    command: &'static str,
    file: String,
    out: String,
    declarations_parsed: usize,
    exported: usize,
    skipped: usize,
    skipped_axioms: usize,
    failures: Vec<ExportFailure>,
    exported_theorems: Vec<String>,
    duration_ms: u128,
    project: String,
    sorry_axioms_observed: u64,
    kernel_check_failures: u64,
    /// Per-decl transitive AXIOM-CLOSURE dump (#97 increment #3).
    ///
    /// For each exported theorem, the non-foundational axioms reachable in its
    /// transitive `axiom_deps` closure. An EMPTY list means the closure is
    /// `⊆ {propext, Quot.sound, Classical.choice, Eq builtins}` — mechanically
    /// pinning the C3 soundness claim PER THEOREM (previously only the global
    /// `sorry_axioms_observed` was reported).
    per_decl_axiom_closure: Vec<DeclAxiomClosure>,
    /// True iff EVERY exported theorem's closure is foundational-only.
    all_axiom_closures_foundational_only: bool,
}

/// One theorem's transitive axiom-closure entry.
#[derive(Debug, Clone, Serialize)]
struct DeclAxiomClosure {
    /// Theorem name.
    declaration: String,
    /// Non-foundational axioms in the transitive closure (sorted). Empty ⇒
    /// closure ⊆ the foundational set.
    non_foundational_axioms: Vec<String>,
    /// Trust markers (`sorry`/`sorryAx`/`trusted*`) in the closure (subset of
    /// `non_foundational_axioms`). Non-empty ⇒ the proof reached a trust hole.
    trust_markers: Vec<String>,
    /// Convenience verdict: `non_foundational_axioms.is_empty()`.
    foundational_only: bool,
}

#[derive(Debug, Serialize)]
struct ExportFailure {
    declaration: Option<String>,
    reason: String,
}

struct RunResult {
    file: PathBuf,
    out: PathBuf,
    declarations_parsed: usize,
    exported: usize,
    skipped: usize,
    skipped_axioms: usize,
    failures: Vec<ExportFailure>,
    exported_theorems: Vec<String>,
    duration_ms: u128,
    project: String,
    sorry_axioms_observed: u64,
    kernel_check_failures: u64,
    per_decl_axiom_closure: Vec<DeclAxiomClosure>,
    all_axiom_closures_foundational_only: bool,
}

impl RunResult {
    fn to_report(&self) -> ExportReport {
        ExportReport {
            schema_version: "Clean-export-cert-report-v2",
            command: "clean export-cert",
            file: self.file.display().to_string(),
            out: self.out.display().to_string(),
            declarations_parsed: self.declarations_parsed,
            exported: self.exported,
            skipped: self.skipped,
            skipped_axioms: self.skipped_axioms,
            failures: self.failures.iter().map(clone_failure).collect(),
            exported_theorems: self.exported_theorems.clone(),
            duration_ms: self.duration_ms,
            project: self.project.clone(),
            sorry_axioms_observed: self.sorry_axioms_observed,
            kernel_check_failures: self.kernel_check_failures,
            per_decl_axiom_closure: self.per_decl_axiom_closure.clone(),
            all_axiom_closures_foundational_only: self.all_axiom_closures_foundational_only,
        }
    }
}

/// Compute the per-decl transitive axiom-closure dump for the exported
/// theorems. For each name, `env.axiom_deps` already filters out the
/// foundational set (propext / Quot.sound / Classical.choice / Eq builtins),
/// so a NON-EMPTY result means the closure escapes the foundational set.
/// `env.trust_marker_deps` isolates the `sorry`/`trusted*` subset.
fn compute_axiom_closures(env: &Environment, names: &[Name]) -> Vec<DeclAxiomClosure> {
    let mut out: Vec<DeclAxiomClosure> = names
        .iter()
        .map(|name| {
            let deps = env.axiom_deps(name).unwrap_or_default();
            let trust = env.trust_marker_deps(name).unwrap_or_default();
            let mut non_foundational: Vec<String> = deps.iter().map(ToString::to_string).collect();
            non_foundational.sort();
            let mut trust_markers: Vec<String> = trust.iter().map(ToString::to_string).collect();
            trust_markers.sort();
            DeclAxiomClosure {
                declaration: name.to_string(),
                foundational_only: non_foundational.is_empty(),
                non_foundational_axioms: non_foundational,
                trust_markers,
            }
        })
        .collect();
    out.sort_by(|a, b| a.declaration.cmp(&b.declaration));
    out
}

fn clone_failure(f: &ExportFailure) -> ExportFailure {
    ExportFailure {
        declaration: f.declaration.clone(),
        reason: f.reason.clone(),
    }
}

fn run_export(args: &ExportCertArgs) -> anyhow::Result<RunResult> {
    let start = Instant::now();
    let content = std::fs::read_to_string(&args.file)
        .map_err(|e| anyhow!("reading {}: {e}", args.file.display()))?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&content, &patterns)
        .map_err(|e| anyhow!("parsing {}: {e}", args.file.display()))?;
    let declarations_parsed = decls.len();

    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let import_search_paths = clean_elab::lake_import_search_paths_for_file(&args.file);
    file_ctx.set_import_search_paths(import_search_paths);

    let mut certs: HashMap<Name, ProofCert> = HashMap::new();
    let mut xproj_certs: HashMap<Name, CrossProjectCert> = HashMap::new();
    let mut failures: Vec<ExportFailure> = Vec::new();
    let mut exported_theorems: Vec<String> = Vec::new();
    let mut skipped: usize = 0;
    let mut skipped_axioms: usize = 0;

    for decl in &decls {
        let processed_decl = preprocess_decl_with_context(decl, &mut file_ctx);
        // Thread `file_ctx` so standalone `open`/`export` aliases and
        // file-scope notation persist across declarations (gap sweep B13),
        // keeping this surface consistent with `clean check`.
        match elaborate_decl_and_register_with_context_and_warning(
            &mut env,
            &processed_decl,
            &mut file_ctx,
        ) {
            Ok(registered) => {
                process_elab_result(
                    &registered.result,
                    &env,
                    args.include_axioms,
                    &mut certs,
                    &mut xproj_certs,
                    &mut exported_theorems,
                    &mut failures,
                    &mut skipped,
                    &mut skipped_axioms,
                );
            }
            Err(err) => {
                failures.push(ExportFailure {
                    declaration: None,
                    reason: format!("elaboration error: {err}"),
                });
            }
        }
    }

    let exported = certs.len();
    let project = derive_project_name(&args.file);
    let clean_version = env!("CARGO_PKG_VERSION");

    // Per-decl transitive AXIOM-CLOSURE dump (#97 increment #3). Computed
    // BEFORE the bundle build consumes `env`. Pins "axiom closure ⊆
    // {propext, Quot.sound, Classical.choice}" PER exported theorem.
    let exported_names: Vec<Name> = certs.keys().cloned().collect();
    let per_decl_axiom_closure = compute_axiom_closures(&env, &exported_names);
    let all_axiom_closures_foundational_only =
        per_decl_axiom_closure.iter().all(|d| d.foundational_only);

    let bundle = CertBundle::build(&project, clean_version, env, certs, xproj_certs, None)
        .map_err(|e| anyhow!("bundle build failed: {e}"))?;

    if let Some(parent) = args.out.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|e| anyhow!("creating directory {}: {e}", parent.display()))?;
        }
    }
    bundle
        .save(&args.out)
        .map_err(|e| anyhow!("writing {}: {e}", args.out.display()))?;

    Ok(RunResult {
        file: args.file.clone(),
        out: args.out.clone(),
        declarations_parsed,
        exported,
        skipped,
        skipped_axioms,
        failures,
        exported_theorems,
        duration_ms: start.elapsed().as_millis(),
        project,
        sorry_axioms_observed: sorry_count(),
        kernel_check_failures: kernel_check_failure_count(),
        per_decl_axiom_closure,
        all_axiom_closures_foundational_only,
    })
}

#[allow(clippy::too_many_arguments)]
fn process_elab_result(
    result: &ElabResult,
    env: &Environment,
    include_axioms: bool,
    certs: &mut HashMap<Name, ProofCert>,
    xproj_certs: &mut HashMap<Name, CrossProjectCert>,
    exported_theorems: &mut Vec<String>,
    failures: &mut Vec<ExportFailure>,
    skipped: &mut usize,
    skipped_axioms: &mut usize,
) {
    match result {
        ElabResult::Theorem { name, proof, .. } => {
            export_theorem(
                env,
                name,
                proof,
                certs,
                xproj_certs,
                exported_theorems,
                failures,
            );
        }
        ElabResult::Multiple(inner) => {
            for r in inner {
                process_elab_result(
                    r,
                    env,
                    include_axioms,
                    certs,
                    xproj_certs,
                    exported_theorems,
                    failures,
                    skipped,
                    skipped_axioms,
                );
            }
        }
        ElabResult::Axiom { name, .. } => {
            if include_axioms {
                // Axioms have no proof term to certify — they enter the
                // bundle's environment but produce no replayable cert.
                *skipped_axioms += 1;
                exported_theorems.push(format!("(axiom) {}", name));
            } else {
                *skipped_axioms += 1;
            }
        }
        ElabResult::Definition { .. }
        | ElabResult::Opaque { .. }
        | ElabResult::Inductive { .. }
        | ElabResult::MutualInductive { .. }
        | ElabResult::Structure { .. }
        | ElabResult::Instance { .. }
        | ElabResult::Command(_)
        // A `Failed` inner decl has no proof term to certify (it never
        // type-checked), so it produces no cert — count it as skipped here.
        | ElabResult::Failed { .. }
        // An `example` is anonymous and never registered (B02): there is no
        // environment `Name` for a cert to reference, so it exports nothing.
        | ElabResult::Example { .. }
        | ElabResult::Skipped => {
            *skipped += 1;
        }
    }
}

fn export_theorem(
    env: &Environment,
    name: &Name,
    proof: &clean_kernel::Expr,
    certs: &mut HashMap<Name, ProofCert>,
    xproj_certs: &mut HashMap<Name, CrossProjectCert>,
    exported_theorems: &mut Vec<String>,
    failures: &mut Vec<ExportFailure>,
) {
    let theorem_label = name.to_string();
    // Generate the proof certificate by re-running type inference with cert
    // emission over the elaborated proof term. This is the soundness-relevant
    // step: the cert is what `clean kernel cert verify` will replay.
    match verify_expr(env, proof) {
        Ok(evidence) => {
            let cert = evidence.cert().clone();
            let xproj_result = CrossProjectCert::from_environment(
                env,
                theorem_label.clone(),
                prover_info(),
                Vec::new(),
            );
            match xproj_result {
                Ok(xproj) => {
                    certs.insert(name.clone(), cert);
                    xproj_certs.insert(name.clone(), xproj);
                    exported_theorems.push(theorem_label);
                }
                Err(err) => {
                    failures.push(ExportFailure {
                        declaration: Some(theorem_label),
                        reason: format!("cross-project cert build failed: {err}"),
                    });
                }
            }
        }
        Err(err) => {
            failures.push(ExportFailure {
                declaration: Some(theorem_label),
                reason: format!("cert generation failed: {err}"),
            });
        }
    }
}

fn prover_info() -> ProverInfo {
    ProverInfo::new(
        ProverSystem::Clean,
        "clean export-cert",
        Some(env!("CARGO_PKG_VERSION").to_string()),
    )
}

fn derive_project_name(file: &Path) -> String {
    file.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("clean-export")
        .to_string()
}

fn print_summary(result: &RunResult) {
    println!("export-cert: {}", result.file.display());
    println!("  parsed:    {} declarations", result.declarations_parsed);
    println!("  exported:  {} theorems", result.exported);
    if result.skipped > 0 {
        println!("  skipped:   {} non-theorem declarations", result.skipped);
    }
    if result.skipped_axioms > 0 {
        println!("  axioms:    {} (no proof term)", result.skipped_axioms);
    }
    if !result.failures.is_empty() {
        println!("  failures:  {}", result.failures.len());
        for f in &result.failures {
            let label = f.declaration.as_deref().unwrap_or("(no name)");
            println!("    - {label}: {}", f.reason);
        }
    }
    println!("  bundle:    {}", result.out.display());
    println!("  duration:  {} ms", result.duration_ms);
    if result.sorry_axioms_observed > 0 {
        println!(
            "  trust:     {} sorry axioms observed during elaboration",
            result.sorry_axioms_observed,
        );
    }
    if result.kernel_check_failures > 0 {
        println!(
            "  trust:     {} kernel check failures observed during elaboration",
            result.kernel_check_failures,
        );
    }
    // Per-decl axiom-closure verdict (#97 increment #3).
    if !result.per_decl_axiom_closure.is_empty() {
        if result.all_axiom_closures_foundational_only {
            println!(
                "  axioms:    all {} exported theorems have axiom closure ⊆ \
                 {{propext, Quot.sound, Classical.choice}}",
                result.per_decl_axiom_closure.len(),
            );
        } else {
            let escaping: Vec<&DeclAxiomClosure> = result
                .per_decl_axiom_closure
                .iter()
                .filter(|d| !d.foundational_only)
                .collect();
            println!(
                "  axioms:    {} of {} exported theorems escape the foundational set:",
                escaping.len(),
                result.per_decl_axiom_closure.len(),
            );
            for d in escaping {
                println!(
                    "    - {}: {}",
                    d.declaration,
                    d.non_foundational_axioms.join(", ")
                );
            }
        }
    }
}

fn write_json_report(path: &Path, result: &RunResult) -> anyhow::Result<()> {
    let report = result.to_report();
    let json = serde_json::to_string_pretty(&report)?;
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|e| anyhow!("creating {}: {e}", parent.display()))?;
        }
    }
    std::fs::write(path, json).map_err(|e| anyhow!("writing {}: {e}", path.display()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_args(file: PathBuf, out: PathBuf) -> ExportCertArgs {
        ExportCertArgs {
            file,
            out,
            json_report: None,
            include_axioms: false,
            allow_empty: false,
        }
    }

    fn write_tmp(dir: &Path, name: &str, contents: &str) -> PathBuf {
        let path = dir.join(name);
        std::fs::write(&path, contents).expect("write tmp file");
        path
    }

    #[test]
    fn export_cert_trivial_theorem_produces_loadable_bundle() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let lean_path = write_tmp(
            dir.path(),
            "trivial.lean",
            "theorem trivial_true : True := True.intro\n",
        );
        let bundle_path = dir.path().join("trivial.cleancert");

        let args = fresh_args(lean_path, bundle_path.clone());
        handle_export_cert_command(args).expect("export-cert succeeds");

        // Bundle file exists and loads back via the kernel API.
        assert!(bundle_path.exists(), "bundle file should exist");
        let bundle = CertBundle::load(&bundle_path).expect("load bundle");
        assert_eq!(bundle.theorem_count(), 1, "expected one exported theorem");
        assert!(
            bundle.has_theorem("trivial_true"),
            "bundle should contain the exported theorem",
        );

        // Bundle verifies — the soundness-grounded path is closed end-to-end.
        let result = bundle.verify_all().expect("verify bundle");
        assert!(
            result.all_passed(),
            "verify failures: {:?}",
            result.failures,
        );
        assert_eq!(result.passed, 1);
    }

    #[test]
    fn export_cert_broken_theorem_errors_cleanly() {
        let dir = tempfile::tempdir().expect("create temp dir");
        // `BogusConst` is not in the prelude, so elaboration will fail.
        let lean_path = write_tmp(
            dir.path(),
            "broken.lean",
            "theorem broken : True := BogusConstThatDoesNotExist\n",
        );
        let bundle_path = dir.path().join("broken.cleancert");

        let args = fresh_args(lean_path, bundle_path.clone());
        let err = handle_export_cert_command(args)
            .expect_err("broken theorem should produce a non-zero exit");
        assert!(
            err.to_string().contains("no theorems exported"),
            "unexpected error: {err}",
        );
    }

    #[test]
    fn export_cert_skips_definitions_and_inductive() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let lean_path = write_tmp(
            dir.path(),
            "mixed.lean",
            "def my_zero : Nat := Nat.zero\n\
             theorem trivial2 : True := True.intro\n",
        );
        let bundle_path = dir.path().join("mixed.cleancert");

        let args = fresh_args(lean_path, bundle_path.clone());
        handle_export_cert_command(args).expect("export-cert succeeds");
        let bundle = CertBundle::load(&bundle_path).expect("load bundle");
        assert_eq!(bundle.theorem_count(), 1);
        assert!(bundle.has_theorem("trivial2"));
    }
}
