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
    preprocess_decl_with_context, ElabResult, FileContext, RegistrationWarningKind,
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
    // The verdict below reads the process-wide trust counters, so no other
    // in-process run may reset or bump them in between (the test harness is
    // exactly such a concurrent caller).
    let _guard = crate::cmd_core::check_file_lock();
    reset_sorry_counter();
    reset_kernel_check_counter();
    let result = run_export(&args)?;

    if let Some(json_path) = &args.json_report {
        write_json_report(json_path, &result)?;
    }

    print_summary(&result);
    // A run that refused anything is not an export. Before this gate a failed
    // declaration, a `sorry`, a kernel check failure or a sorry-tainted
    // exported theorem were each PRINTED and the command still exited 0
    // (round-22 verification), so a caller reading the exit code was told the
    // file certified. `--allow-empty` waives only the empty-bundle refusal
    // (one entry of `export_refusals`); it never waives any other.
    let refusals = export_refusals(&result);
    if !refusals.is_empty() {
        bail!(
            "export-cert: {} refused: {}",
            args.file.display(),
            refusals.join("; ")
        );
    }
    Ok(())
}

/// Every reason this run is not a clean export, one entry per class.
///
/// The empty-bundle refusal is one of them, decided HERE and not after the
/// bundle is saved: it used to be checked in the handler after `run_export`
/// had already written the (empty) bundle to `--out`, so a refused run left an
/// artifact behind (round-24 verification of 29de4ae8b).
fn export_refusals(result: &RunResult) -> Vec<String> {
    let mut refusals = Vec::new();
    if !result.failures.is_empty() {
        refusals.push(format!("{} declaration(s) failed", result.failures.len()));
    }
    if result.sorry_axioms_observed > 0 {
        refusals.push(format!(
            "{} declaration(s) whose constant closure reaches sorry",
            result.sorry_axioms_observed
        ));
    }
    if result.kernel_check_failures > 0 {
        refusals.push(format!(
            "{} kernel check failure(s) observed during elaboration",
            result.kernel_check_failures
        ));
    }
    let tainted: Vec<&str> = result
        .per_decl_axiom_closure
        .iter()
        .filter(|d| !d.trust_markers.is_empty())
        .map(|d| d.declaration.as_str())
        .collect();
    if !tainted.is_empty() {
        refusals.push(format!(
            "exported theorem(s) whose closure reaches a trust marker: {}",
            tainted.join(", ")
        ));
    }
    // Last, so a refusal for a failed declaration is named first.
    if result.exported == 0 && !result.allow_empty {
        refusals.push("no theorems exported (use --allow-empty to suppress)".to_string());
    }
    refusals
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
    /// Declarations of this run whose constant closure reaches `sorryAx` /
    /// `sorry` — in any position, behind any alias or cited lemma — counted as
    /// `clean check`'s `trust_summary.sorry_axioms` counts them. Until
    /// `Clean-export-cert-report-v3` this was the elaborator's count of sorry
    /// terms CREATED, which a sorry reached through a cited constant never
    /// raised; that count is `sorry_terms_minted`.
    sorry_axioms_observed: u64,
    /// Sorry terms the elaborator created during the run (additive in v3).
    sorry_terms_minted: u64,
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
    /// Imported modules taken from artifacts AS BUILT, with no source
    /// compared (see `import_binding.rs`): the exported statements hold of
    /// those artifacts' definitions, which the bundle's environment carries.
    artifact_imports: Vec<String>,
    /// Whether the bundle was written (false on a refused run).
    bundle_written: bool,
    /// Why the run was refused; empty on a clean export.
    refusals: Vec<String>,
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
    sorry_terms_minted: u64,
    kernel_check_failures: u64,
    per_decl_axiom_closure: Vec<DeclAxiomClosure>,
    all_axiom_closures_foundational_only: bool,
    /// See [`ExportReport::artifact_imports`].
    artifact_imports: Vec<String>,
    /// Whether the bundle was written to `out` (never on a refused run).
    written: bool,
    /// `--allow-empty`: an export of zero theorems is not refused.
    allow_empty: bool,
}

impl RunResult {
    fn to_report(&self) -> ExportReport {
        ExportReport {
            // v3: `sorry_axioms_observed` is the closure census (see the
            // field), and `sorry_terms_minted` is new.
            schema_version: "Clean-export-cert-report-v3",
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
            sorry_terms_minted: self.sorry_terms_minted,
            kernel_check_failures: self.kernel_check_failures,
            per_decl_axiom_closure: self.per_decl_axiom_closure.clone(),
            all_axiom_closures_foundational_only: self.all_axiom_closures_foundational_only,
            artifact_imports: self.artifact_imports.clone(),
            bundle_written: self.written,
            refusals: export_refusals(self),
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
            // Unambiguous rendering: a one-component `«Eq.refl»` must not read
            // as the kernel's `Eq.refl`.
            let mut non_foundational: Vec<String> =
                deps.iter().map(Name::to_unambiguous_string).collect();
            non_foundational.sort();
            let mut trust_markers: Vec<String> =
                trust.iter().map(Name::to_unambiguous_string).collect();
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
    // The gate's base: the environment BEFORE any import. Everything an
    // `import` loads enters structurally (never type-checked), so a
    // declaration's cited closure is re-admitted by the kernel over this base
    // before the declaration may be exported — exactly as `clean check`
    // credits it. Without this, `export-cert` exported a theorem citing an
    // imported artifact whose proof was never checked (module-trust
    // 2026-09-26: a leftover `sorry`, a flipped proof term, an imported axiom).
    let mut import_gate = clean_olean::ImportedConeGate::new(&env);
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(&args.file);

    let mut certs: HashMap<Name, ProofCert> = HashMap::new();
    let mut xproj_certs: HashMap<Name, CrossProjectCert> = HashMap::new();
    let mut failures: Vec<ExportFailure> = Vec::new();
    let mut exported_theorems: Vec<String> = Vec::new();
    let mut skipped: usize = 0;
    let mut skipped_axioms: usize = 0;
    let mut import_binding = crate::import_binding::ImportBinding::default();
    let mut artifact_imports: Vec<String> = Vec::new();
    // The sorry census, as `clean check` takes it: a registered declaration
    // (examples included) whose constant closure reaches `sorryAx` / `sorry`.
    let mut sorry_closure = clean_kernel::env::DomainAxiomClosure::new();
    let mut sorry_declarations: u64 = 0;

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
                let mut leaves: Vec<&ElabResult> = Vec::new();
                registered.result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    if matches!(leaf, ElabResult::Failed { .. }) {
                        continue;
                    }
                    if clean_elab::register::registration_warning_for_leaf_in(
                        &mut sorry_closure,
                        &env,
                        leaf,
                    )
                    .is_some_and(|warning| {
                        matches!(
                            warning.kind,
                            RegistrationWarningKind::ExplicitSorry
                                | RegistrationWarningKind::SyntheticSorry
                        )
                    }) {
                        sorry_declarations = sorry_declarations.saturating_add(1);
                    }
                    if let Err(reason) = crate::check_import_gate::gate_declaration(
                        &mut import_gate,
                        &env,
                        leaf,
                        false,
                    ) {
                        let declaration = match leaf {
                            ElabResult::Theorem { name, .. } => Some(name.to_string()),
                            _ => crate::cmd_core::surface_decl_name(decl),
                        };
                        failures.push(ExportFailure {
                            declaration,
                            reason: format!("cited closure not credited: {reason}"),
                        });
                    }
                }
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
                    declaration: crate::cmd_core::surface_decl_name(decl),
                    reason: format!("elaboration error: {err}"),
                });
                // A failed `import` leaves a partial environment; nothing is
                // exported (or counted accepted) against it.
                if matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
                    break;
                }
            }
        }
        // An `import` just loaded artifacts: each must be the build of its
        // source where that source is present (module-trust round 27,
        // `import_binding.rs`); otherwise nothing is exported against it.
        if matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
            let findings = import_binding.examine(&file_ctx);
            artifact_imports.extend(findings.disclosures);
            if !findings.refusals.is_empty() {
                failures.extend(findings.refusals.into_iter().map(|reason| ExportFailure {
                    declaration: None,
                    reason,
                }));
                break;
            }
        }
    }
    // Imports nested inside a block: examined too.
    {
        let findings = import_binding.examine(&file_ctx);
        artifact_imports.extend(findings.disclosures);
        failures.extend(findings.refusals.into_iter().map(|reason| ExportFailure {
            declaration: None,
            reason,
        }));
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

    let bundle_project = project.clone();
    let mut result = RunResult {
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
        sorry_axioms_observed: sorry_declarations,
        sorry_terms_minted: sorry_count(),
        kernel_check_failures: kernel_check_failure_count(),
        per_decl_axiom_closure,
        all_axiom_closures_foundational_only,
        artifact_imports,
        written: false,
        allow_empty: args.allow_empty,
    };

    // A refused run writes NO bundle: an artifact at `--out` is what a
    // downstream `clean kernel cert verify` consumes as this file's export,
    // and it must not exist for a file that did not export cleanly. The
    // bundle is BUILT only for a run that will be written: the trust
    // constructor re-derives the whole environment from the canonical base
    // (`clean_kernel::cert::bundle_recheck`), and a run already refused (a
    // cited artifact the import gate did not credit, say) must report that
    // refusal, not the rebuild's view of the same defect.
    if export_refusals(&result).is_empty() {
        let bundle = CertBundle::build(
            &bundle_project,
            clean_version,
            env,
            certs,
            xproj_certs,
            None,
        )
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
        result.written = true;
    }
    Ok(result)
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
        ElabResult::Diagnosed { result, diagnostics } => {
            failures.push(ExportFailure {
                declaration: result.declaration_name().map(ToString::to_string),
                reason: diagnostics.iter().map(|d| d.error.to_string()).collect::<Vec<_>>().join("\n"),
            });
        }
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
        // A `Failed` inner decl (a member of a namespace / section / mutual
        // block) is a declaration that did NOT check. It used to fall into the
        // `skipped` arm below, so `namespace A … theorem bad : 1 = 2 := rfl …
        // end A` printed `skipped: 1 non-theorem declarations` and exited 0
        // (round-22 verification). It is a failure, named and counted as one.
        ElabResult::Failed { name, error, .. } => {
            failures.push(ExportFailure {
                declaration: Some(name.clone()),
                reason: format!("elaboration error: {error}"),
            });
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
    // On a refused run nothing was exported: say how many theorems were
    // accepted, never that they were exported next to `bundle: not written`.
    if result.written {
        println!("  exported:  {} theorems", result.exported);
    } else {
        println!(
            "  exported:  0 theorems ({} accepted; refused run, nothing written)",
            result.exported
        );
    }
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
    if result.written {
        println!("  bundle:    {}", result.out.display());
    } else {
        println!("  bundle:    not written (refused run)");
    }
    if !result.artifact_imports.is_empty() {
        println!(
            "  imports:   {} {}:",
            result.artifact_imports.len(),
            crate::import_binding::DISCLOSURE_HEADING
        );
        for row in result
            .artifact_imports
            .iter()
            .take(crate::import_binding::DISCLOSURE_ROWS_SHOWN)
        {
            println!("    - {row}");
        }
        if result.artifact_imports.len() > crate::import_binding::DISCLOSURE_ROWS_SHOWN {
            println!(
                "    … and {} more (all of them are in the `--json-report`)",
                result.artifact_imports.len() - crate::import_binding::DISCLOSURE_ROWS_SHOWN
            );
        }
    }
    println!("  duration:  {} ms", result.duration_ms);
    if result.sorry_axioms_observed > 0 {
        println!(
            "  trust:     {} declaration(s) whose constant closure reaches sorry",
            result.sorry_axioms_observed,
        );
    }
    if result.sorry_terms_minted != result.sorry_axioms_observed && result.sorry_terms_minted > 0 {
        println!(
            "  trust:     {} sorry term(s) created during elaboration",
            result.sorry_terms_minted,
        );
    }
    if result.kernel_check_failures > 0 {
        println!(
            "  trust:     {} kernel check failures observed during elaboration",
            result.kernel_check_failures,
        );
    }
    // Per-decl axiom-closure verdict (#97 increment #3).
    // On a refused run nothing was exported, and a theorem refused by the
    // import gate has no closure worth vouching for: name them as what they
    // are.
    let theorems = if result.written {
        "exported theorems"
    } else {
        "accepted (NOT exported) theorems"
    };
    if !result.per_decl_axiom_closure.is_empty() {
        if result.all_axiom_closures_foundational_only {
            println!(
                "  axioms:    all {} {theorems} have axiom closure ⊆ \
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
                "  axioms:    {} of {} {theorems} escape the foundational set:",
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
        // Refused for the failed declaration itself (named in the report),
        // not merely for exporting nothing.
        assert!(
            err.to_string().contains("refused: 1 declaration(s) failed"),
            "unexpected error: {err}",
        );
        assert!(!bundle_path.exists(), "a refused run writes no bundle");
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

    /// Round-22 verification of `317f48b45` (and clean `main`): a theorem
    /// that failed inside a `namespace` / `section` was reported as `skipped:
    /// 1 non-theorem declarations`, a failure or a `sorry` was printed, and
    /// every one of these exited 0 with a bundle written.
    #[test]
    fn export_cert_refuses_every_failed_or_tainted_run_and_writes_no_bundle() {
        let attacks: &[(&str, &str, Option<&str>)] = &[
            (
                "namespace",
                "namespace A\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend A\n",
                Some("A.bad"),
            ),
            (
                "section",
                "section S\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend S\n",
                Some("bad"),
            ),
            (
                "top level",
                "theorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\n",
                Some("bad"),
            ),
            (
                "sorry theorem in a namespace",
                "theorem good : 1 = 1 := rfl\nnamespace A\ntheorem bad : 1 = 2 := sorry\nend A\n",
                None,
            ),
        ];
        for (label, source, failed_name) in attacks {
            let dir = tempfile::tempdir().expect("create temp dir");
            let lean_path = write_tmp(dir.path(), "attack.lean", source);
            let bundle_path = dir.path().join("attack.cleancert");
            let report_path = dir.path().join("attack.json");
            let mut args = fresh_args(lean_path, bundle_path.clone());
            args.json_report = Some(report_path.clone());
            // `--allow-empty` must not waive a refusal either.
            args.allow_empty = true;
            let err = handle_export_cert_command(args)
                .expect_err(&format!("{label}: a refused run must exit non-zero"));
            assert!(
                err.to_string().contains("refused"),
                "{label}: unexpected error: {err}"
            );
            assert!(
                !bundle_path.exists(),
                "{label}: a refused run must not write a bundle"
            );
            let report: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(&report_path).expect("report"))
                    .expect("report parses");
            assert_eq!(report["bundle_written"], false, "{label}");
            assert!(
                !report["refusals"].as_array().expect("refusals").is_empty(),
                "{label}"
            );
            if let Some(name) = failed_name {
                let failures = report["failures"].as_array().expect("failures");
                assert!(
                    failures
                        .iter()
                        .any(|f| f["declaration"].as_str() == Some(*name)),
                    "{label}: the failed theorem must be NAMED as a failure, got {failures:?}"
                );
                assert_eq!(
                    report["skipped"], 0,
                    "{label}: a failed theorem is not a skipped non-theorem"
                );
            } else {
                // The only row with no named failure is the sorry attack: it
                // must be refused FOR the sorry, not for an unrelated reason.
                let refusals = report["refusals"].as_array().expect("refusals");
                assert!(
                    refusals
                        .iter()
                        .filter_map(|r| r.as_str())
                        .any(|r| r.contains("sorry") || r.contains("trust marker")),
                    "{label}: a sorry-tainted run must be refused for the sorry / trust marker, got {refusals:?}"
                );
            }
        }
    }

    /// Round-24 verification of 29de4ae8b: an export of zero theorems without
    /// `--allow-empty` exited 1 but had already written the empty bundle to
    /// `--out`. A refused run writes nothing; `--allow-empty` still writes.
    #[test]
    fn export_cert_empty_export_is_refused_before_anything_is_written() {
        for (label, source) in [
            ("definitions only", "def my_zero : Nat := Nat.zero\n"),
            ("comment only", "-- nothing here\n"),
        ] {
            let dir = tempfile::tempdir().expect("create temp dir");
            let lean_path = write_tmp(dir.path(), "empty.lean", source);
            let bundle_path = dir.path().join("empty.cleancert");
            let report_path = dir.path().join("empty.json");
            let mut args = fresh_args(lean_path.clone(), bundle_path.clone());
            args.json_report = Some(report_path.clone());
            let err = handle_export_cert_command(args)
                .expect_err(&format!("{label}: an empty export must be refused"));
            assert!(
                err.to_string().contains("no theorems exported"),
                "{label}: unexpected error: {err}"
            );
            assert!(
                !bundle_path.exists(),
                "{label}: a refused empty export must not write a bundle"
            );
            let report: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(&report_path).expect("report"))
                    .expect("report parses");
            assert_eq!(report["bundle_written"], false, "{label}");

            let mut args = fresh_args(lean_path, bundle_path.clone());
            args.allow_empty = true;
            handle_export_cert_command(args)
                .unwrap_or_else(|e| panic!("{label}: --allow-empty must accept: {e}"));
            assert!(
                bundle_path.exists(),
                "{label}: --allow-empty writes the bundle"
            );
        }
    }

    /// Measured on origin/main 4bacc8770: `axiom proofIrrel : False` (a name
    /// on the old foundational whitelist, declared nowhere by the kernel) and a
    /// theorem of `False` through it exported with "all exported theorems have
    /// axiom closure ⊆ {propext, Quot.sound, Classical.choice}", and the bundle
    /// verified `all_passed` with nothing disclosed. Now the closure names the
    /// axiom, and the bundle's verify result discloses it.
    #[test]
    fn export_cert_discloses_a_legacy_whitelist_name_axiom() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let lean_path = write_tmp(
            dir.path(),
            "spoof.lean",
            "axiom proofIrrel : False
theorem bad : False := proofIrrel
",
        );
        let bundle_path = dir.path().join("spoof.cleancert");
        let report_path = dir.path().join("spoof.json");
        let mut args = fresh_args(lean_path, bundle_path.clone());
        args.json_report = Some(report_path.clone());
        handle_export_cert_command(args).expect("an axiom-backed export is not refused");
        let report: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&report_path).expect("report"))
                .expect("report parses");
        assert_eq!(report["all_axiom_closures_foundational_only"], false);
        assert_eq!(
            report["per_decl_axiom_closure"][0]["non_foundational_axioms"],
            serde_json::json!(["proofIrrel"])
        );

        let bundle = CertBundle::load(&bundle_path).expect("load bundle");
        let result = bundle.verify_all().expect("verify bundle");
        assert!(result.all_passed());
        assert!(result
            .axioms
            .other_axioms
            .contains(&"proofIrrel".to_string()));
        assert_eq!(
            result.axioms.theorem_assumptions,
            vec![("bad".to_string(), vec!["proofIrrel".to_string()])]
        );
    }

    /// `sorry_axioms_observed` is the closure census `clean check` takes
    /// (`trust_summary.sorry_axioms`): a declaration whose constant closure
    /// reaches `sorryAx`, in any position. Measured on origin/main 4bacc8770:
    /// `clean check` counted 1 and 2 for these sources while export-cert
    /// reported 0 for both — it counted the elaborator's CREATED sorry terms,
    /// which a non-literal `@sorryAx` and a sorry behind an alias never raise.
    #[test]
    fn export_cert_sorry_census_is_the_closure_census() {
        for (label, source, census) in [
            (
                "example with a non-literal flag",
                "theorem ok : True := True.intro\nexample : False := @sorryAx False (!true)\n",
                1,
            ),
            (
                "sorry behind an alias",
                "def s := @sorryAx\ntheorem ok : True := True.intro\ntheorem bad : False := s False true\n",
                2,
            ),
        ] {
            let dir = tempfile::tempdir().expect("create temp dir");
            let lean_path = write_tmp(dir.path(), "sorry.lean", source);
            let bundle_path = dir.path().join("sorry.cleancert");
            let report_path = dir.path().join("sorry.json");
            let mut args = fresh_args(lean_path, bundle_path.clone());
            args.json_report = Some(report_path.clone());
            let err = handle_export_cert_command(args)
                .expect_err(&format!("{label}: a sorry-reaching run is refused"));
            assert!(
                err.to_string()
                    .contains("declaration(s) whose constant closure reaches sorry"),
                "{label}: the refusal names the sorry census: {err}"
            );
            let report: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(&report_path).expect("report"))
                    .expect("report parses");
            assert_eq!(report["schema_version"], "Clean-export-cert-report-v3");
            assert_eq!(report["sorry_axioms_observed"], census, "{label}: {report}");
            assert_eq!(report["sorry_terms_minted"], 0, "{label}: {report}");
            assert!(!bundle_path.exists(), "{label}: a refused run writes no bundle");
        }
    }

    /// A one-component `«Quot.sound»` prints exactly like the kernel's
    /// `Quot.sound`; it is refused at the declaration, so nothing is exported.
    #[test]
    fn export_cert_refuses_a_printed_form_foundation_spoof() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let lean_path = write_tmp(
            dir.path(),
            "spoof.lean",
            "axiom «Quot.sound» : False
theorem bad : False := «Quot.sound»
",
        );
        let bundle_path = dir.path().join("spoof.cleancert");
        let err = handle_export_cert_command(fresh_args(lean_path, bundle_path.clone()))
            .expect_err("a reserved kernel name must refuse the export");
        assert!(
            err.to_string().contains("declaration(s) failed"),
            "unexpected error: {err}"
        );
        assert!(!bundle_path.exists(), "a refused run writes no bundle");
    }
}

#[cfg(test)]
#[path = "cmd_export_cert_gate_tests.rs"]
mod gate_tests;
