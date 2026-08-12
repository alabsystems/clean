// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_shard coq-import` — the COQ-6 one-command scale harness.
//!
//! ONE command imports + kernel-rechecks every dumped Coq library and reports
//! the per-library trust distribution with zero silent degradation: every
//! unparsable file, skipped form, and dropped value is counted; the kernel's
//! verdict is the only thing that can mint `KernelVerified` for value-bearing
//! declarations (enforced by a fail-closed soundness floor before
//! verification).
//!
//! # Regular reimport recipe (maintenance entry point)
//!
//! 1. **Dump** the Coq 8.20 stdlib from the pinned opam switch
//!    (`~/.opam/mathverse-serapi/bin/sertop`, coq.8.20.0 + coq-serapi):
//!
//!    ```text
//!    scripts/build_coq_serapi_dumps.sh [--force] [--jobs=N]
//!    ```
//!
//!    This drives `mathverse_coq_dump` to write per-module importer-form
//!    dumps under `data/corpora/coq-sexp/stdlib/<Logical.Module.Path>.sexp`
//!    (+ `.meta.json` sidecars and a `manifest.json`). Each library is one
//!    subdirectory of the sexp root (`stdlib` today; more can be added).
//!
//! 2. **Import + verify + stamp** every library in one command:
//!
//!    ```text
//!    cargo run --locked --release -p clean-mathverse --bin mathverse_shard -- \
//!        coq-import --sexp-root=data/corpora/coq-sexp --out=<out-dir> \
//!        [--json=<report.json>]
//!    ```
//!
//! 3. **Expected artifacts** per library `<lib>`:
//!    - `<out>/<lib>/coq_<lib>.mathverse` — the converted shard, stamped in
//!      place with the kernel's `KernelVerified` verdicts (unless
//!      `--no-stamp`);
//!    - `<out>/<lib>/kernel-verified.json` — the [`KernelVerifiedManifest`]
//!      sidecar naming exactly which constants Clean's kernel re-verified.
//!
//! The pipeline per library is the proven Template-B verify+stamp spine:
//! convert with honest sub-`KernelVerified` labels → soundness floor → merge
//! shards into a [`MathverseLibrary`] → prelude-seeded kernel env →
//! [`verify_corpus_incremental_with_env_policy`] → manifest sidecar → stamp →
//! stored-count audit → BEDROCK (empty transitive non-foundational axiom
//! closure) count.
//!
//! # Refresh pipeline (gate + promote)
//!
//! The recurring import→gate→promote maintenance loop is ONE command:
//!
//! ```text
//! mathverse_shard coq-import --sexp-root=data/corpora/coq-sexp --out=<scratch> \
//!     --gate-baseline=data/corpora/coq-mathverse --promote-on-green
//! ```
//!
//! `--gate-baseline=DIR` diffs, per library, the fresh
//! `kernel_verified_names` against the promoted baseline manifest at
//! `DIR/<library>/kernel-verified.json` and prints a gate table. The
//! 0-REGRESSION RULE: the fresh set must be a SUPERSET of the baseline's —
//! any baseline name missing from the fresh import is a regression and the
//! command exits nonzero. A library without a baseline manifest is a first
//! import and gates green. With `--json`, each library's report gains a
//! `"gate"` object (`baseline` / `new` / `net` / `regressed` capped at 100 /
//! `regressed_truncated`).
//!
//! `--promote-on-green` (only valid with `--gate-baseline`) copies each
//! successfully imported library's fresh outputs (`kernel-verified.json` +
//! `*.mathverse`) over `DIR/<library>/` when the gate is fully green,
//! creating directories as needed. On a red gate NOTHING is promoted.

use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_mathverse::library::{
    count_stored_kernel_verified, stamp_shard_dir_kernel_verified, MathverseLibrary,
};
use clean_mathverse::shard::ShardReader;
use clean_mathverse::shard_verify::discover_mathverse_files;
use clean_mathverse::structured_import::{convert_coq_sexp_dir_with_context, CoqConvertDirStats};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{DeclKind, ImportConfidence};
use clean_mathverse::verify::incremental::{
    verify_corpus_incremental_with_env_policy, IncrementalVerifyReport, InductiveReplayPolicy,
};
use clean_mathverse::verify::kernel_verified_manifest::{
    KernelVerifiedManifest, StampEnvFingerprint,
};

const USAGE: &str = "Usage: mathverse_shard coq-import --sexp-root=<dir> --out=<dir> \
     [--library=<name>]... [--json=<path>] [--lean-faithful] [--no-stamp] \
     [--gate-baseline=<dir>] [--promote-on-green]";

/// Parsed `coq-import` command-line arguments (`=`-form flags only, matching
/// the other `mathverse_shard` subcommands).
#[derive(Debug)]
struct CoqImportArgs {
    sexp_root: PathBuf,
    out_dir: PathBuf,
    libraries: Vec<String>,
    json: Option<PathBuf>,
    /// Baseline root for the 0-regression gate
    /// (`<dir>/<library>/kernel-verified.json`).
    gate_baseline: Option<PathBuf>,
    /// Promote fresh outputs over the baseline when the gate is fully green.
    /// Only valid together with `gate_baseline` (enforced by [`parse_args`]).
    promote_on_green: bool,
    options: CoqImportOptions,
}

/// Behavior knobs for the per-library pipeline, separated from argv so the
/// pipeline is directly testable.
#[derive(Debug)]
pub(crate) struct CoqImportOptions {
    /// Replay inductive families with [`InductiveReplayPolicy::LeanFaithful`]
    /// instead of the default `Generate`.
    pub(crate) lean_faithful: bool,
    /// Stamp the kernel's verdict back into the shard bytes on disk.
    pub(crate) stamp: bool,
}

/// Everything the harness learned about one library, for the stdout table and
/// the optional aggregate JSON.
#[derive(Debug)]
pub(crate) struct CoqLibraryOutcome {
    pub(crate) converted: CoqConvertDirStats,
    /// `None` when the library directory produced no shard (e.g. every file
    /// failed to parse) — conversion stats still carry the loss accounting.
    pub(crate) verified: Option<IncrementalVerifyReport>,
    /// KernelVerified constants whose transitive non-foundational axiom
    /// closure is empty (`env.axiom_deps` empty).
    pub(crate) bedrock: usize,
    /// Stored `KernelVerified` header count on disk before stamping
    /// (`None` when `--no-stamp` or nothing was verified).
    pub(crate) stored_kernel_verified_before: Option<usize>,
    /// Stored `KernelVerified` header count on disk after stamping.
    pub(crate) stored_kernel_verified_after: Option<usize>,
    /// First 10 masked-failure axiom-fallback roots as `(constant name,
    /// kernel reason)` pairs (reasons truncated to
    /// [`FALLBACK_REASON_MAX_CHARS`] chars).
    pub(crate) top_fallback_roots: Vec<(String, String)>,
}

/// Character cap applied to each fallback root's kernel reason in the stdout
/// table and the `--json` report (kept short — these are diagnostics, not
/// the durable record).
const FALLBACK_REASON_MAX_CHARS: usize = 160;

/// Truncate `reason` to `max_chars` characters, appending `…` when cut
/// (char-boundary safe).
fn truncate_reason(reason: &str, max_chars: usize) -> String {
    let mut chars = reason.chars();
    let head: String = chars.by_ref().take(max_chars).collect();
    if chars.next().is_some() {
        format!("{head}…")
    } else {
        head
    }
}

fn parse_args(args: &[String]) -> Result<CoqImportArgs, String> {
    let mut sexp_root: Option<PathBuf> = None;
    let mut out_dir: Option<PathBuf> = None;
    let mut libraries = Vec::new();
    let mut json = None;
    let mut gate_baseline: Option<PathBuf> = None;
    let mut promote_on_green = false;
    let mut lean_faithful = false;
    let mut no_stamp = false;

    for arg in args {
        if let Some(v) = arg.strip_prefix("--sexp-root=") {
            sexp_root = Some(PathBuf::from(v));
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out_dir = Some(PathBuf::from(v));
        } else if let Some(v) = arg.strip_prefix("--library=") {
            libraries.push(v.to_string());
        } else if let Some(v) = arg.strip_prefix("--json=") {
            json = Some(PathBuf::from(v));
        } else if let Some(v) = arg.strip_prefix("--gate-baseline=") {
            gate_baseline = Some(PathBuf::from(v));
        } else if arg == "--promote-on-green" {
            promote_on_green = true;
        } else if arg == "--lean-faithful" {
            lean_faithful = true;
        } else if arg == "--no-stamp" {
            no_stamp = true;
        } else {
            return Err(format!("Unknown option: {arg}\n{USAGE}"));
        }
    }

    if promote_on_green && gate_baseline.is_none() {
        return Err(format!(
            "--promote-on-green requires --gate-baseline=<dir>\n{USAGE}"
        ));
    }

    Ok(CoqImportArgs {
        sexp_root: sexp_root.ok_or_else(|| format!("Missing --sexp-root=<dir>\n{USAGE}"))?,
        out_dir: out_dir.ok_or_else(|| format!("Missing --out=<dir>\n{USAGE}"))?,
        libraries,
        json,
        gate_baseline,
        promote_on_green,
        options: CoqImportOptions {
            lean_faithful,
            stamp: !no_stamp,
        },
    })
}

/// Discover library names: the (sorted) subdirectories of `sexp_root`, or the
/// explicit `--library` selection validated against them.
fn discover_libraries(sexp_root: &Path, requested: &[String]) -> Result<Vec<String>, String> {
    let rd = std::fs::read_dir(sexp_root)
        .map_err(|e| format!("cannot read --sexp-root {}: {e}", sexp_root.display()))?;
    let mut all: Vec<String> = rd
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    all.sort();

    if requested.is_empty() {
        if all.is_empty() {
            return Err(format!(
                "no library subdirectories under {} (expected <sexp-root>/<library>/<module>.sexp)",
                sexp_root.display()
            ));
        }
        return Ok(all);
    }
    for lib in requested {
        if !all.iter().any(|a| a == lib) {
            return Err(format!(
                "--library={lib} not found under {} (available: {})",
                sexp_root.display(),
                all.join(", ")
            ));
        }
    }
    Ok(requested.to_vec())
}

/// SOUNDNESS FLOOR (Mathlib-stamp pattern): before kernel verification, NO
/// non-inductive constant may already carry an import-time `KernelVerified`
/// stamp — only Clean's kernel re-verification may mint that verdict for
/// value-bearing declarations. Returns the breaching constant names.
///
/// `DeclKind::Inductive` / `DeclKind::Constructor` entries are exempt and
/// documented: `import_serapi_inductive` tags the `NO_VALUE` family
/// certificate entries `KernelVerified` at import time because they are
/// replayed through the CHECKED `Environment::add_inductive` path during
/// corpus verification — the tag marks the family-replay lane, not a minted
/// proof verdict, and a family that fails its checked replay surfaces as a
/// verification failure, never as a silently trusted constant.
fn soundness_floor_breaches(readers: &[(PathBuf, ShardReader)]) -> Vec<String> {
    let target = ImportConfidence::KernelVerified as u8;
    let mut breaches = Vec::new();
    for (path, reader) in readers {
        for c in &reader.constants {
            if c.import_confidence == target
                && c.decl_kind != DeclKind::Inductive as u8
                && c.decl_kind != DeclKind::Constructor as u8
            {
                let name = reader
                    .strings
                    .get(c.name_idx as usize)
                    .map(String::as_str)
                    .unwrap_or("<unnamed>");
                breaches.push(format!("{name} ({})", path.display()));
            }
        }
    }
    breaches
}

/// Reproducibility fingerprint for the coq-import manifest. No `.olean`
/// closure loading or proof-value elision happens on this pipeline, so those
/// fields record the pipeline's fixed facts (`elision "none"`, bare prelude,
/// `max_closure_modules 0` = no closure loader engaged).
fn coq_import_fingerprint() -> StampEnvFingerprint {
    StampEnvFingerprint {
        kernel_version: clean_kernel::VERSION.to_string(),
        toolchain: option_env!("CLEAN_MATHVERSE_TOOLCHAIN_VERSION")
            .unwrap_or("unknown")
            .to_string(),
        heartbeat: std::env::var("CLEAN_KERNEL_HEARTBEAT")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "default".to_string()),
        elision_policy: "none".to_string(),
        max_closure_modules: 0,
        prelude_variant: "prelude-only".to_string(),
    }
}

/// Run the full per-library pipeline: convert → soundness floor → merge →
/// prelude env → corpus verify → manifest sidecar → stamp + audit → bedrock.
///
/// Pure function of paths + options (no argv) so the command internals are
/// end-to-end testable.
#[cfg(test)]
pub(crate) fn run_coq_import_library(
    name: &str,
    sexp_dir: &Path,
    out_lib_dir: &Path,
    opts: &CoqImportOptions,
) -> Result<CoqLibraryOutcome, String> {
    run_coq_import_library_with_context(name, sexp_dir, out_lib_dir, opts, &[], None)
        .map(|(outcome, _env)| outcome)
}

/// [`run_coq_import_library`] with UPSTREAM-LIBRARY context: `context_sexp_dirs`
/// register the upstream libraries' inductive/constant metadata into the
/// conversion session (registration only — nothing upstream is imported into
/// this library's shard), and `base_env` supplies the post-verification kernel
/// environment of the upstream libraries as this library's verification prelude
/// (so its constants' references to upstream declarations resolve against the
/// kernel-checked upstream, with this library's own counters unpolluted).
/// Returns the outcome plus the post-verification environment for the NEXT
/// library in dependency order.
pub(crate) fn run_coq_import_library_with_context(
    name: &str,
    sexp_dir: &Path,
    out_lib_dir: &Path,
    opts: &CoqImportOptions,
    context_sexp_dirs: &[PathBuf],
    base_env: Option<clean_kernel::Environment>,
) -> Result<(CoqLibraryOutcome, clean_kernel::Environment), String> {
    // (a) Convert into the per-library shard (upstream context registered
    // first, so cross-library Case/Fix reconstruction resolves).
    let shard_name = format!("coq_{name}.mathverse");
    let converted =
        convert_coq_sexp_dir_with_context(sexp_dir, context_sexp_dirs, out_lib_dir, &shard_name);
    if let Some(e) = &converted.shard_write_error {
        return Err(format!("{name}: shard write failed: {e}"));
    }

    // Read every shard of the library dir ONCE (floor scan + merge reuse them).
    let shard_files = discover_mathverse_files(out_lib_dir);
    let mut readers: Vec<(PathBuf, ShardReader)> = Vec::with_capacity(shard_files.len());
    for path in shard_files {
        let reader = ShardReader::from_file(&path)
            .map_err(|e| format!("{name}: unreadable shard {}: {e}", path.display()))?;
        readers.push((path, reader));
    }

    // (b) Soundness floor: abort BEFORE verification on any import-time
    // KernelVerified stamp outside the exempt inductive-family certificate lane.
    let breaches = soundness_floor_breaches(&readers);
    if !breaches.is_empty() {
        return Err(format!(
            "{name}: SOUNDNESS FLOOR breach: {} non-inductive constant(s) carry an \
             import-time KernelVerified stamp before kernel verification (only Clean's \
             kernel may mint KernelVerified for value-bearing declarations); first: {}",
            breaches.len(),
            breaches[0]
        ));
    }

    if readers.is_empty() {
        // Nothing importable (e.g. every file failed to parse). Report the
        // conversion loss honestly; there is nothing to verify or stamp. The
        // upstream environment (or a fresh prelude) passes through unchanged
        // for the next library in dependency order.
        let env = match base_env {
            Some(env) => env,
            None => clean_kernel::Environment::try_with_prelude_for_import()
                .map_err(|e| format!("{name}: kernel prelude environment: {e}"))?,
        };
        return Ok((
            CoqLibraryOutcome {
                converted,
                verified: None,
                bedrock: 0,
                stored_kernel_verified_before: None,
                stored_kernel_verified_after: None,
                top_fallback_roots: Vec::new(),
            },
            env,
        ));
    }

    // (c) Merge all shards of this library into one globally-indexed library.
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    let mut loaded = 0usize;
    for (path, reader) in &readers {
        library
            .load_shard(reader)
            .map_err(|e| format!("{name}: load shard {}: {e}", path.display()))?;
        loaded += 1;
    }

    // (d) Prelude-seeded kernel environment — the upstream libraries'
    // post-verification environment when given (dependency-ordered multi-
    // library run), else a fresh prelude.
    let mut prelude = match base_env {
        Some(env) => env,
        None => clean_kernel::Environment::try_with_prelude_for_import()
            .map_err(|e| format!("{name}: kernel prelude environment: {e}"))?,
    };
    // COQ LANE: Coq's type theory (pCIC) is CUMULATIVE (`Prop ≤ Set ≤ Type`),
    // so re-verify Coq-sourced declarations with cumulative subtyping. This is
    // the sound, faithful rule for the source system; it is scoped to this
    // Coq import path and does not affect the Lean/olean verification lane.
    // Idempotent when the upstream env already set it.
    prelude.set_cumulative(true);

    // (e) Global dependency-ordered corpus verification. Masked failures
    // (values the kernel rejected) surface as axiom_fallback, never as
    // KernelVerified — honest withholding for free.
    let policy = if opts.lean_faithful {
        InductiveReplayPolicy::LeanFaithful
    } else {
        InductiveReplayPolicy::Generate
    };
    let (env, report) = verify_corpus_incremental_with_env_policy(&library, prelude, policy);

    // (h) BEDROCK = KernelVerified AND empty transitive non-foundational axiom
    // closure (⊆ propext / Quot.sound / Classical.choice). Mirrors the
    // `verify-kernel --corpus` accounting.
    let bedrock = report
        .kernel_verified_names
        .iter()
        .filter(|n| {
            env.axiom_deps(&clean_kernel::Name::from_string(n))
                .map(|d| d.is_empty())
                .unwrap_or(false)
        })
        .count();

    // (f) Non-destructive manifest sidecar recording exactly what the kernel
    // re-verified.
    let manifest =
        KernelVerifiedManifest::from_report(&out_lib_dir.display().to_string(), loaded, &report)
            .with_env_fingerprint(coq_import_fingerprint());
    let manifest_path = out_lib_dir.join("kernel-verified.json");
    manifest
        .write_to_file(&manifest_path)
        .map_err(|e| format!("{name}: write {}: {e}", manifest_path.display()))?;

    // (g) Stamp the kernel's verdict into the shard bytes, with a before/after
    // stored-count audit re-read from disk.
    let (before, after) = if opts.stamp {
        let (b, _) = count_stored_kernel_verified(out_lib_dir)
            .map_err(|e| format!("{name}: pre-stamp stored count: {e}"))?;
        stamp_shard_dir_kernel_verified(out_lib_dir, &manifest)
            .map_err(|e| format!("{name}: stamp: {e}"))?;
        let (a, unreadable) = count_stored_kernel_verified(out_lib_dir)
            .map_err(|e| format!("{name}: post-stamp stored count: {e}"))?;
        if !unreadable.is_empty() {
            return Err(format!(
                "{name}: unreadable shard(s) after stamp: {}",
                unreadable.join(", ")
            ));
        }
        (Some(b), Some(a))
    } else {
        (None, None)
    };

    let top_fallback_roots = report
        .axiom_fallback_names
        .iter()
        .take(10)
        .map(|(n, reason)| {
            (
                n.clone(),
                truncate_reason(reason, FALLBACK_REASON_MAX_CHARS),
            )
        })
        .collect();

    Ok((
        CoqLibraryOutcome {
            converted,
            verified: Some(report),
            bedrock,
            stored_kernel_verified_before: before,
            stored_kernel_verified_after: after,
            top_fallback_roots,
        },
        env,
    ))
}

/// Run the pipeline for every selected library under `sexp_root`. A failing
/// library (floor breach, unreadable shards, ...) never aborts the others; its
/// error is carried in the result list.
pub(crate) fn run_coq_import_root(
    sexp_root: &Path,
    out_dir: &Path,
    requested: &[String],
    opts: &CoqImportOptions,
) -> Result<Vec<(String, Result<CoqLibraryOutcome, String>)>, String> {
    let mut libs = discover_libraries(sexp_root, requested)?;
    // DEPENDENCY ORDER: the Coq stdlib is upstream of every other library
    // (mathcomp et al. reference `Coq.Init.*` inductives and constants), so it
    // imports and verifies first; each later library then receives the
    // registration context and post-verification kernel environment of the
    // libraries before it. Within the non-stdlib tail, keep the sorted order.
    libs.sort_by_key(|l| (l != "stdlib", l.clone()));
    let mut base_env: Option<clean_kernel::Environment> = None;
    let mut context_dirs: Vec<PathBuf> = Vec::new();
    let mut results = Vec::with_capacity(libs.len());
    for lib in libs {
        let lib_sexp_dir = sexp_root.join(&lib);
        let outcome = run_coq_import_library_with_context(
            &lib,
            &lib_sexp_dir,
            &out_dir.join(&lib),
            opts,
            &context_dirs,
            base_env.take(),
        );
        match outcome {
            Ok((o, env)) => {
                base_env = Some(env);
                context_dirs.push(lib_sexp_dir);
                results.push((lib, Ok(o)));
            }
            Err(e) => {
                // A failed library contributes neither context nor environment;
                // the next library starts from a fresh prelude (fail closed —
                // never verify against a half-built upstream).
                results.push((lib, Err(e)));
            }
        }
    }
    Ok(results)
}

/// Diff of a fresh kernel-verified name set against a promoted baseline
/// (the 0-regression gate's per-library verdict).
#[derive(Debug)]
pub(crate) struct GateDiff {
    /// `kernel_verified_names` count in the baseline manifest.
    pub(crate) baseline_len: usize,
    /// `kernel_verified_names` count in the fresh import.
    pub(crate) new_len: usize,
    /// Baseline names MISSING from the fresh import (sorted, deduped).
    /// Non-empty = regression = red gate.
    pub(crate) regressed: Vec<String>,
}

impl GateDiff {
    /// Net change in kernel-verified count (`new - baseline`; can be negative).
    pub(crate) fn net(&self) -> i64 {
        self.new_len as i64 - self.baseline_len as i64
    }

    /// Green iff the fresh set is a superset of the baseline set.
    pub(crate) fn is_green(&self) -> bool {
        self.regressed.is_empty()
    }
}

/// Per-library gate verdict against a baseline root directory.
#[derive(Debug)]
pub(crate) enum LibraryGate {
    /// No `kernel-verified.json` baseline for this library — first import,
    /// treated as green. Carries the fresh count for the JSON report.
    NoBaseline { new_len: usize },
    /// Diffed against the library's baseline manifest.
    Diffed(GateDiff),
}

/// Pure gate diff: which `baseline` names are missing from `fresh`?
/// The 0-regression rule holds iff the result's `regressed` is empty.
pub(crate) fn diff_kernel_verified(baseline: &[String], fresh: &[String]) -> GateDiff {
    let fresh_set: std::collections::HashSet<&str> = fresh.iter().map(String::as_str).collect();
    let mut regressed: Vec<String> = baseline
        .iter()
        .filter(|n| !fresh_set.contains(n.as_str()))
        .cloned()
        .collect();
    regressed.sort();
    regressed.dedup();
    GateDiff {
        baseline_len: baseline.len(),
        new_len: fresh.len(),
        regressed,
    }
}

/// Gate every library outcome against `baseline_root/<library>/
/// kernel-verified.json` (read via [`KernelVerifiedManifest::from_file`]).
/// A library that errored or produced no shard has an EMPTY fresh set, so
/// with a baseline present every baseline name regresses (fail closed).
/// An unreadable baseline manifest is a hard error — never gate against
/// a half-read baseline.
pub(crate) fn gate_results(
    baseline_root: &Path,
    results: &[(String, Result<CoqLibraryOutcome, String>)],
) -> Result<Vec<(String, LibraryGate)>, String> {
    const EMPTY: &[String] = &[];
    let mut gates = Vec::with_capacity(results.len());
    for (name, res) in results {
        let fresh: &[String] = match res {
            Ok(o) => o
                .verified
                .as_ref()
                .map_or(EMPTY, |r| &r.kernel_verified_names),
            Err(_) => EMPTY,
        };
        let manifest_path = baseline_root.join(name).join("kernel-verified.json");
        let gate = if manifest_path.is_file() {
            let baseline = KernelVerifiedManifest::from_file(&manifest_path)
                .map_err(|e| format!("gate baseline {}: {e}", manifest_path.display()))?;
            LibraryGate::Diffed(diff_kernel_verified(&baseline.kernel_verified_names, fresh))
        } else {
            LibraryGate::NoBaseline {
                new_len: fresh.len(),
            }
        };
        gates.push((name.clone(), gate));
    }
    Ok(gates)
}

/// The whole gate is green iff every baselined library kept the superset
/// invariant (libraries without a baseline are green by definition).
pub(crate) fn gate_is_green(gates: &[(String, LibraryGate)]) -> bool {
    gates.iter().all(|(_, g)| match g {
        LibraryGate::NoBaseline { .. } => true,
        LibraryGate::Diffed(d) => d.is_green(),
    })
}

/// Max regressed names printed per library in the gate table.
const GATE_REGRESSED_PRINT_CAP: usize = 10;

fn print_gate_table(baseline_root: &Path, gates: &[(String, LibraryGate)]) {
    println!("=== Gate (baseline: {}) ===", baseline_root.display());
    for (name, gate) in gates {
        match gate {
            LibraryGate::NoBaseline { .. } => {
                println!("  [gate] {name}: no baseline (first import)");
            }
            LibraryGate::Diffed(d) => {
                println!(
                    "  [gate] {name}: KV {} -> {} (net {}{})  REGRESSED {}",
                    d.baseline_len,
                    d.new_len,
                    if d.net() >= 0 { "+" } else { "" },
                    d.net(),
                    d.regressed.len()
                );
                for r in d.regressed.iter().take(GATE_REGRESSED_PRINT_CAP) {
                    println!("    regressed: {r}");
                }
                if d.regressed.len() > GATE_REGRESSED_PRINT_CAP {
                    println!(
                        "    ... and {} more",
                        d.regressed.len() - GATE_REGRESSED_PRINT_CAP
                    );
                }
            }
        }
    }
}

/// Promotable outputs of a library dir: the manifest sidecar + the shards.
fn is_promotable_file(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|n| n == "kernel-verified.json")
        || path.extension().is_some_and(|e| e == "mathverse")
}

// ---------------------------------------------------------------------------
// Corpus drift detection (2026-07-13, incident-driven): a worktree session
// once mutated the shared corpus with MTIME-PRESERVING copies — timestamps
// lied, and the change surfaced only as unexplained KV regressions an hour of
// bisecting later. The gate now content-hashes each library's corpus inputs
// (`.sexp` + `.meta.json` — sidecar notes feed stand-in recovery) against the
// hashes recorded at the LAST PROMOTION, and announces any drift up front.
// Drift is INFORMATIONAL (legitimate re-dumps are routine); the value is that
// a corpus change is never silent again.
// ---------------------------------------------------------------------------

/// File name of the per-library corpus hash record, stored next to the
/// promoted `kernel-verified.json`.
pub(crate) const CORPUS_HASHES_FILE: &str = "corpus-hashes.json";

/// SHA-256 hex digests of a library's corpus inputs, keyed by file name.
pub(crate) fn hash_corpus_library(
    sexp_root: &Path,
    library: &str,
) -> Result<std::collections::BTreeMap<String, String>, String> {
    use sha2::{Digest, Sha256};
    let dir = sexp_root.join(library);
    let mut out = std::collections::BTreeMap::new();
    let rd = std::fs::read_dir(&dir).map_err(|e| format!("corpus hash {}: {e}", dir.display()))?;
    let mut files: Vec<PathBuf> = rd
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.is_file()
                && (p.extension().is_some_and(|x| x == "sexp")
                    || p.file_name()
                        .is_some_and(|n| n.to_string_lossy().ends_with(".meta.json")))
        })
        .collect();
    files.sort();
    for f in files {
        let bytes = std::fs::read(&f).map_err(|e| format!("corpus hash {}: {e}", f.display()))?;
        let digest = Sha256::digest(&bytes);
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        let name = f
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        out.insert(name, hex);
    }
    Ok(out)
}

/// Per-library corpus drift vs the last-promoted hash record.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct CorpusDrift {
    pub(crate) changed: Vec<String>,
    pub(crate) added: Vec<String>,
    pub(crate) removed: Vec<String>,
}

impl CorpusDrift {
    pub(crate) fn is_clean(&self) -> bool {
        self.changed.is_empty() && self.added.is_empty() && self.removed.is_empty()
    }
}

/// Diff fresh corpus hashes against the recorded baseline hashes.
pub(crate) fn diff_corpus_hashes(
    baseline: &std::collections::BTreeMap<String, String>,
    fresh: &std::collections::BTreeMap<String, String>,
) -> CorpusDrift {
    let mut d = CorpusDrift::default();
    for (name, hash) in fresh {
        match baseline.get(name) {
            None => d.added.push(name.clone()),
            Some(b) if b != hash => d.changed.push(name.clone()),
            _ => {}
        }
    }
    for name in baseline.keys() {
        if !fresh.contains_key(name) {
            d.removed.push(name.clone());
        }
    }
    d
}

/// Load a library's recorded corpus hashes (`None` = never recorded).
pub(crate) fn load_corpus_hashes(
    baseline_root: &Path,
    library: &str,
) -> Result<Option<std::collections::BTreeMap<String, String>>, String> {
    let path = baseline_root.join(library).join(CORPUS_HASHES_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let text =
        std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    serde_json::from_str(&text)
        .map(Some)
        .map_err(|e| format!("parse {}: {e}", path.display()))
}

/// Write a library's corpus hashes next to its promoted manifest.
pub(crate) fn write_corpus_hashes(
    baseline_root: &Path,
    library: &str,
    hashes: &std::collections::BTreeMap<String, String>,
) -> Result<(), String> {
    let dir = baseline_root.join(library);
    std::fs::create_dir_all(&dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
    let path = dir.join(CORPUS_HASHES_FILE);
    let text = serde_json::to_string_pretty(hashes)
        .map_err(|e| format!("serialize corpus hashes: {e}"))?;
    std::fs::write(&path, text).map_err(|e| format!("write {}: {e}", path.display()))
}

/// Cap on drifted file names printed per library.
const CORPUS_DRIFT_PRINT_CAP: usize = 8;

fn print_corpus_drift(name: &str, drift: Option<&CorpusDrift>, file_count: usize) {
    match drift {
        None => println!(
            "  [corpus] {name}: no hash baseline ({file_count} files) — will record on promote"
        ),
        Some(d) if d.is_clean() => println!("  [corpus] {name}: unchanged ({file_count} files)"),
        Some(d) => {
            println!(
                "  [corpus] {name}: DRIFT — {} changed, {} added, {} removed (since last promote)",
                d.changed.len(),
                d.added.len(),
                d.removed.len()
            );
            for f in d
                .changed
                .iter()
                .chain(d.added.iter())
                .chain(d.removed.iter())
                .take(CORPUS_DRIFT_PRINT_CAP)
            {
                println!("    drift: {f}");
            }
        }
    }
}

/// Copy each successfully imported library's fresh outputs
/// (`kernel-verified.json` + `*.mathverse`) from `out_dir/<library>/` over
/// `baseline_root/<library>/`, creating directories as needed. Errored
/// libraries and libraries with no promotable outputs are skipped. Returns
/// `(library, promoted file names)` pairs.
///
/// GREEN-GATE ONLY: callers must check the gate first —
/// [`promote_if_green`] is the safe entry point.
pub(crate) fn promote_libraries(
    out_dir: &Path,
    baseline_root: &Path,
    results: &[(String, Result<CoqLibraryOutcome, String>)],
) -> Result<Vec<(String, Vec<String>)>, String> {
    let mut promoted = Vec::new();
    for (name, res) in results {
        if res.is_err() {
            continue; // a failed library has no trustworthy outputs
        }
        let src_dir = out_dir.join(name);
        if !src_dir.is_dir() {
            continue;
        }
        let mut files: Vec<PathBuf> = std::fs::read_dir(&src_dir)
            .map_err(|e| format!("promote: read {}: {e}", src_dir.display()))?
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.is_file() && is_promotable_file(p))
            .collect();
        files.sort();
        if files.is_empty() {
            continue; // nothing importable produced nothing to promote
        }
        let dst_dir = baseline_root.join(name);
        std::fs::create_dir_all(&dst_dir)
            .map_err(|e| format!("promote: create {}: {e}", dst_dir.display()))?;
        let mut copied = Vec::with_capacity(files.len());
        for f in &files {
            let file_name = f
                .file_name()
                .ok_or_else(|| format!("promote: pathological path {}", f.display()))?;
            let dst = dst_dir.join(file_name);
            std::fs::copy(f, &dst)
                .map_err(|e| format!("promote: copy {} -> {}: {e}", f.display(), dst.display()))?;
            copied.push(file_name.to_string_lossy().into_owned());
        }
        promoted.push((name.clone(), copied));
    }
    Ok(promoted)
}

/// The `--promote-on-green` action: promote iff the gate is FULLY green.
/// `Ok(None)` = red gate, nothing touched; `Ok(Some(..))` = what was promoted.
pub(crate) fn promote_if_green(
    gates: &[(String, LibraryGate)],
    out_dir: &Path,
    baseline_root: &Path,
    results: &[(String, Result<CoqLibraryOutcome, String>)],
) -> Result<Option<Vec<(String, Vec<String>)>>, String> {
    if !gate_is_green(gates) {
        return Ok(None);
    }
    promote_libraries(out_dir, baseline_root, results).map(Some)
}

/// Entry point for `mathverse_shard coq-import`. Prints the per-library trust
/// distribution, optionally writes the aggregate JSON, and exits nonzero iff
/// any library errored or has `failed > 0 || reconstruct_failed > 0`
/// (mirroring `verify-kernel --corpus`; axiom_fallback does not fail) — or,
/// with `--gate-baseline`, iff any baselined library regressed.
pub(crate) fn cmd_coq_import(args: &[String]) {
    let parsed = match parse_args(args) {
        Ok(p) => p,
        Err(msg) => {
            eprintln!("{msg}");
            std::process::exit(1);
        }
    };

    println!("=== Mathverse Coq Corpus Import (COQ-6 harness) ===");
    println!("  Sexp root: {}", parsed.sexp_root.display());
    println!("  Out dir:   {}", parsed.out_dir.display());
    println!(
        "  Policy:    {} | {}\n",
        if parsed.options.lean_faithful {
            "LeanFaithful family replay"
        } else {
            "Generate family replay"
        },
        if parsed.options.stamp {
            "stamp verdicts"
        } else {
            "no-stamp (manifest only)"
        }
    );

    let start = Instant::now();
    let results = match run_coq_import_root(
        &parsed.sexp_root,
        &parsed.out_dir,
        &parsed.libraries,
        &parsed.options,
    ) {
        Ok(r) => r,
        Err(msg) => {
            eprintln!("Error: {msg}");
            std::process::exit(1);
        }
    };

    let mut any_failed = false;
    for (name, res) in &results {
        match res {
            Ok(outcome) => print_library_outcome(name, outcome),
            Err(msg) => {
                any_failed = true;
                eprintln!("  ERROR {name}: {msg}\n");
            }
        }
    }

    print_summary_table(&results);
    println!("\n  Completed in {:.2}s", start.elapsed().as_secs_f64());

    // 0-regression gate against the promoted baselines.
    let gates = match &parsed.gate_baseline {
        Some(baseline_root) => match gate_results(baseline_root, &results) {
            Ok(g) => {
                println!();
                print_gate_table(baseline_root, &g);
                Some(g)
            }
            Err(msg) => {
                eprintln!("Error: {msg}");
                std::process::exit(1);
            }
        },
        None => None,
    };
    let any_regressed = gates.as_deref().is_some_and(|g| !gate_is_green(g));

    // Corpus drift report (informational): content-hash each library's corpus
    // inputs against the record from the LAST PROMOTION, so a mutated corpus
    // is announced here instead of surfacing as unexplained KV regressions.
    let mut fresh_corpus_hashes: Vec<(String, std::collections::BTreeMap<String, String>)> =
        Vec::new();
    if let Some(baseline_root) = &parsed.gate_baseline {
        for (name, _) in &results {
            match hash_corpus_library(&parsed.sexp_root, name) {
                Ok(hashes) => {
                    let drift = match load_corpus_hashes(baseline_root, name) {
                        Ok(Some(recorded)) => Some(diff_corpus_hashes(&recorded, &hashes)),
                        Ok(None) => None,
                        Err(e) => {
                            eprintln!("  [corpus] {name}: hash baseline unreadable: {e}");
                            None
                        }
                    };
                    print_corpus_drift(name, drift.as_ref(), hashes.len());
                    fresh_corpus_hashes.push((name.clone(), hashes));
                }
                Err(e) => eprintln!("  [corpus] {name}: hashing failed: {e}"),
            }
        }
    }

    if let Some(json_path) = &parsed.json {
        match write_json_report(json_path, &results, gates.as_deref()) {
            Ok(()) => println!("  Aggregate JSON written to {}", json_path.display()),
            Err(e) => {
                eprintln!("  ERROR writing --json report: {e}");
                any_failed = true;
            }
        }
    }

    for (_, res) in &results {
        if let Ok(o) = res {
            if let Some(r) = &o.verified {
                if r.failed > 0 || r.reconstruct_failed > 0 {
                    any_failed = true;
                }
            }
        }
    }

    // Promote ONLY on a fully green gate (parse_args guarantees the
    // baseline dir is present whenever --promote-on-green is).
    if parsed.promote_on_green {
        if let (Some(baseline_root), Some(gates)) = (&parsed.gate_baseline, &gates) {
            match promote_if_green(gates, &parsed.out_dir, baseline_root, &results) {
                Ok(None) => eprintln!("  [promote] gate RED — nothing promoted"),
                Ok(Some(promoted)) if promoted.is_empty() => {
                    println!("  [promote] gate green, but no library outputs to promote");
                }
                Ok(Some(promoted)) => {
                    for (lib, files) in &promoted {
                        println!(
                            "  [promote] {lib}: {} -> {}",
                            files.join(", "),
                            baseline_root.join(lib).display()
                        );
                        // Record the promoted corpus state so the next run's
                        // drift report measures against THIS corpus.
                        if let Some((_, hashes)) =
                            fresh_corpus_hashes.iter().find(|(n, _)| n == lib)
                        {
                            if let Err(e) = write_corpus_hashes(baseline_root, lib, hashes) {
                                eprintln!("  [corpus] {lib}: hash record failed: {e}");
                            }
                        }
                    }
                }
                Err(e) => {
                    eprintln!("  ERROR promoting: {e}");
                    any_failed = true;
                }
            }
        }
    }

    if any_failed || any_regressed {
        std::process::exit(1);
    }
}

fn print_library_outcome(name: &str, o: &CoqLibraryOutcome) {
    let c = &o.converted;
    println!("=== Library: {name} ===");
    println!(
        "  Converted:   {} files ok, {} failed; {} declarations \
         ({} translated, {} axiomatized)",
        c.files_processed, c.files_failed, c.total_declarations, c.translated, c.axiomatized
    );
    println!(
        "  Import loss: {} skipped forms, {} dropped values (reasons in --json{})",
        c.skipped,
        c.value_translation_failed,
        if c.skip_reasons_truncated
            || c.value_failure_reasons_truncated
            || c.file_failures_truncated
        {
            "; reason lists truncated"
        } else {
            ""
        }
    );
    for (file, err) in c.file_failures.iter().take(5) {
        println!("    file-failed: {file}: {err}");
    }
    match &o.verified {
        Some(r) => {
            println!(
                "  Verified:    total {}, kernel-verified {}, axiom-accepted {}, \
                 axiom-fallback {}, failed {}, cycle-skipped {}, reconstruct-failed {}",
                r.total,
                r.kernel_verified,
                r.axiom_accepted,
                r.axiom_fallback,
                r.failed,
                r.cycle_skipped,
                r.reconstruct_failed
            );
            if !r.standin_blocked_fallbacks.is_empty() {
                println!(
                    "  Stand-in-blocked: {} value rejection(s) classified as clean \
                     type-only fallbacks (conversion blocked by value-less stand-ins; \
                     no taint seeded — audit via CLEAN_SPECULATIVE_REJECT_LOG)",
                    r.standin_blocked_fallbacks.len()
                );
            }
            if !r.discharged_axiom_names.is_empty() {
                println!(
                    "  Discharged:  {} source axiom(s) re-proved as kernel Theorems \
                     (counted in kernel-verified):",
                    r.discharged_axiom_names.len()
                );
                for n in &r.discharged_axiom_names {
                    println!("    discharged: {n}");
                }
            }
            println!(
                "  Bedrock:     {} (axiom_deps ⊆ propext / Quot.sound / Classical.choice)",
                o.bedrock
            );
            match (
                o.stored_kernel_verified_before,
                o.stored_kernel_verified_after,
            ) {
                (Some(b), Some(a)) => println!("  Stamped:     stored KernelVerified {b} → {a}"),
                _ => println!("  Stamped:     skipped (--no-stamp)"),
            }
            if !o.top_fallback_roots.is_empty() {
                println!(
                    "  Fallback roots (first {}, with kernel reasons):",
                    o.top_fallback_roots.len()
                );
                for (root, reason) in &o.top_fallback_roots {
                    println!("    {root}: {reason}");
                }
            }
        }
        None => println!("  Verified:    nothing importable (no shard produced)"),
    }
    println!();
}

fn print_summary_table(results: &[(String, Result<CoqLibraryOutcome, String>)]) {
    println!("=== Per-library trust distribution ===");
    println!(
        "  {:<18} {:>6} {:>6} {:>8} {:>8} {:>7} {:>7} {:>7} {:>5} {:>8} {:>8}",
        "Library",
        "Files",
        "FFail",
        "Decls",
        "KV",
        "AxAcc",
        "AxFb",
        "Failed",
        "Rec",
        "Bedrock",
        "Stored"
    );
    println!("  {}", "-".repeat(98));
    for (name, res) in results {
        match res {
            Ok(o) => {
                let (kv, axacc, axfb, failed, rec) =
                    o.verified.as_ref().map_or((0, 0, 0, 0, 0), |r| {
                        (
                            r.kernel_verified,
                            r.axiom_accepted,
                            r.axiom_fallback,
                            r.failed,
                            r.reconstruct_failed,
                        )
                    });
                println!(
                    "  {:<18} {:>6} {:>6} {:>8} {:>8} {:>7} {:>7} {:>7} {:>5} {:>8} {:>8}",
                    name,
                    o.converted.files_processed,
                    o.converted.files_failed,
                    o.converted.total_declarations,
                    kv,
                    axacc,
                    axfb,
                    failed,
                    rec,
                    o.bedrock,
                    o.stored_kernel_verified_after
                        .map_or_else(|| "-".to_string(), |n| n.to_string()),
                );
            }
            Err(_) => println!("  {name:<18} ERROR (see above)"),
        }
    }
}

/// The `verified` JSON block; all-zero when the library produced no shard
/// (nothing was verified — the conversion loss accounting still tells why).
fn verified_json(report: Option<&IncrementalVerifyReport>) -> serde_json::Value {
    let (total, kv, axacc, axfb, failed, cyc, rec, standin_blocked) =
        report.map_or((0, 0, 0, 0, 0, 0, 0, 0), |r| {
            (
                r.total,
                r.kernel_verified,
                r.axiom_accepted,
                r.axiom_fallback,
                r.failed,
                r.cycle_skipped,
                r.reconstruct_failed,
                r.standin_blocked_fallbacks.len(),
            )
        });
    let discharged: &[String] = report.map_or(&[], |r| r.discharged_axiom_names.as_slice());
    serde_json::json!({
        "total": total,
        "kernel_verified": kv,
        "axiom_accepted": axacc,
        "axiom_fallback": axfb,
        "failed": failed,
        "cycle_skipped": cyc,
        "reconstruct_failed": rec,
        "standin_blocked": standin_blocked,
        "discharged_axioms": discharged.len(),
        "discharged_axiom_names": discharged,
    })
}

/// Max regressed names carried in the JSON `gate` object (with a
/// `regressed_truncated` marker when the cap bites).
const GATE_REGRESSED_JSON_CAP: usize = 100;

/// The per-library `"gate"` JSON object added when `--gate-baseline` is
/// active. A first import (no baseline) reports `baseline`/`net` as null.
fn gate_json(gate: &LibraryGate) -> serde_json::Value {
    match gate {
        LibraryGate::NoBaseline { new_len } => serde_json::json!({
            "baseline": null,
            "new": new_len,
            "net": null,
            "regressed": [],
            "regressed_truncated": false,
        }),
        LibraryGate::Diffed(d) => {
            let capped: Vec<&str> = d
                .regressed
                .iter()
                .take(GATE_REGRESSED_JSON_CAP)
                .map(String::as_str)
                .collect();
            serde_json::json!({
                "baseline": d.baseline_len,
                "new": d.new_len,
                "net": d.net(),
                "regressed": capped,
                "regressed_truncated": d.regressed.len() > GATE_REGRESSED_JSON_CAP,
            })
        }
    }
}

fn write_json_report(
    path: &Path,
    results: &[(String, Result<CoqLibraryOutcome, String>)],
    gates: Option<&[(String, LibraryGate)]>,
) -> Result<(), String> {
    let mut map = serde_json::Map::new();
    for (name, res) in results {
        let mut value = match res {
            Ok(o) => {
                let c = &o.converted;
                let mut obj = serde_json::json!({
                    "converted": {
                        "files_processed": c.files_processed,
                        "files_failed": c.files_failed,
                        "total_declarations": c.total_declarations,
                        "translated": c.translated,
                        "axiomatized": c.axiomatized,
                        "skipped": c.skipped,
                        "value_translation_failed": c.value_translation_failed,
                        "file_failures": c.file_failures,
                        "file_failures_truncated": c.file_failures_truncated,
                        "skip_reasons": c.skip_reasons,
                        "skip_reasons_truncated": c.skip_reasons_truncated,
                        "value_failure_reasons": c.value_failure_reasons,
                        "value_failure_reasons_truncated": c.value_failure_reasons_truncated,
                    },
                    "verified": verified_json(o.verified.as_ref()),
                    "bedrock": o.bedrock,
                    "stored_kernel_verified": o.stored_kernel_verified_after,
                    "top_fallback_roots": o.top_fallback_roots,
                });
                // Full, untruncated per-name verdict lists for regression
                // triage. Gated behind COQ_IMPORT_FULL_REASONS because the
                // lists can run to tens of thousands of names. Distinguishes
                // own-value kernel rejection (`axiom_fallback_names`) from
                // taint-withheld dependents (`failures`).
                if std::env::var_os("COQ_IMPORT_FULL_REASONS").is_some() {
                    if let (Some(map), Some(rep)) = (obj.as_object_mut(), o.verified.as_ref()) {
                        let fallback: Vec<[&str; 2]> = rep
                            .axiom_fallback_names
                            .iter()
                            .map(|(n, r)| [n.as_str(), r.as_str()])
                            .collect();
                        let failed: Vec<[&str; 2]> = rep
                            .failures
                            .iter()
                            .map(|(n, r)| [n.as_str(), r.as_str()])
                            .collect();
                        let standin_blocked: Vec<[&str; 2]> = rep
                            .standin_blocked_fallbacks
                            .iter()
                            .map(|(n, r)| [n.as_str(), r.as_str()])
                            .collect();
                        map.insert(
                            "axiom_fallback_names_full".into(),
                            serde_json::json!(fallback),
                        );
                        map.insert("failed_names_full".into(), serde_json::json!(failed));
                        map.insert(
                            "standin_blocked_full".into(),
                            serde_json::json!(standin_blocked),
                        );
                    }
                }
                obj
            }
            Err(msg) => serde_json::json!({ "error": msg }),
        };
        if let Some(gates) = gates {
            if let (Some((_, gate)), Some(obj)) =
                (gates.iter().find(|(n, _)| n == name), value.as_object_mut())
            {
                obj.insert("gate".into(), gate_json(gate));
            }
        }
        map.insert(name.clone(), value);
    }
    let text =
        serde_json::to_string_pretty(&serde_json::Value::Object(map)).map_err(|e| e.to_string())?;
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    std::fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    use clean_mathverse::coq::alpha::CoqImporter;
    use clean_mathverse::library::stamp_shard_file_kernel_verified;
    use clean_mathverse::shard::ShardWriter;

    /// The alpha.rs golden-test hand dialect (REFL_N closure style): nat + eq
    /// + one Qed theorem carrying its genuine proof term as its value + one
    /// genuine axiom. Kernel-verifies nat(3) + eq(2) + refl_n(1) = 6; the
    /// axiom is AxiomAccepted.
    const GOOD_LIBRARY_SEXP: &str = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqInductive eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 1)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqConstant refl_n
  (Prod n (Ind nat 0) (App (Ind eq 0) (Ind nat 0) (Rel 0) (Rel 0)))
  (Lambda n (Ind nat 0) (App (Construct eq 0 0) (Ind nat 0) (Rel 0))))
(CoqAxiom classic (Sort Prop))"#;

    fn opts() -> CoqImportOptions {
        CoqImportOptions {
            lean_faithful: false,
            stamp: true,
        }
    }

    /// Fallback-reason truncation is char-boundary safe and marks the cut.
    #[test]
    fn test_truncate_reason_char_boundary_safe() {
        assert_eq!(truncate_reason("short reason", 160), "short reason");
        let long = "é".repeat(200);
        let t = truncate_reason(&long, 160);
        assert_eq!(t.chars().count(), 161, "160 kept chars + ellipsis");
        assert!(t.ends_with('…'), "the cut must be visible");
        // Exactly at the cap: no ellipsis.
        let exact = "x".repeat(160);
        assert_eq!(truncate_reason(&exact, 160), exact);
    }

    /// End-to-end over two libraries: the good library kernel-verifies and the
    /// stamp round-trip persists; the corrupt library reports its file failure
    /// LOUDLY without aborting the other library.
    #[test]
    fn test_coq_import_root_good_and_corrupt_libraries() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sexp_root = tmp.path().join("sexp");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(sexp_root.join("goodlib")).expect("mk goodlib");
        std::fs::create_dir_all(sexp_root.join("badlib")).expect("mk badlib");
        std::fs::write(sexp_root.join("goodlib/Mod.sexp"), GOOD_LIBRARY_SEXP)
            .expect("write good fixture");
        std::fs::write(sexp_root.join("badlib/Broken.sexp"), "(CoqConstant broken")
            .expect("write corrupt fixture");

        let results = run_coq_import_root(&sexp_root, &out, &[], &opts())
            .expect("root discovery should succeed");
        let by_name: HashMap<&str, &Result<CoqLibraryOutcome, String>> =
            results.iter().map(|(n, r)| (n.as_str(), r)).collect();

        // Good library: genuine kernel verification + persistent stamp.
        let good = by_name["goodlib"]
            .as_ref()
            .expect("good library pipeline should succeed");
        let report = good.verified.as_ref().expect("good library verifies");
        assert_eq!(report.failed, 0, "failures: {:?}", report.failures);
        assert_eq!(report.reconstruct_failed, 0);
        assert!(
            report.kernel_verified > 0,
            "good library must kernel-verify constants"
        );
        assert_eq!(report.kernel_verified, 6, "nat(3) + eq(2) + refl_n(1)");
        assert_eq!(report.axiom_accepted, 1, "the genuine CoqAxiom");
        assert!(
            report.kernel_verified_names.contains(&"refl_n".to_string()),
            "the Qed theorem must be genuinely kernel-verified"
        );
        // Stamp round-trip: re-read from disk, independently of the report.
        let (stored, unreadable) =
            count_stored_kernel_verified(&out.join("goodlib")).expect("stored count");
        assert!(unreadable.is_empty());
        assert!(stored > 0, "the stamp must persist in the shard bytes");
        assert_eq!(
            good.stored_kernel_verified_after,
            Some(stored),
            "outcome audit must match the on-disk re-read"
        );
        assert!(
            out.join("goodlib/kernel-verified.json").exists(),
            "manifest sidecar written"
        );

        // Corrupt library: counted file failure, no shard, NO abort.
        let bad = by_name["badlib"]
            .as_ref()
            .expect("corrupt file must not abort the library pipeline");
        assert_eq!(bad.converted.files_failed, 1, "never silent");
        assert_eq!(bad.converted.files_processed, 0);
        assert!(
            bad.verified.is_none(),
            "nothing importable, so nothing verified"
        );
    }

    /// The soundness floor aborts BEFORE verification when a value-bearing
    /// Definition in the library dir falsely carries an import-time
    /// KernelVerified stamp.
    #[test]
    fn test_soundness_floor_rejects_false_kernel_verified_definition() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sexp_dir = tmp.path().join("sexp/goodlib");
        let out_lib = tmp.path().join("out/goodlib");
        std::fs::create_dir_all(&sexp_dir).expect("mk sexp dir");
        std::fs::create_dir_all(&out_lib).expect("mk out dir");
        std::fs::write(sexp_dir.join("Mod.sexp"), GOOD_LIBRARY_SEXP).expect("write fixture");

        // Craft a shard whose value-bearing Definition falsely carries
        // KernelVerified (via the destructive stamp helper), and drop it into
        // the library dir the pipeline will load.
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp(
                "(CoqConstant evil (Sort (Type 0)) (Lambda x (Sort (Type 0)) (Rel 0)))",
                &mut w,
            )
            .expect("import evil fixture");
        let evil_path = out_lib.join("evil.mathverse");
        w.write_to_file(&evil_path).expect("write evil shard");
        let names: std::collections::HashSet<String> = ["evil".to_string()].into_iter().collect();
        let stamped =
            stamp_shard_file_kernel_verified(&evil_path, &names).expect("stamp evil shard");
        assert_eq!(stamped, 1, "the false stamp must land for the test to bite");

        let err = run_coq_import_library("goodlib", &sexp_dir, &out_lib, &opts())
            .expect_err("floor breach must abort the library before verification");
        assert!(
            err.contains("SOUNDNESS FLOOR"),
            "error must name the floor: {err}"
        );
        assert!(err.contains("evil"), "error must name the constant: {err}");
        assert!(
            !out_lib.join("kernel-verified.json").exists(),
            "abort happens BEFORE verification/manifest"
        );
    }

    /// Write a synthetic promoted-baseline manifest for `lib` under `root`
    /// carrying exactly `names` as its kernel-verified set.
    fn write_baseline_manifest(root: &Path, lib: &str, names: &[&str]) {
        let manifest = KernelVerifiedManifest::from_worker_parts(
            lib,
            names.len(),
            0,
            0,
            0.0,
            names.iter().map(|s| (*s).to_string()).collect(),
        );
        let lib_dir = root.join(lib);
        std::fs::create_dir_all(&lib_dir).expect("mk baseline lib dir");
        manifest
            .write_to_file(&lib_dir.join("kernel-verified.json"))
            .expect("write baseline manifest");
    }

    /// `--promote-on-green` without `--gate-baseline` is rejected; with it,
    /// both flags parse.
    #[test]
    fn test_parse_args_promote_requires_gate_baseline() {
        let ok: Vec<String> = [
            "--sexp-root=/s",
            "--out=/o",
            "--gate-baseline=/b",
            "--promote-on-green",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
        let parsed = parse_args(&ok).expect("gate+promote flags should parse");
        assert_eq!(parsed.gate_baseline, Some(PathBuf::from("/b")));
        assert!(parsed.promote_on_green);

        let bad: Vec<String> = ["--sexp-root=/s", "--out=/o", "--promote-on-green"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        let err = parse_args(&bad).expect_err("promote without gate-baseline must be rejected");
        assert!(
            err.contains("--gate-baseline"),
            "error must name the missing flag: {err}"
        );
    }

    /// Pure gate diff: a fresh SUPERSET is green with the right net; a
    /// missing baseline name is red and listed.
    #[test]
    fn test_gate_diff_superset_green_missing_name_red() {
        let base: Vec<String> = ["a", "b"].iter().map(|s| (*s).to_string()).collect();
        let fresh: Vec<String> = ["b", "c", "a"].iter().map(|s| (*s).to_string()).collect();
        let d = diff_kernel_verified(&base, &fresh);
        assert!(d.is_green(), "superset must gate green: {:?}", d.regressed);
        assert_eq!((d.baseline_len, d.new_len, d.net()), (2, 3, 1));

        let shrunk: Vec<String> = ["c", "a"].iter().map(|s| (*s).to_string()).collect();
        let d = diff_kernel_verified(&base, &shrunk);
        assert!(!d.is_green(), "a lost baseline name is a regression");
        assert_eq!(d.regressed, vec!["b".to_string()]);
        assert_eq!(d.net(), 0, "net can be flat while names still regress");
    }

    /// The JSON gate object caps `regressed` at 100 and marks the cut.
    #[test]
    fn test_gate_json_caps_regressed_names() {
        let regressed: Vec<String> = (0..150).map(|i| format!("n{i:03}")).collect();
        let gate = LibraryGate::Diffed(GateDiff {
            baseline_len: 150,
            new_len: 0,
            regressed,
        });
        let v = gate_json(&gate);
        assert_eq!(v["baseline"], serde_json::json!(150));
        assert_eq!(v["new"], serde_json::json!(0));
        assert_eq!(v["net"], serde_json::json!(-150));
        assert_eq!(v["regressed"].as_array().expect("array").len(), 100);
        assert_eq!(v["regressed_truncated"], serde_json::json!(true));

        let first = LibraryGate::NoBaseline { new_len: 7 };
        let v = gate_json(&first);
        assert_eq!(v["baseline"], serde_json::Value::Null);
        assert_eq!(v["new"], serde_json::json!(7));
        assert_eq!(v["regressed_truncated"], serde_json::json!(false));
    }

    /// Corpus drift detection: hashing is stable, an edited byte is `changed`,
    /// a new/removed file is `added`/`removed`, and the record round-trips.
    #[test]
    fn test_corpus_drift_detection() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sexp_root = tmp.path().join("sexp");
        let lib_dir = sexp_root.join("lib");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(lib_dir.join("A.sexp"), b"(CoqConstant A ...)").unwrap();
        std::fs::write(lib_dir.join("A.meta.json"), b"{\"skipped\":[]}").unwrap();
        // A non-corpus file must be ignored by the hasher.
        std::fs::write(lib_dir.join("A.other"), b"noise").unwrap();

        let h1 = hash_corpus_library(&sexp_root, "lib").expect("hash");
        assert_eq!(h1.len(), 2, "only .sexp + .meta.json are hashed");
        assert!(h1.contains_key("A.sexp") && h1.contains_key("A.meta.json"));

        // Stable: identical bytes → identical hashes → clean drift.
        let h2 = hash_corpus_library(&sexp_root, "lib").expect("hash");
        assert!(diff_corpus_hashes(&h1, &h2).is_clean());

        // Record + reload round-trips; no drift against itself.
        let baseline_root = tmp.path().join("baseline");
        write_corpus_hashes(&baseline_root, "lib", &h1).expect("write");
        let recorded = load_corpus_hashes(&baseline_root, "lib")
            .expect("load")
            .expect("present");
        assert_eq!(recorded, h1);

        // Edit one byte (mtime-preserving edit is exactly the incident shape).
        std::fs::write(lib_dir.join("A.sexp"), b"(CoqConstant A MUTATED)").unwrap();
        std::fs::write(lib_dir.join("B.sexp"), b"(CoqConstant B ...)").unwrap();
        std::fs::remove_file(lib_dir.join("A.meta.json")).unwrap();
        let h3 = hash_corpus_library(&sexp_root, "lib").expect("hash");
        let drift = diff_corpus_hashes(&recorded, &h3);
        assert!(!drift.is_clean());
        assert_eq!(drift.changed, vec!["A.sexp".to_string()]);
        assert_eq!(drift.added, vec!["B.sexp".to_string()]);
        assert_eq!(drift.removed, vec!["A.meta.json".to_string()]);

        // No recorded baseline → None (first import, will record on promote).
        assert!(load_corpus_hashes(&baseline_root, "unrecorded")
            .expect("load")
            .is_none());
    }

    /// End-to-end gate + promote loop over a real mini import:
    /// no baseline → green first import; subset baseline → green with
    /// positive net and promotion copies manifest + shard (re-gate is net
    /// +0); ghost-name baseline → red, name listed, promote_if_green
    /// touches NOTHING.
    #[test]
    fn test_gate_and_promote_on_green_loop() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sexp_root = tmp.path().join("sexp");
        let out = tmp.path().join("out");
        std::fs::create_dir_all(sexp_root.join("goodlib")).expect("mk goodlib");
        std::fs::write(sexp_root.join("goodlib/Mod.sexp"), GOOD_LIBRARY_SEXP)
            .expect("write fixture");
        let results =
            run_coq_import_root(&sexp_root, &out, &[], &opts()).expect("mini import runs");

        // (a) No baseline manifest anywhere: first import, green.
        let baseline_root = tmp.path().join("baseline");
        std::fs::create_dir_all(&baseline_root).expect("mk baseline root");
        let gates = gate_results(&baseline_root, &results).expect("gate without baseline");
        assert!(
            matches!(gates[0].1, LibraryGate::NoBaseline { new_len: 6 }),
            "first import must be NoBaseline with the fresh count: {gates:?}"
        );
        assert!(gate_is_green(&gates), "first import gates green");

        // (b) Subset baseline: green, net +5; promotion copies the fresh
        // manifest + shard over the baseline dir.
        write_baseline_manifest(&baseline_root, "goodlib", &["refl_n"]);
        let gates = gate_results(&baseline_root, &results).expect("gate against subset");
        match &gates[0].1 {
            LibraryGate::Diffed(d) => {
                assert!(d.is_green(), "superset import must be green");
                assert_eq!((d.baseline_len, d.new_len, d.net()), (1, 6, 5));
            }
            other => panic!("expected a diffed gate, got {other:?}"),
        }
        let promoted = promote_if_green(&gates, &out, &baseline_root, &results)
            .expect("green promote succeeds")
            .expect("green gate must promote");
        assert_eq!(promoted.len(), 1, "exactly the one library promotes");
        let (lib, files) = &promoted[0];
        assert_eq!(lib, "goodlib");
        assert!(
            files.iter().any(|f| f == "kernel-verified.json"),
            "manifest must be promoted: {files:?}"
        );
        assert!(
            files.iter().any(|f| f.ends_with(".mathverse")),
            "shard must be promoted: {files:?}"
        );
        // The promoted baseline now equals the fresh manifest: net +0 green.
        let regates = gate_results(&baseline_root, &results).expect("re-gate after promote");
        match &regates[0].1 {
            LibraryGate::Diffed(d) => {
                assert!(d.is_green());
                assert_eq!(d.net(), 0, "promoted baseline re-gates at net +0");
            }
            other => panic!("expected a diffed gate after promote, got {other:?}"),
        }

        // (c) Baseline claims a name the fresh import lacks: RED, listed,
        // and a red gate promotes NOTHING.
        write_baseline_manifest(&baseline_root, "goodlib", &["refl_n", "ghost_theorem"]);
        let gates = gate_results(&baseline_root, &results).expect("gate against ghost");
        match &gates[0].1 {
            LibraryGate::Diffed(d) => {
                assert_eq!(d.regressed, vec!["ghost_theorem".to_string()]);
            }
            other => panic!("expected a diffed gate, got {other:?}"),
        }
        assert!(!gate_is_green(&gates), "a regression must redden the gate");
        let red = promote_if_green(&gates, &out, &baseline_root, &results)
            .expect("red promote check itself succeeds");
        assert!(red.is_none(), "a red gate must promote nothing");
        let untouched =
            KernelVerifiedManifest::from_file(&baseline_root.join("goodlib/kernel-verified.json"))
                .expect("baseline manifest still readable");
        assert!(
            untouched
                .kernel_verified_names
                .contains(&"ghost_theorem".to_string()),
            "red gate must leave the baseline manifest untouched"
        );
    }

    /// Inductive/constructor family-certificate entries are exempt from the
    /// floor (their import-time tag marks the checked add_inductive replay
    /// lane), so a freshly converted good library passes.
    #[test]
    fn test_soundness_floor_exempts_inductive_family_entries() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sexp_dir = tmp.path().join("sexp/goodlib");
        let out_lib = tmp.path().join("out/goodlib");
        std::fs::create_dir_all(&sexp_dir).expect("mk sexp dir");
        std::fs::write(sexp_dir.join("Mod.sexp"), GOOD_LIBRARY_SEXP).expect("write fixture");

        let outcome = run_coq_import_library(
            "goodlib",
            &sexp_dir,
            &out_lib,
            &CoqImportOptions {
                lean_faithful: false,
                stamp: false,
            },
        )
        .expect("fresh import-time inductive tags must pass the floor");
        assert!(outcome.verified.is_some());
        assert_eq!(
            outcome.stored_kernel_verified_after, None,
            "--no-stamp skips the stamp step"
        );
    }
}
