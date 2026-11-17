// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KV-guardrail CLI commands: the `ratchet`, `elision-gate`, and `fingerprint`
//! verbs under `clean mathverse`.
//!
//! These three are PURE READS of already-produced JSON artifacts plus
//! set/integer comparison and printing — they consolidate two standalone Python
//! guardrails (`scripts/check_kv_ratchet.py`, `scripts/check_kv_elision_subset.py`)
//! into first-class subcommands. None of them touch the kernel, the stamp
//! pipeline, or any `.mathverse` byte, so they cannot raise or lower a
//! `KernelVerified` verdict; they can only turn the local gate RED (fail-closed)
//! on a detected regression, soundness-floor breach, dropped constant, or
//! missing fingerprint.
//!
//! * `ratchet check|update` — monotonic-UP ratchet over a saved `stamp-verified
//!   --json` summary, split by P6 into a development `accepted` baseline and a
//!   reference-stamp baseline (unarmed until the reference producer lands: a
//!   development run must then stamp 0), re-asserting the
//!   `heuristic_kernel_verified == 0` soundness floor on BOTH verbs.
//! * `elision-gate` — fails if the statically-sound `--closure-elide opaque`
//!   run accepted a constant the `opaque-and-theorem` run dropped (eliding may
//!   only ADD acceptances, never drop one). Both manifests must name the same
//!   checker but for exactly that elision.
//! * `fingerprint` — prints a manifest's identity record (theory, checker,
//!   tier).
//!
//! [`StampEnvFingerprint`]: crate::verify::kernel_verified_manifest::StampEnvFingerprint

use std::collections::BTreeSet;
use std::io::{self, Write};

use serde::{Deserialize, Serialize};

use crate::cli::{
    ElisionGateArgs, FingerprintArgs, MathverseCliError, RatchetCheckArgs, RatchetUpdateArgs,
};
use crate::verify::kernel_verified_manifest::{Elision, KernelVerifiedManifest, ManifestError};

/// Default baseline notes written by `ratchet update` when the existing ratchet
/// file carries none. Mirrors `check_kv_ratchet.py`'s `BASELINE_NOTES`.
const BASELINE_NOTES: &str = "Monotonic-UP floor for `clean mathverse stamp-verified` development \
     `accepted` counts. Operator raises it from a real corpus stamp via \
     `clean mathverse ratchet update`.";

/// The fields the ratchet reads from a saved `stamp-verified --json` summary.
///
/// Deliberately a SMALL purpose-built struct rather than the full (private,
/// Serialize-only) `StampVerifiedSummary`: serde ignores unknown fields, so this
/// reads exactly the counts the gate needs. `Option` distinguishes a MISSING
/// field (fail-closed `MalformedSummary`) from a present `0`; a pre-P6 summary
/// (`kernel_verified`, no `tier`) is therefore refused, never read as 0.
///
/// `i64` (not `u64`) means a JSON `true` deserializes as an ERROR rather than
/// `1`, preserving the Python "bool is not int" fail-closed parity.
#[derive(Debug, Deserialize)]
struct RatchetCounts {
    #[serde(default)]
    heuristic_kernel_verified: Option<i64>,
    tier: Option<String>,
    accepted: Option<i64>,
    stored_reference_stamped: Option<i64>,
}

/// The counts [`load_counts`] returns.
#[derive(Debug, Clone, Copy)]
struct Counts {
    accepted: i64,
    stored_reference_stamped: i64,
}

/// On-disk ratchet baseline file (`data/mathlib_kv_ratchet.json`), schema
/// split by P6 (docs/DECISIONS.md, 2026-11-16): the development `accepted`
/// baseline keeps the measured count, and the reference-stamp baseline starts
/// unarmed (`null`) because no producer in this build stamps a header. Unknown
/// fields are refused, so a pre-P6 file (`kernel_verified_baseline`) is an
/// error rather than an all-zero floor.
#[derive(Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RatchetBaseline {
    last_updated: String,
    development_accepted_baseline: i64,
    reference_stamped_baseline: Option<i64>,
    notes: String,
}

/// Machine-readable summary for `ratchet check`, emitted with `--json`.
#[derive(Debug, Serialize)]
struct RatchetCheckSummary {
    ok: bool,
    generated_by: &'static str,
    skipped: bool,
    reason: Option<String>,
    accepted: Option<i64>,
    stored_reference_stamped: Option<i64>,
    development_accepted_baseline: Option<i64>,
    reference_stamped_baseline: Option<i64>,
    violations: Vec<String>,
}

/// Machine-readable summary for `ratchet update`, emitted with `--json`.
#[derive(Debug, Serialize)]
struct RatchetUpdateSummary {
    ok: bool,
    generated_by: &'static str,
    ratchet: String,
    development_accepted_baseline: i64,
    reference_stamped_baseline: Option<i64>,
}

/// Machine-readable summary for `elision-gate`, emitted with `--json`.
#[derive(Debug, Serialize)]
struct ElisionGateSummary {
    ok: bool,
    generated_by: &'static str,
    opaque_count: usize,
    opaque_and_theorem_count: usize,
    gained: usize,
    dropped: Vec<String>,
}

/// Uniform machine-readable error envelope emitted to stdout on ANY failure
/// path of a `--json` invocation (floor breach, malformed summary, regression,
/// dropped constants, missing manifest/file, missing fingerprint). The typed
/// `MathverseCliError`'s `Display` carries the per-violation / per-name detail,
/// so this single shape covers every failure uniformly. The same `Err` is then
/// propagated so the process still exits nonzero.
#[derive(Debug, Serialize)]
struct JsonErrorSummary {
    ok: bool,
    generated_by: &'static str,
    error: String,
}

/// Serialize a `--json` summary and write it (pretty) to stdout.
fn emit_json<T: Serialize>(summary: &T) -> Result<(), MathverseCliError> {
    let rendered = serde_json::to_string_pretty(summary)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    writeln!(out, "{rendered}")?;
    Ok(())
}

/// Emit the uniform `ok:false` error envelope for `--json` failures, then return
/// the original error. Centralizes the "print JSON report THEN return Err"
/// contract (matching `cmd_mathverse.rs`'s download gate) across every cmd_*.
fn json_fail(generated_by: &'static str, err: MathverseCliError) -> MathverseCliError {
    let summary = JsonErrorSummary {
        ok: false,
        generated_by,
        error: err.to_string(),
    };
    // Best-effort: if serialization or the write itself fails, still surface the
    // ORIGINAL typed error (the more informative one) rather than masking it.
    if let Ok(rendered) = serde_json::to_string_pretty(&summary) {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        let _ = writeln!(out, "{rendered}");
    }
    err
}

/// Shared floor + extract used by BOTH `check` and `update`, so neither can
/// ratchet (or pass) a floor-breaching or malformed summary. Mirrors
/// `_load_current` in `check_kv_ratchet.py`.
///
/// Reads `summary_path`, enforces `heuristic_kernel_verified == 0` and
/// `tier == "development"`, and returns the counts. Fail-closed: a
/// missing/non-int field is a `MalformedSummary`, a nonzero floor is a
/// `SoundnessFloor`.
fn load_counts(summary_path: &std::path::Path) -> Result<Counts, MathverseCliError> {
    let data = std::fs::read_to_string(summary_path)?;
    let counts: RatchetCounts = serde_json::from_str(&data).map_err(|e| {
        MathverseCliError::RatchetMalformedSummary(format!("{}: {e}", summary_path.display()))
    })?;

    let heuristic = counts.heuristic_kernel_verified.unwrap_or(0);
    if heuristic != 0 {
        // Heuristic count is always non-negative in practice; clamp to u32 for
        // the typed error message without panicking on a hostile value.
        let breach = u32::try_from(heuristic).unwrap_or(u32::MAX);
        return Err(MathverseCliError::RatchetSoundnessFloor(breach));
    }
    let malformed = |what: &str| {
        MathverseCliError::RatchetMalformedSummary(format!("{}: {what}", summary_path.display()))
    };
    if counts.tier.as_deref() != Some("development") {
        return Err(malformed(
            "`tier` is not \"development\" (a summary written before P6 names no tier)",
        ));
    }
    Ok(Counts {
        accepted: counts
            .accepted
            .ok_or_else(|| malformed("missing integer field `accepted`"))?,
        stored_reference_stamped: counts
            .stored_reference_stamped
            .ok_or_else(|| malformed("missing integer field `stored_reference_stamped`"))?,
    })
}

/// Read the on-disk ratchet baseline. An ABSENT file is the all-zero identity
/// floor, unarmed reference stamp (green on any honest summary). A PRESENT file
/// must parse under the P6 schema: anything else is refused, because a
/// renamed field read through a default would be a vacuous floor.
fn read_baseline(ratchet_path: &std::path::Path) -> Result<RatchetBaseline, MathverseCliError> {
    if !ratchet_path.exists() {
        return Ok(RatchetBaseline::default());
    }
    let data = std::fs::read_to_string(ratchet_path)?;
    serde_json::from_str(&data).map_err(|e| {
        MathverseCliError::RatchetMalformedBaseline(format!("{}: {e}", ratchet_path.display()))
    })
}

/// The violations of `counts` against `baseline`.
fn ratchet_violations(counts: Counts, baseline: &RatchetBaseline) -> Vec<String> {
    let mut violations = Vec::new();
    if counts.accepted < baseline.development_accepted_baseline {
        violations.push(format!(
            "accepted: {} < baseline {} (development accepted count regressed)",
            counts.accepted, baseline.development_accepted_baseline
        ));
    }
    match baseline.reference_stamped_baseline {
        None if counts.stored_reference_stamped != 0 => violations.push(format!(
            "stored_reference_stamped: {} with no reference producer (P6): a development \
             run must leave every shard header as the converter wrote it",
            counts.stored_reference_stamped
        )),
        Some(floor) if counts.stored_reference_stamped < floor => violations.push(format!(
            "stored_reference_stamped: {} < baseline {floor} (reference stamp count regressed)",
            counts.stored_reference_stamped
        )),
        _ => {}
    }
    violations
}

/// `clean mathverse ratchet check`.
///
/// SKIP-green when the summary is absent (preserves the dev workflow: pushes
/// stay green until an operator stamps the real corpus). Otherwise enforces the
/// soundness floor and monotonic-UP ratchet, failing closed on any regression
/// or malformed summary or baseline.
pub(crate) fn cmd_ratchet_check(args: RatchetCheckArgs) -> Result<(), MathverseCliError> {
    const GENERATED_BY: &str = "clean mathverse ratchet check";

    // SKIP-green: an absent summary is exit 0 (the dev-workflow contract), NOT a
    // failure — so it is handled here, never routed through `json_fail`.
    if !args.summary.exists() {
        let reason = format!(
            "no stamp summary at {} — KV ratchet inert until an operator stamps \
             the real corpus (see {})",
            args.summary.display(),
            args.ratchet.display()
        );
        if args.json {
            emit_json(&RatchetCheckSummary {
                ok: true,
                generated_by: GENERATED_BY,
                skipped: true,
                reason: Some(reason),
                accepted: None,
                stored_reference_stamped: None,
                development_accepted_baseline: None,
                reference_stamped_baseline: None,
                violations: Vec::new(),
            })?;
        } else {
            println!("SKIP: {reason}.");
        }
        return Ok(());
    }

    // Soundness floor + extract; on a `--json` failure (floor breach / malformed
    // summary or baseline) emit the uniform `ok:false` envelope before
    // propagating.
    let loaded = load_counts(&args.summary).and_then(|c| Ok((c, read_baseline(&args.ratchet)?)));
    let (counts, baseline) = match loaded {
        Ok(pair) => pair,
        Err(err) if args.json => return Err(json_fail(GENERATED_BY, err)),
        Err(err) => return Err(err),
    };
    let violations = ratchet_violations(counts, &baseline);
    if args.json {
        // The violation branch keeps the RICHER summary (counts + baselines +
        // per-violation list), a superset of the uniform envelope.
        emit_json(&RatchetCheckSummary {
            ok: violations.is_empty(),
            generated_by: GENERATED_BY,
            skipped: false,
            reason: None,
            accepted: Some(counts.accepted),
            stored_reference_stamped: Some(counts.stored_reference_stamped),
            development_accepted_baseline: Some(baseline.development_accepted_baseline),
            reference_stamped_baseline: baseline.reference_stamped_baseline,
            violations: violations.clone(),
        })?;
    }
    if !violations.is_empty() {
        return Err(MathverseCliError::RatchetRegressed(violations));
    }
    if !args.json {
        println!(
            "OK: accepted={} (development) >= baseline {}; stored_reference_stamped={} \
             (reference baseline {}); soundness floor 0.",
            counts.accepted,
            baseline.development_accepted_baseline,
            counts.stored_reference_stamped,
            baseline
                .reference_stamped_baseline
                .map_or_else(|| "unarmed".to_string(), |b| b.to_string()),
        );
    }
    Ok(())
}

/// `clean mathverse ratchet update`.
///
/// Unlike `check`, FAILS (not SKIPs) when the summary is absent. Enforces the
/// SAME soundness floor via [`load_counts`] so a floor-breaching summary can
/// never be ratcheted, then rewrites the baseline JSON preserving any existing
/// operator `notes`. `last_updated` is stored DATE-ONLY for stable diffs.
pub(crate) fn cmd_ratchet_update(args: RatchetUpdateArgs) -> Result<(), MathverseCliError> {
    if !args.summary.exists() {
        return Err(MathverseCliError::RatchetUpdateNoSummary(args.summary));
    }

    let counts = load_counts(&args.summary)?;

    // Preserve the operator's prose `notes` if the existing ratchet file
    // carries a non-empty one; else use the default. The reference-stamp
    // baseline is carried over: no development summary can arm it, and while
    // it is unarmed a summary that stamped anything is refused.
    let existing = read_baseline(&args.ratchet)?;
    if existing.reference_stamped_baseline.is_none() && counts.stored_reference_stamped != 0 {
        return Err(MathverseCliError::RatchetRegressed(ratchet_violations(
            counts, &existing,
        )));
    }
    let notes = if existing.notes.trim().is_empty() {
        BASELINE_NOTES.to_owned()
    } else {
        existing.notes
    };

    // Date-only (first 10 chars `YYYY-MM-DD`) of the ISO-8601 timestamp, so the
    // ratchet diffs only when the counts move, not on every run.
    let last_updated = crate::release::now_iso8601()
        .chars()
        .take(10)
        .collect::<String>();

    let updated = RatchetBaseline {
        last_updated,
        development_accepted_baseline: counts.accepted,
        reference_stamped_baseline: existing.reference_stamped_baseline,
        notes,
    };
    let json = serde_json::to_string_pretty(&updated)?;
    std::fs::write(&args.ratchet, format!("{json}\n"))?;

    if args.json {
        let summary = RatchetUpdateSummary {
            ok: true,
            generated_by: "clean mathverse ratchet update",
            ratchet: args.ratchet.display().to_string(),
            development_accepted_baseline: updated.development_accepted_baseline,
            reference_stamped_baseline: updated.reference_stamped_baseline,
        };
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        println!(
            "Wrote {}: development_accepted_baseline={}.",
            args.ratchet.display(),
            updated.development_accepted_baseline
        );
    }
    Ok(())
}

/// `clean mathverse elision-gate <opaque> <opaque-and-theorem>`.
///
/// Fails (naming the offenders) if any constant the statically-sound `opaque`
/// run accepted is missing from the `opaque-and-theorem` run. Eliding theorem
/// values may only ADD acceptances, never drop one. Fail-closed on a
/// missing/bad/malformed manifest via `from_file`'s typed error, and on two
/// manifests that are not the same checker but for exactly that elision (P6:
/// a subset across two checkers or two theories says nothing about elision).
pub(crate) fn cmd_elision_gate(args: ElisionGateArgs) -> Result<(), MathverseCliError> {
    let opaque = KernelVerifiedManifest::from_file(&args.opaque_manifest)?;
    let oat = KernelVerifiedManifest::from_file(&args.opaque_and_theorem_manifest)?;
    let elisions = (
        opaque.identity().settings().elision,
        oat.identity().settings().elision,
    );
    if elisions != (Elision::Opaque, Elision::OpaqueAndTheorem) {
        return Err(ManifestError::IdentityMismatch(format!(
            "the elision gate compares an `opaque` run with an `opaque-and-theorem` run; \
             got {:?} and {:?}",
            elisions.0, elisions.1
        ))
        .into());
    }
    opaque.identity().same_checker_but_elision(oat.identity())?;

    let opaque_names: BTreeSet<String> = opaque.accepted_names().iter().cloned().collect();
    let oat_names: BTreeSet<String> = oat.accepted_names().iter().cloned().collect();

    let dropped: Vec<String> = opaque_names.difference(&oat_names).cloned().collect();

    if !dropped.is_empty() {
        if args.json {
            let summary = ElisionGateSummary {
                ok: false,
                generated_by: "clean mathverse elision-gate",
                opaque_count: opaque_names.len(),
                opaque_and_theorem_count: oat_names.len(),
                gained: oat_names.difference(&opaque_names).count(),
                dropped: dropped.clone(),
            };
            let stdout = io::stdout();
            let mut out = stdout.lock();
            writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
        }
        return Err(MathverseCliError::ElisionDropped(dropped));
    }

    let gained = oat_names.difference(&opaque_names).count();
    if args.json {
        let summary = ElisionGateSummary {
            ok: true,
            generated_by: "clean mathverse elision-gate",
            opaque_count: opaque_names.len(),
            opaque_and_theorem_count: oat_names.len(),
            gained,
            dropped: Vec::new(),
        };
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        println!(
            "OK: accepted(opaque)={} subset-of accepted(opaque-and-theorem)={} \
             (+{gained} gained by eliding theorem values; development tier).",
            opaque_names.len(),
            oat_names.len()
        );
    }
    Ok(())
}

/// `clean mathverse fingerprint <manifest>`.
///
/// Prints the manifest's identity record: the theory (profile and measured
/// base), the checker (entry, discipline, imports, settings, build) and the
/// tier. Every manifest this build reads carries one (an identity-less file is
/// refused by `from_file`), so the absence of an identity is an error, never
/// an empty print.
pub(crate) fn cmd_fingerprint(args: FingerprintArgs) -> Result<(), MathverseCliError> {
    let manifest = KernelVerifiedManifest::from_file(&args.manifest)?;
    let identity = manifest.identity();
    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(identity)?)?;
    } else {
        let build = identity.build();
        println!("tier: {}", identity.tier().as_str());
        println!("entry: {}", identity.entry().as_str());
        println!("discipline: {}", identity.discipline().as_str());
        println!("imports: {:?}", identity.imports());
        println!("settings: {:?}", identity.settings());
        println!("theory: {:?}", identity.theory());
        println!("kernel_version: {}", build.kernel_version());
        println!("toolchain: {}", build.toolchain());
        println!("exe_sha256: {}", build.exe().sha256());
    }
    Ok(())
}

#[cfg(test)]
#[path = "kv_guardrail_dispatch_tests.rs"]
mod tests;
