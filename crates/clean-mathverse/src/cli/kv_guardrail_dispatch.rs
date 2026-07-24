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
//!   --json` summary's KernelVerified counts, re-asserting the
//!   `heuristic_kernel_verified == 0` soundness floor on BOTH verbs.
//! * `elision-gate` — fails if the statically-sound `--closure-elide opaque`
//!   floor verified a constant the `opaque-and-theorem` run dropped (eliding may
//!   only ADD KernelVerified, never drop one).
//! * `fingerprint` — prints the recorded [`StampEnvFingerprint`] from a manifest.

use std::collections::BTreeSet;
use std::io::{self, Write};

use serde::{Deserialize, Serialize};

use crate::cli::{
    ElisionGateArgs, FingerprintArgs, MathverseCliError, RatchetCheckArgs, RatchetUpdateArgs,
};
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

/// Default baseline notes written by `ratchet update` when the existing ratchet
/// file carries none. Mirrors `check_kv_ratchet.py`'s `BASELINE_NOTES`.
const BASELINE_NOTES: &str =
    "Monotonic-UP floor for `clean mathverse stamp-verified` KernelVerified \
     counts. Operator raises it from a real corpus stamp via \
     `clean mathverse ratchet update`.";

/// The three integer fields the ratchet reads from a saved `stamp-verified
/// --json` summary.
///
/// Deliberately a SMALL purpose-built struct rather than the full (private,
/// Serialize-only) `StampVerifiedSummary`: serde ignores unknown fields, so this
/// reads exactly the three counts the gate needs without coupling to the rest of
/// the summary schema or its `&'static str` fields (which cannot derive
/// `Deserialize`). `Option` distinguishes a MISSING field (fail-closed
/// `MalformedSummary`) from a present `0`.
///
/// `i64` (not `u64`) means a JSON `true` deserializes as an ERROR rather than
/// `1`, preserving the Python "bool is not int" fail-closed parity.
#[derive(Debug, Deserialize)]
struct RatchetCounts {
    #[serde(default)]
    heuristic_kernel_verified: Option<i64>,
    kernel_verified: Option<i64>,
    stored_kernel_verified: Option<i64>,
}

/// On-disk ratchet baseline file (`data/mathlib_kv_ratchet.json`). Owned by this
/// tool: `check` reads it, `update` rewrites it.
#[derive(Debug, Default, Serialize, Deserialize)]
struct RatchetBaseline {
    #[serde(default)]
    last_updated: String,
    #[serde(default)]
    kernel_verified_baseline: i64,
    #[serde(default)]
    stored_kernel_verified_baseline: i64,
    #[serde(default)]
    notes: String,
}

/// Machine-readable summary for `ratchet check`, emitted with `--json`.
#[derive(Debug, Serialize)]
struct RatchetCheckSummary {
    ok: bool,
    generated_by: &'static str,
    skipped: bool,
    reason: Option<String>,
    kernel_verified: Option<i64>,
    stored_kernel_verified: Option<i64>,
    kernel_verified_baseline: Option<i64>,
    stored_kernel_verified_baseline: Option<i64>,
    violations: Vec<String>,
}

/// Machine-readable summary for `ratchet update`, emitted with `--json`.
#[derive(Debug, Serialize)]
struct RatchetUpdateSummary {
    ok: bool,
    generated_by: &'static str,
    ratchet: String,
    kernel_verified_baseline: i64,
    stored_kernel_verified_baseline: i64,
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
/// Reads `summary_path`, enforces `heuristic_kernel_verified == 0`, and returns
/// `(kernel_verified, stored_kernel_verified)`. Fail-closed: a missing/non-int
/// field is a `MalformedSummary`, a nonzero floor is a `SoundnessFloor`.
fn load_counts(summary_path: &std::path::Path) -> Result<(i64, i64), MathverseCliError> {
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

    let kernel_verified = counts.kernel_verified.ok_or_else(|| {
        MathverseCliError::RatchetMalformedSummary(format!(
            "{}: missing integer field `kernel_verified`",
            summary_path.display()
        ))
    })?;
    let stored_kernel_verified = counts.stored_kernel_verified.ok_or_else(|| {
        MathverseCliError::RatchetMalformedSummary(format!(
            "{}: missing integer field `stored_kernel_verified`",
            summary_path.display()
        ))
    })?;

    Ok((kernel_verified, stored_kernel_verified))
}

/// Read the on-disk ratchet baseline, defaulting to an all-zero identity floor
/// when the file is absent or unparsable (mirrors the Python's tolerant load:
/// missing baselines default to 0, which is always green).
fn read_baseline(ratchet_path: &std::path::Path) -> RatchetBaseline {
    std::fs::read_to_string(ratchet_path)
        .ok()
        .and_then(|data| serde_json::from_str(&data).ok())
        .unwrap_or_default()
}

/// `clean mathverse ratchet check`.
///
/// SKIP-green when the summary is absent (preserves the dev workflow: pushes
/// stay green until an operator stamps the real corpus). Otherwise enforces the
/// soundness floor and monotonic-UP ratchet, failing closed on any regression
/// or malformed summary.
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
                kernel_verified: None,
                stored_kernel_verified: None,
                kernel_verified_baseline: None,
                stored_kernel_verified_baseline: None,
                violations: Vec::new(),
            })?;
        } else {
            println!("SKIP: {reason}.");
        }
        return Ok(());
    }

    // Soundness floor + extract; on a `--json` failure (floor breach / malformed
    // summary) emit the uniform `ok:false` envelope to stdout before propagating.
    let (kernel_verified, stored_kernel_verified) = match load_counts(&args.summary) {
        Ok(counts) => counts,
        Err(err) if args.json => return Err(json_fail(GENERATED_BY, err)),
        Err(err) => return Err(err),
    };
    let baseline = read_baseline(&args.ratchet);

    let mut violations = Vec::new();
    if kernel_verified < baseline.kernel_verified_baseline {
        violations.push(format!(
            "kernel_verified: {kernel_verified} < baseline {} (KernelVerified count regressed)",
            baseline.kernel_verified_baseline
        ));
    }
    if stored_kernel_verified < baseline.stored_kernel_verified_baseline {
        violations.push(format!(
            "stored_kernel_verified: {stored_kernel_verified} < baseline {} \
             (KernelVerified count regressed)",
            baseline.stored_kernel_verified_baseline
        ));
    }

    if !violations.is_empty() {
        if args.json {
            // Computed-violation branch keeps the RICHER summary (counts +
            // baselines + per-violation list) — a superset of the uniform
            // envelope — then returns the typed Err.
            emit_json(&RatchetCheckSummary {
                ok: false,
                generated_by: GENERATED_BY,
                skipped: false,
                reason: None,
                kernel_verified: Some(kernel_verified),
                stored_kernel_verified: Some(stored_kernel_verified),
                kernel_verified_baseline: Some(baseline.kernel_verified_baseline),
                stored_kernel_verified_baseline: Some(baseline.stored_kernel_verified_baseline),
                violations: violations.clone(),
            })?;
        }
        return Err(MathverseCliError::RatchetRegressed(violations));
    }

    if args.json {
        emit_json(&RatchetCheckSummary {
            ok: true,
            generated_by: GENERATED_BY,
            skipped: false,
            reason: None,
            kernel_verified: Some(kernel_verified),
            stored_kernel_verified: Some(stored_kernel_verified),
            kernel_verified_baseline: Some(baseline.kernel_verified_baseline),
            stored_kernel_verified_baseline: Some(baseline.stored_kernel_verified_baseline),
            violations: Vec::new(),
        })?;
    } else {
        println!(
            "OK: kernel_verified={kernel_verified} stored_kernel_verified={stored_kernel_verified} \
             >= ratcheted baselines; soundness floor 0."
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

    let (kernel_verified, stored_kernel_verified) = load_counts(&args.summary)?;

    // Preserve the operator's prose `notes` if the existing ratchet file parses
    // and carries a non-empty one; else use the default.
    let existing = read_baseline(&args.ratchet);
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
        kernel_verified_baseline: kernel_verified,
        stored_kernel_verified_baseline: stored_kernel_verified,
        notes,
    };
    let json = serde_json::to_string_pretty(&updated)?;
    std::fs::write(&args.ratchet, format!("{json}\n"))?;

    if args.json {
        let summary = RatchetUpdateSummary {
            ok: true,
            generated_by: "clean mathverse ratchet update",
            ratchet: args.ratchet.display().to_string(),
            kernel_verified_baseline: kernel_verified,
            stored_kernel_verified_baseline: stored_kernel_verified,
        };
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        println!(
            "Wrote {}: kernel_verified_baseline={kernel_verified} \
             stored_kernel_verified_baseline={stored_kernel_verified}.",
            args.ratchet.display()
        );
    }
    Ok(())
}

/// `clean mathverse elision-gate <opaque> <opaque-and-theorem>`.
///
/// Fails (naming the offenders) if any constant the statically-sound `opaque`
/// floor kernel-verified is missing from the `opaque-and-theorem` run. Eliding
/// theorem values may only ADD KernelVerified, never drop one. Fail-closed on a
/// missing/bad/malformed manifest via `from_file`'s typed error.
pub(crate) fn cmd_elision_gate(args: ElisionGateArgs) -> Result<(), MathverseCliError> {
    let opaque = KernelVerifiedManifest::from_file(&args.opaque_manifest)?;
    let oat = KernelVerifiedManifest::from_file(&args.opaque_and_theorem_manifest)?;

    let opaque_names: BTreeSet<String> = opaque.kernel_verified_names.iter().cloned().collect();
    let oat_names: BTreeSet<String> = oat.kernel_verified_names.iter().cloned().collect();

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
            "OK: KV(opaque)={} subset-of KV(opaque-and-theorem)={} \
             (+{gained} gained by eliding theorem values).",
            opaque_names.len(),
            oat_names.len()
        );
    }
    Ok(())
}

/// `clean mathverse fingerprint <manifest>`.
///
/// Prints the recorded reproducibility [`StampEnvFingerprint`]. Fails when the
/// manifest carries none (a legacy manifest written before the field existed),
/// so the absence is visible rather than silently printing nothing.
pub(crate) fn cmd_fingerprint(args: FingerprintArgs) -> Result<(), MathverseCliError> {
    let manifest = KernelVerifiedManifest::from_file(&args.manifest)?;
    match manifest.env_fingerprint {
        Some(fp) => {
            if args.json {
                let stdout = io::stdout();
                let mut out = stdout.lock();
                writeln!(out, "{}", serde_json::to_string_pretty(&fp)?)?;
            } else {
                println!("kernel_version: {}", fp.kernel_version);
                println!("toolchain: {}", fp.toolchain);
                println!("heartbeat: {}", fp.heartbeat);
                println!("elision_policy: {}", fp.elision_policy);
                println!("max_closure_modules: {}", fp.max_closure_modules);
                println!("prelude_variant: {}", fp.prelude_variant);
            }
            Ok(())
        }
        None => Err(MathverseCliError::MissingEnvFingerprint(args.manifest)),
    }
}

#[cfg(test)]
#[path = "kv_guardrail_dispatch_tests.rs"]
mod tests;
