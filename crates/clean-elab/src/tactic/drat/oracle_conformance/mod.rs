// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT oracle-conformance gate.
//!
//! Differential testing of clean's native LRAT verifiers against an external
//! oracle (`ay-lrat-check` or `cake_lpr`) on a maintained proof corpus.
//!
//! This module owns: corpus definition, temporary DIMACS/LRAT materialization,
//! external-process invocation, result normalization, and report rendering.
//!
//! Design: `designs/2026-03-14-936-lrat-oracle-conformance-gate.md`

mod corpus;
mod report;

use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::lrat_verifier::{LratCheckpoint, LratVerifier};
use super::streaming::StreamingLratVerifier;
use super::types::{CnfFormula, LratProof, StepResult};

pub use corpus::{build_corpus, render_dimacs, render_lrat};
pub use report::render_report;

// ============================================================================
// Oracle types
// ============================================================================

/// Kind of external oracle checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleKind {
    AyLratCheck,
    CakeLpr,
}

impl fmt::Display for OracleKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OracleKind::AyLratCheck => write!(f, "ay-lrat-check"),
            OracleKind::CakeLpr => write!(f, "cake_lpr"),
        }
    }
}

/// Outcome of an external oracle invocation on a single case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleOutcome {
    Accepted,
    Rejected,
    InvocationError { exit_code: Option<i32> },
}

/// Full verdict from an oracle invocation including captured output.
#[derive(Debug, Clone)]
pub struct OracleVerdict {
    pub outcome: OracleOutcome,
    pub stdout: String,
    pub stderr: String,
}

/// Classification of a corpus case comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseClassification {
    AllAgree,
    InternalDisagreement,
    OracleMismatch,
    OracleInvocationError,
    OracleUnavailable,
}

impl fmt::Display for CaseClassification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CaseClassification::AllAgree => write!(f, "AllAgree"),
            CaseClassification::InternalDisagreement => write!(f, "InternalDisagreement"),
            CaseClassification::OracleMismatch => write!(f, "OracleMismatch"),
            CaseClassification::OracleInvocationError => write!(f, "OracleInvocationError"),
            CaseClassification::OracleUnavailable => write!(f, "OracleUnavailable"),
        }
    }
}

/// A single test case in the LRAT conformance corpus.
pub struct LratCorpusCase {
    pub name: &'static str,
    pub formula: CnfFormula,
    pub proof: LratProof,
    /// Expected verdict from the internal verifiers (true = accept/UNSAT).
    pub expected_internal: bool,
}

/// Result of running all verifiers on a single corpus case.
pub struct CaseResult {
    pub name: &'static str,
    pub expected: bool,
    pub batch_verdict: bool,
    pub streaming_verdict: bool,
    pub checkpoint_verdict: bool,
    pub oracle_verdicts: Vec<(OracleKind, OracleVerdict)>,
    pub classification: CaseClassification,
}

/// Discovered oracle executable.
pub struct ResolvedOracle {
    pub kind: OracleKind,
    pub path: PathBuf,
}

/// Configuration for the oracle conformance harness.
pub struct HarnessConfig {
    pub oracles: Vec<ResolvedOracle>,
    pub update_report: bool,
    pub report_path: PathBuf,
}

// ============================================================================
// Oracle discovery
// ============================================================================

/// Discover the `ay-lrat-check` executable.
///
/// Search order (design §2, rule 7):
/// 1. Explicit path if provided
/// 2. Sibling ay workspace: `target/{release,debug}`
/// 3. Sibling ay workspace: `target/{worker,prover,researcher,manager}_*/{release,debug}`
///    (newest matching binary wins)
/// 4. `PATH`
pub fn discover_ay_lrat_check(explicit: Option<&Path>) -> Option<ResolvedOracle> {
    if let Some(p) = explicit {
        if p.is_file() {
            return Some(ResolvedOracle {
                kind: OracleKind::AyLratCheck,
                path: p.to_path_buf(),
            });
        }
    }

    let binary_name = "ay-lrat-check";

    if let Some(found) = search_ay_workspace(binary_name) {
        return Some(ResolvedOracle {
            kind: OracleKind::AyLratCheck,
            path: found,
        });
    }

    search_path(binary_name).map(|p| ResolvedOracle {
        kind: OracleKind::AyLratCheck,
        path: p,
    })
}

/// Discover the `cake_lpr` executable.
pub fn discover_cake_lpr(explicit: Option<&Path>) -> Option<ResolvedOracle> {
    if let Some(p) = explicit {
        if p.is_file() {
            return Some(ResolvedOracle {
                kind: OracleKind::CakeLpr,
                path: p.to_path_buf(),
            });
        }
    }

    search_path("cake_lpr").map(|p| ResolvedOracle {
        kind: OracleKind::CakeLpr,
        path: p,
    })
}

fn search_ay_workspace(binary_name: &str) -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let ay_target = PathBuf::from(&home).join("ay").join("target");
    if !ay_target.is_dir() {
        return None;
    }

    // Prefer release over debug in standard target dirs
    for profile in &["release", "debug"] {
        let candidate = ay_target.join(profile).join(binary_name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    // Search worker/prover/researcher/manager target dirs, choose newest
    let entries = std::fs::read_dir(&ay_target).ok()?;
    let prefixes = ["worker_", "prover_", "researcher_", "manager_"];
    let mut candidates: Vec<PathBuf> = Vec::new();

    for entry in entries.flatten() {
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if prefixes.iter().any(|p| name_str.starts_with(p)) {
            for profile in &["release", "debug"] {
                let candidate = entry.path().join(profile).join(binary_name);
                if candidate.is_file() {
                    candidates.push(candidate);
                }
            }
        }
    }

    if candidates.is_empty() {
        return None;
    }

    candidates.sort_by(|a, b| {
        let ma = a.metadata().and_then(|m| m.modified()).ok();
        let mb = b.metadata().and_then(|m| m.modified()).ok();
        mb.cmp(&ma) // newest first
    });
    Some(candidates.remove(0))
}

fn search_path(binary_name: &str) -> Option<PathBuf> {
    let output = Command::new("which").arg(binary_name).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if path_str.is_empty() {
        return None;
    }
    let path = PathBuf::from(&path_str);
    if path.is_file() {
        Some(path)
    } else {
        None
    }
}

// ============================================================================
// Oracle invocation
// ============================================================================

/// Invoke an oracle on a DIMACS/LRAT file pair.
///
/// Design §2 rule 8: exit 0 = accepted, exit 1 = rejected, other = error.
pub fn invoke_oracle(
    oracle: &ResolvedOracle,
    dimacs_path: &Path,
    lrat_path: &Path,
) -> OracleVerdict {
    let result = Command::new(&oracle.path)
        .arg(dimacs_path)
        .arg(lrat_path)
        .output();

    match result {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let outcome = match output.status.code() {
                Some(0) => OracleOutcome::Accepted,
                Some(1) => OracleOutcome::Rejected,
                code => OracleOutcome::InvocationError { exit_code: code },
            };
            OracleVerdict {
                outcome,
                stdout,
                stderr,
            }
        }
        Err(e) => OracleVerdict {
            outcome: OracleOutcome::InvocationError { exit_code: None },
            stdout: String::new(),
            stderr: format!("Failed to spawn oracle: {}", e),
        },
    }
}

// ============================================================================
// Internal verification helpers
// ============================================================================

fn verify_batch(formula: &CnfFormula, proof: &LratProof) -> bool {
    LratVerifier::verify(formula, proof).unwrap_or(false)
}

fn verify_streaming(formula: &CnfFormula, proof: &LratProof) -> bool {
    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(formula);
    for op in &proof.operations {
        match verifier.process_step(op) {
            Ok(StepResult::Complete) => return true,
            Ok(StepResult::Continue) => {}
            Err(_) => return false,
        }
    }
    verifier.finalize().unwrap_or(false)
}

/// Streaming verification with checkpoint/resume after the first step.
fn verify_streaming_checkpoint(formula: &CnfFormula, proof: &LratProof) -> bool {
    if proof.operations.is_empty() {
        return false;
    }

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(formula);

    match verifier.process_step(&proof.operations[0]) {
        Ok(StepResult::Complete) => return true,
        Ok(StepResult::Continue) => {}
        Err(_) => return false,
    }

    // Checkpoint → serialize → deserialize → resume
    let checkpoint = verifier.checkpoint();
    let bytes = checkpoint.to_bytes();
    let restored = match LratCheckpoint::from_bytes(&bytes) {
        Ok(c) => c,
        Err(_) => return false,
    };
    let mut resumed = StreamingLratVerifier::resume(restored);

    for op in &proof.operations[1..] {
        match resumed.process_step(op) {
            Ok(StepResult::Complete) => return true,
            Ok(StepResult::Continue) => {}
            Err(_) => return false,
        }
    }
    resumed.finalize().unwrap_or(false)
}

// ============================================================================
// Harness runner
// ============================================================================

/// Run the full oracle conformance harness.
///
/// Returns the per-case results and a boolean indicating overall success
/// (true = no mismatches or internal disagreements).
pub fn run_harness(config: &HarnessConfig) -> (Vec<CaseResult>, bool) {
    let corpus = build_corpus();
    let mut results = Vec::new();
    let mut all_pass = true;

    let tmp_dir = std::env::temp_dir().join("clean_lrat_oracle");
    let _ = std::fs::create_dir_all(&tmp_dir);

    for case in &corpus {
        let result = run_single_case(case, &config.oracles, &tmp_dir);
        if result.classification != CaseClassification::AllAgree
            && result.classification != CaseClassification::OracleUnavailable
        {
            all_pass = false;
        }
        results.push(result);
    }

    let _ = std::fs::remove_dir_all(&tmp_dir);
    (results, all_pass)
}

fn run_single_case(
    case: &LratCorpusCase,
    oracles: &[ResolvedOracle],
    tmp_dir: &Path,
) -> CaseResult {
    let batch = verify_batch(&case.formula, &case.proof);
    let streaming = verify_streaming(&case.formula, &case.proof);
    let checkpoint = verify_streaming_checkpoint(&case.formula, &case.proof);

    let oracle_verdicts = run_oracle_checks(case, oracles, tmp_dir);

    let classification = classify(
        case.expected_internal,
        batch,
        streaming,
        checkpoint,
        &oracle_verdicts,
    );

    CaseResult {
        name: case.name,
        expected: case.expected_internal,
        batch_verdict: batch,
        streaming_verdict: streaming,
        checkpoint_verdict: checkpoint,
        oracle_verdicts,
        classification,
    }
}

fn run_oracle_checks(
    case: &LratCorpusCase,
    oracles: &[ResolvedOracle],
    tmp_dir: &Path,
) -> Vec<(OracleKind, OracleVerdict)> {
    let mut verdicts = Vec::new();

    for oracle in oracles {
        let dimacs_path = tmp_dir.join(format!("{}.cnf", case.name));
        let lrat_path = tmp_dir.join(format!("{}.lrat", case.name));

        let dimacs_text = render_dimacs(&case.formula);
        let lrat_text = render_lrat(&case.proof);

        if std::fs::write(&dimacs_path, &dimacs_text).is_ok()
            && std::fs::write(&lrat_path, &lrat_text).is_ok()
        {
            verdicts.push((oracle.kind, invoke_oracle(oracle, &dimacs_path, &lrat_path)));
        } else {
            verdicts.push((
                oracle.kind,
                OracleVerdict {
                    outcome: OracleOutcome::InvocationError { exit_code: None },
                    stdout: String::new(),
                    stderr: "Failed to write temporary files".to_string(),
                },
            ));
        }
    }

    verdicts
}

fn classify(
    expected: bool,
    batch: bool,
    streaming: bool,
    checkpoint: bool,
    oracle_verdicts: &[(OracleKind, OracleVerdict)],
) -> CaseClassification {
    if batch != streaming || batch != checkpoint || batch != expected {
        return CaseClassification::InternalDisagreement;
    }

    if oracle_verdicts.is_empty() {
        return CaseClassification::OracleUnavailable;
    }

    for (_, verdict) in oracle_verdicts {
        match &verdict.outcome {
            OracleOutcome::InvocationError { .. } => {
                return CaseClassification::OracleInvocationError;
            }
            OracleOutcome::Accepted if !expected => return CaseClassification::OracleMismatch,
            OracleOutcome::Rejected if expected => return CaseClassification::OracleMismatch,
            _ => {}
        }
    }

    CaseClassification::AllAgree
}
