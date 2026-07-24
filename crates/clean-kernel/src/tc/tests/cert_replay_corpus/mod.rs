// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-verification Wave 0: Fixed corpus + baseline metrics.
//!
//! Runs the full certificate-replay pipeline on a fixed corpus of 50+
//! expressions: `infer_type_with_cert` → `replay_and_verify` →
//! `cross_validate_with_micro`.
//!
//! Part of #1890 / #371. Design: designs/2026-02-15-371-certificate-replay-alternative.md

mod data;

use super::*;
use crate::cert::{CertVerifier, ProofCert};
use crate::micro::cross_validate_with_micro;
use data::{build_corpus, CorpusEntry};

// =========================================================================
// Metrics types
// =========================================================================

#[derive(Debug)]
struct EntryResult {
    name: &'static str,
    cert_ok: bool,
    replay_ok: bool,
    micro_supported: bool,
    micro_ok: bool,
    error: Option<String>,
}

#[derive(Debug, Default)]
struct CorpusMetrics {
    total: usize,
    cert_pass: usize,
    cert_fail: usize,
    replay_pass: usize,
    replay_fail: usize,
    micro_supported: usize,
    micro_unsupported: usize,
    micro_pass: usize,
    micro_fail: usize,
}

impl std::fmt::Display for CorpusMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pct = |n: usize, d: usize| -> f64 {
            if d > 0 {
                n as f64 / d as f64 * 100.0
            } else {
                0.0
            }
        };
        writeln!(f, "=== Self-Verification Wave 0 Baseline ===")?;
        writeln!(f, "Total corpus entries:    {}", self.total)?;
        writeln!(
            f,
            "Cert generation:        {}/{} pass ({:.1}%)",
            self.cert_pass,
            self.total,
            pct(self.cert_pass, self.total)
        )?;
        writeln!(
            f,
            "Replay verification:    {}/{} pass ({:.1}%)",
            self.replay_pass,
            self.cert_pass,
            pct(self.replay_pass, self.cert_pass)
        )?;
        writeln!(
            f,
            "Micro-checker supported: {}/{} ({:.1}%)",
            self.micro_supported,
            self.cert_pass,
            pct(self.micro_supported, self.cert_pass)
        )?;
        writeln!(
            f,
            "Micro-checker pass:     {}/{} ({:.1}%)",
            self.micro_pass,
            self.micro_supported,
            pct(self.micro_pass, self.micro_supported)
        )
    }
}

// =========================================================================
// Pipeline runner
// =========================================================================

fn run_pipeline(entry: &CorpusEntry) -> EntryResult {
    let tc = TypeChecker::new(&entry.env);

    let (ty, cert) = match tc.infer_type_with_cert(&entry.expr) {
        Ok(r) => r,
        Err(e) => {
            return EntryResult {
                name: entry.name,
                cert_ok: false,
                replay_ok: false,
                micro_supported: false,
                micro_ok: false,
                error: Some(format!("cert generation failed: {e}")),
            }
        }
    };

    if let Err(e) = verify_replay(&entry.env, &cert, &entry.expr, &ty) {
        return EntryResult {
            name: entry.name,
            cert_ok: true,
            replay_ok: false,
            micro_supported: false,
            micro_ok: false,
            error: Some(format!("replay failed: {e}")),
        };
    }

    let (micro_supported, micro_ok, error) =
        match cross_validate_with_micro(&entry.expr, &ty, &cert) {
            Ok(true) => (true, true, None),
            Ok(false) => (false, false, None),
            Err(e) => (true, false, Some(format!("micro failed: {e}"))),
        };

    EntryResult {
        name: entry.name,
        cert_ok: true,
        replay_ok: true,
        micro_supported,
        micro_ok,
        error,
    }
}

fn verify_replay(
    env: &Environment,
    cert: &ProofCert,
    original_expr: &Expr,
    expected_type: &Expr,
) -> Result<(), String> {
    let mut verifier = CertVerifier::new(env);
    let (replayed, verified_ty) = verifier
        .replay_and_verify(cert)
        .map_err(|e| format!("{e}"))?;
    if replayed != *original_expr {
        return Err(format!(
            "replayed expr mismatch: expected {original_expr:?}, got {replayed:?}"
        ));
    }
    if verified_ty != *expected_type {
        return Err(format!(
            "type mismatch: inferred {expected_type:?}, verified {verified_ty:?}"
        ));
    }
    Ok(())
}

fn collect_metrics(results: &[EntryResult]) -> CorpusMetrics {
    let mut m = CorpusMetrics {
        total: results.len(),
        ..Default::default()
    };
    for r in results {
        if r.cert_ok {
            m.cert_pass += 1;
        } else {
            m.cert_fail += 1;
        }
        if r.replay_ok {
            m.replay_pass += 1;
        } else if r.cert_ok {
            m.replay_fail += 1;
        }
        if r.micro_supported {
            m.micro_supported += 1;
            if r.micro_ok {
                m.micro_pass += 1;
            } else {
                m.micro_fail += 1;
            }
        } else if r.cert_ok {
            m.micro_unsupported += 1;
        }
    }
    m
}

// =========================================================================
// Tests
// =========================================================================

/// Wave 0 baseline: runs full pipeline on all corpus entries, prints metrics.
///
/// Run: `cargo test -p clean-kernel --lib -- cert_replay_corpus_baseline`
#[test]
fn test_cert_replay_corpus_baseline() {
    let corpus = build_corpus();
    assert!(
        corpus.len() >= 50,
        "Corpus must have >=50 entries, got {}",
        corpus.len()
    );

    let results: Vec<EntryResult> = corpus.iter().map(run_pipeline).collect();
    let metrics = collect_metrics(&results);
    eprintln!("\n{metrics}");

    let failures: Vec<&EntryResult> = results.iter().filter(|r| r.error.is_some()).collect();
    if !failures.is_empty() {
        eprintln!("--- Failures ({}) ---", failures.len());
        for f in &failures {
            eprintln!("  {}: {}", f.name, f.error.as_deref().unwrap_or("unknown"));
        }
    }
    assert!(
        metrics.cert_pass > 0,
        "At least some entries must pass cert generation"
    );
}

/// Core invariant: cert generation success implies replay success.
#[test]
fn test_cert_replay_corpus_replay_agreement() {
    let corpus = build_corpus();
    let mut failures = Vec::new();
    for entry in &corpus {
        let tc = TypeChecker::new(&entry.env);
        if let Ok((ty, cert)) = tc.infer_type_with_cert(&entry.expr) {
            let mut verifier = CertVerifier::new(&entry.env);
            match verifier.replay_and_verify(&cert) {
                Ok((replayed, verified_ty)) => {
                    if replayed != entry.expr {
                        failures.push(format!("{}: replayed expr mismatch", entry.name));
                    }
                    if verified_ty != ty {
                        failures.push(format!("{}: type mismatch", entry.name));
                    }
                }
                Err(e) => failures.push(format!("{}: replay error: {e}", entry.name)),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "Replay failures:\n{}",
        failures.join("\n")
    );
}

/// Micro-checker must not disagree with kernel on supported expressions.
#[test]
fn test_cert_replay_corpus_micro_agreement() {
    let corpus = build_corpus();
    let mut failures = Vec::new();
    for entry in &corpus {
        let tc = TypeChecker::new(&entry.env);
        if let Ok((ty, cert)) = tc.infer_type_with_cert(&entry.expr) {
            if let Err(e) = cross_validate_with_micro(&entry.expr, &ty, &cert) {
                failures.push(format!("{}: micro disagrees: {e}", entry.name));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "Micro disagreements:\n{}",
        failures.join("\n")
    );
}
