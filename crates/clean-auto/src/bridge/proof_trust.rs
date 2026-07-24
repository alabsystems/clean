// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge-level trust-accounting helpers.
//!
//! This module is the canonical public home for helpers that both `clean-auto`
//! and `clean-elab` use to count embedded `trustedAy` sub-terms identically.
//! Keeping the implementation here (rather than inside `ay_backend`) makes the
//! cross-crate trust contract visible in the import path and avoids exposing
//! raw ay backend internals.

use std::fs::OpenOptions;
use std::io::Write;
use std::sync::Mutex;

use clean_kernel::{Expr, ExprVisitor, LevelVec, Name};

// ---------------------------------------------------------------------------
// TrustBoundary audit lane (#2875)
// ---------------------------------------------------------------------------

/// One audit record capturing a trust-boundary hit during a test run.
///
/// Emitted only when `CLEAN_TRUST_BOUNDARY_AUDIT_PATH` is set. The record is
/// appended as a single tab-separated line to the file at that path.
pub struct TrustBoundaryAuditRecord {
    pub lane: &'static str,
    pub crate_name: &'static str,
    pub test_name: String,
    pub tactic: Option<String>,
    pub proof_kind: Option<String>,
    pub subsystem: Option<String>,
    pub description: Option<String>,
    pub step_index: Option<u32>,
    pub arithmetic_boundary_steps: usize,
    pub local_gap_steps: usize,
    pub trust_subterm_count: usize,
}

/// Serialization lock so parallel test threads do not interleave TSV lines.
static AUDIT_LOCK: Mutex<()> = Mutex::new(());

/// Sanitize a string for TSV output: replace tabs and newlines with spaces.
fn sanitize_tsv(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '\t' | '\n' | '\r' => ' ',
            other => other,
        })
        .collect()
}

/// Append one trust-boundary audit record to the file at
/// `CLEAN_TRUST_BOUNDARY_AUDIT_PATH`.
///
/// If the env var is unset, this is a no-op. The TSV columns are:
///
/// ```text
/// lane \t crate_name \t test_name \t tactic \t proof_kind \t subsystem \t description \t step_index \t arithmetic_boundary_steps \t local_gap_steps \t trust_subterm_count
/// ```
pub fn append_trust_boundary_audit_record(record: &TrustBoundaryAuditRecord) {
    let path = match std::env::var("CLEAN_TRUST_BOUNDARY_AUDIT_PATH") {
        Ok(p) if !p.is_empty() => p,
        _ => return,
    };

    let line = format!(
        "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
        record.lane,
        record.crate_name,
        sanitize_tsv(&record.test_name),
        record.tactic.as_deref().unwrap_or("-"),
        record.proof_kind.as_deref().unwrap_or("-"),
        record
            .subsystem
            .as_deref()
            .map(sanitize_tsv)
            .unwrap_or_else(|| "-".to_string()),
        record
            .description
            .as_deref()
            .map(sanitize_tsv)
            .unwrap_or_else(|| "-".to_string()),
        record
            .step_index
            .map(|i| i.to_string())
            .unwrap_or_else(|| "-".to_string()),
        record.arithmetic_boundary_steps,
        record.local_gap_steps,
        record.trust_subterm_count,
    );

    let _guard = AUDIT_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(&path) {
        let _ = file.write_all(line.as_bytes());
    }
}

// ---------------------------------------------------------------------------
// trustedAy constant counter
// ---------------------------------------------------------------------------

struct TrustedAyConstCounter;

impl ExprVisitor for TrustedAyConstCounter {
    type Result = usize;

    fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result {
        a + b
    }

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
        if name.to_string() == "trustedAy" {
            1
        } else {
            0
        }
    }
}

/// Count embedded `trustedAy` constant references in a kernel expression.
///
/// This is the canonical implementation shared across crates. `clean-elab`
/// re-exports this function so both crates count with identical logic.
pub fn count_embedded_trusted_ay_terms(expr: &Expr) -> usize {
    let mut counter = TrustedAyConstCounter;
    counter.visit_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;
    use std::fs;

    fn make_test_record(lane: &'static str, crate_name: &'static str) -> TrustBoundaryAuditRecord {
        TrustBoundaryAuditRecord {
            lane,
            crate_name,
            test_name: "test_example".to_string(),
            tactic: None,
            proof_kind: None,
            subsystem: Some("lra_chain".to_string()),
            description: Some("symbolic endpoints".to_string()),
            step_index: Some(0),
            arithmetic_boundary_steps: 1,
            local_gap_steps: 0,
            trust_subterm_count: 0,
        }
    }

    #[test]
    #[serial(trust_boundary_audit)]
    fn test_audit_lane_no_file_when_env_unset() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("audit.tsv");
        // Ensure the env var is NOT set (restored on guard drop).
        let _guard = crate::test_env::ScopedEnvVar::unset("CLEAN_TRUST_BOUNDARY_AUDIT_PATH");

        append_trust_boundary_audit_record(&make_test_record("proof_reconstruct", "clean-auto"));

        assert!(
            !path.exists(),
            "audit file should not be created when env var is unset"
        );
    }

    #[test]
    #[serial(trust_boundary_audit)]
    fn test_audit_lane_appends_record_when_env_set() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("audit.tsv");
        let _guard = crate::test_env::ScopedEnvVar::set(
            "CLEAN_TRUST_BOUNDARY_AUDIT_PATH",
            path.to_str().unwrap(),
        );

        append_trust_boundary_audit_record(&make_test_record("proof_reconstruct", "clean-auto"));
        let contents = fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = contents.lines().collect();
        assert_eq!(lines.len(), 1, "should have exactly one audit line");

        let cols: Vec<&str> = lines[0].split('\t').collect();
        assert_eq!(cols.len(), 11, "TSV should have 11 columns");
        assert_eq!(cols[0], "proof_reconstruct");
        assert_eq!(cols[1], "clean-auto");
        assert_eq!(cols[2], "test_example");
        assert_eq!(cols[3], "-"); // tactic
        assert_eq!(cols[4], "-"); // proof_kind
        assert_eq!(cols[5], "lra_chain");
        assert_eq!(cols[6], "symbolic endpoints");
        assert_eq!(cols[7], "0"); // step_index
        assert_eq!(cols[8], "1"); // arithmetic_boundary_steps
        assert_eq!(cols[9], "0"); // local_gap_steps
        assert_eq!(cols[10], "0"); // trust_subterm_count
    }

    #[test]
    #[serial(trust_boundary_audit)]
    fn test_audit_lane_sanitizes_tabs_and_newlines() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("audit.tsv");
        let _guard = crate::test_env::ScopedEnvVar::set(
            "CLEAN_TRUST_BOUNDARY_AUDIT_PATH",
            path.to_str().unwrap(),
        );

        let record = TrustBoundaryAuditRecord {
            lane: "proof_reconstruct",
            crate_name: "clean-auto",
            test_name: "test\twith\ttabs".to_string(),
            tactic: None,
            proof_kind: None,
            subsystem: Some("sub\nsystem".to_string()),
            description: Some("desc\r\nription".to_string()),
            step_index: None,
            arithmetic_boundary_steps: 2,
            local_gap_steps: 1,
            trust_subterm_count: 3,
        };
        append_trust_boundary_audit_record(&record);
        let contents = fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = contents.lines().collect();
        assert_eq!(lines.len(), 1, "sanitized record should be one line");

        let cols: Vec<&str> = lines[0].split('\t').collect();
        assert_eq!(
            cols.len(),
            11,
            "TSV should have 11 columns after sanitization"
        );
        assert_eq!(
            cols[2], "test with tabs",
            "tabs in test_name should be replaced with spaces"
        );
        assert_eq!(
            cols[5], "sub system",
            "newlines in subsystem should be replaced with spaces"
        );
    }

    #[test]
    #[serial(trust_boundary_audit)]
    fn test_audit_lane_with_tactic_and_proof_kind() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("audit.tsv");
        let _guard = crate::test_env::ScopedEnvVar::set(
            "CLEAN_TRUST_BOUNDARY_AUDIT_PATH",
            path.to_str().unwrap(),
        );

        let record = TrustBoundaryAuditRecord {
            lane: "selected_direct_proof",
            crate_name: "clean-elab",
            test_name: "test_smt_goal".to_string(),
            tactic: Some("smt".to_string()),
            proof_kind: Some("direct_ay".to_string()),
            subsystem: None,
            description: None,
            step_index: None,
            arithmetic_boundary_steps: 1,
            local_gap_steps: 2,
            trust_subterm_count: 1,
        };
        append_trust_boundary_audit_record(&record);
        let contents = fs::read_to_string(&path).unwrap();
        let cols: Vec<&str> = contents.lines().next().unwrap().split('\t').collect();
        assert_eq!(cols[0], "selected_direct_proof");
        assert_eq!(cols[1], "clean-elab");
        assert_eq!(cols[3], "smt");
        assert_eq!(cols[4], "direct_ay");
        assert_eq!(cols[5], "-"); // subsystem None
        assert_eq!(cols[6], "-"); // description None
        assert_eq!(cols[7], "-"); // step_index None
    }
}
