// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-COMP 2026 exact-string protocol tests for the trust module (#3340).
//!
//! These tests pin the exact verdict strings required by SMT-COMP judges
//! (`valid`, `holey`, `invalid`). Any deviation (capitalization, whitespace,
//! alternate spelling) would disqualify the checker, so they are asserted
//! as literal string matches. They also lock the classification semantics
//! of [`SmtVerifyStats::is_fully_verified`]: a proof whose only non-kernel
//! steps are `structurally_accepted` must be routed to the `holey` bucket,
//! not `valid` — this is the gap flagged by AI Model 3.1 Pro in the original
//! #3340 bug report.

#![cfg(test)]

use crate::smt_verify::trust::SmtVerifyStats;

#[test]
fn test_competition_verdict_valid_literal_string() {
    let stats = SmtVerifyStats {
        total_steps: 1,
        kernel_verified: 1,
        ..Default::default()
    };
    // Must be the literal "valid" — not "VALID", "Valid", or "valid."
    let v: &'static str = stats.competition_verdict();
    assert_eq!(v, "valid");
}

#[test]
fn test_competition_verdict_holey_literal_string() {
    let stats = SmtVerifyStats {
        total_steps: 1,
        structurally_accepted: 1,
        ..Default::default()
    };
    let v: &'static str = stats.competition_verdict();
    assert_eq!(v, "holey");
}

#[test]
fn test_competition_verdict_invalid_literal_string() {
    let stats = SmtVerifyStats {
        total_steps: 1,
        trusted: 1,
        ..Default::default()
    };
    let v: &'static str = stats.competition_verdict();
    assert_eq!(v, "invalid");
}

#[test]
fn test_is_fully_verified_rejects_structurally_accepted_only() {
    // The SMT-COMP classification gap identified by AI Model 3.1 Pro:
    // a proof with only structurally_accepted steps (no trusted steps)
    // must be classified "holey", not "valid". `is_fully_verified` must
    // return false so callers route these proofs to the holey bucket.
    let stats = SmtVerifyStats {
        total_steps: 5,
        structurally_accepted: 5,
        ..Default::default()
    };
    assert!(
        !stats.is_fully_verified(),
        "structurally_accepted steps must not count as fully verified"
    );
    assert!(stats.is_holey());
    assert_eq!(stats.competition_verdict(), "holey");
}

#[test]
fn test_classification_mixed_structurally_and_kernel_is_holey() {
    // Mix of kernel_verified and structurally_accepted (no trusted): holey.
    let stats = SmtVerifyStats {
        total_steps: 10,
        kernel_verified: 7,
        structurally_accepted: 3,
        ..Default::default()
    };
    assert!(!stats.is_fully_verified());
    assert!(stats.is_holey());
    assert_eq!(stats.competition_verdict(), "holey");
}

#[test]
fn test_classification_one_trusted_among_many_verified_is_invalid() {
    // Even a single trusted step must demote the whole proof to "invalid",
    // per SMT-COMP strict classification rules.
    let stats = SmtVerifyStats {
        total_steps: 101,
        kernel_verified: 100,
        trusted: 1,
        ..Default::default()
    };
    assert!(!stats.is_fully_verified());
    assert!(!stats.is_holey());
    assert_eq!(stats.competition_verdict(), "invalid");
}
