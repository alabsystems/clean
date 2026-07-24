// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SAT-COMP competition output wrappers.
//!
//! SAT-COMP proof judges expect one of two terminal strings on stdout:
//! `s VERIFIED` or `s NOT VERIFIED`. These strings are fixed by the
//! competition protocol and cannot vary.
//!
//! This module exposes the protocol as a library-level surface so callers
//! do not have to shell out to the `proof_check` CLI binary to obtain the
//! correct output. It mirrors the structure of the SMT-COMP wrappers in
//! [`crate::smt_verify::pipeline`] (`SmtCompVerdict`,
//! `verify_smt_competition_entry`, `format_competition_output`).
//!
//! # Entry points
//!
//! - [`verify_sat_competition_entry`] — run the SAT verification pipeline
//!   on raw formula + proof bytes and return a [`SatCompetitionResult`].
//! - [`format_sat_competition_output`] — render the result as stdout text
//!   with the protocol verdict on line 1 and diagnostic `c` comments after.
//!
//! # Protocol invariants
//!
//! * Line 1 is always exactly `s VERIFIED` or `s NOT VERIFIED`, no
//!   trailing punctuation, no alternate capitalization.
//! * Additional lines are `c`-prefixed comments, which judges ignore.
//! * Any internal error maps to `NotVerified` with a diagnostic comment.
//!
//! Reference: SAT Competition checker protocol (`s` lines).

use super::pipeline::{verify_any_proof, ProofFormat, TrustLevel};

/// SAT-COMP unsat-proof verdict.
///
/// Two possible verdicts matching the SAT-COMP protocol exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SatCompVerdict {
    /// Proof verified as a valid refutation.
    Verified,
    /// Proof did not verify.
    NotVerified,
}

impl std::fmt::Display for SatCompVerdict {
    /// Emits the exact string required by the SAT-COMP protocol.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SatCompVerdict::Verified => write!(f, "s VERIFIED"),
            SatCompVerdict::NotVerified => write!(f, "s NOT VERIFIED"),
        }
    }
}

/// Result wrapper for SAT-COMP competition output.
#[derive(Debug, Clone)]
pub struct SatCompetitionResult {
    /// Protocol verdict (`s VERIFIED` | `s NOT VERIFIED`).
    pub verdict: SatCompVerdict,
    /// Detected proof format.
    pub format: ProofFormat,
    /// Trust level classification for the verification pipeline.
    pub trust_level: TrustLevel,
    /// Number of proof steps verified.
    pub steps_verified: usize,
    /// Number of proof steps accepted on trust (not kernel-verified).
    pub steps_trusted: usize,
    /// Wall-clock verification time in microseconds.
    pub verification_time_us: u64,
    /// Error message, if verification could not produce a valid result.
    pub error: Option<String>,
}

/// Verify a SAT proof against a CNF formula and return a SAT-COMP result.
///
/// Wraps [`verify_any_proof`] and translates the outcome into a
/// [`SatCompetitionResult`] whose terminal verdict string (`s VERIFIED`
/// or `s NOT VERIFIED`) matches the SAT-COMP checker protocol exactly.
///
/// Never returns an error: failures are captured as
/// `SatCompVerdict::NotVerified` with an attached error message so the
/// caller can still emit a protocol-compliant `s NOT VERIFIED` line.
///
/// The `formula` parameter is DIMACS CNF bytes (usually UTF-8 text).
/// The `proof` parameter is raw proof bytes (DRAT, LRAT, or FRAT).
#[must_use]
pub fn verify_sat_competition_entry(formula: &[u8], proof: &[u8]) -> SatCompetitionResult {
    match verify_any_proof(formula, proof) {
        Ok(result) => {
            // SOUNDNESS (root cause C): `s VERIFIED` is a discharge claim, so
            // require full kernel verification. `result.valid` alone is only the
            // structural "derives the empty clause" signal — for a proof routed
            // through the SMT checker it is true even when the empty clause was
            // laundered from a structurally-accepted step. A holey/partially-
            // verified proof maps to `NotVerified`. See
            // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
            let fully_verified = result.valid && result.trust_level == TrustLevel::KernelVerified;
            let verdict = if fully_verified {
                SatCompVerdict::Verified
            } else {
                SatCompVerdict::NotVerified
            };
            let error = if fully_verified {
                None
            } else if result.valid {
                Some(format!(
                    "proof derives the empty clause but is not fully kernel-verified \
                     (trust: {}, trusted steps: {})",
                    result.trust_level, result.steps_trusted
                ))
            } else if result.errors.is_empty() {
                Some("proof did not verify as a valid refutation".to_owned())
            } else {
                Some(result.errors.join("; "))
            };
            SatCompetitionResult {
                verdict,
                format: result.format,
                trust_level: result.trust_level,
                steps_verified: result.steps_verified,
                steps_trusted: result.steps_trusted,
                verification_time_us: result.verification_time_us,
                error,
            }
        }
        Err(e) => SatCompetitionResult {
            verdict: SatCompVerdict::NotVerified,
            format: ProofFormat::Unknown,
            trust_level: TrustLevel::Unverified,
            steps_verified: 0,
            steps_trusted: 0,
            verification_time_us: 0,
            error: Some(e.to_string()),
        },
    }
}

/// Format a SAT-COMP competition result as stdout output.
///
/// Line 1 is always the literal protocol verdict (`s VERIFIED` or
/// `s NOT VERIFIED`). Optional diagnostic lines follow as `c` comments
/// (SAT-COMP comment convention); judges parse only the `s` line.
///
/// Example (verified):
/// ```text
/// s VERIFIED
/// c format: LRAT  steps_verified: 42  steps_trusted: 0
/// ```
///
/// Example (not verified):
/// ```text
/// s NOT VERIFIED
/// c error: proof did not derive the empty clause
/// ```
#[must_use]
pub fn format_sat_competition_output(result: &SatCompetitionResult) -> String {
    let mut out = String::with_capacity(128);
    out.push_str(&result.verdict.to_string());
    out.push('\n');

    match result.verdict {
        SatCompVerdict::Verified => {
            out.push_str(&format!(
                "c format: {}  steps_verified: {}  steps_trusted: {}\n",
                result.format, result.steps_verified, result.steps_trusted,
            ));
        }
        SatCompVerdict::NotVerified => {
            if let Some(ref err) = result.error {
                out.push_str(&format!("c error: {err}\n"));
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Exact-string protocol tests (#3340) ----
    // SAT-COMP requires these literal strings; any deviation disqualifies
    // the checker.

    #[test]
    fn test_sat_comp_verdict_display_verified_exact_string() {
        assert_eq!(SatCompVerdict::Verified.to_string(), "s VERIFIED");
    }

    #[test]
    fn test_sat_comp_verdict_display_not_verified_exact_string() {
        assert_eq!(SatCompVerdict::NotVerified.to_string(), "s NOT VERIFIED");
    }

    // ---- Wrapper behavior tests ----

    #[test]
    fn test_sat_comp_wrapper_verified_drat() {
        let dimacs = b"p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";
        let result = verify_sat_competition_entry(dimacs, drat);

        assert_eq!(result.verdict, SatCompVerdict::Verified);
        assert_eq!(result.format, ProofFormat::Drat);
        assert!(result.steps_verified > 0);
        assert_eq!(result.steps_trusted, 0);
        assert!(result.error.is_none());
    }

    #[test]
    fn test_sat_comp_wrapper_verified_lrat() {
        let dimacs = b"c Simple UNSAT\np cnf 1 2\n1 0\n-1 0\n";
        let lrat = b"3 0 1 2 0\n";
        let result = verify_sat_competition_entry(dimacs, lrat);

        assert_eq!(result.verdict, SatCompVerdict::Verified);
        assert_eq!(result.format, ProofFormat::Lrat);
        assert_eq!(result.trust_level, TrustLevel::KernelVerified);
        assert!(result.error.is_none());
    }

    #[test]
    fn test_sat_comp_wrapper_not_verified_empty_proof() {
        let dimacs = b"p cnf 1 2\n1 0\n-1 0\n";
        let result = verify_sat_competition_entry(dimacs, b"");
        assert_eq!(result.verdict, SatCompVerdict::NotVerified);
        assert!(result.error.is_some());
    }

    #[test]
    fn test_sat_comp_wrapper_not_verified_unknown_format() {
        let dimacs = b"p cnf 1 2\n1 0\n-1 0\n";
        let result = verify_sat_competition_entry(dimacs, b"zzz garbage\n");
        assert_eq!(result.verdict, SatCompVerdict::NotVerified);
        assert!(result.error.is_some());
    }

    // ---- Output formatter tests ----

    #[test]
    fn test_format_sat_competition_output_verified_starts_with_protocol_line() {
        let result = SatCompetitionResult {
            verdict: SatCompVerdict::Verified,
            format: ProofFormat::Lrat,
            trust_level: TrustLevel::KernelVerified,
            steps_verified: 42,
            steps_trusted: 0,
            verification_time_us: 1000,
            error: None,
        };
        let output = format_sat_competition_output(&result);
        let first_line = output.lines().next().expect("output should have lines");
        assert_eq!(first_line, "s VERIFIED");
    }

    #[test]
    fn test_format_sat_competition_output_not_verified_starts_with_protocol_line() {
        let result = SatCompetitionResult {
            verdict: SatCompVerdict::NotVerified,
            format: ProofFormat::Unknown,
            trust_level: TrustLevel::Unverified,
            steps_verified: 0,
            steps_trusted: 0,
            verification_time_us: 0,
            error: Some("proof format could not be detected".to_owned()),
        };
        let output = format_sat_competition_output(&result);
        let first_line = output.lines().next().expect("output should have lines");
        assert_eq!(first_line, "s NOT VERIFIED");
        assert!(output.contains("c error: proof format could not be detected"));
    }

    #[test]
    fn test_sat_comp_roundtrip_end_to_end() {
        // Verified path.
        let dimacs = b"p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";
        let result = verify_sat_competition_entry(dimacs, drat);
        let output = format_sat_competition_output(&result);
        assert!(
            output.starts_with("s VERIFIED\n"),
            "verified output must start with exact protocol string, got {output:?}"
        );

        // Not-verified path.
        let bad = verify_sat_competition_entry(dimacs, b"zzz\n");
        let bad_output = format_sat_competition_output(&bad);
        assert!(
            bad_output.starts_with("s NOT VERIFIED\n"),
            "not-verified output must start with exact protocol string, got {bad_output:?}"
        );
    }
}
