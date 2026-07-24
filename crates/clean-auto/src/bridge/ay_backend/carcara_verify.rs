// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature-gated Carcara proof verification adapter.

use super::proof_backend::VerifyError;

/// Normalize `la_generic` steps that are missing required `:args` coefficients
/// by degrading them to `hole` steps.
///
/// Without Farkas coefficients, Carcara cannot verify `la_generic` steps and
/// returns a hard error. This converts the error into a holey-proof result so
/// callers get `Ok(false)` instead of `Err(CarcaraError)`.
///
/// Part of #2701: ay's QF_LIA Alethe export omits `:args` on `la_generic`.
#[cfg(feature = "carcara-verify")]
fn normalize_la_generic_missing_args(proof: &str) -> String {
    let mut result = String::with_capacity(proof.len());
    for (i, line) in proof.split('\n').enumerate() {
        if i > 0 {
            result.push('\n');
        }
        if line.contains(":rule la_generic") && !line.contains(":args") {
            result.push_str(&line.replace(":rule la_generic", ":rule hole"));
        } else {
            result.push_str(line);
        }
    }
    result
}

/// Verify an Alethe proof using Carcara
///
/// Requires the `carcara-verify` feature to be enabled.
///
/// Applies `la_generic` normalization before checking: steps missing required
/// `:args` coefficients are degraded to `hole` to avoid hard Carcara errors
/// (Part of #2701).
///
/// # Arguments
///
/// * `problem` - SMT-LIB2 problem string (declarations and assertions)
/// * `proof` - Alethe proof string
///
/// # Returns
///
/// * `Ok(true)` - Proof fully verified (no holes)
/// * `Ok(false)` - Proof is holey (contains unverified `hole`/`trust` steps)
/// * `Err(...)` - Verification error (parse error, etc.)
#[cfg(feature = "carcara-verify")]
pub fn verify_alethe_proof(problem: &str, proof: &str) -> Result<bool, VerifyError> {
    use carcara::{check, checker::Config as CheckerConfig, parser::Config as ParserConfig};
    use std::io::BufReader;

    let normalized_proof = normalize_la_generic_missing_args(proof);
    let problem_reader = BufReader::new(problem.as_bytes());
    let proof_reader = BufReader::new(normalized_proof.as_bytes());

    let result = check(
        problem_reader,
        proof_reader,
        None::<BufReader<&[u8]>>,
        ParserConfig::default(),
        CheckerConfig::default(),
        false,
    );

    match result {
        Ok(is_holey) => Ok(!is_holey),
        Err(e) => Err(VerifyError::CarcaraError(e.to_string())),
    }
}

/// Stub for when Carcara feature is not enabled
#[cfg(not(feature = "carcara-verify"))]
pub fn verify_alethe_proof(_problem: &str, _proof: &str) -> Result<bool, VerifyError> {
    Err(VerifyError::CarcaraNotEnabled)
}

#[cfg(test)]
#[cfg(feature = "carcara-verify")]
mod tests {
    use super::{normalize_la_generic_missing_args, verify_alethe_proof};

    fn uf_contradiction_problem() -> &'static str {
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
    }

    fn uf_contradiction_proof(rule: &str) -> String {
        format!(
            "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule {rule} :premises (t1 t0))\n"
        )
    }

    #[test]
    fn test_la_generic_without_args_replaced_with_hole() {
        let proof = "(assume h1 (> x 0))\n\
                     (assume h2 (< x 0))\n\
                     (step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic)";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule hole"),
            "la_generic without :args should be replaced with hole"
        );
        assert!(
            !normalized.contains("la_generic"),
            "la_generic without :args should not remain after normalization"
        );
    }

    #[test]
    fn test_la_generic_with_args_preserved() {
        let proof = "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule la_generic"),
            "la_generic WITH :args should be preserved"
        );
        assert!(
            !normalized.contains(":rule hole"),
            "la_generic WITH :args should not be replaced with hole"
        );
    }

    #[test]
    fn test_other_rules_untouched() {
        let proof = "(step t1 (cl (= a b)) :rule eq_transitive :premises (h1 h2))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert_eq!(
            normalized, proof,
            "non-la_generic rules should be untouched"
        );
    }

    #[test]
    fn test_la_generic_with_premises_but_no_args_replaced() {
        let proof = "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :premises (h1 h2))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule hole"),
            "la_generic with :premises but no :args should be replaced with hole"
        );
    }

    #[test]
    fn test_verify_alethe_proof_returns_true_for_fully_verified_proof() {
        let valid = verify_alethe_proof(
            uf_contradiction_problem(),
            &uf_contradiction_proof("resolution"),
        )
        .expect("complete UF contradiction proof should verify");
        assert!(valid, "complete proof should report valid=true");
    }

    #[test]
    fn test_verify_alethe_proof_returns_false_for_holey_proof() {
        let valid =
            verify_alethe_proof(uf_contradiction_problem(), &uf_contradiction_proof("hole"))
                .expect("holey proof should return Ok(false), not a transport error");
        assert!(!valid, "holey proof should report valid=false");
    }
}
