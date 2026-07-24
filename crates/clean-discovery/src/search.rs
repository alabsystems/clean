// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exhaustive search runner for candidate theorem verification.
//!
//! The search runner takes a batch of candidates, GENUINELY verifies that each
//! candidate's proof term proves its claimed statement, and collects results
//! with statistics.
//!
//! # Honest verification
//!
//! A candidate is marked `verified` **only** when it carries a proof term whose
//! inferred type is definitionally equal to the candidate's stated proposition.
//! This is exactly the kernel's [`TypeChecker::check_type`] contract:
//! `infer_type(proof)` followed by `is_def_eq(inferred, statement)`.
//!
//! Concretely this means a proof that is merely *well-typed* — e.g. a bare
//! reference to an axiom whose type is **not** the candidate's statement — is
//! REJECTED. Earlier revisions of this runner inferred the proof's type and
//! reported "verified" whenever inference *succeeded*, regardless of whether the
//! inferred type matched the claim; that made the loop overstate. The check
//! below closes that hole: the kernel is the oracle, and it only accepts a proof
//! that genuinely inhabits the stated type.
//!
//! A candidate with no proof term is honestly reported as **Unverified** (its
//! statement may be well-formed, but no proof of it was supplied).
//!
//! Part of #3258.

use crate::candidate::{CandidateTheorem, VerificationOutcome};
use clean_kernel::{Environment, TypeChecker};

/// Result of a search run over a batch of candidates.
#[derive(Debug)]
pub struct SearchResult {
    /// Outcomes for each candidate (same order as input).
    pub outcomes: Vec<VerificationOutcome>,
    /// Aggregate statistics.
    pub stats: SearchStats,
}

/// Aggregate statistics for a search run.
#[derive(Debug, Clone)]
pub struct SearchStats {
    /// Total candidates evaluated.
    pub total_evaluated: u64,
    /// Candidates that passed type checking.
    pub total_verified: u64,
    /// Candidates that failed type checking.
    pub total_failed: u64,
    /// Wall-clock time in nanoseconds.
    pub wall_time_ns: u64,
    /// Throughput: candidates per second.
    pub throughput_per_sec: f64,
}

/// Exhaustive search: verify every candidate in the batch.
///
/// This is the primary search strategy for small search spaces (<10K candidates).
/// It evaluates every candidate against the kernel and returns all results.
pub struct ExhaustiveSearch;

impl ExhaustiveSearch {
    /// Run exhaustive, genuine verification on all candidates.
    ///
    /// For each candidate with a proof term, the kernel checks that the proof
    /// term's inferred type is definitionally equal to the candidate's stated
    /// proposition (`TypeChecker::check_type`). Only then is the candidate
    /// marked `verified`. A candidate without a proof term, or whose proof does
    /// not have the statement as its type, is honestly reported as NOT verified.
    pub fn run(env: &Environment, candidates: &[CandidateTheorem]) -> SearchResult {
        let wall_start = std::time::Instant::now();

        let outcomes: Vec<VerificationOutcome> = candidates
            .iter()
            .map(|candidate| verify_candidate(env, candidate))
            .collect();

        let wall_time_ns = wall_start.elapsed().as_nanos() as u64;

        let total_evaluated = outcomes.len() as u64;
        let total_verified = outcomes.iter().filter(|o| o.verified).count() as u64;
        let total_failed = total_evaluated - total_verified;
        let elapsed_secs = wall_time_ns as f64 / 1_000_000_000.0;
        let throughput_per_sec = if elapsed_secs > 0.0 {
            total_evaluated as f64 / elapsed_secs
        } else {
            0.0
        };

        SearchResult {
            outcomes,
            stats: SearchStats {
                total_evaluated,
                total_verified,
                total_failed,
                wall_time_ns,
                throughput_per_sec,
            },
        }
    }

    /// Find the first GENUINELY verified candidate (early termination).
    ///
    /// Returns the index of the first candidate whose proof term genuinely
    /// proves its statement, together with the proven statement.
    pub fn find_first_valid(
        env: &Environment,
        candidates: &[CandidateTheorem],
    ) -> Option<(usize, clean_kernel::Expr)> {
        candidates.iter().enumerate().find_map(|(idx, candidate)| {
            let outcome = verify_candidate(env, candidate);
            outcome.verified.then(|| (idx, candidate.statement.clone()))
        })
    }
}

/// Genuinely verify a single candidate against the kernel.
///
/// The candidate is verified iff it carries a proof term whose inferred type is
/// definitionally equal to its statement. This is the kernel `check_type`
/// contract: `infer_type(proof)` then `is_def_eq(inferred, statement)`.
fn verify_candidate(env: &Environment, candidate: &CandidateTheorem) -> VerificationOutcome {
    let start = std::time::Instant::now();
    let tc = TypeChecker::new(env);

    let (verified, inferred_type, error) = match &candidate.proof {
        Some(proof) => match tc.check_type(proof, &candidate.statement) {
            // Proof genuinely inhabits the stated proposition.
            Ok(()) => (true, Some(candidate.statement.clone()), None),
            // Proof is well-typed-or-not, but does NOT have the statement as its
            // type: honestly rejected.
            Err(e) => (false, None, Some(e.to_string())),
        },
        // No proof supplied: the claim is unproven, hence not verified.
        None => (
            false,
            None,
            Some("candidate has no proof term (unverified)".to_string()),
        ),
    };

    VerificationOutcome {
        candidate_id: candidate.id,
        verified,
        inferred_type,
        error,
        time_ns: start.elapsed().as_nanos() as u64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::{CandidateId, ParamVec};
    use crate::family::TheoremFamily;
    use clean_kernel::{BinderInfo, Environment, Expr, Level};

    /// Build an environment with the NN-verify proof-complexity declarations,
    /// which include `ibp_cert_polynomial_axiom : forall (d w : Nat)
    /// (cert : IBPCertificate), ibp_cert_size cert <= d * (w * w)`.
    fn pc_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_proof_complexity()
            .expect("init proof complexity");
        env
    }

    /// The exact statement proven by `ibp_cert_polynomial_axiom`:
    /// `forall (d w : Nat) (cert : IBPCertificate),
    ///    LE.le @Nat instLENat (ibp_cert_size cert) (Nat.mul d (Nat.mul w w))`.
    fn ibp_polynomial_statement() -> Expr {
        let nat = Expr::const_str("Nat");
        let ibp_cert = Expr::const_str("NNVerify.ProofComplexity.IBPCertificate");
        let ibp_cert_size = Expr::const_str("NNVerify.ProofComplexity.ibp_cert_size");
        let le_le = Expr::const_str_levels("LE.le", vec![Level::zero()]);
        let inst_le_nat = Expr::const_str("instLENat");
        let nat_mul = Expr::const_str("Nat.mul");

        // d = BVar(2), w = BVar(1), cert = BVar(0)
        let cert_sz = Expr::app(ibp_cert_size, Expr::bvar(0));
        let w_sq = Expr::apps(nat_mul.clone(), [Expr::bvar(1), Expr::bvar(1)]);
        let bound = Expr::apps(nat_mul, [Expr::bvar(2), w_sq]);
        let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);
        let body = Expr::pi(BinderInfo::Default, ibp_cert, le_expr);
        let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
        Expr::pi(BinderInfo::Default, nat, body)
    }

    fn ibp_polynomial_proof() -> Expr {
        Expr::const_str("NNVerify.ProofComplexity.ibp_cert_polynomial_axiom")
    }

    /// (a) Core positive case: a candidate whose proof term genuinely has the
    /// statement as its type is reported as Verified.
    #[test]
    fn test_genuine_proof_is_verified() {
        let env = pc_env();
        let candidates = vec![CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement: ibp_polynomial_statement(),
            proof: Some(ibp_polynomial_proof()),
        }];

        let result = ExhaustiveSearch::run(&env, &candidates);
        assert_eq!(result.stats.total_evaluated, 1);
        assert_eq!(
            result.stats.total_verified, 1,
            "proof that genuinely inhabits the statement must verify"
        );
        assert!(result.outcomes[0].verified);
        assert!(result.outcomes[0].inferred_type.is_some());
        assert!(result.outcomes[0].error.is_none());
    }

    /// (b) Core regression guard: a candidate whose proof is a well-typed term
    /// that does NOT prove the statement is REJECTED.
    ///
    /// Here `proof : Q` (the polynomial axiom, type `... <= d * (w*w)`) but the
    /// claimed `statement : P` is the SAME shape with a spurious leading
    /// `Nat.mul 1 (...)` multiplier. `Nat.mul` is an axiom in this environment
    /// (not reducible), so `1 * x` is NOT definitionally equal to `x`; the proof
    /// is well-typed but does not inhabit `P`. The OLD infer-only verifier
    /// accepted this (the axiom reference type-checks); the genuine verifier
    /// rejects it.
    #[test]
    fn test_wellt_typed_proof_of_wrong_statement_is_rejected() {
        let env = pc_env();

        // P: same as the axiom's type but with a spurious `Nat.mul 1 (...)`.
        let nat = Expr::const_str("Nat");
        let ibp_cert = Expr::const_str("NNVerify.ProofComplexity.IBPCertificate");
        let ibp_cert_size = Expr::const_str("NNVerify.ProofComplexity.ibp_cert_size");
        let le_le = Expr::const_str_levels("LE.le", vec![Level::zero()]);
        let inst_le_nat = Expr::const_str("instLENat");
        let nat_mul = Expr::const_str("Nat.mul");
        let cert_sz = Expr::app(ibp_cert_size, Expr::bvar(0));
        let w_sq = Expr::apps(nat_mul.clone(), [Expr::bvar(1), Expr::bvar(1)]);
        let d_w_sq = Expr::apps(nat_mul.clone(), [Expr::bvar(2), w_sq]);
        let bound = Expr::apps(nat_mul, [Expr::nat_lit(1), d_w_sq]);
        let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);
        let body = Expr::pi(BinderInfo::Default, ibp_cert, le_expr);
        let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
        let wrong_statement = Expr::pi(BinderInfo::Default, nat, body);

        let candidates = vec![CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement: wrong_statement,
            // The proof IS well-typed (it is a real axiom reference), so the
            // OLD infer-only path accepted it. Its type is `... <= d*(w*w)`,
            // which is NOT def-eq to the claimed `... <= 1*(d*(w*w))`.
            proof: Some(ibp_polynomial_proof()),
        }];

        let result = ExhaustiveSearch::run(&env, &candidates);
        assert_eq!(result.stats.total_evaluated, 1);
        assert_eq!(
            result.stats.total_verified, 0,
            "well-typed proof of the WRONG statement must be rejected"
        );
        assert!(!result.outcomes[0].verified);
        assert!(
            result.outcomes[0].error.is_some(),
            "rejected candidate must carry an explanatory error"
        );
    }

    /// Sanity: the rejected proof above really IS well-typed on its own, so the
    /// rejection is genuinely due to the def-eq mismatch (not a malformed term).
    #[test]
    fn test_rejected_proof_is_itself_well_typed() {
        let env = pc_env();
        let tc = TypeChecker::new(&env);
        let proof = ibp_polynomial_proof();
        assert!(
            tc.infer_type(&proof).is_ok(),
            "the axiom reference must be well-typed (this is why the OLD verifier accepted it)"
        );
    }

    /// A candidate with no proof term is honestly Unverified (not "verified" via
    /// statement well-formedness).
    #[test]
    fn test_no_proof_is_unverified() {
        let env = Environment::new();
        let candidates = vec![CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            // Prop is a perfectly well-formed type, but no proof is supplied.
            params: ParamVec::new(),
            statement: Expr::prop(),
            proof: None,
        }];

        let result = ExhaustiveSearch::run(&env, &candidates);
        assert_eq!(result.stats.total_evaluated, 1);
        assert_eq!(
            result.stats.total_verified, 0,
            "a statement with no proof is NOT verified"
        );
        assert!(!result.outcomes[0].verified);
        assert!(result.outcomes[0].error.is_some());
    }

    #[test]
    fn test_exhaustive_search_empty_candidates() {
        let env = Environment::new();
        let candidates: Vec<CandidateTheorem> = vec![];

        let result = ExhaustiveSearch::run(&env, &candidates);
        assert_eq!(result.stats.total_evaluated, 0);
        assert_eq!(result.stats.total_verified, 0);
    }

    #[test]
    fn test_exhaustive_search_invalid_proof() {
        let env = Environment::new();

        // A proof referencing a non-existent constant cannot prove anything.
        let candidates = vec![CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement: Expr::prop(),
            proof: Some(Expr::const_str("NonExistent.Const")),
        }];

        let result = ExhaustiveSearch::run(&env, &candidates);
        assert_eq!(result.stats.total_evaluated, 1);
        assert_eq!(result.stats.total_failed, 1);
        assert!(!result.outcomes[0].verified);
        assert!(result.outcomes[0].error.is_some());
    }

    #[test]
    fn test_search_stats_throughput() {
        let stats = SearchStats {
            total_evaluated: 1000,
            total_verified: 100,
            total_failed: 900,
            wall_time_ns: 1_000_000_000, // 1 second
            throughput_per_sec: 1000.0,
        };
        assert_eq!(stats.throughput_per_sec, 1000.0);
    }

    #[test]
    fn test_find_first_valid_returns_genuine_index() {
        let env = pc_env();

        let candidates = vec![
            // Index 0: well-typed proof of the WRONG statement -> rejected.
            CandidateTheorem {
                id: CandidateId(0),
                family: TheoremFamily::CertSizeBound,
                params: ParamVec::new(),
                statement: Expr::prop(), // proof is not a proof of Prop
                proof: Some(ibp_polynomial_proof()),
            },
            // Index 1: genuine proof of its statement -> the first valid one.
            CandidateTheorem {
                id: CandidateId(1),
                family: TheoremFamily::CertSizeBound,
                params: ParamVec::new(),
                statement: ibp_polynomial_statement(),
                proof: Some(ibp_polynomial_proof()),
            },
        ];

        let result = ExhaustiveSearch::find_first_valid(&env, &candidates);
        assert!(result.is_some());
        let (idx, _) = result.unwrap();
        assert_eq!(idx, 1, "must skip the wrong-proof candidate at index 0");
    }
}
