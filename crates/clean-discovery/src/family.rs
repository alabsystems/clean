// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem family definitions and candidate generators.
//!
//! Each `TheoremFamily` variant defines a parameterized search space of
//! candidate theorems. The generator produces `CandidateTheorem` instances
//! by iterating over all parameter combinations.
//!
//! ## Family 1: Certificate Size Bounds (T90)
//!
//! Searches for the tightest constant C such that:
//! ```text
//! forall (d w : Nat) (cert : IBPCertificate),
//!   ibp_cert_size(cert) <= C * d * w^2
//! ```
//!
//! Part of #3258.

use crate::candidate::{CandidateId, CandidateTheorem, ParamValue, ParamVec};
use clean_kernel::{BinderInfo, Expr};

/// Theorem family identifier.
///
/// Each variant represents a class of parameterized theorems about
/// neural network verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TheoremFamily {
    /// Certificate size upper bounds: ibp_cert_size <= f(d, w).
    /// Parameters: (depth_min, width_min, constant_C, bound_function_variant).
    CertSizeBound,
    /// Domain tightness comparisons (Phase B).
    DomainTightness,
    /// Verification complexity results (Phase C).
    VerificationComplexity,
    /// New abstract domain constructions (Phase D).
    NewAbstractDomain,
}

impl std::fmt::Display for TheoremFamily {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CertSizeBound => write!(f, "CertSizeBound"),
            Self::DomainTightness => write!(f, "DomainTightness"),
            Self::VerificationComplexity => write!(f, "VerificationComplexity"),
            Self::NewAbstractDomain => write!(f, "NewAbstractDomain"),
        }
    }
}

/// Bound function variants for certificate size bounds.
///
/// Each variant represents a different polynomial bound function f(d, w).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundFunction {
    /// C * d * w
    Linear,
    /// C * d * w^2
    QuadraticWidth,
    /// C * d^2 * w
    QuadraticDepth,
    /// C * d^2 * w^2
    QuadraticBoth,
}

impl BoundFunction {
    /// All bound function variants.
    pub(crate) const ALL: &[Self] = &[
        Self::Linear,
        Self::QuadraticWidth,
        Self::QuadraticDepth,
        Self::QuadraticBoth,
    ];

    /// Build the bound expression: f(d, w) * C using kernel Expr constructors.
    ///
    /// `d`, `w` are bound variable references, `c_val` is a Nat literal for C.
    pub(crate) fn build_bound_expr(&self, d: Expr, w: Expr, c_val: u64) -> Expr {
        let nat_mul = Expr::const_str("Nat.mul");
        let c = Expr::nat_lit(c_val);

        match self {
            // C * d * w
            Self::Linear => {
                let dw = Expr::apps(nat_mul.clone(), [d, w]);
                Expr::apps(nat_mul, [c, dw])
            }
            // C * d * w^2
            Self::QuadraticWidth => {
                let w_sq = Expr::apps(nat_mul.clone(), [w.clone(), w]);
                let d_w_sq = Expr::apps(nat_mul.clone(), [d, w_sq]);
                Expr::apps(nat_mul, [c, d_w_sq])
            }
            // C * d^2 * w
            Self::QuadraticDepth => {
                let d_sq = Expr::apps(nat_mul.clone(), [d.clone(), d]);
                let d_sq_w = Expr::apps(nat_mul.clone(), [d_sq, w]);
                Expr::apps(nat_mul, [c, d_sq_w])
            }
            // C * d^2 * w^2
            Self::QuadraticBoth => {
                let d_sq = Expr::apps(nat_mul.clone(), [d.clone(), d]);
                let w_sq = Expr::apps(nat_mul.clone(), [w.clone(), w]);
                let d_sq_w_sq = Expr::apps(nat_mul.clone(), [d_sq, w_sq]);
                Expr::apps(nat_mul, [c, d_sq_w_sq])
            }
        }
    }

    /// Build the bound expression `d * (w * w)` WITHOUT a leading constant
    /// multiplier — i.e. exactly the shape proven by
    /// `NNVerify.ProofComplexity.ibp_cert_polynomial_axiom`.
    ///
    /// This is used to emit the ONE candidate in the `CertSizeBound` family for
    /// which we have a genuine kernel proof. We cannot honestly reuse
    /// [`Self::build_bound_expr`] here because that wraps the bound in
    /// `Nat.mul C (...)`; `Nat.mul` is an axiom (not reducible) in the discovery
    /// environment, so even `Nat.mul 1 x` is NOT definitionally equal to `x` and
    /// the axiom would fail to prove the wrapped statement.
    fn build_bare_quadratic_width(d: Expr, w: Expr) -> Expr {
        let nat_mul = Expr::const_str("Nat.mul");
        let w_sq = Expr::apps(nat_mul.clone(), [w.clone(), w]);
        Expr::apps(nat_mul, [d, w_sq])
    }
}

/// Configuration for the CertSizeBound search space.
#[derive(Debug, Clone)]
pub struct CertSizeBoundConfig {
    /// Maximum depth parameter to search.
    pub max_depth: u64,
    /// Maximum width parameter to search.
    pub max_width: u64,
    /// Maximum constant C to search.
    pub max_c: u64,
}

impl Default for CertSizeBoundConfig {
    fn default() -> Self {
        Self {
            max_depth: 5,
            max_width: 5,
            max_c: 5,
        }
    }
}

impl CertSizeBoundConfig {
    /// Total number of candidates in this search space.
    pub fn total_candidates(&self) -> u64 {
        let bound_fns = BoundFunction::ALL.len() as u64;
        bound_fns * self.max_c * self.max_depth * self.max_width
    }
}

/// Generate all candidate theorems for the CertSizeBound family.
///
/// Each candidate claims:
/// ```text
/// forall (d w : Nat) (cert : IBPCertificate),
///   LE.le (ibp_cert_size cert) (f(d, w, C))
/// ```
///
/// where f is one of the bound functions and C is a constant.
///
/// # Honesty
///
/// A candidate carries a proof term **only** when the discovery loop can
/// construct a genuine kernel proof of its statement. Currently that is the
/// single case `QuadraticWidth` with `C = 1`, whose statement is exactly the
/// type of `NNVerify.ProofComplexity.ibp_cert_polynomial_axiom` (the bound
/// `ibp_cert_size cert <= d * (w * w)`). Every other `(bound_fn, C)` candidate
/// is emitted with `proof: None` and is therefore honestly reported as
/// Unverified — we do NOT attach an axiom reference that fails to prove the
/// claim. (The earlier implementation hard-coded the polynomial axiom as the
/// "proof" of every candidate, which the genuine verifier now rejects.)
pub fn generate_cert_size_candidates(config: &CertSizeBoundConfig) -> Vec<CandidateTheorem> {
    let mut candidates = Vec::with_capacity(config.total_candidates() as usize);
    let mut next_id: u64 = 0;

    for (bf_idx, bound_fn) in BoundFunction::ALL.iter().enumerate() {
        for c_val in 1..=config.max_c {
            for d_min in 1..=config.max_depth {
                for w_min in 1..=config.max_width {
                    let (statement, proof) =
                        build_cert_size_bound_candidate(*bound_fn, c_val, d_min, w_min);

                    candidates.push(CandidateTheorem {
                        id: CandidateId(next_id),
                        family: TheoremFamily::CertSizeBound,
                        params: ParamVec(vec![
                            ParamValue::Choice(bf_idx),
                            ParamValue::Nat(c_val),
                            ParamValue::Nat(d_min),
                            ParamValue::Nat(w_min),
                        ]),
                        statement,
                        proof,
                    });
                    next_id += 1;
                }
            }
        }
    }

    candidates
}

/// Returns `true` when the discovery loop has a genuine kernel proof for the
/// `(bound_fn, C)` certificate-size bound.
///
/// The only proof currently available is `ibp_cert_polynomial_axiom`, which
/// proves the bound `ibp_cert_size cert <= d * (w * w)` — i.e. `QuadraticWidth`
/// with `C = 1`.
fn has_genuine_proof(bound_fn: BoundFunction, c_val: u64) -> bool {
    bound_fn == BoundFunction::QuadraticWidth && c_val == 1
}

/// Build a single CertSizeBound candidate theorem.
///
/// Statement type:
/// ```text
/// forall (d w : Nat) (cert : IBPCertificate),
///   LE.le @Nat instLENat (ibp_cert_size cert) (bound_fn(d, w, C))
/// ```
///
/// Returns `(statement, proof)` where `proof` is `Some(..)` only when a genuine
/// kernel proof exists for this `(bound_fn, C)` pair (see [`has_genuine_proof`]).
///
/// For the genuine case the statement is built with the bare `d * (w * w)` bound
/// (no leading `Nat.mul C`), matching the axiom's type exactly so the kernel's
/// `is_def_eq` accepts the axiom as a proof. For all other pairs the statement
/// keeps its `Nat.mul C (...)` form and the proof is `None`.
fn build_cert_size_bound_candidate(
    bound_fn: BoundFunction,
    c_val: u64,
    _d_min: u64,
    _w_min: u64,
) -> (Expr, Option<Expr>) {
    let nat = Expr::const_str("Nat");
    let ibp_cert = Expr::const_str("NNVerify.ProofComplexity.IBPCertificate");
    let ibp_cert_size = Expr::const_str("NNVerify.ProofComplexity.ibp_cert_size");
    let le_le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le_nat = Expr::const_str("instLENat");

    // Build: forall (d w : Nat) (cert : IBPCertificate), ...
    // Using de Bruijn indices:
    //   d = BVar(2), w = BVar(1), cert = BVar(0)

    let d = Expr::bvar(2);
    let w = Expr::bvar(1);
    let cert = Expr::bvar(0);

    // ibp_cert_size cert
    let cert_sz = Expr::app(ibp_cert_size, cert);

    let genuine = has_genuine_proof(bound_fn, c_val);

    // For the genuine case, build the bound EXACTLY as the axiom states it
    // (`d * (w * w)`, no leading constant) so the kernel accepts the axiom as a
    // proof. Otherwise, build the parameterized `bound_fn(d, w, C)` bound.
    let bound = if genuine {
        BoundFunction::build_bare_quadratic_width(d, w)
    } else {
        bound_fn.build_bound_expr(d, w, c_val)
    };

    // LE.le @Nat instLENat (ibp_cert_size cert) bound
    let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);

    // forall (cert : IBPCertificate), le_expr
    let body = Expr::pi(BinderInfo::Default, ibp_cert, le_expr);
    // forall (w : Nat), body
    let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
    // forall (d : Nat), body
    let statement = Expr::pi(BinderInfo::Default, nat, body);

    // Proof: only attach the polynomial axiom when it genuinely proves the
    // statement. Never attach an axiom reference that does not have the
    // statement as its type.
    let proof = if genuine {
        Some(Expr::const_str(
            "NNVerify.ProofComplexity.ibp_cert_polynomial_axiom",
        ))
    } else {
        None
    };

    (statement, proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_theorem_family_display() {
        assert_eq!(TheoremFamily::CertSizeBound.to_string(), "CertSizeBound");
        assert_eq!(
            TheoremFamily::DomainTightness.to_string(),
            "DomainTightness"
        );
    }

    #[test]
    fn test_cert_size_bound_config_default() {
        let config = CertSizeBoundConfig::default();
        assert_eq!(config.max_depth, 5);
        assert_eq!(config.max_width, 5);
        assert_eq!(config.max_c, 5);
    }

    #[test]
    fn test_cert_size_bound_total_candidates() {
        let config = CertSizeBoundConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 2,
        };
        // 4 bound functions * 2 C values * 2 depths * 2 widths = 32
        assert_eq!(config.total_candidates(), 32);
    }

    #[test]
    fn test_generate_cert_size_candidates_count() {
        let config = CertSizeBoundConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 2,
        };
        let candidates = generate_cert_size_candidates(&config);
        assert_eq!(candidates.len(), 32);
    }

    #[test]
    fn test_candidate_ids_are_sequential() {
        let config = CertSizeBoundConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 1,
        };
        let candidates = generate_cert_size_candidates(&config);
        for (i, c) in candidates.iter().enumerate() {
            assert_eq!(c.id, CandidateId(i as u64));
        }
    }

    #[test]
    fn test_candidate_statement_is_pi_type() {
        let config = CertSizeBoundConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
        };
        let candidates = generate_cert_size_candidates(&config);
        // Every candidate statement should be a Pi type (forall ...)
        for c in &candidates {
            assert!(c.statement.is_pi(), "statement should be a Pi/forall type");
        }
    }

    #[test]
    fn test_bound_function_build_expr_is_app() {
        let d = Expr::bvar(1);
        let w = Expr::bvar(0);

        for bf in BoundFunction::ALL {
            let expr = bf.build_bound_expr(d.clone(), w.clone(), 3);
            assert!(
                expr.is_app(),
                "bound expr for {bf:?} should be an application"
            );
        }
    }

    #[test]
    fn test_only_genuine_candidate_carries_a_proof() {
        // QuadraticWidth + C=1 is the only case with a genuine kernel proof.
        let (_, proof) = build_cert_size_bound_candidate(BoundFunction::QuadraticWidth, 1, 1, 1);
        assert!(
            proof.is_some(),
            "QuadraticWidth with C=1 must carry the polynomial-axiom proof"
        );

        // Any other (bound_fn, C) is honestly unproven.
        let (_, no_proof) = build_cert_size_bound_candidate(BoundFunction::Linear, 1, 1, 1);
        assert!(
            no_proof.is_none(),
            "Linear bound has no genuine proof -> proof must be None"
        );
        let (_, no_proof_c2) =
            build_cert_size_bound_candidate(BoundFunction::QuadraticWidth, 2, 1, 1);
        assert!(
            no_proof_c2.is_none(),
            "QuadraticWidth with C=2 has no genuine proof -> proof must be None"
        );
    }

    #[test]
    fn test_generated_candidates_have_proof_only_when_genuine() {
        let config = CertSizeBoundConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 2,
        };
        let candidates = generate_cert_size_candidates(&config);
        // Exactly one (bf, C, d, w) combination is genuine: QuadraticWidth, C=1.
        let with_proof = candidates.iter().filter(|c| c.proof.is_some()).count();
        assert_eq!(
            with_proof, 1,
            "exactly one generated candidate should carry a genuine proof"
        );
    }
}
