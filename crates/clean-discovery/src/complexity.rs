// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VerificationComplexity theorem family: architecture-specific certificate
//! size bounds.
//!
//! The core claim for each candidate:
//! ```text
//! forall (d w : Nat) (cert : IBPCertificate),
//!   LE.le @Nat instLENat (ibp_cert_size cert) (f_arch(d, w))
//! ```
//!
//! where `f_arch` varies by architecture type. The hypothesis is that
//! specialized architectures (skip connections, bottleneck, residual) admit
//! tighter certificate size bounds than the general `C * d * w^2` bound.
//!
//! For each architecture type, ALL `BoundFunction` variants are tried.
//! The kernel determines which bounds actually type-check; the interesting
//! results are when a weaker bound function (e.g., `Linear`) type-checks
//! for a specific architecture.
//!
//! Part of #3270.

use crate::candidate::{CandidateId, CandidateTheorem, ParamValue, ParamVec};
use crate::family::{BoundFunction, TheoremFamily};
use clean_kernel::{BinderInfo, Expr};

/// Neural network architecture types with different verification complexity
/// characteristics.
///
/// Each architecture has a hypothesized certificate size bound function
/// that may be tighter than the general IBP bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArchitectureType {
    /// Standard feedforward network. Bound: `C * d * w^2` (same as general IBP).
    Plain,
    /// Network with skip connections. Hypothesis: `C * d * w` (linear in width).
    SkipConnection,
    /// Network with bottleneck layers. Hypothesis: `C * d * w` (bottleneck
    /// width dominates, so effective width is smaller).
    Bottleneck,
    /// Residual network. Hypothesis: `C * d * w` for small depth
    /// (residual connections reduce depth dependence).
    Residual,
}

impl ArchitectureType {
    /// All architecture type variants for iteration.
    pub const ALL: &[Self] = &[
        Self::Plain,
        Self::SkipConnection,
        Self::Bottleneck,
        Self::Residual,
    ];
}

impl std::fmt::Display for ArchitectureType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Plain => write!(f, "Plain"),
            Self::SkipConnection => write!(f, "SkipConnection"),
            Self::Bottleneck => write!(f, "Bottleneck"),
            Self::Residual => write!(f, "Residual"),
        }
    }
}

/// Configuration for the VerificationComplexity search space.
#[derive(Debug, Clone)]
pub struct VerificationComplexityConfig {
    /// Maximum depth parameter to search.
    pub max_depth: u64,
    /// Maximum width parameter to search.
    pub max_width: u64,
    /// Maximum constant C to search.
    pub max_c: u64,
    /// Architecture types to include in the search.
    pub architectures: Vec<ArchitectureType>,
}

impl Default for VerificationComplexityConfig {
    fn default() -> Self {
        Self {
            max_depth: 4,
            max_width: 6,
            max_c: 3,
            architectures: ArchitectureType::ALL.to_vec(),
        }
    }
}

impl VerificationComplexityConfig {
    /// Total number of candidates in this search space.
    pub fn total_candidates(&self) -> u64 {
        let arch_count = self.architectures.len() as u64;
        let bound_fns = BoundFunction::ALL.len() as u64;
        arch_count * bound_fns * self.max_c * self.max_depth * self.max_width
    }
}

/// Generate all candidate theorems for the VerificationComplexity family.
///
/// For each combination of (architecture, bound_function, C, depth, width),
/// produces a candidate claiming:
/// ```text
/// forall (d w : Nat) (cert : IBPCertificate),
///   LE.le @Nat instLENat (ibp_cert_size cert) (bound_fn(d, w) * C)
/// ```
///
/// The proof term references an architecture-specific axiom so the kernel
/// can accept or reject each candidate.
pub(crate) fn generate_verification_complexity_candidates(
    config: &VerificationComplexityConfig,
) -> Vec<CandidateTheorem> {
    let mut candidates = Vec::with_capacity(config.total_candidates() as usize);
    let mut next_id: u64 = 0;

    for (arch_idx, arch) in config.architectures.iter().enumerate() {
        for (bf_idx, bound_fn) in BoundFunction::ALL.iter().enumerate() {
            for c_val in 1..=config.max_c {
                for d_min in 1..=config.max_depth {
                    for w_min in 1..=config.max_width {
                        let (statement, proof) =
                            build_complexity_candidate(*arch, *bound_fn, c_val, d_min, w_min);

                        candidates.push(CandidateTheorem {
                            id: CandidateId(next_id),
                            family: TheoremFamily::VerificationComplexity,
                            params: ParamVec(vec![
                                ParamValue::Choice(arch_idx),
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
    }

    candidates
}

/// Build a single VerificationComplexity candidate theorem.
///
/// Statement type:
/// ```text
/// forall (d w : Nat) (cert : IBPCertificate),
///   LE.le @Nat instLENat (ibp_cert_size cert) (bound_fn(d, w) * C)
/// ```
///
/// # Honesty
///
/// The architecture-specific `ibp_cert_<arch>_axiom`s are all registered with
/// the SAME type (`ibp_cert_size cert <= d * (w * w)`); none of them has the
/// candidate's `bound_fn(d, w) * C` statement as its type (the candidate wraps
/// the bound in `Nat.mul C`, which is not definitionally equal to the axiom's
/// bare bound). We therefore return `proof: None`: these candidates are honestly
/// reported as Unverified rather than "verified" by an axiom that does not prove
/// them. The `arch` argument is retained for the parameter encoding only.
fn build_complexity_candidate(
    _arch: ArchitectureType,
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

    // De Bruijn indices: d = BVar(2), w = BVar(1), cert = BVar(0)
    let d = Expr::bvar(2);
    let w = Expr::bvar(1);
    let cert = Expr::bvar(0);

    // ibp_cert_size cert
    let cert_sz = Expr::app(ibp_cert_size, cert);

    // bound_fn(d, w, C) — reuses BoundFunction::build_bound_expr from family.rs
    let bound = bound_fn.build_bound_expr(d, w, c_val);

    // LE.le @Nat instLENat (ibp_cert_size cert) bound
    let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);

    // forall (cert : IBPCertificate), le_expr
    let body = Expr::pi(BinderInfo::Default, ibp_cert, le_expr);
    // forall (w : Nat), body
    let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
    // forall (d : Nat), body
    let statement = Expr::pi(BinderInfo::Default, nat, body);

    // No genuine proof exists for these architecture-specific bounds (see fn
    // docs): emit None so the candidate is honestly Unverified.
    (statement, None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_architecture_type_all_count() {
        assert_eq!(ArchitectureType::ALL.len(), 4);
    }

    #[test]
    fn test_architecture_type_display() {
        assert_eq!(ArchitectureType::Plain.to_string(), "Plain");
        assert_eq!(
            ArchitectureType::SkipConnection.to_string(),
            "SkipConnection"
        );
        assert_eq!(ArchitectureType::Bottleneck.to_string(), "Bottleneck");
        assert_eq!(ArchitectureType::Residual.to_string(), "Residual");
    }

    #[test]
    fn test_verification_complexity_config_default() {
        let config = VerificationComplexityConfig::default();
        assert_eq!(config.max_depth, 4);
        assert_eq!(config.max_width, 6);
        assert_eq!(config.max_c, 3);
        assert_eq!(config.architectures.len(), 4);
    }

    #[test]
    fn test_verification_complexity_total_candidates() {
        let config = VerificationComplexityConfig {
            max_depth: 2,
            max_width: 3,
            max_c: 1,
            architectures: ArchitectureType::ALL.to_vec(),
        };
        // 4 architectures * 4 bound functions * 1 C * 2 depths * 3 widths = 96
        assert_eq!(config.total_candidates(), 96);
    }

    #[test]
    fn test_verification_complexity_total_candidates_subset() {
        let config = VerificationComplexityConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 2,
            architectures: vec![ArchitectureType::Plain, ArchitectureType::Residual],
        };
        // 2 architectures * 4 bound functions * 2 C * 2 depths * 2 widths = 64
        assert_eq!(config.total_candidates(), 64);
    }

    #[test]
    fn test_generate_candidates_count() {
        let config = VerificationComplexityConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 1,
            architectures: ArchitectureType::ALL.to_vec(),
        };
        let candidates = generate_verification_complexity_candidates(&config);
        assert_eq!(candidates.len(), config.total_candidates() as usize);
    }

    #[test]
    fn test_generate_candidates_ids_sequential() {
        let config = VerificationComplexityConfig {
            max_depth: 2,
            max_width: 2,
            max_c: 1,
            architectures: vec![ArchitectureType::Plain],
        };
        let candidates = generate_verification_complexity_candidates(&config);
        for (i, c) in candidates.iter().enumerate() {
            assert_eq!(c.id, CandidateId(i as u64));
        }
    }

    #[test]
    fn test_generate_candidates_all_verification_complexity_family() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: ArchitectureType::ALL.to_vec(),
        };
        let candidates = generate_verification_complexity_candidates(&config);
        for c in &candidates {
            assert_eq!(c.family, TheoremFamily::VerificationComplexity);
        }
    }

    #[test]
    fn test_generate_candidates_are_honestly_unproven() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: vec![ArchitectureType::SkipConnection],
        };
        let candidates = generate_verification_complexity_candidates(&config);
        for c in &candidates {
            // No genuine proof exists for these architecture-specific bounds, so
            // every candidate is honestly emitted WITHOUT a proof term.
            assert!(
                c.proof.is_none(),
                "complexity candidates have no genuine proof -> proof must be None"
            );
        }
    }

    #[test]
    fn test_generate_candidates_statements_are_pi_types() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: ArchitectureType::ALL.to_vec(),
        };
        let candidates = generate_verification_complexity_candidates(&config);
        for c in &candidates {
            assert!(c.statement.is_pi(), "statement should be a Pi/forall type");
        }
    }

    #[test]
    fn test_generate_candidates_architecture_coverage() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: ArchitectureType::ALL.to_vec(),
        };
        let candidates = generate_verification_complexity_candidates(&config);

        // With 4 archs * 4 bound fns * 1 C * 1 d * 1 w = 16 candidates
        assert_eq!(candidates.len(), 16);

        // Each architecture should have exactly 4 candidates (one per bound fn)
        for arch_idx in 0..4 {
            let arch_count = candidates
                .iter()
                .filter(|c| matches!(c.params.0[0], ParamValue::Choice(idx) if idx == arch_idx))
                .count();
            assert_eq!(
                arch_count, 4,
                "architecture index {arch_idx} should have 4 candidates (one per bound fn)"
            );
        }
    }

    #[test]
    fn test_generate_candidates_bound_function_coverage() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: vec![ArchitectureType::Plain],
        };
        let candidates = generate_verification_complexity_candidates(&config);

        // 1 arch * 4 bound fns * 1 C * 1 d * 1 w = 4 candidates
        assert_eq!(candidates.len(), 4);

        // Each bound function variant should appear once
        for bf_idx in 0..4 {
            let bf_count = candidates
                .iter()
                .filter(|c| matches!(c.params.0[1], ParamValue::Choice(idx) if idx == bf_idx))
                .count();
            assert_eq!(
                bf_count, 1,
                "bound function index {bf_idx} should appear exactly once"
            );
        }
    }

    #[test]
    fn test_build_complexity_candidate_plain() {
        let (statement, proof) = build_complexity_candidate(
            ArchitectureType::Plain,
            BoundFunction::QuadraticWidth,
            2,
            1,
            1,
        );
        assert!(statement.is_pi());
        assert!(proof.is_none(), "no genuine proof -> proof must be None");
    }

    #[test]
    fn test_build_complexity_candidate_skip() {
        let (statement, proof) = build_complexity_candidate(
            ArchitectureType::SkipConnection,
            BoundFunction::Linear,
            1,
            1,
            1,
        );
        assert!(statement.is_pi());
        assert!(proof.is_none(), "no genuine proof -> proof must be None");
    }

    #[test]
    fn test_params_structure() {
        let config = VerificationComplexityConfig {
            max_depth: 1,
            max_width: 1,
            max_c: 1,
            architectures: vec![ArchitectureType::Bottleneck],
        };
        let candidates = generate_verification_complexity_candidates(&config);
        let c = &candidates[0];

        // params: [arch_choice, bf_choice, c_val, d_min, w_min]
        assert_eq!(c.params.0.len(), 5);
        assert!(matches!(c.params.0[0], ParamValue::Choice(0))); // First (only) arch in config
        assert!(matches!(c.params.0[1], ParamValue::Choice(0))); // First bound fn
        assert!(matches!(c.params.0[2], ParamValue::Nat(1))); // c_val = 1
        assert!(matches!(c.params.0[3], ParamValue::Nat(1))); // d_min = 1
        assert!(matches!(c.params.0[4], ParamValue::Nat(1))); // w_min = 1
    }

    #[test]
    fn test_empty_architectures_produces_no_candidates() {
        let config = VerificationComplexityConfig {
            max_depth: 3,
            max_width: 3,
            max_c: 2,
            architectures: vec![],
        };
        let candidates = generate_verification_complexity_candidates(&config);
        assert!(candidates.is_empty());
        assert_eq!(config.total_candidates(), 0);
    }

    #[test]
    fn test_default_config_total_candidates() {
        let config = VerificationComplexityConfig::default();
        // 4 archs * 4 bound fns * 3 C * 4 depths * 6 widths = 1152
        assert_eq!(config.total_candidates(), 1152);
    }
}
