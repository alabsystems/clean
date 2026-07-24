// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DomainTightness (T91) candidate generation for the proof discovery loop.
//!
//! Generates candidates comparing abstract domain tightness for neural network
//! verification. The theorem family searches for results of the form:
//!
//! ```text
//! forall (ibp_cert : IBPCertificate) (zono_cert : ZonotopeCertificate),
//!   LE.le @Nat instLENat (zonotope_cert_size zono_cert) (Nat.mul C (ibp_cert_size ibp_cert))
//! ```
//!
//! Parameters swept: tightness ratio C (1..max_ratio), comparison type
//! (IBP vs Zonotope, IBP vs DeepPoly, Zonotope vs DeepPoly).
//!
//! Part of #3258.

use crate::candidate::{CandidateId, CandidateTheorem, ParamValue, ParamVec};
use crate::family::TheoremFamily;
use clean_kernel::{BinderInfo, Expr};

/// Comparison type for domain tightness candidates.
///
/// Each variant represents a pair of abstract domains whose certificate
/// sizes are compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ComparisonType {
    /// IBP (cheapest) vs Zonotope (moderate): zonotope_cert_size <= C * ibp_cert_size
    IbpVsZonotope,
    /// IBP (cheapest) vs DeepPoly (most expensive): deep_poly_cert_size <= C * ibp_cert_size
    IbpVsDeepPoly,
    /// Zonotope (moderate) vs DeepPoly (most expensive): deep_poly_cert_size <= C * zonotope_cert_size
    ZonotopeVsDeepPoly,
}

impl ComparisonType {
    /// All comparison type variants.
    pub const ALL: &[Self] = &[
        Self::IbpVsZonotope,
        Self::IbpVsDeepPoly,
        Self::ZonotopeVsDeepPoly,
    ];

    /// Returns the certificate type and size function names for the "smaller" domain.
    fn smaller_domain(&self) -> (&str, &str) {
        match self {
            Self::IbpVsZonotope | Self::IbpVsDeepPoly => (
                "NNVerify.ProofComplexity.IBPCertificate",
                "NNVerify.ProofComplexity.ibp_cert_size",
            ),
            Self::ZonotopeVsDeepPoly => (
                "NNVerify.ProofComplexity.ZonotopeCertificate",
                "NNVerify.ProofComplexity.zonotope_cert_size",
            ),
        }
    }

    /// Returns the certificate type and size function names for the "larger" domain.
    fn larger_domain(&self) -> (&str, &str) {
        match self {
            Self::IbpVsZonotope => (
                "NNVerify.ProofComplexity.ZonotopeCertificate",
                "NNVerify.ProofComplexity.zonotope_cert_size",
            ),
            Self::IbpVsDeepPoly | Self::ZonotopeVsDeepPoly => (
                "NNVerify.ProofComplexity.DeepPolyCertificate",
                "NNVerify.ProofComplexity.deep_poly_cert_size",
            ),
        }
    }
}

impl std::fmt::Display for ComparisonType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IbpVsZonotope => write!(f, "IBP_vs_Zonotope"),
            Self::IbpVsDeepPoly => write!(f, "IBP_vs_DeepPoly"),
            Self::ZonotopeVsDeepPoly => write!(f, "Zonotope_vs_DeepPoly"),
        }
    }
}

/// Configuration for the DomainTightness search space.
#[derive(Debug, Clone)]
pub struct DomainTightnessConfig {
    /// Maximum tightness ratio constant C to search (1..=max_ratio).
    pub max_ratio: u64,
    /// Maximum network depth for context parameters (1..=max_depth).
    pub max_depth: u64,
    /// Maximum network width for context parameters (2..=max_width).
    pub max_width: u64,
}

impl Default for DomainTightnessConfig {
    fn default() -> Self {
        Self {
            max_ratio: 8,
            max_depth: 4,
            max_width: 8,
        }
    }
}

impl DomainTightnessConfig {
    /// Total number of candidates in this search space.
    ///
    /// 3 comparison types * max_ratio * max_depth * (max_width - 1)
    /// (width starts at 2, so we have max_width - 1 values).
    pub fn total_candidates(&self) -> u64 {
        let comparisons = ComparisonType::ALL.len() as u64;
        let width_range = self.max_width.saturating_sub(1);
        comparisons * self.max_ratio * self.max_depth * width_range
    }
}

/// Generate all candidate theorems for the DomainTightness family.
///
/// Each candidate claims that the certificate size of the "larger" abstract
/// domain is at most C times the certificate size of the "smaller" domain:
///
/// ```text
/// forall (cert_small : SmallDomainCert) (cert_large : LargeDomainCert),
///   LE.le @Nat instLENat (large_cert_size cert_large) (Nat.mul C (small_cert_size cert_small))
/// ```
///
/// The discovery loop will determine which (comparison_type, C) pairs
/// actually type-check against the kernel's axioms.
pub fn generate_domain_tightness_candidates(
    config: &DomainTightnessConfig,
) -> Vec<CandidateTheorem> {
    let mut candidates = Vec::with_capacity(config.total_candidates() as usize);
    let mut next_id: u64 = 0;

    for (cmp_idx, comparison) in ComparisonType::ALL.iter().enumerate() {
        for ratio in 1..=config.max_ratio {
            for d_min in 1..=config.max_depth {
                for w_min in 2..=config.max_width {
                    let (statement, proof) =
                        build_tightness_candidate(*comparison, ratio, d_min, w_min);

                    candidates.push(CandidateTheorem {
                        id: CandidateId(next_id),
                        family: TheoremFamily::DomainTightness,
                        params: ParamVec(vec![
                            ParamValue::Choice(cmp_idx),
                            ParamValue::Nat(ratio),
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

/// Build a single DomainTightness candidate theorem.
///
/// Statement type:
/// ```text
/// forall (cert_small : SmallDomainCert) (cert_large : LargeDomainCert),
///   LE.le @Nat instLENat (large_cert_size cert_large) (Nat.mul C (small_cert_size cert_small))
/// ```
///
/// The `_d_min` and `_w_min` parameters are reserved for future use as
/// network dimension constraints in the statement body, but are not
/// currently encoded in the forall.
///
/// # Honesty
///
/// The discovery loop has no genuine proof of these `large_cert <= C * small_cert`
/// claims: `cert_hierarchy_axiom` proves the bare hierarchy
/// `ibp <= zonotope <= deep_poly` (wrapped in `And`), which is NOT the type of
/// any candidate statement here (different domains, a `Nat.mul C` multiplier,
/// and a different proposition head). We therefore return `proof: None` for
/// every candidate, so they are honestly reported as Unverified rather than
/// being "verified" by an axiom reference that does not prove them.
pub(crate) fn build_tightness_candidate(
    comparison: ComparisonType,
    ratio: u64,
    _d_min: u64,
    _w_min: u64,
) -> (Expr, Option<Expr>) {
    let nat = Expr::const_str("Nat");
    let le_le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le_nat = Expr::const_str("instLENat");
    let nat_mul = Expr::const_str("Nat.mul");

    let (smaller_cert_type_name, smaller_size_fn_name) = comparison.smaller_domain();
    let (larger_cert_type_name, larger_size_fn_name) = comparison.larger_domain();

    let smaller_cert_type = Expr::const_str(smaller_cert_type_name);
    let smaller_size_fn = Expr::const_str(smaller_size_fn_name);
    let larger_cert_type = Expr::const_str(larger_cert_type_name);
    let larger_size_fn = Expr::const_str(larger_size_fn_name);

    // De Bruijn indices:
    //   cert_small = BVar(1), cert_large = BVar(0)
    let cert_small = Expr::bvar(1);
    let cert_large = Expr::bvar(0);

    // large_cert_size cert_large
    let large_sz = Expr::app(larger_size_fn, cert_large);

    // Nat.mul C (small_cert_size cert_small)
    let small_sz = Expr::app(smaller_size_fn, cert_small);
    let c = Expr::nat_lit(ratio);
    let bound = Expr::apps(nat_mul, [c, small_sz]);

    // LE.le @Nat instLENat (large_cert_size cert_large) (Nat.mul C (small_cert_size cert_small))
    let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, large_sz, bound]);

    // forall (cert_large : LargeDomainCert), le_expr
    let body = Expr::pi(BinderInfo::Default, larger_cert_type, le_expr);
    // forall (cert_small : SmallDomainCert), body
    let statement = Expr::pi(BinderInfo::Default, smaller_cert_type, body);

    // No genuine proof is available for these claims (see fn docs): emit None so
    // the candidate is honestly Unverified rather than "verified" by an axiom
    // reference that does not have this statement as its type.
    (statement, None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_tightness_config_default() {
        let config = DomainTightnessConfig::default();
        assert_eq!(config.max_ratio, 8);
        assert_eq!(config.max_depth, 4);
        assert_eq!(config.max_width, 8);
    }

    #[test]
    fn test_domain_tightness_total_candidates() {
        let config = DomainTightnessConfig {
            max_ratio: 2,
            max_depth: 2,
            max_width: 3,
        };
        // 3 comparisons * 2 ratios * 2 depths * (3 - 1 = 2) widths = 24
        assert_eq!(config.total_candidates(), 24);
    }

    #[test]
    fn test_generate_domain_tightness_candidates_count() {
        let config = DomainTightnessConfig {
            max_ratio: 2,
            max_depth: 2,
            max_width: 3,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        assert_eq!(candidates.len(), config.total_candidates() as usize);
    }

    #[test]
    fn test_candidate_ids_are_sequential() {
        let config = DomainTightnessConfig {
            max_ratio: 1,
            max_depth: 1,
            max_width: 3,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        for (i, c) in candidates.iter().enumerate() {
            assert_eq!(c.id, CandidateId(i as u64));
        }
    }

    #[test]
    fn test_all_candidates_are_domain_tightness_family() {
        let config = DomainTightnessConfig {
            max_ratio: 1,
            max_depth: 1,
            max_width: 2,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        for c in &candidates {
            assert_eq!(c.family, TheoremFamily::DomainTightness);
        }
    }

    #[test]
    fn test_candidate_statement_is_pi_type() {
        let config = DomainTightnessConfig {
            max_ratio: 1,
            max_depth: 1,
            max_width: 2,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        for c in &candidates {
            assert!(c.statement.is_pi(), "statement should be a Pi/forall type");
        }
    }

    #[test]
    fn test_candidates_are_honestly_unproven() {
        let config = DomainTightnessConfig {
            max_ratio: 1,
            max_depth: 1,
            max_width: 2,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        for c in &candidates {
            // The discovery loop has no genuine proof of these tightness claims,
            // so every candidate is honestly emitted WITHOUT a proof term.
            assert!(
                c.proof.is_none(),
                "domain-tightness candidates have no genuine proof -> proof must be None"
            );
        }
    }

    #[test]
    fn test_comparison_type_coverage() {
        let config = DomainTightnessConfig {
            max_ratio: 1,
            max_depth: 1,
            max_width: 2,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        // 3 comparison types * 1 ratio * 1 depth * 1 width = 3 candidates
        assert_eq!(candidates.len(), 3);

        // Verify all comparison types are represented via Choice param
        let choices: Vec<usize> = candidates
            .iter()
            .map(|c| match &c.params.0[0] {
                ParamValue::Choice(i) => *i,
                _ => panic!("expected Choice for comparison type"),
            })
            .collect();
        assert!(choices.contains(&0), "should have IbpVsZonotope");
        assert!(choices.contains(&1), "should have IbpVsDeepPoly");
        assert!(choices.contains(&2), "should have ZonotopeVsDeepPoly");
    }

    #[test]
    fn test_comparison_type_display() {
        assert_eq!(ComparisonType::IbpVsZonotope.to_string(), "IBP_vs_Zonotope");
        assert_eq!(ComparisonType::IbpVsDeepPoly.to_string(), "IBP_vs_DeepPoly");
        assert_eq!(
            ComparisonType::ZonotopeVsDeepPoly.to_string(),
            "Zonotope_vs_DeepPoly"
        );
    }

    #[test]
    fn test_build_tightness_candidate_ibp_vs_zonotope() {
        let (statement, proof) = build_tightness_candidate(ComparisonType::IbpVsZonotope, 3, 1, 2);
        assert!(statement.is_pi(), "statement should be forall (Pi type)");
        assert!(proof.is_none(), "no genuine proof -> proof must be None");
    }

    #[test]
    fn test_build_tightness_candidate_ibp_vs_deep_poly() {
        let (statement, proof) = build_tightness_candidate(ComparisonType::IbpVsDeepPoly, 5, 2, 4);
        assert!(statement.is_pi(), "statement should be forall (Pi type)");
        assert!(proof.is_none(), "no genuine proof -> proof must be None");
    }

    #[test]
    fn test_build_tightness_candidate_zonotope_vs_deep_poly() {
        let (statement, proof) =
            build_tightness_candidate(ComparisonType::ZonotopeVsDeepPoly, 1, 1, 2);
        assert!(statement.is_pi(), "statement should be forall (Pi type)");
        assert!(proof.is_none(), "no genuine proof -> proof must be None");
    }

    #[test]
    fn test_smaller_domain_names() {
        let (cert, size) = ComparisonType::IbpVsZonotope.smaller_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.IBPCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.ibp_cert_size");

        let (cert, size) = ComparisonType::IbpVsDeepPoly.smaller_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.IBPCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.ibp_cert_size");

        let (cert, size) = ComparisonType::ZonotopeVsDeepPoly.smaller_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.ZonotopeCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.zonotope_cert_size");
    }

    #[test]
    fn test_larger_domain_names() {
        let (cert, size) = ComparisonType::IbpVsZonotope.larger_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.ZonotopeCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.zonotope_cert_size");

        let (cert, size) = ComparisonType::IbpVsDeepPoly.larger_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.DeepPolyCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.deep_poly_cert_size");

        let (cert, size) = ComparisonType::ZonotopeVsDeepPoly.larger_domain();
        assert_eq!(cert, "NNVerify.ProofComplexity.DeepPolyCertificate");
        assert_eq!(size, "NNVerify.ProofComplexity.deep_poly_cert_size");
    }

    #[test]
    fn test_zero_width_range_produces_no_candidates() {
        let config = DomainTightnessConfig {
            max_ratio: 2,
            max_depth: 2,
            max_width: 1, // width starts at 2, so 1 means 0 values
        };
        assert_eq!(config.total_candidates(), 0);
        let candidates = generate_domain_tightness_candidates(&config);
        assert!(candidates.is_empty());
    }

    #[test]
    fn test_params_encode_all_dimensions() {
        let config = DomainTightnessConfig {
            max_ratio: 2,
            max_depth: 1,
            max_width: 3,
        };
        let candidates = generate_domain_tightness_candidates(&config);
        for c in &candidates {
            assert_eq!(
                c.params.0.len(),
                4,
                "should have 4 params: comparison, ratio, depth, width"
            );
        }
    }
}
