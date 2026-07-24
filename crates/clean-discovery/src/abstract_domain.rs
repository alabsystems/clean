// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NewAbstractDomain theorem family: candidate generation for novel abstract
//! domain constructions with machine-checked soundness proofs.
//!
//! Each candidate expresses a certificate size bound for a hypothetical
//! abstract domain parameterized by a [`DomainShape`]. The kernel verifies
//! whether the bound claim type-checks given the axioms about
//! `CertificateSize` and `NetworkComplexity`.
//!
//! ## Domain Shape Families
//!
//! - **KCorrelation(k)** — domain with k-dimensional linear correlations.
//!   k=0 is IBP (no correlations), k=1 is zonotope-like.
//! - **PiecewiseLinear(m)** — m piecewise-linear segments per neuron for
//!   ReLU approximation. m=1 is IBP, m=2 is DeepPoly-like.
//! - **Hybrid(k, m)** — combines k-correlation with m-segment piecewise-linear.
//!
//! Part of #3258.

use crate::candidate::{CandidateId, CandidateTheorem, ParamValue, ParamVec};
use crate::family::TheoremFamily;
use clean_kernel::{BinderInfo, Expr, Level};

/// Shape of a hypothetical abstract domain.
///
/// Each variant defines how the domain's certificate size scales relative
/// to IBP's certificate size on the same network.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum DomainShape {
    /// k-dimensional linear correlations between neurons.
    /// k=0 is IBP, k=1 is zonotope-like. Higher k = tighter but costlier.
    KCorrelation { k: u64 },
    /// Piecewise-linear ReLU approximation with `segments` segments per neuron.
    /// segments=1 is IBP, segments=2 is DeepPoly-like.
    PiecewiseLinear { segments: u64 },
    /// Combines k-correlation with piecewise-linear segments.
    Hybrid { k: u64, segments: u64 },
}

impl DomainShape {
    /// Build the certificate-size expression for this domain shape applied
    /// to network complexity `net_dw`.
    ///
    /// Returns `CertificateSize(scale_factor * net_dw)` where `scale_factor`
    /// depends on the domain shape parameters.
    fn build_domain_cert_size(&self, net_dw: Expr) -> Expr {
        let nat_mul = Expr::const_str("Nat.mul");
        let nat_add = Expr::const_str("Nat.add");
        let cert_size = Expr::const_str("NNVerify.ProofComplexity.CertificateSize");

        let scaled = match *self {
            // KCorrelation(k): certificate size scales as k * NetworkComplexity(d, w)
            Self::KCorrelation { k } => {
                if k <= 1 {
                    // k=0 or k=1: CertificateSize(net_dw) — no multiplier needed
                    net_dw
                } else {
                    Expr::apps(nat_mul, [Expr::nat_lit(k), net_dw])
                }
            }
            // PiecewiseLinear(m): scales as m * NetworkComplexity(d, w)
            Self::PiecewiseLinear { segments } => {
                if segments <= 1 {
                    net_dw
                } else {
                    Expr::apps(nat_mul, [Expr::nat_lit(segments), net_dw])
                }
            }
            // Hybrid(k, m): scales as (k + m) * NetworkComplexity(d, w)
            Self::Hybrid { k, segments } => {
                let sum = Expr::apps(nat_add, [Expr::nat_lit(k), Expr::nat_lit(segments)]);
                Expr::apps(nat_mul, [sum, net_dw])
            }
        };

        Expr::app(cert_size, scaled)
    }

    /// Short name for display and param labeling.
    fn variant_index(&self) -> usize {
        match self {
            Self::KCorrelation { .. } => 0,
            Self::PiecewiseLinear { .. } => 1,
            Self::Hybrid { .. } => 2,
        }
    }
}

/// Configuration for the NewAbstractDomain search space.
#[derive(Debug, Clone)]
pub struct AbstractDomainConfig {
    /// Maximum k for KCorrelation domains (k=1..max_k).
    pub max_k: u64,
    /// Maximum segments for PiecewiseLinear domains (m=1..max_segments).
    pub max_segments: u64,
    /// Maximum network depth parameter to sweep.
    pub max_depth: u64,
    /// Maximum network width parameter to sweep.
    pub max_width: u64,
    /// Maximum constant C in the bound ratio (C=1..max_c).
    pub max_c: u64,
}

impl Default for AbstractDomainConfig {
    fn default() -> Self {
        Self {
            max_k: 3,
            max_segments: 3,
            max_depth: 3,
            max_width: 4,
            max_c: 4,
        }
    }
}

impl AbstractDomainConfig {
    /// Enumerate all domain shapes from the configuration.
    fn domain_shapes(&self) -> Vec<DomainShape> {
        let mut shapes = Vec::new();

        // KCorrelation: k=1..max_k
        for k in 1..=self.max_k {
            shapes.push(DomainShape::KCorrelation { k });
        }

        // PiecewiseLinear: m=1..max_segments
        for m in 1..=self.max_segments {
            shapes.push(DomainShape::PiecewiseLinear { segments: m });
        }

        // Hybrid: all (k, m) combinations with k >= 1, m >= 1
        for k in 1..=self.max_k {
            for m in 1..=self.max_segments {
                shapes.push(DomainShape::Hybrid { k, segments: m });
            }
        }

        shapes
    }

    /// Total number of candidates in this search space.
    pub fn total_candidates(&self) -> u64 {
        let shapes = self.domain_shapes().len() as u64;
        shapes * self.max_c * self.max_depth * self.max_width
    }
}

/// Generate all candidate theorems for the NewAbstractDomain family.
///
/// Each candidate claims:
/// ```text
/// forall (d w : Nat),
///   LE.le @Nat instLENat
///     (CertificateSize (shape_scale * NetworkComplexity d w))
///     (Nat.mul C (CertificateSize (NetworkComplexity d w)))
/// ```
///
/// This says: a domain with the given shape has certificate size at most
/// C times the IBP certificate size on the same network(d, w).
pub fn generate_abstract_domain_candidates(config: &AbstractDomainConfig) -> Vec<CandidateTheorem> {
    let shapes = config.domain_shapes();
    let capacity = config.total_candidates() as usize;
    let mut candidates = Vec::with_capacity(capacity);
    let mut next_id: u64 = 0;

    for shape in &shapes {
        for c_val in 1..=config.max_c {
            for d_val in 1..=config.max_depth {
                for w_val in 1..=config.max_width {
                    let statement = build_abstract_domain_statement(*shape, c_val);
                    let proof = build_abstract_domain_proof(*shape, c_val, d_val, w_val);

                    let params = build_params(*shape, c_val, d_val, w_val);

                    candidates.push(CandidateTheorem {
                        id: CandidateId(next_id),
                        family: TheoremFamily::NewAbstractDomain,
                        params,
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

/// Build the universally quantified statement for a domain-shape candidate.
///
/// ```text
/// forall (d w : Nat),
///   LE.le @Nat instLENat
///     (CertificateSize (shape_scale * NetworkComplexity d w))
///     (Nat.mul C (CertificateSize (NetworkComplexity d w)))
/// ```
///
/// De Bruijn indices: d = BVar(1), w = BVar(0) (innermost binder is w).
fn build_abstract_domain_statement(shape: DomainShape, c_val: u64) -> Expr {
    let nat = Expr::const_str("Nat");
    let le_le = Expr::const_str_levels("LE.le", vec![Level::zero()]);
    let inst_le_nat = Expr::const_str("instLENat");
    let nat_mul = Expr::const_str("Nat.mul");
    let cert_size = Expr::const_str("NNVerify.ProofComplexity.CertificateSize");
    let net_complexity = Expr::const_str("NNVerify.ProofComplexity.NetworkComplexity");

    // d = BVar(1), w = BVar(0) under two forall binders
    let d = Expr::bvar(1);
    let w = Expr::bvar(0);

    // NetworkComplexity d w
    let net_dw = Expr::apps(net_complexity, [d, w]);

    // LHS: CertificateSize(shape_scale * NetworkComplexity d w)
    let lhs = shape.build_domain_cert_size(net_dw.clone());

    // RHS: Nat.mul C (CertificateSize (NetworkComplexity d w))
    let ibp_size = Expr::app(cert_size, net_dw);
    let rhs = Expr::apps(nat_mul, [Expr::nat_lit(c_val), ibp_size]);

    // LE.le @Nat instLENat lhs rhs
    let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, lhs, rhs]);

    // forall (w : Nat), le_expr
    let body = Expr::pi(BinderInfo::Default, nat.clone(), le_expr);
    // forall (d : Nat), body
    Expr::pi(BinderInfo::Default, nat, body)
}

/// Build a proof term for a domain-shape candidate, if one genuinely exists.
///
/// # Honesty
///
/// A genuine proof of these `CertificateSize(scale * net) <= C * CertificateSize(net)`
/// claims would require *composing* the `cert_size_monotone` axiom with an
/// arithmetic fact relating `scale` and `C` and instantiating it at the bound
/// variables — the discovery loop does not construct such terms. A bare
/// reference to `cert_size_monotone` does NOT have any candidate's statement as
/// its type (its type is `forall a b, a <= b -> CertificateSize a <= CertificateSize b`,
/// a completely different proposition). So there is no honest proof to attach,
/// and we return `None`: the candidate is reported as Unverified rather than
/// "verified" by an axiom that does not prove it.
fn build_abstract_domain_proof(
    _shape: DomainShape,
    _c_val: u64,
    _d_val: u64,
    _w_val: u64,
) -> Option<Expr> {
    None
}

/// Build the parameter vector for a candidate.
fn build_params(shape: DomainShape, c_val: u64, d_val: u64, w_val: u64) -> ParamVec {
    let shape_params: Vec<ParamValue> = match shape {
        DomainShape::KCorrelation { k } => vec![
            ParamValue::Choice(shape.variant_index()),
            ParamValue::Nat(k),
            ParamValue::Nat(0), // segments slot unused
        ],
        DomainShape::PiecewiseLinear { segments } => vec![
            ParamValue::Choice(shape.variant_index()),
            ParamValue::Nat(0), // k slot unused
            ParamValue::Nat(segments),
        ],
        DomainShape::Hybrid { k, segments } => vec![
            ParamValue::Choice(shape.variant_index()),
            ParamValue::Nat(k),
            ParamValue::Nat(segments),
        ],
    };

    let mut params = shape_params;
    params.push(ParamValue::Nat(c_val));
    params.push(ParamValue::Nat(d_val));
    params.push(ParamValue::Nat(w_val));
    ParamVec(params)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_domain_config_default_and_shapes() {
        let config = AbstractDomainConfig::default();
        assert_eq!(config.max_k, 3);
        assert_eq!(config.max_segments, 3);
        assert_eq!(config.max_depth, 3);
        assert_eq!(config.max_width, 4);
        assert_eq!(config.max_c, 4);
        // shapes: k_corr(3) + pwl(3) + hybrid(3*3=9) = 15
        // 15 * 4 C * 3 depth * 4 width = 720
        assert_eq!(config.total_candidates(), 720);
        let shapes = config.domain_shapes();
        assert_eq!(shapes.len(), 15);
    }

    #[test]
    fn test_total_candidates_and_generation() {
        let config = AbstractDomainConfig {
            max_k: 2,
            max_segments: 2,
            max_depth: 2,
            max_width: 2,
            max_c: 2,
        };
        // shapes: k_corr(2) + pwl(2) + hybrid(2*2=4) = 8; 8*2*2*2 = 64
        assert_eq!(config.total_candidates(), 64);
        let candidates = generate_abstract_domain_candidates(&config);
        assert_eq!(candidates.len(), 64);
    }

    #[test]
    fn test_candidate_ids_family_and_proofs() {
        let config = AbstractDomainConfig {
            max_k: 1,
            max_segments: 1,
            max_depth: 2,
            max_width: 2,
            max_c: 1,
        };
        let candidates = generate_abstract_domain_candidates(&config);
        for (i, c) in candidates.iter().enumerate() {
            assert_eq!(c.id, CandidateId(i as u64));
            assert_eq!(c.family, TheoremFamily::NewAbstractDomain);
            // No genuine proof exists for these abstract-domain bounds, so each
            // candidate is honestly emitted WITHOUT a proof term.
            assert!(
                c.proof.is_none(),
                "candidate {} has no genuine proof -> proof must be None",
                c.id.0
            );
        }
    }

    #[test]
    fn test_candidate_statements_are_pi_types() {
        let config = AbstractDomainConfig {
            max_k: 2,
            max_segments: 2,
            max_depth: 1,
            max_width: 1,
            max_c: 1,
        };
        let candidates = generate_abstract_domain_candidates(&config);
        for c in &candidates {
            assert!(c.statement.is_pi(), "candidate {} should be Pi", c.id.0);
        }
    }

    #[test]
    fn test_domain_shape_variant_indices() {
        assert_eq!(DomainShape::KCorrelation { k: 1 }.variant_index(), 0);
        assert_eq!(
            DomainShape::PiecewiseLinear { segments: 2 }.variant_index(),
            1
        );
        assert_eq!(DomainShape::Hybrid { k: 1, segments: 2 }.variant_index(), 2);
    }

    #[test]
    fn test_domain_cert_size_all_shapes() {
        let net_dw = Expr::const_str("test_net");
        // k=1 passthrough, k=2 scaled, hybrid
        for shape in [
            DomainShape::KCorrelation { k: 1 },
            DomainShape::KCorrelation { k: 2 },
            DomainShape::PiecewiseLinear { segments: 3 },
            DomainShape::Hybrid { k: 2, segments: 3 },
        ] {
            let result = shape.build_domain_cert_size(net_dw.clone());
            assert!(result.is_app(), "{shape:?} cert size should be an app");
        }
    }

    #[test]
    fn test_statement_structure_double_forall() {
        let stmt = build_abstract_domain_statement(DomainShape::KCorrelation { k: 2 }, 3);
        assert!(stmt.is_pi(), "outer should be pi");
    }

    #[test]
    fn test_params_encoding() {
        // KCorrelation: [choice(0), k=2, segments=0, C=3, d=4, w=5]
        let p = build_params(DomainShape::KCorrelation { k: 2 }, 3, 4, 5);
        assert_eq!(p.0.len(), 6);
        match &p.0[0] {
            ParamValue::Choice(0) => {}
            o => panic!("got {o:?}"),
        }
        match &p.0[1] {
            ParamValue::Nat(2) => {}
            o => panic!("got {o:?}"),
        }

        // Hybrid: [choice(2), k=2, segments=3, C=4, d=1, w=2]
        let p = build_params(DomainShape::Hybrid { k: 2, segments: 3 }, 4, 1, 2);
        assert_eq!(p.0.len(), 6);
        match &p.0[0] {
            ParamValue::Choice(2) => {}
            o => panic!("got {o:?}"),
        }
    }

    #[test]
    fn test_shape_coverage_all_three_variants() {
        let config = AbstractDomainConfig {
            max_k: 1,
            max_segments: 1,
            max_depth: 1,
            max_width: 1,
            max_c: 1,
        };
        let candidates = generate_abstract_domain_candidates(&config);
        assert_eq!(candidates.len(), 3);
        let variant_indices: Vec<usize> = candidates
            .iter()
            .map(|c| match &c.params.0[0] {
                ParamValue::Choice(i) => *i,
                _ => panic!("first param should be Choice"),
            })
            .collect();
        assert!(variant_indices.contains(&0), "should have KCorrelation");
        assert!(variant_indices.contains(&1), "should have PiecewiseLinear");
        assert!(variant_indices.contains(&2), "should have Hybrid");
    }
}
