// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for proof complexity lower bounds for NN verification certificates.
//!
//! Contains definition type builders and theorem type builders:
//!
//! Definitions:
//! - `CertificateSize` — size of an NN verification certificate
//! - `NetworkComplexity` — depth * width complexity measure
//! - `BoundTightness` — tightness ratio cert/optimal
//! - `VerificationProblem` — the NN verification decision problem
//! - `IBPCertificate`, `ZonotopeCertificate`, `DeepPolyCertificate` — certificate types
//!
//! Theorems:
//! 1. `cert_size_lower_bound` — any certificate requires size >= f(depth, width)
//! 2. `ibp_cert_polynomial` — IBP certificates are polynomial in network size
//! 3. `tighter_bound_larger_cert` — tighter bounds require larger certificates
//! 4. `depth_width_tradeoff` — certificate size grows with depth*width product
//! 5. `cert_hierarchy` — IBP < zonotope < DeepPoly certificate sizes
//!
//! Part of #3260.

use super::nn_verify_proof_complexity::ProofComplexityConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `NNVerify.ProofComplexity.CertificateSize : Nat -> Nat`
///
/// Maps a certificate (encoded as Nat) to its size (number of proof steps/nodes).
pub(super) fn build_certificate_size_type(c: &ProofComplexityConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone())
}

/// `NNVerify.ProofComplexity.NetworkComplexity : Nat -> Nat -> Nat`
///
/// `NetworkComplexity depth width = depth * width` — a combined complexity measure.
pub(super) fn build_network_complexity_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, _) = b.fresh_local(c.nat.clone());
    let (w_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_pi(w_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.BoundTightness : Rat -> Rat -> Rat`
///
/// `BoundTightness cert_bound optimal_bound = cert_bound / optimal_bound`
/// Measures how close a certificate's bound is to the optimal.
pub(super) fn build_bound_tightness_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cert_id, _) = b.fresh_local(c.rat.clone());
    let (opt_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(opt_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(cert_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.VerificationProblem : Type`
///
/// The NN verification decision problem: given a network f, input region S,
/// output spec, decide whether f(x) satisfies the spec for all x in S.
pub(super) fn build_verification_problem_type(c: &ProofComplexityConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ProofComplexity.IBPCertificate : Type`
pub(super) fn build_ibp_certificate_type(c: &ProofComplexityConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ProofComplexity.ZonotopeCertificate : Type`
pub(super) fn build_zonotope_certificate_type(c: &ProofComplexityConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ProofComplexity.DeepPolyCertificate : Type`
pub(super) fn build_deep_poly_certificate_type(c: &ProofComplexityConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ProofComplexity.ibp_cert_size : IBPCertificate -> Nat`
pub(super) fn build_ibp_cert_size_type(c: &ProofComplexityConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.ibp_cert.clone(), c.nat.clone())
}

/// `NNVerify.ProofComplexity.zonotope_cert_size : ZonotopeCertificate -> Nat`
pub(super) fn build_zonotope_cert_size_type(c: &ProofComplexityConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.zonotope_cert.clone(), c.nat.clone())
}

/// `NNVerify.ProofComplexity.deep_poly_cert_size : DeepPolyCertificate -> Nat`
pub(super) fn build_deep_poly_cert_size_type(c: &ProofComplexityConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.deep_poly_cert.clone(), c.nat.clone())
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `NNVerify.ProofComplexity.cert_size_lower_bound`:
/// ```text
/// forall (depth width cert : Nat),
///   LE.le (NetworkComplexity depth width) (CertificateSize cert)
/// ```
///
/// Any certificate proving a property of a network with given depth and width
/// must have size at least NetworkComplexity(depth, width).
pub(super) fn build_cert_size_lower_bound_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.nat.clone());
    let (cert_id, cert) = b.fresh_local(c.nat.clone());
    // NetworkComplexity depth width
    let nc = Expr::apps(c.network_complexity.clone(), [d, w]);
    // CertificateSize cert
    let cs = Expr::app(c.certificate_size.clone(), cert);
    // LE.le @Nat instLENat nc cs
    let concl = c.nat_le(nc, cs);
    let e = b.mk_pi(cert_id, BinderInfo::Default, c.nat.clone(), concl);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.ibp_cert_polynomial`:
/// ```text
/// forall (depth width : Nat) (cert : IBPCertificate),
///   LE.le (ibp_cert_size cert) (Nat.mul depth (Nat.mul width width))
/// ```
///
/// IBP certificates are polynomial (O(d * w^2)) in network size.
pub(super) fn build_ibp_cert_polynomial_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.nat.clone());
    let (cert_id, cert) = b.fresh_local(c.ibp_cert.clone());
    // ibp_cert_size cert
    let cert_sz = Expr::app(c.ibp_cert_size.clone(), cert);
    // d * w * w
    let w_sq = Expr::apps(c.nat_mul.clone(), [w.clone(), w]);
    let bound = Expr::apps(c.nat_mul.clone(), [d, w_sq]);
    let concl = c.nat_le(cert_sz, bound);
    let e = b.mk_pi(cert_id, BinderInfo::Default, c.ibp_cert.clone(), concl);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.tighter_bound_larger_cert`:
/// ```text
/// forall (cert_bound1 cert_bound2 optimal : Rat),
///   0 < optimal ->
///   LE.le cert_bound1 cert_bound2 ->
///   LE.le (BoundTightness cert_bound2 optimal) (BoundTightness cert_bound1 optimal)
/// ```
///
/// Tighter bounds (smaller cert_bound) imply larger tightness ratios,
/// requiring larger certificates. This formalizes the precision-cost trade-off.
pub(super) fn build_tighter_bound_larger_cert_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cb1_id, cb1) = b.fresh_local(c.rat.clone());
    let (cb2_id, cb2) = b.fresh_local(c.rat.clone());
    let (opt_id, opt) = b.fresh_local(c.rat.clone());
    // hypothesis 1: 0 < optimal
    let hyp_pos = c.rat_lt(c.rat_zero.clone(), opt.clone());
    let (h1_id, _) = b.fresh_local(hyp_pos.clone());
    // hypothesis 2: cert_bound1 <= cert_bound2
    let hyp_le = c.rat_le(cb1.clone(), cb2.clone());
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    // conclusion: BoundTightness cb2 opt <= BoundTightness cb1 opt
    let tight2 = Expr::apps(c.bound_tightness.clone(), [cb2, opt.clone()]);
    let tight1 = Expr::apps(c.bound_tightness.clone(), [cb1, opt]);
    let concl = c.rat_le(tight2, tight1);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_pos, e);
    let e = b.mk_pi(opt_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(cb2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(cb1_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.depth_width_tradeoff`:
/// ```text
/// forall (depth1 width1 depth2 width2 : Nat),
///   LE.le (Nat.mul depth1 width1) (Nat.mul depth2 width2) ->
///   LE.le (NetworkComplexity depth1 width1) (NetworkComplexity depth2 width2)
/// ```
///
/// Certificate size is monotone in the depth*width product.
pub(super) fn build_depth_width_tradeoff_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d1_id, d1) = b.fresh_local(c.nat.clone());
    let (w1_id, w1) = b.fresh_local(c.nat.clone());
    let (d2_id, d2) = b.fresh_local(c.nat.clone());
    let (w2_id, w2) = b.fresh_local(c.nat.clone());
    // hypothesis: d1*w1 <= d2*w2
    let prod1 = Expr::apps(c.nat_mul.clone(), [d1.clone(), w1.clone()]);
    let prod2 = Expr::apps(c.nat_mul.clone(), [d2.clone(), w2.clone()]);
    let hyp = c.nat_le(prod1, prod2);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: NetworkComplexity d1 w1 <= NetworkComplexity d2 w2
    let nc1 = Expr::apps(c.network_complexity.clone(), [d1, w1]);
    let nc2 = Expr::apps(c.network_complexity.clone(), [d2, w2]);
    let concl = c.nat_le(nc1, nc2);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(w2_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(d2_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(w1_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(d1_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ProofComplexity.cert_hierarchy`:
/// ```text
/// forall (ibp : IBPCertificate) (zono : ZonotopeCertificate) (dp : DeepPolyCertificate),
///   And (LE.le (ibp_cert_size ibp) (zonotope_cert_size zono))
///       (LE.le (zonotope_cert_size zono) (deep_poly_cert_size dp))
/// ```
///
/// Strict hierarchy of certificate sizes: IBP <= zonotope <= DeepPoly.
/// IBP uses axis-aligned boxes (cheapest), zonotopes track affine correlations
/// (moderate cost), DeepPoly uses full back-substitution (most expensive).
pub(super) fn build_cert_hierarchy_type(c: &ProofComplexityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (ibp_id, ibp) = b.fresh_local(c.ibp_cert.clone());
    let (zono_id, zono) = b.fresh_local(c.zonotope_cert.clone());
    let (dp_id, dp) = b.fresh_local(c.deep_poly_cert.clone());
    // ibp_cert_size ibp <= zonotope_cert_size zono
    let ibp_sz = Expr::app(c.ibp_cert_size.clone(), ibp);
    let zono_sz = Expr::app(c.zonotope_cert_size.clone(), zono);
    let dp_sz = Expr::app(c.deep_poly_cert_size.clone(), dp);
    let le1 = c.nat_le(ibp_sz, zono_sz.clone());
    let le2 = c.nat_le(zono_sz, dp_sz);
    // And le1 le2
    let concl = Expr::apps(c.and.clone(), [le1, le2]);
    let e = b.mk_pi(dp_id, BinderInfo::Default, c.deep_poly_cert.clone(), concl);
    let e = b.mk_pi(zono_id, BinderInfo::Default, c.zonotope_cert.clone(), e);
    let e = b.mk_pi(ibp_id, BinderInfo::Default, c.ibp_cert.clone(), e);
    b.finish(e)
}
