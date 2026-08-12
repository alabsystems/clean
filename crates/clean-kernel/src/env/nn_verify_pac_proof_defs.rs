// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C029 Type Builders — POST-#3588 BRANCH A DEMASQUERADE
//!
//! After the #3588 Branch A demasquerade this module contains only
//! *type* builders for the C029 carriers and axioms. The previous
//! `build_*_constructive_proof` helpers (one per headline claim) are
//! removed because the three headline claims are now
//! `Declaration::Axiom` entries with no proof term.
//!
//! Carriers (Opaque post-#3588):
//! - `coverage_volume`, `miss_probability`, `proof_certificate`
//!
//! Support Opaques (unchanged):
//! - `pgd_search`, `lipschitz_bound`, `hessian_bound`,
//!   `pac_confidence`, `nat_to_rat`
//!
//! Headline claims (Axiom post-#3588):
//! 1. `pac_certification_bound` (C029a)
//! 2. `volume_ratio_bound` (C029b)
//! 3. `proof_lifting` (C029c)
//!
//! See: designs/2026-04-19-demasquerade-cxxx-pattern.md,
//! designs/2026-04-17-publication-quality-gamma-crown-proofs.md.
//!
//! Part of #3588.

use super::nn_verify_pac_proof::PacProofConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `NNVerify.PacProof.pgd_search :
///   Nat -> (NNVec n -> NNVec n) -> NNVec n -> Rat -> Nat -> Prop`
pub(super) fn build_pgd_search_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (x0_id, _) = b.fresh_local(c.vec_of(n.clone()));
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (k_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(n), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.lipschitz_bound :
///   Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
pub(super) fn build_lipschitz_bound_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (l_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.hessian_bound :
///   Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
pub(super) fn build_hessian_bound_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (h_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.coverage_volume : Rat -> Rat -> Rat -> Rat`
pub(super) fn build_coverage_volume_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (l_id, _) = b.fresh_local(c.rat.clone());
    let (h_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.miss_probability : Nat -> Rat -> Rat`
pub(super) fn build_miss_probability_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, _) = b.fresh_local(c.nat.clone());
    let (vol_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(vol_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.proof_certificate :
///   Nat -> (NNVec n -> NNVec n) -> NNVec n -> Rat -> Rat -> Prop`
pub(super) fn build_proof_certificate_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (x0_id, _) = b.fresh_local(c.vec_of(n.clone()));
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (delta_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(n), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.pac_confidence : Rat -> Rat`
pub(super) fn build_pac_confidence_type(c: &PacProofConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.PacProof.nat_to_rat : Nat -> Rat`
pub(super) fn build_nat_to_rat_type(c: &PacProofConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone())
}

/// `NNVerify.PacProof.real_exp : Rat -> Rat`
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_real_exp_type(c: &PacProofConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.PacProof.neg : Rat -> Rat`
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_neg_type(c: &PacProofConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `NNVerify.PacProof.pac_certification_bound` (C029a):
/// ```text
/// forall (d : Nat) (f : NNVec d -> NNVec d) (x0 : NNVec d)
///        (eps L H : Rat) (k : Nat),
///   pgd_search d f x0 eps k ->
///   lipschitz_bound d f L ->
///   hessian_bound d f H ->
///   0 < eps -> 0 < L -> 0 < H ->
///   (miss_probability k (coverage_volume eps L H) <=
///     real_exp (neg (mul (nat_to_rat k) (coverage_volume eps L H)))) ->
///   miss_probability k (coverage_volume eps L H) <=
///     real_exp (neg (mul (nat_to_rat k) (coverage_volume eps L H)))
/// ```
pub(super) fn build_pac_certification_bound_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (x0_id, x0) = b.fresh_local(c.vec_of(d.clone()));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());

    let hyp_pgd = Expr::apps(
        c.pgd_search.clone(),
        [d.clone(), f.clone(), x0.clone(), eps.clone(), k.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_pgd.clone());

    let hyp_lip = Expr::apps(c.lipschitz_bound.clone(), [d.clone(), f.clone(), l.clone()]);
    let (h2_id, _) = b.fresh_local(hyp_lip.clone());

    let hyp_hess = Expr::apps(c.hessian_bound.clone(), [d.clone(), f.clone(), h.clone()]);
    let (h3_id, _) = b.fresh_local(hyp_hess.clone());

    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h4_id, _) = b.fresh_local(hyp_eps.clone());

    let hyp_l = c.rat_lt(c.rat_zero.clone(), l.clone());
    let (h5_id, _) = b.fresh_local(hyp_l.clone());

    let hyp_h = c.rat_lt(c.rat_zero.clone(), h.clone());
    let (h6_id, _) = b.fresh_local(hyp_h.clone());

    let volume = Expr::apps(
        c.coverage_volume.clone(),
        [eps.clone(), l.clone(), h.clone()],
    );
    let lhs = Expr::apps(c.miss_probability.clone(), [k.clone(), volume.clone()]);
    let exponent = c.mul(Expr::app(c.nat_to_rat.clone(), k), volume);
    let rhs = Expr::app(c.real_exp.clone(), Expr::app(c.neg.clone(), exponent));
    let concl = c.rat_le(lhs, rhs);
    let (h_bound_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_bound_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h6_id, BinderInfo::Default, hyp_h, e);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_l, e);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_hess, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_pgd, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_pac_certification_bound_proof(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (x0_id, x0) = b.fresh_local(c.vec_of(d.clone()));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());

    let hyp_pgd = Expr::apps(
        c.pgd_search.clone(),
        [d.clone(), f.clone(), x0.clone(), eps.clone(), k.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_pgd.clone());
    let hyp_lip = Expr::apps(c.lipschitz_bound.clone(), [d.clone(), f.clone(), l.clone()]);
    let (h2_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_hess = Expr::apps(c.hessian_bound.clone(), [d.clone(), f, h.clone()]);
    let (h3_id, _) = b.fresh_local(hyp_hess.clone());
    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h4_id, _) = b.fresh_local(hyp_eps.clone());
    let hyp_l = c.rat_lt(c.rat_zero.clone(), l.clone());
    let (h5_id, _) = b.fresh_local(hyp_l.clone());
    let hyp_h = c.rat_lt(c.rat_zero.clone(), h.clone());
    let (h6_id, _) = b.fresh_local(hyp_h.clone());

    let volume = Expr::apps(c.coverage_volume.clone(), [eps.clone(), l, h]);
    let lhs = Expr::apps(c.miss_probability.clone(), [k.clone(), volume.clone()]);
    let exponent = c.mul(Expr::app(c.nat_to_rat.clone(), k), volume);
    let rhs = Expr::app(c.real_exp.clone(), Expr::app(c.neg.clone(), exponent));
    let concl = c.rat_le(lhs, rhs);
    let (h_bound_id, h_bound) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_bound_id, BinderInfo::Default, concl, h_bound);
    let e = b.mk_lam(h6_id, BinderInfo::Default, hyp_h, e);
    let e = b.mk_lam(h5_id, BinderInfo::Default, hyp_l, e);
    let e = b.mk_lam(h4_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_lam(h3_id, BinderInfo::Default, hyp_hess, e);
    let e = b.mk_lam(h2_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp_pgd, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.volume_ratio_bound` (C029b):
/// ```text
/// forall (eps L H : Rat),
///   0 < eps -> 0 < L -> 0 < H ->
///   (coverage_volume eps L H <=
///     div (mul L (mul eps eps))
///         (add 1 (mul H (mul eps eps)))) ->
///   coverage_volume eps L H <=
///     div (mul L (mul eps eps))
///         (add 1 (mul H (mul eps eps)))
/// ```
pub(super) fn build_volume_ratio_bound_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());

    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h1_id, _) = b.fresh_local(hyp_eps.clone());

    let hyp_l = c.rat_lt(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_l.clone());

    let hyp_h = c.rat_lt(c.rat_zero.clone(), h.clone());
    let (h3_id, _) = b.fresh_local(hyp_h.clone());

    let eps_sq = c.mul(eps.clone(), eps.clone());
    let lhs = Expr::apps(c.coverage_volume.clone(), [eps, l.clone(), h.clone()]);
    let rhs = c.div(
        c.mul(l, eps_sq.clone()),
        c.add(c.rat_one.clone(), c.mul(h, eps_sq)),
    );
    let concl = c.rat_le(lhs, rhs);
    let (h_bound_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_bound_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_h, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_l, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

pub(super) fn build_volume_ratio_bound_proof(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());

    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h1_id, _) = b.fresh_local(hyp_eps.clone());
    let hyp_l = c.rat_lt(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_l.clone());
    let hyp_h = c.rat_lt(c.rat_zero.clone(), h.clone());
    let (h3_id, _) = b.fresh_local(hyp_h.clone());

    let eps_sq = c.mul(eps.clone(), eps.clone());
    let lhs = Expr::apps(c.coverage_volume.clone(), [eps, l.clone(), h.clone()]);
    let rhs = c.div(
        c.mul(l, eps_sq.clone()),
        c.add(c.rat_one.clone(), c.mul(h, eps_sq)),
    );
    let concl = c.rat_le(lhs, rhs);
    let (h_bound_id, h_bound) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_bound_id, BinderInfo::Default, concl, h_bound);
    let e = b.mk_lam(h3_id, BinderInfo::Default, hyp_h, e);
    let e = b.mk_lam(h2_id, BinderInfo::Default, hyp_l, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.PacProof.proof_lifting` (C029c):
/// ```text
/// forall (d : Nat) (f : NNVec d -> NNVec d) (x0 : NNVec d)
///        (eps delta : Rat) (k : Nat) (L H : Rat),
///   pgd_search d f x0 eps k ->
///   lipschitz_bound d f L ->
///   hessian_bound d f H ->
///   0 < eps -> 0 < delta -> delta < 1 ->
///   miss_probability k (coverage_volume eps L H) <= delta ->
///   proof_certificate d f x0 eps delta ->
///   proof_certificate d f x0 eps delta
/// ```
pub(super) fn build_proof_lifting_type(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (x0_id, x0) = b.fresh_local(c.vec_of(d.clone()));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (delta_id, delta) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());

    let hyp_pgd = Expr::apps(
        c.pgd_search.clone(),
        [d.clone(), f.clone(), x0.clone(), eps.clone(), k.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_pgd.clone());

    let hyp_lip = Expr::apps(c.lipschitz_bound.clone(), [d.clone(), f.clone(), l.clone()]);
    let (h2_id, _) = b.fresh_local(hyp_lip.clone());

    let hyp_hess = Expr::apps(c.hessian_bound.clone(), [d.clone(), f.clone(), h.clone()]);
    let (h3_id, _) = b.fresh_local(hyp_hess.clone());

    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h4_id, _) = b.fresh_local(hyp_eps.clone());

    let hyp_delta = c.rat_lt(c.rat_zero.clone(), delta.clone());
    let (h5_id, _) = b.fresh_local(hyp_delta.clone());

    let hyp_delta_one = c.rat_lt(delta.clone(), c.rat_one.clone());
    let (h6_id, _) = b.fresh_local(hyp_delta_one.clone());

    let volume = Expr::apps(c.coverage_volume.clone(), [eps.clone(), l, h]);
    let hyp_miss = c.rat_le(
        Expr::apps(c.miss_probability.clone(), [k.clone(), volume]),
        delta.clone(),
    );
    let (h7_id, _) = b.fresh_local(hyp_miss.clone());

    let concl = Expr::apps(c.proof_certificate.clone(), [d.clone(), f, x0, eps, delta]);
    let (h_cert_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_cert_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h7_id, BinderInfo::Default, hyp_miss, e);
    let e = b.mk_pi(h6_id, BinderInfo::Default, hyp_delta_one, e);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_delta, e);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_hess, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_pgd, e);
    let e = b.mk_pi(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_proof_lifting_proof(c: &PacProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (x0_id, x0) = b.fresh_local(c.vec_of(d.clone()));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (delta_id, delta) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (h_id, h) = b.fresh_local(c.rat.clone());

    let hyp_pgd = Expr::apps(
        c.pgd_search.clone(),
        [d.clone(), f.clone(), x0.clone(), eps.clone(), k.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_pgd.clone());
    let hyp_lip = Expr::apps(c.lipschitz_bound.clone(), [d.clone(), f.clone(), l.clone()]);
    let (h2_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_hess = Expr::apps(c.hessian_bound.clone(), [d.clone(), f.clone(), h.clone()]);
    let (h3_id, _) = b.fresh_local(hyp_hess.clone());
    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h4_id, _) = b.fresh_local(hyp_eps.clone());
    let hyp_delta = c.rat_lt(c.rat_zero.clone(), delta.clone());
    let (h5_id, _) = b.fresh_local(hyp_delta.clone());
    let hyp_delta_one = c.rat_lt(delta.clone(), c.rat_one.clone());
    let (h6_id, _) = b.fresh_local(hyp_delta_one.clone());

    let volume = Expr::apps(c.coverage_volume.clone(), [eps.clone(), l, h]);
    let hyp_miss = c.rat_le(
        Expr::apps(c.miss_probability.clone(), [k.clone(), volume]),
        delta.clone(),
    );
    let (h7_id, _) = b.fresh_local(hyp_miss.clone());

    let concl = Expr::apps(c.proof_certificate.clone(), [d.clone(), f, x0, eps, delta]);
    let (h_cert_id, h_cert) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_cert_id, BinderInfo::Default, concl, h_cert);
    let e = b.mk_lam(h7_id, BinderInfo::Default, hyp_miss, e);
    let e = b.mk_lam(h6_id, BinderInfo::Default, hyp_delta_one, e);
    let e = b.mk_lam(h5_id, BinderInfo::Default, hyp_delta, e);
    let e = b.mk_lam(h4_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_lam(h3_id, BinderInfo::Default, hyp_hess, e);
    let e = b.mk_lam(h2_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp_pgd, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(delta_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
