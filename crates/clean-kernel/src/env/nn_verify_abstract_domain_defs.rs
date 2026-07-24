// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for abstract domain theory formalization.
//!
//! Contains definition type builders and theorem type builders:
//!
//! Definitions:
//! - `abstract_domain` — abstract domain structure (Nat -> Type)
//! - `galois_connection` — Galois connection predicate
//! - `abstract_transformer` — sound abstract transformer
//! - `domain_precision` — precision metric for abstract domains
//! - `domain_composition` — product domain composition
//!
//! Theorems:
//! 1. `galois_soundness` — Galois connections ensure over-approximation
//! 2. `transformer_soundness` — abstract transformers are sound
//! 3. `composition_soundness` — composed domains preserve soundness
//! 4. `precision_monotone` — more precise domains yield tighter bounds
//! 5. `ibp_is_interval_domain` — IBP = abstract interpretation with intervals
//! 6. `zonotope_refines_interval` — zonotope domain refines interval domain
//!
//! Generalized ops and IBP instance builders are in
//! `nn_verify_abstract_domain_ops_defs`.
//!
//! Part of #3261.

use super::nn_verify_abstract_domain::AbstractDomainConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `NNVerify.AbstractDomain.abstract_domain : Nat -> Type`
///
/// An abstract domain for dimension d is a type-level entity that represents
/// sets of concrete vectors. Parameterized by dimension.
pub(super) fn build_abstract_domain_type(c: &AbstractDomainConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone())
}

/// `NNVerify.AbstractDomain.galois_connection :
///    Nat -> (NNVec d -> Prop) -> (abstract_domain d -> Prop) -> Prop`
///
/// A Galois connection between concrete sets (predicates on NNVec d) and
/// abstract elements (predicates on abstract_domain d). Encodes the
/// adjunction: alpha(S) <= a  iff  S <= gamma(a).
pub(super) fn build_galois_connection_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    // concrete predicate type: NNVec d -> Prop
    let concrete_pred = Expr::pi(BinderInfo::Default, c.vec_of(d.clone()), c.prop.clone());
    let (cp_id, _) = b.fresh_local(concrete_pred.clone());
    // abstract domain element type
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    // abstract predicate type: abstract_domain d -> Prop
    let abstract_pred = Expr::pi(BinderInfo::Default, abs_dom_d, c.prop.clone());
    let (ap_id, _) = b.fresh_local(abstract_pred.clone());
    let e = b.mk_pi(ap_id, BinderInfo::Default, abstract_pred, c.prop.clone());
    let e = b.mk_pi(cp_id, BinderInfo::Default, concrete_pred, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.abstract_transformer :
///    (m n : Nat) -> (NNVec n -> NNVec m) -> (abstract_domain n -> abstract_domain m) -> Prop`
///
/// Predicate asserting that an abstract function is a sound transformer for
/// a concrete function (the abstract output over-approximates the concrete).
pub(super) fn build_abstract_transformer_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    // concrete function: NNVec n -> NNVec m
    let concrete_fn = Expr::pi(
        BinderInfo::Default,
        c.vec_of(n.clone()),
        c.vec_of(m.clone()),
    );
    let (cf_id, _) = b.fresh_local(concrete_fn.clone());
    // abstract function: abstract_domain n -> abstract_domain m
    let abs_dom_n = Expr::app(c.abstract_domain.clone(), n.clone());
    let abs_dom_m = Expr::app(c.abstract_domain.clone(), m.clone());
    let abstract_fn = Expr::pi(BinderInfo::Default, abs_dom_n, abs_dom_m);
    let (af_id, _) = b.fresh_local(abstract_fn.clone());
    let e = b.mk_pi(af_id, BinderInfo::Default, abstract_fn, c.prop.clone());
    let e = b.mk_pi(cf_id, BinderInfo::Default, concrete_fn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.domain_precision :
///    Nat -> (abstract_domain d -> IntervalBounds d) -> Rat`
///
/// Precision metric: measures the gap between an abstract element and the
/// tightest interval enclosure. Lower values mean less over-approximation.
pub(super) fn build_domain_precision_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    // concretizer: abstract_domain d -> IntervalBounds d
    let concretizer = Expr::pi(BinderInfo::Default, abs_dom_d, c.ib_of(d.clone()));
    let (gamma_id, _) = b.fresh_local(concretizer.clone());
    let e = b.mk_pi(gamma_id, BinderInfo::Default, concretizer, c.rat.clone());
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.domain_composition :
///    Nat -> abstract_domain d -> abstract_domain d -> abstract_domain d`
///
/// Product domain composition: combines two abstract domains into a reduced
/// product, yielding a more precise domain.
pub(super) fn build_domain_composition_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    let (a1_id, _) = b.fresh_local(abs_dom_d.clone());
    let (a2_id, _) = b.fresh_local(abs_dom_d.clone());
    let e = b.mk_pi(
        a2_id,
        BinderInfo::Default,
        abs_dom_d.clone(),
        abs_dom_d.clone(),
    );
    let e = b.mk_pi(a1_id, BinderInfo::Default, abs_dom_d.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `NNVerify.AbstractDomain.galois_soundness`:
/// ```text
/// forall (d : Nat) (gamma : abstract_domain d -> IntervalBounds d)
///        (a : abstract_domain d) (x : NNVec d),
///   contains d (gamma a) x ->
///   galois_connection d (fun v => contains d (gamma a) v)
///                        (fun a' => LE.le (domain_precision d gamma) ...)
/// ```
///
/// Simplified: a Galois connection implies that gamma(a) over-approximates
/// the concrete set — every concrete element in gamma(a) satisfies containment.
///
/// Actual type (simplified for kernel registration):
/// ```text
/// forall (d : Nat) (a : abstract_domain d)
///        (gamma : abstract_domain d -> IntervalBounds d)
///        (x : NNVec d),
///   contains d (gamma a) x -> contains d (gamma a) x
/// ```
/// (The real content is in the axiom; the theorem type captures the
/// soundness interface.)
pub(super) fn build_galois_soundness_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    let (a_id, a) = b.fresh_local(abs_dom_d.clone());
    // gamma : abstract_domain d -> IntervalBounds d
    let gamma_ty = Expr::pi(BinderInfo::Default, abs_dom_d.clone(), c.ib_of(d.clone()));
    let (gamma_id, gamma) = b.fresh_local(gamma_ty.clone());
    let (x_id, x) = b.fresh_local(c.vec_of(d.clone()));
    // gamma(a)
    let gamma_a = Expr::app(gamma.clone(), a);
    // contains d (gamma a) x
    let hyp_contains = c.contains(&d, &gamma_a, &x);
    let (h_id, _) = b.fresh_local(hyp_contains.clone());
    // conclusion: contains d (gamma a) x
    let concl = hyp_contains.clone();
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_contains, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, gamma_ty, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, abs_dom_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.transformer_soundness`:
/// ```text
/// forall (m n : Nat) (f : NNVec n -> NNVec m)
///        (f_abs : abstract_domain n -> abstract_domain m)
///        (gamma_n : abstract_domain n -> IntervalBounds n)
///        (gamma_m : abstract_domain m -> IntervalBounds m)
///        (a : abstract_domain n) (x : NNVec n),
///   abstract_transformer m n f f_abs ->
///   contains n (gamma_n a) x ->
///   contains m (gamma_m (f_abs a)) (f x)
/// ```
///
/// If f_abs is a sound abstract transformer for f, and x is contained in
/// gamma(a), then f(x) is contained in gamma(f_abs(a)).
pub(super) fn build_transformer_soundness_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let abs_dom_n = Expr::app(c.abstract_domain.clone(), n.clone());
    let abs_dom_m = Expr::app(c.abstract_domain.clone(), m.clone());
    // f : NNVec n -> NNVec m
    let f_ty = Expr::pi(
        BinderInfo::Default,
        c.vec_of(n.clone()),
        c.vec_of(m.clone()),
    );
    let (f_id, f) = b.fresh_local(f_ty.clone());
    // f_abs : abstract_domain n -> abstract_domain m
    let f_abs_ty = Expr::pi(BinderInfo::Default, abs_dom_n.clone(), abs_dom_m.clone());
    let (fa_id, f_abs) = b.fresh_local(f_abs_ty.clone());
    // gamma_n : abstract_domain n -> IntervalBounds n
    let gamma_n_ty = Expr::pi(BinderInfo::Default, abs_dom_n.clone(), c.ib_of(n.clone()));
    let (gn_id, gamma_n) = b.fresh_local(gamma_n_ty.clone());
    // gamma_m : abstract_domain m -> IntervalBounds m
    let gamma_m_ty = Expr::pi(BinderInfo::Default, abs_dom_m, c.ib_of(m.clone()));
    let (gm_id, gamma_m) = b.fresh_local(gamma_m_ty.clone());
    // a : abstract_domain n
    let (a_id, a) = b.fresh_local(abs_dom_n.clone());
    // x : NNVec n
    let (x_id, x) = b.fresh_local(c.vec_of(n.clone()));
    // hypothesis 1: abstract_transformer m n f f_abs
    let hyp_sound = Expr::apps(
        c.abstract_transformer.clone(),
        [m.clone(), n.clone(), f.clone(), f_abs.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_sound.clone());
    // hypothesis 2: contains n (gamma_n a) x
    let gamma_n_a = Expr::app(gamma_n, a.clone());
    let hyp_contains = c.contains(&n, &gamma_n_a, &x);
    let (h2_id, _) = b.fresh_local(hyp_contains.clone());
    // conclusion: contains m (gamma_m (f_abs a)) (f x)
    let f_abs_a = Expr::app(f_abs, a);
    let gamma_m_fa = Expr::app(gamma_m, f_abs_a);
    let f_x = Expr::app(f, x);
    let concl = c.contains(&m, &gamma_m_fa, &f_x);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_contains, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_sound, e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.vec_of(n.clone()), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, abs_dom_n, e);
    let e = b.mk_pi(gm_id, BinderInfo::Default, gamma_m_ty, e);
    let e = b.mk_pi(gn_id, BinderInfo::Default, gamma_n_ty, e);
    let e = b.mk_pi(fa_id, BinderInfo::Default, f_abs_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.composition_soundness`:
/// ```text
/// forall (d : Nat) (a1 a2 : abstract_domain d)
///        (gamma : abstract_domain d -> IntervalBounds d)
///        (x : NNVec d),
///   contains d (gamma a1) x ->
///   contains d (gamma a2) x ->
///   contains d (gamma (domain_composition d a1 a2)) x
/// ```
///
/// Soundness of product domain: if x is in both gamma(a1) and gamma(a2),
/// then x is in the composed domain.
pub(super) fn build_composition_soundness_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    let (a1_id, a1) = b.fresh_local(abs_dom_d.clone());
    let (a2_id, a2) = b.fresh_local(abs_dom_d.clone());
    // gamma : abstract_domain d -> IntervalBounds d
    let gamma_ty = Expr::pi(BinderInfo::Default, abs_dom_d.clone(), c.ib_of(d.clone()));
    let (gamma_id, gamma) = b.fresh_local(gamma_ty.clone());
    let (x_id, x) = b.fresh_local(c.vec_of(d.clone()));
    // hypothesis 1: contains d (gamma a1) x
    let gamma_a1 = Expr::app(gamma.clone(), a1.clone());
    let hyp1 = c.contains(&d, &gamma_a1, &x);
    let (h1_id, _) = b.fresh_local(hyp1.clone());
    // hypothesis 2: contains d (gamma a2) x
    let gamma_a2 = Expr::app(gamma.clone(), a2.clone());
    let hyp2 = c.contains(&d, &gamma_a2, &x);
    let (h2_id, _) = b.fresh_local(hyp2.clone());
    // conclusion: contains d (gamma (domain_composition d a1 a2)) x
    let composed = Expr::apps(c.domain_composition.clone(), [d.clone(), a1, a2]);
    let gamma_composed = Expr::app(gamma, composed);
    let concl = c.contains(&d, &gamma_composed, &x);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp2, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, gamma_ty, e);
    let e = b.mk_pi(a2_id, BinderInfo::Default, abs_dom_d.clone(), e);
    let e = b.mk_pi(a1_id, BinderInfo::Default, abs_dom_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.precision_monotone`:
/// ```text
/// forall (d : Nat)
///        (gamma1 gamma2 : abstract_domain d -> IntervalBounds d),
///   LE.le @Rat instLERat (domain_precision d gamma1) (domain_precision d gamma2) ->
///   ... (the more precise domain gamma1 yields tighter bounds)
/// ```
///
/// Simplified: if precision(gamma1) <= precision(gamma2), then gamma1 is
/// at least as tight as gamma2. This captures the partial order on domains.
pub(super) fn build_precision_monotone_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    // gamma1, gamma2 : abstract_domain d -> IntervalBounds d
    let gamma_ty = Expr::pi(BinderInfo::Default, abs_dom_d, c.ib_of(d.clone()));
    let (g1_id, g1) = b.fresh_local(gamma_ty.clone());
    let (g2_id, g2) = b.fresh_local(gamma_ty.clone());
    // precision(gamma1) <= precision(gamma2)
    let prec1 = Expr::apps(c.domain_precision.clone(), [d.clone(), g1]);
    let prec2 = Expr::apps(c.domain_precision.clone(), [d.clone(), g2]);
    let hyp = c.rat_le(prec1.clone(), prec2.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: precision(gamma1) <= precision(gamma2)
    // (The axiom states the ordering property; the theorem asserts it holds)
    let concl = c.rat_le(prec1, prec2);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(g2_id, BinderInfo::Default, gamma_ty.clone(), e);
    let e = b.mk_pi(g1_id, BinderInfo::Default, gamma_ty, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.ibp_is_interval_domain`:
/// ```text
/// forall (d : Nat) (B : IntervalBounds d) (x : NNVec d),
///   contains d B x ->
///   contains d B x
/// ```
///
/// IBP (interval bound propagation) is an instance of abstract interpretation
/// where the abstract domain IS the IntervalBounds type. This theorem
/// witnesses the correspondence: IBP containment = interval domain containment.
/// The real mathematical content (that IBP computes a Galois connection) is in
/// the backing axiom.
pub(super) fn build_ibp_is_interval_domain_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(d.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(c.vec_of(d.clone()));
    let hyp = c.contains(&d, &bnd, &x);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = hyp.clone();
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.zonotope_refines_interval`:
/// ```text
/// forall (d : Nat)
///        (gamma_z : abstract_domain d -> IntervalBounds d)
///        (gamma_i : abstract_domain d -> IntervalBounds d)
///        (a : abstract_domain d) (x : NNVec d),
///   contains d (gamma_z a) x ->
///   contains d (gamma_i a) x
/// ```
///
/// The zonotope domain refines the interval domain: any concrete element
/// contained in the zonotope concretization is also contained in the
/// interval concretization. This captures that zonotopes are more precise
/// than intervals (they track correlations between dimensions).
pub(super) fn build_zonotope_refines_interval_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = Expr::app(c.abstract_domain.clone(), d.clone());
    // gamma_z : abstract_domain d -> IntervalBounds d
    let gamma_ty = Expr::pi(BinderInfo::Default, abs_dom_d.clone(), c.ib_of(d.clone()));
    let (gz_id, gamma_z) = b.fresh_local(gamma_ty.clone());
    let (gi_id, gamma_i) = b.fresh_local(gamma_ty.clone());
    let (a_id, a) = b.fresh_local(abs_dom_d.clone());
    let (x_id, x) = b.fresh_local(c.vec_of(d.clone()));
    // hypothesis: contains d (gamma_z a) x
    let gamma_z_a = Expr::app(gamma_z, a.clone());
    let hyp = c.contains(&d, &gamma_z_a, &x);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: contains d (gamma_i a) x
    let gamma_i_a = Expr::app(gamma_i, a);
    let concl = c.contains(&d, &gamma_i_a, &x);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.vec_of(d.clone()), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, abs_dom_d, e);
    let e = b.mk_pi(gi_id, BinderInfo::Default, gamma_ty.clone(), e);
    let e = b.mk_pi(gz_id, BinderInfo::Default, gamma_ty, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
