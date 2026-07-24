// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for generalized abstract domain operations and IBP instances.
//!
//! Generalized operations (parameterized by abstract domain):
//! - `ad_contains` — membership predicate
//! - `sound_linear` — soundness through linear layers
//! - `sound_relu` — soundness through ReLU
//! - `sound_compose` — soundness of linear+ReLU composition
//! - `tighter_than` — partial order on domains
//!
//! IBP instance type builders:
//! - `ibp_instance` — IntervalBounds is an abstract domain
//! - `ibp_sound_linear` — T80 expressed as instance proof
//! - `ibp_sound_relu` — T81 expressed as instance proof
//! - `ibp_sound_compose` — T82 expressed as instance proof
//!
//! Part of #3261.

use super::nn_verify_abstract_domain::AbstractDomainConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Generalized abstract domain type builders
// =============================================================================

/// `NNVerify.AbstractDomain.ad_contains`:
/// ```text
/// (d : Nat) -> abstract_domain d -> (Fin d -> Rat) -> Prop
/// ```
///
/// Generalized membership predicate: given a dimension d, an abstract
/// element of type `abstract_domain d`, and a concrete vector
/// (as `Fin d -> Rat`), returns a proposition asserting membership.
///
/// For IBP, this reduces to `IntervalBounds.contains d b x` where
/// the abstract element is an IntervalBounds.
pub(super) fn build_ad_contains_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = c.abs_dom_of(d.clone());
    let (_a_id, _a) = b.fresh_local(abs_dom_d.clone());
    // concrete vector type: Fin d -> Rat
    let fin_d = c.fin_of(d.clone());
    let concrete_vec = Expr::pi(BinderInfo::Default, fin_d, c.rat.clone());
    let (_x_id, _x) = b.fresh_local(concrete_vec.clone());
    let e = b.mk_pi(_x_id, BinderInfo::Default, concrete_vec, c.prop.clone());
    let e = b.mk_pi(_a_id, BinderInfo::Default, abs_dom_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.sound_linear`:
/// ```text
/// forall (m n : Nat) (W : NNMat m n) (b : NNVec m)
///        (a : abstract_domain n) (x : Fin n -> Rat),
///   ad_contains n a x ->
///   ad_contains m (linear_transform_abs m n W b a) (linear_output m n W b x)
/// ```
///
/// Soundness through linear layers: if x is in the abstract element a,
/// then W*x + b is in the abstract image of a under the linear map.
/// Generalizes T80 (IBP linear soundness).
///
/// Simplified kernel type (abstract transform is folded into axiom):
/// ```text
/// (m n : Nat) -> NNMat m n -> NNVec m -> abstract_domain n ->
///   (Fin n -> Rat) -> Prop
/// ```
pub(super) fn build_ad_sound_linear_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let abs_dom_n = c.abs_dom_of(n.clone());
    // Concrete vector type: Fin n -> Rat
    let fin_n = c.fin_of(n.clone());
    let concrete_vec_n = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
    let (_w_id, _w) = b.fresh_local(mat_mn.clone());
    let (_bias_id, _bias) = b.fresh_local(vec_m.clone());
    let (_a_id, _a) = b.fresh_local(abs_dom_n.clone());
    let (_x_id, _x) = b.fresh_local(concrete_vec_n.clone());
    let e = b.mk_pi(_x_id, BinderInfo::Default, concrete_vec_n, c.prop.clone());
    let e = b.mk_pi(_a_id, BinderInfo::Default, abs_dom_n, e);
    let e = b.mk_pi(_bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(_w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.sound_relu`:
/// ```text
/// (d : Nat) -> abstract_domain d -> (Fin d -> Rat) -> Prop
/// ```
///
/// Soundness through ReLU activation. Asserts that if x is in the
/// abstract element a, then relu(x) is in the abstract image of a
/// under the ReLU transformer. Generalizes T81.
pub(super) fn build_ad_sound_relu_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = c.abs_dom_of(d.clone());
    let fin_d = c.fin_of(d.clone());
    let concrete_vec = Expr::pi(BinderInfo::Default, fin_d, c.rat.clone());
    let (_a_id, _a) = b.fresh_local(abs_dom_d.clone());
    let (_x_id, _x) = b.fresh_local(concrete_vec.clone());
    let e = b.mk_pi(_x_id, BinderInfo::Default, concrete_vec, c.prop.clone());
    let e = b.mk_pi(_a_id, BinderInfo::Default, abs_dom_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.sound_compose`:
/// ```text
/// (m n : Nat) -> NNMat m n -> NNVec m ->
///   abstract_domain n -> (Fin n -> Rat) -> Prop
/// ```
///
/// Soundness through composition of linear + ReLU. Asserts that
/// if x is in abstract element a, then relu(W*x + b) is in
/// the abstract image. Generalizes T82.
pub(super) fn build_ad_sound_compose_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let abs_dom_n = c.abs_dom_of(n.clone());
    let fin_n = c.fin_of(n.clone());
    let concrete_vec_n = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
    let (_w_id, _w) = b.fresh_local(mat_mn.clone());
    let (_bias_id, _bias) = b.fresh_local(vec_m.clone());
    let (_a_id, _a) = b.fresh_local(abs_dom_n.clone());
    let (_x_id, _x) = b.fresh_local(concrete_vec_n.clone());
    let e = b.mk_pi(_x_id, BinderInfo::Default, concrete_vec_n, c.prop.clone());
    let e = b.mk_pi(_a_id, BinderInfo::Default, abs_dom_n, e);
    let e = b.mk_pi(_bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(_w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.tighter_than`:
/// ```text
/// (contains1 contains2 : (d : Nat) -> abstract_domain d -> (Fin d -> Rat) -> Prop) -> Prop
/// ```
///
/// Domain D1 is tighter than D2 iff:
///   forall d a x, contains1 d a x -> contains2 d a x
///
/// This means D1's membership is more restrictive — every element
/// certified by D1 is also certified by D2, but D1 may reject
/// elements that D2 accepts (tighter bounds).
pub(super) fn build_ad_tighter_than_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    // contains_type = (d : Nat) -> abstract_domain d -> (Fin d -> Rat) -> Prop
    let contains_type = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.nat.clone());
        let abs_dom_d = c.abs_dom_of(d.clone());
        let fin_d = c.fin_of(d.clone());
        let concrete_vec = Expr::pi(BinderInfo::Default, fin_d, c.rat.clone());
        let (_a_id, _a) = ch.fresh_local(abs_dom_d.clone());
        let (_x_id, _x) = ch.fresh_local(concrete_vec.clone());
        let r = ch.mk_pi(_x_id, BinderInfo::Default, concrete_vec, c.prop.clone());
        let r = ch.mk_pi(_a_id, BinderInfo::Default, abs_dom_d, r);
        let r = ch.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        ch.finish_child(r)
    };
    let (c1_id, _c1) = b.fresh_local(contains_type.clone());
    let (c2_id, _c2) = b.fresh_local(contains_type.clone());
    let e = b.mk_pi(
        c2_id,
        BinderInfo::Default,
        contains_type.clone(),
        c.prop.clone(),
    );
    let e = b.mk_pi(c1_id, BinderInfo::Default, contains_type, e);
    b.finish(e)
}

// =============================================================================
// IBP instance type builders
// =============================================================================

/// `NNVerify.AbstractDomain.ibp_instance`:
/// ```text
/// (d : Nat) -> abstract_domain d
/// ```
///
/// Witnesses that for every dimension d, there is an abstract domain
/// element that represents IBP (interval bound propagation).
/// This is the canonical embedding of IntervalBounds into the
/// abstract domain framework.
pub(super) fn build_ad_ibp_instance_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let abs_dom_d = c.abs_dom_of(d);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), abs_dom_d);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.ibp_sound_linear`:
/// ```text
/// forall (m n : Nat) (W : NNMat m n) (b : NNVec m)
///        (B : IntervalBounds n) (x : NNVec n),
///   IntervalBounds.contains B x ->
///   IntervalBounds.contains (ibp_linear_bounds m n W b B) (linear_output m n W b x)
/// ```
///
/// This is the same type as T80 (ibp_linear_sound), expressed as an
/// instance proof for the abstract domain framework. The axiom-backed
/// proof witnesses that IBP satisfies sound_linear.
pub(super) fn build_ad_ibp_sound_linear_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let ib_n = c.ib_of(n.clone());
    let vec_n = c.vec_of(n.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());
    // hypothesis: contains n B x
    let hyp = c.contains(&n, &bnd, &x);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // ibp_linear_bounds m n W b B
    let output_bounds = Expr::apps(
        c.ibp_linear_bounds.clone(),
        [m.clone(), n.clone(), w.clone(), bias.clone(), bnd],
    );
    // linear_output m n W b x
    let output_vec = Expr::apps(c.linear_output.clone(), [m.clone(), n.clone(), w, bias, x]);
    // conclusion: contains m (ibp_linear_bounds ...) (linear_output ...)
    let concl = c.contains(&m, &output_bounds, &output_vec);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.ibp_sound_relu`:
/// ```text
/// forall (d : Nat) (B : IntervalBounds d) (x : NNVec d),
///   IntervalBounds.contains B x ->
///   IntervalBounds.contains (ibp_relu_bounds d B) (relu_vec d x)
/// ```
///
/// Same type as T81, expressed as an instance proof.
pub(super) fn build_ad_ibp_sound_relu_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(d.clone());
    let vec_d = c.vec_of(d.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(vec_d.clone());
    // hypothesis: contains d B x
    let hyp = c.contains(&d, &bnd, &x);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // ibp_relu_bounds d B
    let output_bounds = Expr::apps(c.ibp_relu_bounds.clone(), [d.clone(), bnd]);
    // relu_vec d x
    let output_vec = Expr::apps(c.relu_vec.clone(), [d.clone(), x]);
    // conclusion
    let concl = c.contains(&d, &output_bounds, &output_vec);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.AbstractDomain.ibp_sound_compose`:
/// ```text
/// forall (m n : Nat) (W : NNMat m n) (b : NNVec m)
///        (B : IntervalBounds n) (x : NNVec n),
///   IntervalBounds.contains B x ->
///   IntervalBounds.contains (ibp_relu_bounds m (ibp_linear_bounds m n W b B))
///                            (relu_vec m (linear_output m n W b x))
/// ```
///
/// Same type as T82, expressed as an instance proof.
pub(super) fn build_ad_ibp_sound_compose_type(c: &AbstractDomainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let ib_n = c.ib_of(n.clone());
    let vec_n = c.vec_of(n.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());
    // hypothesis: contains n B x
    let hyp = c.contains(&n, &bnd, &x);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // ibp_relu_bounds m (ibp_linear_bounds m n W b B)
    let linear_bounds = Expr::apps(
        c.ibp_linear_bounds.clone(),
        [m.clone(), n.clone(), w.clone(), bias.clone(), bnd],
    );
    let output_bounds = Expr::apps(c.ibp_relu_bounds.clone(), [m.clone(), linear_bounds]);
    // relu_vec m (linear_output m n W b x)
    let linear_out = Expr::apps(c.linear_output.clone(), [m.clone(), n.clone(), w, bias, x]);
    let output_vec = Expr::apps(c.relu_vec.clone(), [m.clone(), linear_out]);
    // conclusion
    let concl = c.contains(&m, &output_bounds, &output_vec);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
