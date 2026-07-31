// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for certified training declarations.
//!
//! Contains definition type builders and theorem type builders for the
//! differentiable IBP certified training formalization.
//!
//! Part of #3257.

#[cfg(test)]
use super::nn_verify_certified_training::CertTrainConsts;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Auxiliary definition type builders
// =============================================================================

/// `(n_out : Nat) -> NNVec n_out -> NNVec n_out -> Rat`
#[cfg(test)]
pub(super) fn build_standard_loss_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n_out);
    let (pred_id, _) = b.fresh_local(vec_n.clone());
    let (tgt_id, _) = b.fresh_local(vec_n.clone());
    let e = b.mk_pi(tgt_id, BinderInfo::Default, vec_n.clone(), c.rat.clone());
    let e = b.mk_pi(pred_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `(n_in n_out : Nat) -> (NNVec n_in -> NNVec n_out) ->
///  (NNVec n_out -> NNVec n_out -> Rat) ->
///  NNVec n_out -> NNVec n_in -> Rat -> Rat`
#[cfg(test)]
pub(super) fn build_worst_case_loss_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, _) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out);
    let vec_n_in = c.vec_of(n_in);
    let (y_id, _) = b.fresh_local(vec_n_out.clone());
    let (x_id, _) = b.fresh_local(vec_n_in.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `(n_w : Nat) -> (NNVec n_w -> Rat) -> Prop`
#[cfg(test)]
pub(super) fn build_is_differentiable_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_w_id, n_w) = b.fresh_local(c.nat.clone());
    let fn_ty = Expr::pi(BinderInfo::Default, c.vec_of(n_w), c.rat.clone());
    let (f_id, _) = b.fresh_local(fn_ty.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, c.prop.clone());
    let e = b.mk_pi(n_w_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `(n_in n_out : Nat) -> (NNVec n_in -> NNVec n_out) ->
///  IntervalBounds n_in -> IntervalBounds n_out`
#[cfg(test)]
pub(super) fn build_ibp_bounds_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let ib_in = c.ib_of(n_in);
    let ib_out = c.ib_of(n_out);
    let (ib_id, _) = b.fresh_local(ib_in.clone());
    let e = b.mk_pi(ib_id, BinderInfo::Default, ib_in, ib_out);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Main definition type builders
// =============================================================================

/// Same signature as worst_case_loss.
#[cfg(test)]
pub(super) fn build_ibp_loss_type(c: &CertTrainConsts) -> Expr {
    build_worst_case_loss_type(c)
}

/// `(n_in n_out : Nat) -> (NNVec n_in -> NNVec n_out) -> NNVec n_in -> Rat`
#[cfg(test)]
pub(super) fn build_certified_radius_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let vec_n_in = c.vec_of(n_in);
    let (x_id, _) = b.fresh_local(vec_n_in.clone());
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, c.rat.clone());
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `(n_in n_out : Nat) -> ... -> Rat -> NNVec n_out -> NNVec n_in -> Rat -> Rat`
#[cfg(test)]
pub(super) fn build_training_objective_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, _) = b.fresh_local(loss_ty.clone());
    let (lambda_id, _) = b.fresh_local(c.rat.clone());
    let vec_n_out = c.vec_of(n_out);
    let vec_n_in = c.vec_of(n_in);
    let (y_id, _) = b.fresh_local(vec_n_out.clone());
    let (x_id, _) = b.fresh_local(vec_n_in.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(lambda_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Same signature as worst_case_loss.
#[cfg(test)]
pub(super) fn build_bound_tightness_type(c: &CertTrainConsts) -> Expr {
    build_worst_case_loss_type(c)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// IBP loss upper bounds worst-case loss.
#[cfg(test)]
pub(super) fn build_ibp_loss_upper_bound_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, loss) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (y_id, y) = b.fresh_local(vec_n_out.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let wc = Expr::apps(
        c.worst_case_loss.clone(),
        [
            n_in.clone(),
            n_out.clone(),
            net.clone(),
            loss.clone(),
            y.clone(),
            x.clone(),
            eps.clone(),
        ],
    );
    let ibp = Expr::apps(c.ibp_loss.clone(), [n_in, n_out, net, loss, y, x, eps]);
    let concl = c.rat_le(wc, ibp);

    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// certified_radius >= eps and 0 < eps =>
/// worst_case_loss <= ibp_loss (soundness: radius implies bound).
#[cfg(test)]
pub(super) fn build_certified_radius_sound_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, loss) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (y_id, y) = b.fresh_local(vec_n_out.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let radius = Expr::apps(
        c.certified_radius.clone(),
        [n_in.clone(), n_out.clone(), net.clone(), x.clone()],
    );
    let hyp_le = c.rat_le(eps.clone(), radius);
    let (h1_id, _) = b.fresh_local(hyp_le.clone());

    let hyp_pos = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h2_id, _) = b.fresh_local(hyp_pos.clone());

    let wc = Expr::apps(
        c.worst_case_loss.clone(),
        [n_in, n_out, net, loss, y, x, eps],
    );
    let concl = c.rat_le(wc, c.rat_zero.clone());

    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_pos, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_le, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// bound_tightness >= 0 (nonneg, from ibp_loss >= worst_case_loss).
#[cfg(test)]
pub(super) fn build_training_convergence_bound_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, loss) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (y_id, y) = b.fresh_local(vec_n_out.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hyp_pos = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h_id, _) = b.fresh_local(hyp_pos.clone());

    let tightness = Expr::apps(
        c.bound_tightness.clone(),
        [n_in, n_out, net, loss, y, x, eps],
    );
    let concl = c.rat_ge(tightness, c.rat_zero.clone());

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_pos, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// IBP loss is differentiable w.r.t. weights.
///
/// `forall (n_in n_out n_w : Nat) (make_net : NNVec n_w -> NNVec n_in -> NNVec n_out)
///   (loss : NNVec n_out -> NNVec n_out -> Rat)
///   (y : NNVec n_out) (x : NNVec n_in) (eps : Rat),
///   0 < eps ->
///   is_differentiable n_w (fun w => ibp_loss n_in n_out (make_net w) loss y x eps)`
#[cfg(test)]
pub(super) fn build_ibp_loss_differentiable_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let (n_w_id, n_w) = b.fresh_local(c.nat.clone());
    let make_net_ty = Expr::pi(
        BinderInfo::Default,
        c.vec_of(n_w.clone()),
        c.network_ty(&n_in, &n_out),
    );
    let (make_net_id, make_net) = b.fresh_local(make_net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, loss) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (y_id, y) = b.fresh_local(vec_n_out.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hyp_pos = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h_id, _) = b.fresh_local(hyp_pos.clone());

    // Build the lambda: fun (w : NNVec n_w) => ibp_loss n_in n_out (make_net w) loss y x eps
    let w_ty = c.vec_of(n_w.clone());
    let (w_id, w) = b.fresh_local(w_ty.clone());
    let lam_body = Expr::apps(
        c.ibp_loss.clone(),
        [n_in, n_out, Expr::app(make_net, w), loss, y, x, eps],
    );
    let the_fn = b.mk_lam(w_id, BinderInfo::Default, w_ty, lam_body);

    // Conclusion: is_differentiable n_w the_fn
    let concl = Expr::apps(c.is_differentiable.clone(), [n_w, the_fn]);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_pos, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(make_net_id, BinderInfo::Default, make_net_ty, e);
    let e = b.mk_pi(n_w_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Certified training produces verified networks.
#[cfg(test)]
pub(super) fn build_certified_training_sound_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let loss_ty = c.loss_fn_ty(&n_out);
    let (loss_id, loss) = b.fresh_local(loss_ty.clone());
    let vec_n_out = c.vec_of(n_out.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (y_id, y) = b.fresh_local(vec_n_out.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (lambda_id, lambda) = b.fresh_local(c.rat.clone());

    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h1_id, _) = b.fresh_local(hyp_eps.clone());
    let hyp_lam = c.rat_lt(c.rat_zero.clone(), lambda.clone());
    let (h2_id, _) = b.fresh_local(hyp_lam.clone());
    let hyp_lam_bound = c.rat_le(lambda.clone(), c.rat_one.clone());
    let (h3_id, _) = b.fresh_local(hyp_lam_bound.clone());

    let wc = Expr::apps(
        c.worst_case_loss.clone(),
        [
            n_in.clone(),
            n_out.clone(),
            net.clone(),
            loss.clone(),
            y.clone(),
            x.clone(),
            eps.clone(),
        ],
    );
    let ibp = Expr::apps(
        c.ibp_loss.clone(),
        [
            n_in.clone(),
            n_out.clone(),
            net.clone(),
            loss.clone(),
            y.clone(),
            x.clone(),
            eps.clone(),
        ],
    );
    let part1 = c.rat_le(wc, ibp.clone());

    let obj = Expr::apps(
        c.training_objective.clone(),
        [n_in, n_out, net, loss, lambda, y, x, eps],
    );
    let part2 = c.rat_le(ibp, obj);

    let concl = Expr::app(Expr::app(c.and.clone(), part1), part2);

    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_lam_bound, concl);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_lam, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(lambda_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(y_id, BinderInfo::Default, vec_n_out, e);
    let e = b.mk_pi(loss_id, BinderInfo::Default, loss_ty, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
