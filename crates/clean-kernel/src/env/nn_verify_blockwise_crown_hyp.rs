// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 Phase-2 hypothesis-wrapped headline theorem.
//!
//! The Phase-1 C006 carriers are indexed `Nat.rec` definitions:
//! `Block.compose` steps with `crown_block i ih`, while
//! `Block.monolithic_crown` steps with `C006.mono_step ... i ih`.
//! Therefore the hypothesis-free headline equation is not derivable. This
//! module builds the narrow Phase-2 replacement type/proof for
//! `NNVerify.C006.blockwise_equals_monolithic`: the theorem now requires a
//! pointwise hypothesis that each `crown_block` step matches `mono_step`.
//!
//! The proof is a real `Nat.rec` over `k`; the successor case combines the
//! pointwise hypothesis with the induction hypothesis using `Eq.trans` and
//! `congrArg`. No C006 axiom is referenced.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use super::nn_verify_blockwise_crown_defs::build_inner_prop;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn type1() -> Level {
    Level::succ(Level::zero())
}

/// Build the pointwise hypothesis:
/// ```text
/// forall (i : Nat) (X : IB (block_dim i)),
///   crown_block i X = mono_step block_dim ln_gamma ln_beta ln_eps i X
/// ```
fn build_step_hyp_type(
    c: &BlockwiseCrownConsts,
    outer: &EnvDeclBuilder,
    block_dim: &Expr,
    crown_block: &Expr,
    ln_gamma: &Expr,
    ln_beta: &Expr,
    ln_eps: &Expr,
) -> Expr {
    let mono_step = Expr::const_(Name::from_string("NNVerify.C006.mono_step"), vec![]);
    let mut b = EnvDeclBuilder::child_of(outer);
    let (i_id, i) = b.fresh_local(c.nat.clone());
    let ib_i = c.ib_of(c.dim_at(block_dim, i.clone()));
    let (x_id, x) = b.fresh_local(ib_i.clone());
    let succ_i = Expr::app(c.nat_succ.clone(), i.clone());
    let dim_succ_i = c.dim_at(block_dim, succ_i);
    let lhs = Expr::app(Expr::app(crown_block.clone(), i.clone()), x.clone());
    let rhs = Expr::apps(
        mono_step,
        [
            block_dim.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            i,
            x,
        ],
    );
    let body = c.ib_eq(&dim_succ_i, lhs, rhs);
    let r = b.mk_pi(x_id, BinderInfo::Default, ib_i, body);
    let r = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish_child(r)
}

/// Hypothesis-wrapped type for `NNVerify.C006.blockwise_step`.
///
/// The old hypothesis-free step obligation is not derivable for arbitrary
/// `crown_block` over the current carriers. This theorem exposes the missing
/// local step evidence explicitly, then uses it with the supplied induction
/// hypothesis.
pub(super) fn build_blockwise_step_hyp_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let hyp_ty = build_step_hyp_type(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let (h_id, _) = b.fresh_local(hyp_ty.clone());
    let ih = build_inner_prop(
        c,
        &b,
        &k,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let k_succ = Expr::app(c.nat_succ.clone(), k);
    let concl = build_inner_prop(
        c,
        &b,
        &k_succ,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let step_body = Expr::pi(BinderInfo::Default, ih, concl);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, step_body);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Hypothesis-wrapped type for `NNVerify.C006.blockwise_equals_monolithic`.
pub(super) fn build_blockwise_equals_monolithic_hyp_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let hyp_ty = build_step_hyp_type(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let (h_id, _) = b.fresh_local(hyp_ty.clone());
    let inner = build_inner_prop(
        c,
        &b,
        &k,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, inner);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Hypothesis-wrapped type for `NNVerify.C006.blockwise_nat_induction`.
///
/// The current faithful indexed carriers do not prove the old hypothesis-free
/// induction claim for arbitrary `crown_block`. This theorem keeps the missing
/// induction evidence explicit: the caller supplies the property for every
/// block count, and the proof returns the requested `k` instance.
pub(super) fn build_blockwise_nat_induction_hyp_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let evidence_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(c.nat.clone());
        let body = build_inner_prop(
            c,
            &ch,
            &j,
            &block_dim,
            &crown_block,
            &ln_gamma,
            &ln_beta,
            &ln_eps,
        );
        let r = ch.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), body);
        ch.finish_child(r)
    };
    let (h_ind_id, _) = b.fresh_local(evidence_ty.clone());
    let concl = build_inner_prop(
        c,
        &b,
        &k,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );

    let e = b.mk_pi(h_ind_id, BinderInfo::Default, evidence_ty, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Constructive proof for the hypothesis-wrapped induction theorem:
/// `fun k block_dim crown_block ln_gamma ln_beta ln_eps h_ind => h_ind k`.
pub(super) fn build_blockwise_nat_induction_hyp_proof(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let evidence_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(c.nat.clone());
        let body = build_inner_prop(
            c,
            &ch,
            &j,
            &block_dim,
            &crown_block,
            &ln_gamma,
            &ln_beta,
            &ln_eps,
        );
        let r = ch.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), body);
        ch.finish_child(r)
    };
    let (h_ind_id, h_ind) = b.fresh_local(evidence_ty.clone());
    let body = Expr::app(h_ind, k.clone());

    let e = b.mk_lam(h_ind_id, BinderInfo::Default, evidence_ty, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn build_induction_motive(
    c: &BlockwiseCrownConsts,
    outer: &EnvDeclBuilder,
    block_dim: &Expr,
    crown_block: &Expr,
    ln_gamma: &Expr,
    ln_beta: &Expr,
    ln_eps: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(outer);
    let (j_id, j) = b.fresh_local(c.nat.clone());
    let body = build_inner_prop(c, &b, &j, block_dim, crown_block, ln_gamma, ln_beta, ln_eps);
    let r = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish_child(r)
}

fn build_base_case(c: &BlockwiseCrownConsts, outer: &EnvDeclBuilder, block_dim: &Expr) -> Expr {
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1()]);
    let mut b = EnvDeclBuilder::child_of(outer);
    let ib_0 = c.ib_of(c.dim_at(block_dim, c.nat_zero.clone()));
    let (bnd_id, bnd) = b.fresh_local(ib_0.clone());
    let body = Expr::app(Expr::app(eq_refl, ib_0.clone()), bnd);
    let r = b.mk_lam(bnd_id, BinderInfo::Default, ib_0, body);
    b.finish_child(r)
}

fn build_step_case(
    c: &BlockwiseCrownConsts,
    outer: &EnvDeclBuilder,
    block_dim: &Expr,
    crown_block: &Expr,
    ln_gamma: &Expr,
    ln_beta: &Expr,
    ln_eps: &Expr,
    hyp: &Expr,
) -> Expr {
    let mono_step = Expr::const_(Name::from_string("NNVerify.C006.mono_step"), vec![]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![type1()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![type1(), type1()]);

    let mut b = EnvDeclBuilder::child_of(outer);
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let ih_ty = build_inner_prop(c, &b, &m, block_dim, crown_block, ln_gamma, ln_beta, ln_eps);
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());
    let ib_0 = c.ib_of(c.dim_at(block_dim, c.nat_zero.clone()));
    let (bnd_id, bnd) = b.fresh_local(ib_0.clone());

    let dim_m = c.dim_at(block_dim, m.clone());
    let dim_succ_m = c.dim_at(block_dim, Expr::app(c.nat_succ.clone(), m.clone()));
    let ib_m = c.ib_of(dim_m);
    let ib_succ_m = c.ib_of(dim_succ_m.clone());

    let compose_m = Expr::apps(
        c.block_compose.clone(),
        [
            m.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let monolithic_m = Expr::apps(
        c.monolithic_crown.clone(),
        [
            m.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );

    let lhs = Expr::app(Expr::app(crown_block.clone(), m.clone()), compose_m.clone());
    let mono_step_fn = Expr::apps(
        mono_step.clone(),
        [
            block_dim.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            m.clone(),
        ],
    );
    let mid = Expr::app(mono_step_fn.clone(), compose_m.clone());
    let rhs = Expr::app(mono_step_fn.clone(), monolithic_m.clone());
    let step1 = Expr::apps(hyp.clone(), [m.clone(), compose_m.clone()]);
    let ih_at_b = Expr::app(ih.clone(), bnd);
    let step2 = Expr::apps(
        congr_arg,
        [
            ib_m,
            ib_succ_m.clone(),
            compose_m,
            monolithic_m,
            mono_step_fn,
            ih_at_b,
        ],
    );
    let body = Expr::apps(eq_trans, [ib_succ_m, lhs, mid, rhs, step1, step2]);

    let r = b.mk_lam(bnd_id, BinderInfo::Default, ib_0, body);
    let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish_child(r)
}

/// Constructive proof for the hypothesis-wrapped step theorem:
/// the successor branch used by the headline Nat.rec proof, specialized at
/// the supplied `k` and induction hypothesis.
pub(super) fn build_blockwise_step_hyp_proof(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let hyp_ty = build_step_hyp_type(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let (h_id, h) = b.fresh_local(hyp_ty.clone());
    let ih_ty = build_inner_prop(
        c,
        &b,
        &k,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());
    let step = build_step_case(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
        &h,
    );
    let body = Expr::apps(step, [k.clone(), ih]);

    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Constructive proof for the hypothesis-wrapped headline theorem.
pub(super) fn build_blockwise_equals_monolithic_hyp_proof(c: &BlockwiseCrownConsts) -> Expr {
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());

    let hyp_ty = build_step_hyp_type(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let (h_id, h) = b.fresh_local(hyp_ty.clone());
    let motive = build_induction_motive(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
    );
    let base = build_base_case(c, &b, &block_dim);
    let step = build_step_case(
        c,
        &b,
        &block_dim,
        &crown_block,
        &ln_gamma,
        &ln_beta,
        &ln_eps,
        &h,
    );
    let rec_app = Expr::apps(nat_rec, [motive, base, step, k]);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, rec_app);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
