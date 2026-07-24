// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 Phase-1 body builders — pure `Expr` construction for the indexed
//! `Nat.rec` carriers and their helper constants.
//!
//! Split out of `nn_verify_blockwise_crown_values.rs` at #3638 Phase-1 to
//! stay under the 500-line file-size ratchet. The two modules are paired:
//! `nn_verify_blockwise_crown_values.rs` holds the type builders,
//! `Declaration::*` registration wrappers, and (pre-existing) `zero_ib`
//! oracle; this file holds the body-term builders invoked by those
//! registration wrappers.
//!
//! See the module-level docstring in
//! `nn_verify_blockwise_crown_values.rs` for the carrier redesign
//! narrative (Phase 1 of the C006 faithful-carrier programme, #3638).

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use super::nn_verify_blockwise_crown_values::build_c006_zero_ib;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build the indexed motive `fun (i : Nat) => IB (block_dim i)` for the
/// C006 carrier `Nat.rec` bodies.
pub(super) fn build_indexed_ib_motive(
    outer: &EnvDeclBuilder,
    c: &BlockwiseCrownConsts,
    block_dim: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (i_id, i) = ch.fresh_local(c.nat.clone());
    let body = c.ib_of(c.dim_at(block_dim, i));
    let r = ch.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), body);
    ch.finish_child(r)
}

/// Build the Phase-1 type-correct body for `C006.mono_step`.
///
/// The output dimension `IB (block_dim (i+1))` differs from the input
/// `IB (block_dim i)`, so an identity-on-`ih` body would not type-check.
/// Phase-1 returns `zero_ib (block_dim (succ i))` — structurally
/// depends on `block_dim` and `i`. Phase 4 replaces this with the real
/// LayerNorm interval-arithmetic transport through C004.
pub(super) fn build_mono_step_value(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (i_id, i) = b.fresh_local(c.nat.clone());
    let ib_i = c.ib_of(c.dim_at(&block_dim, i.clone()));
    let succ_i = Expr::app(c.nat_succ.clone(), i);
    let dim_si = c.dim_at(&block_dim, succ_i);
    let (ih_id, _) = b.fresh_local(ib_i.clone());
    let body = build_c006_zero_ib(&mut b, c, &dim_si);
    let e = b.mk_lam(ih_id, BinderInfo::Default, ib_i, body);
    let e = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}

/// Build Phase-1 True-valued Opaque body for
/// `C006.per_block_crown_matches_mono`. The body returns `True` for any
/// configuration — Phase 4 replaces with the real `forall i X, cb i X =
/// mono_step … i X` proposition.
pub(super) fn build_per_block_hyp_value(c: &BlockwiseCrownConsts) -> Expr {
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, _) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), true_const);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}

/// Build the indexed-`Nat.rec` body for `Block.compose`:
/// ```text
/// fun k bd cb lg lb eps B =>
///   @Nat.rec.{1} (fun i => IB (bd i)) B (fun i ih => cb i ih) k
/// ```
/// Step case references both `i` (via `cb i`) and `ih`, inverting
/// masquerade Rule M3.
pub(super) fn build_block_compose_value(c: &BlockwiseCrownConsts) -> Expr {
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let mut b = EnvDeclBuilder::new();
    let (k_id, k_var) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, cb_var) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let ib_0 = c.ib_of(c.dim_at(&block_dim, c.nat_zero.clone()));
    let (bnd_id, b_var) = b.fresh_local(ib_0.clone());

    let motive = build_indexed_ib_motive(&b, c, &block_dim);
    let step = build_compose_step(&b, c, &block_dim, &cb_var);
    let rec_app = Expr::apps(nat_rec, [motive, b_var, step, k_var]);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_0, rec_app);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `fun (i : Nat) (ih : IB (block_dim i)) => cb i ih`
fn build_compose_step(
    outer: &EnvDeclBuilder,
    c: &BlockwiseCrownConsts,
    block_dim: &Expr,
    cb_var: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (i_id, i) = ch.fresh_local(c.nat.clone());
    let ib_i = c.ib_of(c.dim_at(block_dim, i.clone()));
    let (ih_id, ih) = ch.fresh_local(ib_i.clone());
    let apply = Expr::app(Expr::app(cb_var.clone(), i.clone()), ih);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_i, apply);
    let r = ch.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), r);
    ch.finish_child(r)
}

/// Build the indexed-`Nat.rec` body for `Block.monolithic_crown`:
/// ```text
/// fun k bd cb lg lb eps B =>
///   @Nat.rec.{1} (fun i => IB (bd i)) B
///     (fun i ih => C006.mono_step bd lg lb eps i ih) k
/// ```
/// Step-case body is `mono_step bd lg lb eps i ih` — syntactically
/// distinct from `Block.compose`'s `cb i ih`, so δ-reduction cannot
/// collapse `compose k … = monolithic k …` to the shared placeholder.
pub(super) fn build_monolithic_crown_value(c: &BlockwiseCrownConsts) -> Expr {
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let mono_step = Expr::const_(Name::from_string("NNVerify.C006.mono_step"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (k_id, k_var) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, _) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, lg_var) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, lb_var) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, eps_var) = b.fresh_local(c.rat.clone());
    let ib_0 = c.ib_of(c.dim_at(&block_dim, c.nat_zero.clone()));
    let (bnd_id, b_var) = b.fresh_local(ib_0.clone());

    let motive = build_indexed_ib_motive(&b, c, &block_dim);
    let step = build_monolithic_step(&b, c, &block_dim, &mono_step, &lg_var, &lb_var, &eps_var);
    let rec_app = Expr::apps(nat_rec, [motive, b_var, step, k_var]);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_0, rec_app);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `fun (i : Nat) (ih : IB (block_dim i)) =>
///     mono_step block_dim lg lb eps i ih`
fn build_monolithic_step(
    outer: &EnvDeclBuilder,
    c: &BlockwiseCrownConsts,
    block_dim: &Expr,
    mono_step: &Expr,
    lg_var: &Expr,
    lb_var: &Expr,
    eps_var: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (i_id, i) = ch.fresh_local(c.nat.clone());
    let ib_i = c.ib_of(c.dim_at(block_dim, i.clone()));
    let (ih_id, ih) = ch.fresh_local(ib_i.clone());
    let apply = Expr::apps(
        mono_step.clone(),
        [
            block_dim.clone(),
            lg_var.clone(),
            lb_var.clone(),
            eps_var.clone(),
            i,
            ih,
        ],
    );
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_i, apply);
    let r = ch.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), r);
    ch.finish_child(r)
}
