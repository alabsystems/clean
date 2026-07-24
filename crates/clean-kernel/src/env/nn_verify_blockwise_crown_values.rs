// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 definition type builders and `Declaration::*` registration
//! wrappers.
//!
//! Registers the C006 carrier family (`Block.ibp_transfer`, `Block.compose`,
//! `Block.monolithic_crown`) and the Phase-1 helper constants
//! (`C006.mono_step`, `C006.per_block_crown_matches_mono`).
//!
//! Body-term builders for the indexed-`Nat.rec` carriers live in
//! `nn_verify_blockwise_crown_value_builders.rs` (split out #3638 Phase 1
//! to stay under the 500-line file-size ratchet). This module owns:
//! - the shared Pi type builders (`build_ibp_transfer_type`,
//!   `build_block_compose_type`, `build_mono_step_type`,
//!   `build_per_block_hyp_type`);
//! - the legacy `build_c006_zero_ib` oracle helper (still used by
//!   sibling `nn_verify_blockwise_crown_base.rs` /
//!   `nn_verify_blockwise_crown_ext_carriers.rs`);
//! - the `impl Environment` `register_*` methods that wire the types +
//!   values into `Declaration::*` kernel entries.
//!
//! # Phase 1 carrier redesign (2026-04-20, #3638)
//!
//! Per `designs/2026-04-20-c006-block-compose-faithful-carriers.md`, the
//! previous `Declaration::Opaque` bodies with `build_c006_zero_ib(block_dim k)`
//! were a MASQUERADE-Branch-A guard: both `Block.compose` and
//! `Block.monolithic_crown` had the same argument-discarding body, and the
//! Opaque kind was the only thing blocking δ-collapse to `zero_ib = zero_ib`.
//!
//! Phase 1 replaces both bodies with indexed `@Nat.rec` carriers whose
//! motive depends on `block_dim`:
//!
//! ```text
//! Block.compose k block_dim cb lg lb eps B
//!   := @Nat.rec.{1} (fun (i : Nat) => IB (block_dim i))
//!                   B                              -- base case
//!                   (fun (i : Nat) (ih : IB (block_dim i)) => cb i ih)
//!                   k
//!
//! Block.monolithic_crown k block_dim cb lg lb eps B
//!   := @Nat.rec.{1} (fun (i : Nat) => IB (block_dim i))
//!                   B                              -- base case
//!                   (fun (i : Nat) (ih : IB (block_dim i)) =>
//!                      C006.mono_step block_dim lg lb eps i ih)
//!                   k
//! ```
//!
//! The step bodies differ syntactically (`cb i ih` vs `mono_step … i ih`),
//! so δ-collapse no longer makes the two carriers equal. Both bodies
//! structurally consume their step-index `i`, their induction hypothesis
//! `ih`, and (for `Block.compose`) the per-block `cb` family. This inverts
//! masquerade Rules M1 (alias-collapse), M2 (argument-discarding), and M3
//! (IH-ignoring step).
//!
//! The declaration kind flips from `Declaration::Opaque` back to reducible
//! `Declaration::Definition` — the indexed-Nat.rec bodies carry real
//! iota-reduction content that downstream proof terms need to unfold.
//! δ-collapse to a shared placeholder is structurally blocked by the
//! distinct step bodies, so reducibility is safe.
//!
//! Part of #3638 — Phase 1 of the C006 faithful-carrier programme.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use super::nn_verify_blockwise_crown_value_builders::{
    build_block_compose_value, build_mono_step_value, build_monolithic_crown_value,
    build_per_block_hyp_value,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build type for `NNVerify.Block.ibp_transfer`:
/// ```text
/// (n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) ->
///   (B : IntervalBounds n) -> IntervalBounds n
/// ```
pub(super) fn build_ibp_transfer_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, _beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, _bnd) = b.fresh_local(ib_n.clone());
    let result = ib_n.clone();
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, result);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.Block.compose` / `NNVerify.Block.monolithic_crown`:
/// ```text
/// (k : Nat) -> (block_dim : Nat -> Nat) ->
///   (crown_block : (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1))) ->
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1))) ->
///   (ln_eps : Rat) ->
///   (B : IntervalBounds (block_dim 0)) ->
///   IntervalBounds (block_dim k)
/// ```
pub(super) fn build_block_compose_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, _crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _ln_eps) = b.fresh_local(c.rat.clone());
    let ib_0 = c.ib_of(c.dim_at(&block_dim, c.nat_zero.clone()));
    let (bnd_id, _bnd) = b.fresh_local(ib_0.clone());
    let result = c.ib_of(c.dim_at(&block_dim, k));

    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_0, result);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build a zero IntervalBounds for the given dimension expression.
/// Returns `IntervalBounds.mk @dim (fun _ => 0) (fun _ => 0) (fun _ => le_refl 0)`.
///
/// Used by sibling modules (`nn_verify_blockwise_crown_base.rs`,
/// `nn_verify_blockwise_crown_ext_carriers.rs`) for building test-oracle
/// placeholder bounds, and by `nn_verify_blockwise_crown_value_builders`
/// for the Phase-1 `C006.mono_step` body. No longer used as the body for
/// `Block.compose` / `Block.monolithic_crown` post-#3638 Phase 1 (those
/// now carry indexed Nat.rec bodies).
pub(super) fn build_c006_zero_ib(
    b: &mut EnvDeclBuilder,
    _c: &BlockwiseCrownConsts,
    dim: &Expr,
) -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let le_refl_const = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_d = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), dim.clone());
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), rat_zero.clone());
        ch.finish_child(r)
    };
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let proof = Expr::app(le_refl_const, rat_zero);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(r)
    };
    Expr::apps(ib_mk, [dim.clone(), zero_vec.clone(), zero_vec, valid])
}

/// Build type for `C006.mono_step`:
/// ```text
/// (block_dim : Nat -> Nat) ->
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1))) ->
///   (ln_eps : Rat) ->
///   (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1))
/// ```
pub(super) fn build_mono_step_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (i_id, i) = b.fresh_local(c.nat.clone());
    let ib_i = c.ib_of(c.dim_at(&block_dim, i.clone()));
    let ib_si = c.ib_of(c.dim_at(&block_dim, Expr::app(c.nat_succ.clone(), i)));
    let (ih_id, _) = b.fresh_local(ib_i.clone());
    let e = b.mk_pi(ih_id, BinderInfo::Default, ib_i, ib_si);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}

/// Build type for `C006.per_block_crown_matches_mono`:
/// ```text
/// (block_dim : Nat -> Nat) ->
///   (crown_block : (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1))) ->
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1))) ->
///   (ln_eps : Rat) -> Prop
/// ```
pub(super) fn build_per_block_hyp_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, _) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, _) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, _) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}

impl Environment {
    /// `NNVerify.Block.ibp_transfer` — interval transfer through LayerNorm.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    /// Placeholder: returns the input bounds unchanged (identity).
    pub(super) fn register_ibp_transfer(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Block.ibp_transfer"))
            .is_some()
        {
            return Ok(());
        }
        let ty = build_ibp_transfer_type(c);
        let value = build_ibp_transfer_identity_value(c);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Block.ibp_transfer"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Block.compose` — block-wise CROWN composition function.
    ///
    /// **Phase 1 (2026-04-20, #3638):** body is now the indexed
    /// `@Nat.rec` over motive `fun i => IB (block_dim i)` with step case
    /// `cb i ih`. Flipped from `Declaration::Opaque` (with
    /// `build_c006_zero_ib` body) back to reducible
    /// `Declaration::Definition` — the new body structurally depends on
    /// `cb`, `B`, `block_dim`, and `k`, so δ-collapse cannot alias
    /// `compose` with `monolithic_crown` (whose step case uses
    /// `mono_step` instead). See module-level docs and the EXECUTE design
    /// `designs/2026-04-20-c006-block-compose-faithful-carriers.md` §3.1.
    pub(super) fn register_block_compose(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Block.compose"))
            .is_some()
        {
            return Ok(());
        }
        let ty = build_block_compose_type(c);
        let value = build_block_compose_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.Block.compose"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Block.monolithic_crown` — monolithic CROWN over entire network.
    ///
    /// **Phase 1 (2026-04-20, #3638):** body is the indexed `@Nat.rec`
    /// over motive `fun i => IB (block_dim i)` with step case
    /// `C006.mono_step block_dim lg lb eps i ih`. The step body is
    /// syntactically distinct from `Block.compose`'s (`cb i ih`), so the
    /// two carriers cannot δ-collapse to the same term. Flipped from
    /// `Declaration::Opaque` back to reducible `Declaration::Definition`
    /// — Phase-1 design §3.2.
    pub(super) fn register_monolithic_crown(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
            .is_some()
        {
            return Ok(());
        }
        let ty = build_block_compose_type(c);
        let value = build_monolithic_crown_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.Block.monolithic_crown"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.C006.mono_step` — Phase-1 monolithic step helper.
    ///
    /// Type: `(bd : Nat -> Nat) -> ... -> (i : Nat) -> IB (bd i) -> IB (bd (i+1))`.
    /// Phase-1 body returns `zero_ib (bd (i+1))` — a placeholder that is
    /// type-correct against the output dimension `bd (i+1)` and is
    /// structurally distinct from `cb i ih` (used in
    /// `Block.compose`'s step). Phase 4 upgrades to real LayerNorm
    /// interval arithmetic. Registered as reducible
    /// `Declaration::Definition` so `Block.monolithic_crown`'s step
    /// body iota-unfolds during proof-term checking.
    pub(super) fn register_mono_step(&mut self, c: &BlockwiseCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C006.mono_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_mono_step_type(c);
        let value = build_mono_step_value(c);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.C006.per_block_crown_matches_mono` — per-block
    /// CROWN-matches-mono_step hypothesis predicate (Phase 1).
    ///
    /// Type: `(bd : Nat -> Nat) -> (cb : ...) -> ... -> Prop`. Phase-1
    /// body returns `True` for any configuration; Phase 4 replaces with
    /// the real `forall i X, cb i X = mono_step bd lg lb eps i X`
    /// proposition. Registered as `Declaration::Opaque` per the
    /// proposition-valued-function convention (cf.
    /// `C006.follows_from_c004`).
    pub(super) fn register_per_block_crown_matches_mono(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C006.per_block_crown_matches_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_per_block_hyp_type(c);
        let value = build_per_block_hyp_value(c);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Identity body for `Block.ibp_transfer`:
/// `fun (n : Nat) (_ _ : NNVec n) (_ : Rat) (B : IB n) => B`.
fn build_ibp_transfer_identity_value(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n_var) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n_var.clone());
    let ib_n = c.ib_of(n_var);
    let (gamma_id, _) = b.fresh_local(vec_n.clone());
    let (beta_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, bnd);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
