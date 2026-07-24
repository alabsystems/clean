// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 base-case hypothesis-wrapped theorem builder.
//!
//! Split from `nn_verify_blockwise_crown_defs` for file-size compliance.
//! Contains the strengthened #3489 statement builder for
//! `NNVerify.C006.blockwise_base`:
//!
//! - `build_blockwise_base_type` pins `compose 0` / `monolithic_crown 0` to
//!   an explicit `zero_ib` (`IntervalBounds.mk`) value instead of just
//!   restating a reducible alias identity. With the Phase-1 indexed carriers,
//!   the theorem now requires the missing input hypothesis `B = zero_ib`.
//!
//! The old `build_blockwise_base_proof` (And.intro of two Eq.refl witnesses)
//! and `build_blockwise_nat_induction_proof` (Nat.rec combining base and
//! step) were **removed in #3519** when `blockwise_base` and
//! `blockwise_nat_induction` were demoted from `Declaration::Theorem` to
//! `Declaration::Axiom` to finalize the 2026-04-19 masquerade demotion.
//! The proof below is a different, hypothesis-wrapped statement: at k=0 the
//! indexed carriers reduce to the input bounds `B`, and the supplied
//! `B = zero_ib` witness proves both conjuncts via `And.intro`.
//!
//! See `nn_verify_blockwise_crown_defs` for the full rationale.
//!
//! Part of #3375, #3489, #3519.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use super::nn_verify_blockwise_crown_values::build_c006_zero_ib;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// =============================================================================
// Base case theorem type (strengthened — #3489)
// =============================================================================

/// Build type for `NNVerify.C006.blockwise_base`:
/// ```text
/// forall (block_dim : Nat -> Nat)
///   (crown_block : (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1)))
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1)))
///   (ln_eps : Rat)
///   (B : IB (block_dim 0)),
///   Eq (IB (block_dim 0)) B
///      (IntervalBounds.mk (block_dim 0)
///         (fun _ => Rat.zero) (fun _ => Rat.zero)
///         (fun _ => Rat.le_refl Rat.zero)) ->
///   And
///     (Eq (IB (block_dim 0))
///       (Block.compose 0 block_dim crown_block ln_gamma ln_beta ln_eps B)
///       (IntervalBounds.mk (block_dim 0)
///          (fun _ => Rat.zero) (fun _ => Rat.zero)
///          (fun _ => Rat.le_refl Rat.zero)))
///     (Eq (IB (block_dim 0))
///       (Block.monolithic_crown 0 block_dim crown_block ln_gamma ln_beta ln_eps B)
///       (IntervalBounds.mk (block_dim 0)
///          (fun _ => Rat.zero) (fun _ => Rat.zero)
///          (fun _ => Rat.le_refl Rat.zero)))
/// ```
///
/// **#3489 — why the And:** The previous statement was `compose 0 ... B =
/// monolithic 0 ... B`, which closes with `Eq.refl` only because `compose` and
/// `monolithic_crown` are reducibly defined with **identical** bodies. Under
/// that statement the theorem proves "zero_ib = zero_ib" and carries no
/// mathematical content beyond the alias.
///
/// The new statement quantifies over an **unrelated** term (the explicit
/// `IntervalBounds.mk` application returned by `build_c006_zero_ib`). The
/// Phase-1 carriers reduce at k=0 to the input `B`, so the theorem requires the
/// exact missing hypothesis `B = zero_ib` and reuses it for both conjuncts. The
/// original `compose 0 = monolithic 0` fact was derived via `Eq.trans
/// (And.left _) (Eq.symm (And.right _))` inside the former
/// `build_blockwise_nat_induction_proof` (removed in #3519 when the induction
/// theorem was demoted to an axiom).
///
/// Note: no `k` parameter — the base case is specifically at k=0.
pub(super) fn build_blockwise_base_type(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());
    let dim_0 = c.dim_at(&block_dim, c.nat_zero.clone());
    let ib_0 = c.ib_of(dim_0.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_0.clone());

    // Explicit zero_ib at dimension `block_dim 0` — a literal IntervalBounds.mk
    // term that is structurally distinct from `Block.compose 0 ...` / `Block.
    // monolithic_crown 0 ...` until reducibility kicks in. Referencing this
    // distinct term is what makes the theorem statement non-trivial.
    let zero_ib = build_c006_zero_ib(&mut b, c, &dim_0);

    let compose_app = Expr::apps(
        c.block_compose.clone(),
        [
            c.nat_zero.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let monolithic_app = Expr::apps(
        c.monolithic_crown.clone(),
        [
            c.nat_zero.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let left_eq = c.ib_eq(&dim_0, compose_app, zero_ib.clone());
    let right_eq = c.ib_eq(&dim_0, monolithic_app, zero_ib.clone());
    let input_eq = c.ib_eq(&dim_0, bnd.clone(), zero_ib);

    // And left_eq right_eq
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let conjunction = Expr::app(Expr::app(and_const, left_eq), right_eq);

    let (h_zero_id, _) = b.fresh_local(input_eq.clone());
    let e = b.mk_pi(h_zero_id, BinderInfo::Default, input_eq, conjunction);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_0, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}

/// Constructive proof for the hypothesis-wrapped base theorem:
/// ```text
/// fun block_dim crown_block ln_gamma ln_beta ln_eps B h_zero =>
///   And.intro h_zero h_zero
/// ```
///
/// Both uses of `h_zero` type-check because `Block.compose 0 ... B` and
/// `Block.monolithic_crown 0 ... B` iota-reduce to `B` under the Phase-1
/// indexed carriers.
pub(super) fn build_blockwise_base_proof(c: &BlockwiseCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let block_dim_ty = c.block_dim_ty();
    let (bd_id, block_dim) = b.fresh_local(block_dim_ty.clone());
    let crown_block_ty = c.crown_block_family_ty(&b, &block_dim);
    let (cb_id, crown_block) = b.fresh_local(crown_block_ty.clone());
    let ln_param_ty = c.ln_param_family_ty(&b, &block_dim);
    let (lg_id, ln_gamma) = b.fresh_local(ln_param_ty.clone());
    let (lb_id, ln_beta) = b.fresh_local(ln_param_ty.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());
    let dim_0 = c.dim_at(&block_dim, c.nat_zero.clone());
    let ib_0 = c.ib_of(dim_0.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_0.clone());
    let zero_ib = build_c006_zero_ib(&mut b, c, &dim_0);

    let compose_app = Expr::apps(
        c.block_compose.clone(),
        [
            c.nat_zero.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let monolithic_app = Expr::apps(
        c.monolithic_crown.clone(),
        [
            c.nat_zero.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let left_eq = c.ib_eq(&dim_0, compose_app, zero_ib.clone());
    let right_eq = c.ib_eq(&dim_0, monolithic_app, zero_ib.clone());
    let input_eq = c.ib_eq(&dim_0, bnd, zero_ib);
    let (h_zero_id, h_zero) = b.fresh_local(input_eq.clone());

    let body = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [left_eq, right_eq, h_zero.clone(), h_zero],
    );

    let e = b.mk_lam(h_zero_id, BinderInfo::Default, input_eq, body);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_0, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_lam(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_lam(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_lam(bd_id, BinderInfo::Default, block_dim_ty, e);
    b.finish(e)
}
