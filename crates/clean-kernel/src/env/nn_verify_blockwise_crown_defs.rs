// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C006 theorem type builders — AXIOMATIZED (MASQUERADE DEMOTED 2026-04-19 to 2026-04-20).
//!
//! Split from `nn_verify_blockwise_crown` for file-size compliance. Contains
//! the shared `build_inner_prop` motive helper and the *type* builders for
//! `blockwise_step`, `blockwise_equals_monolithic`, and the
//! `follows_from_c004` implication.
//!
//! **Post-#3493 Branch A (2026-04-20) shape:** The proof-term builders that
//! previously lived alongside each type builder (`build_blockwise_step_proof`,
//! `build_blockwise_equals_monolithic_proof`) were deleted together with the
//! Declaration::Theorem registrations they fed. After #3489-#3493 demoted
//! the headline C006 claims to `Declaration::Axiom`, these functions became
//! dead code — no register site referenced them. The #3493 Branch A
//! cleanup removed them to match the honest axiom shape documented in
//! `data/axiom_audit.json` (`c006`: 5 axioms, `masquerade_demoted`). The
//! companion carrier flip — `Block.compose` / `Block.monolithic_crown`
//! from reducible `Declaration::Definition` to `Declaration::Opaque` with
//! SAME body (see `nn_verify_blockwise_crown_values.rs`) — closes the
//! δ-reduction loophole that previously let `Eq.refl` discharge the
//! headline claim through alias collapse. Prior versions of these proof
//! builders are preserved in git history.
//!
//! The base-case (`blockwise_base`) and induction combinator
//! (`blockwise_nat_induction`) live in `nn_verify_blockwise_crown_base`
//! (split out for #3489, when the base statement was strengthened from an
//! alias identity to an explicit `zero_ib` value characterization that uses
//! `And` / `And.intro` / `Eq.trans` / `Eq.symm`). See that module for the
//! rationale behind the strengthened statement.
//!
//! The `follows_from_c004` Opaque proposition-valued helper remains as an
//! Opaque returning `True` (Category A proposition-valued carrier).
//!
//! Part of #3375, #3489, #3493.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// =============================================================================
// Inner proposition helper
// =============================================================================

/// Build the inner proposition at a given `k` expression:
/// ```text
/// forall (B : IB (block_dim 0)),
///   Eq (IB (block_dim k))
///     (Block.compose k block_dim crown_block ln_gamma ln_beta ln_eps B)
///     (Block.monolithic_crown k block_dim crown_block ln_gamma ln_beta ln_eps B)
/// ```
///
/// The caller must have already allocated the free variables for
/// `block_dim`, `crown_block`, `ln_gamma`, `ln_beta`, `ln_eps`.
///
/// Shared with `nn_verify_blockwise_crown_base` so the base and induction-
/// combinator proof builders can construct the same motive shape.
pub(super) fn build_inner_prop(
    c: &BlockwiseCrownConsts,
    b: &EnvDeclBuilder,
    k: &Expr,
    block_dim: &Expr,
    crown_block: &Expr,
    ln_gamma: &Expr,
    ln_beta: &Expr,
    ln_eps: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let ib_0 = c.ib_of(c.dim_at(block_dim, c.nat_zero.clone()));
    let (bnd_id, bnd) = ch.fresh_local(ib_0.clone());

    let compose_result = Expr::apps(
        c.block_compose.clone(),
        [
            k.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let monolithic_result = Expr::apps(
        c.monolithic_crown.clone(),
        [
            k.clone(),
            block_dim.clone(),
            crown_block.clone(),
            ln_gamma.clone(),
            ln_beta.clone(),
            ln_eps.clone(),
            bnd.clone(),
        ],
    );
    let eq = c.ib_eq(
        &c.dim_at(block_dim, k.clone()),
        compose_result,
        monolithic_result,
    );
    let r = ch.mk_pi(bnd_id, BinderInfo::Default, ib_0, eq);
    ch.finish_child(r)
}

// =============================================================================
// Inductive step axiom type
// =============================================================================

/// Build type for `NNVerify.C006.blockwise_step`:
/// ```text
/// forall (k : Nat) (block_dim : Nat -> Nat)
///   (crown_block : (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1)))
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1)))
///   (ln_eps : Rat),
///   (forall B : IB (block_dim 0), Eq ... compose k ... B = monolithic k ... B)
///   -> (forall B : IB (block_dim 0), Eq ... compose (k+1) ... B = monolithic (k+1) ... B)
/// ```
///
/// Takes the induction hypothesis at k and produces the result at succ k.
/// Uses C004 at the LayerNorm boundary between blocks k and k+1.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_blockwise_step_type(c: &BlockwiseCrownConsts) -> Expr {
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

    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), step_body);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// NOTE (#3493 Branch A, 2026-04-20): `build_blockwise_step_proof` was
// deleted together with the `Declaration::Theorem` registration for
// `C006.blockwise_step` (demoted to `Declaration::Axiom` in #3491, see
// `register_blockwise_step` in `nn_verify_blockwise_crown.rs`). The prior
// body was a lambda that bound the induction hypothesis and discharged the
// conclusion with `Eq.refl` via δ-reduction of the carriers
// `Block.compose` / `Block.monolithic_crown` (both reducible Definitions
// whose body was `zero_ib (block_dim k)`). With those carriers now
// `Declaration::Opaque` and the theorem demoted to an axiom, the
// proof-term builder became dead code. The historical version (last
// present pre-#3493) is recoverable from git history — in the event a
// future pass implements substantive CROWN/IBP carriers and re-promotes
// the axioms, a new proof term must be written that actually references
// its induction hypothesis.

// =============================================================================
// Main theorem type
// =============================================================================

/// Build type for `NNVerify.C006.blockwise_equals_monolithic`:
/// ```text
/// forall (k : Nat) (block_dim : Nat -> Nat)
///   (crown_block : (i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1)))
///   (ln_gamma ln_beta : (i : Nat) -> NNVec (block_dim (i+1)))
///   (ln_eps : Rat)
///   (B : IntervalBounds (block_dim 0)),
///   Eq (IntervalBounds (block_dim k))
///     (Block.compose k block_dim crown_block ln_gamma ln_beta ln_eps B)
///     (Block.monolithic_crown k block_dim crown_block ln_gamma ln_beta ln_eps B)
/// ```
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_blockwise_equals_monolithic_type(c: &BlockwiseCrownConsts) -> Expr {
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

    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), inner);
    let e = b.mk_pi(lb_id, BinderInfo::Default, ln_param_ty.clone(), e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, ln_param_ty, e);
    let e = b.mk_pi(cb_id, BinderInfo::Default, crown_block_ty, e);
    let e = b.mk_pi(bd_id, BinderInfo::Default, block_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// NOTE (#3493 Branch A, 2026-04-20): `build_blockwise_equals_monolithic_proof`
// was deleted together with the `Declaration::Theorem` registration for
// `C006.blockwise_equals_monolithic` (demoted to `Declaration::Axiom` in
// #3493, see `register_blockwise_equals_monolithic_impl` in
// `nn_verify_blockwise_crown.rs`). The prior body was a lambda-apply
// wrapper that delegated to `C006.blockwise_nat_induction` (itself an
// axiom since #3492). A `Declaration::Theorem` whose proof term is
// `fun ... => axiom ...` is a restatement of that axiom, not a proof —
// per the design doc Proof Soundness Rules. The wrapper also closed
// trivially because the reducible carriers `Block.compose` /
// `Block.monolithic_crown` δ-collapsed both sides of the equality.
// Deleting the builder and flipping those carriers to
// `Declaration::Opaque` (#3493 Branch A in `..._values.rs`) closes the
// loophole. Historical version recoverable from git.

// =============================================================================
// C004 dependency implication
// =============================================================================

/// Build type for `NNVerify.C006.follows_from_c004`:
/// ```text
/// forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
///   Eq (IB n) (CROWN.backward_layernorm n gamma beta ln_eps B)
///             (IBP.forward_layernorm n gamma beta ln_eps B)
///   -> Prop
/// ```
/// The implication: C004 implies C006 (for any block count).
///
/// Since the conclusion is `Prop`, this is a proposition-valued function.
/// See `build_follows_from_c004_value` for the Opaque value.
pub(super) fn build_follows_from_c004_type(c: &BlockwiseCrownConsts) -> Expr {
    let crown_backward_ln = Expr::const_(
        Name::from_string("NNVerify.CROWN.backward_layernorm"),
        vec![],
    );
    let ibp_forward_ln = Expr::const_(Name::from_string("NNVerify.IBP.forward_layernorm"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let crown_app = Expr::apps(
        crown_backward_ln,
        [
            n.clone(),
            gamma.clone(),
            beta.clone(),
            eps.clone(),
            bnd.clone(),
        ],
    );
    let ibp_app = Expr::apps(ibp_forward_ln, [n.clone(), gamma, beta, eps, bnd]);
    let c004_hyp = c.ib_eq(&n, crown_app, ibp_app);

    let conclusion = c.prop.clone();

    let (hyp_id, _hyp) = b.fresh_local(c004_hyp.clone());
    let e = b.mk_pi(hyp_id, BinderInfo::Default, c004_hyp, conclusion);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build Opaque value for `NNVerify.C006.follows_from_c004`.
///
/// Since the type's conclusion is `Prop`, we return `True` for any input:
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (eps : Rat) (B : IB n)
///     (_ : Eq (IB n) (CROWN.backward_layernorm ...) (IBP.forward_layernorm ...)) =>
///   True
/// ```
///
/// Category A: proposition-valued function — the axiom just says "given C004,
/// there exists _some_ proposition", which is trivially satisfied by `True`.
pub(super) fn build_follows_from_c004_value(c: &BlockwiseCrownConsts) -> Expr {
    let crown_backward_ln = Expr::const_(
        Name::from_string("NNVerify.CROWN.backward_layernorm"),
        vec![],
    );
    let ibp_forward_ln = Expr::const_(Name::from_string("NNVerify.IBP.forward_layernorm"), vec![]);
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let crown_app = Expr::apps(
        crown_backward_ln,
        [
            n.clone(),
            gamma.clone(),
            beta.clone(),
            eps.clone(),
            bnd.clone(),
        ],
    );
    let ibp_app = Expr::apps(ibp_forward_ln, [n.clone(), gamma, beta, eps, bnd]);
    let c004_hyp = c.ib_eq(&n, crown_app, ibp_app);

    let (hyp_id, _hyp) = b.fresh_local(c004_hyp.clone());
    let e = b.mk_lam(hyp_id, BinderInfo::Default, c004_hyp, true_const);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
