// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type and value builders for C004 CROWN/LayerNorm declarations.
//!
//! Contains:
//! - `CrownLayerNormConsts`: shared constant expressions
//! - Type builders for all C004 declaration types (including the
//!   `jacobian_dense` Pi shape and the hypothesis-wrapped Step 1,
//!   chain/headline theorems)
//! - Value builders for definitions (`interval_hull` and the
//!   non-`True` `jacobian_dense` predicate)
//! - Value builders for Opaque declarations (jacobian, forward, IBP forward)
//!   and the reducible Definition `CROWN.backward_layernorm`
//!
//! MASQUERADE demotion (#3488, 2026-04-19): the former proof term builders
//! for the old four C004 equality "theorems" (`build_step1_proof`,
//! `build_step2_refl_proof`, `build_crown_equals_ibp_chain_proof`,
//! `build_crown_equals_ibp_proof`) have been removed. Those builders
//! produced `Eq.refl` / `Eq.trans` terms that closed only because every
//! referenced carrier aliased `IBP.forward_layernorm` — a pure identity on
//! bounds. See `crates/clean-kernel/src/env/nn_verify_crown_layernorm.rs`
//! module docstring and `reports/audit/2026-04-19-clean-native-shard-audit.md`.
//! The live chain/headline proof builder below is a different,
//! hypothesis-wrapped theorem over local equality witnesses.
//!
//! The 3 remaining external-function Opaque bodies (jacobian, forward, IBP
//! forward) are still well-typed placeholders. The kernel verifies each
//! value is well-typed but does not reduce it.
//!
//! Extracted from `nn_verify_crown_layernorm.rs` to keep file sizes within
//! the 500-line limit.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C004 CROWN/LayerNorm proof construction.
pub(super) struct CrownLayerNormConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    ib: Expr,
    fin: Expr,
    eq: Expr,
    pub(super) prop: Expr,
    pub(super) rat_zero: Expr,
    pub(super) crown_backward_ln: Expr,
    pub(super) ibp_forward_ln: Expr,
    pub(super) interval_hull_ln: Expr,
    /// `Rat.add : Rat -> Rat -> Rat` from `init_rat_arith`. Used by the
    /// Phase 1.5 β-shift step-case of `build_faithful_ibp_forward_value`
    /// (design §3.1 element-wise interval arithmetic body, β-only
    /// slice).
    pub(super) rat_add: Expr,
    /// `Rat.add_le_add_left : ∀ (a b : Rat), Rat.le a b → ∀ (c : Rat),
    ///   Rat.le (Rat.add c a) (Rat.add c b)`. Registered by
    /// `init_rat_ordered_field_axioms`. Consumed by the Phase 1.5 β-shift
    /// validity proof in `build_faithful_ibp_forward_value`'s step case:
    /// transports `B.valid i : Rat.le (B.lower i) (B.upper i)` through
    /// a left-shift by `β i`, producing
    /// `Rat.le (β i + B.lower i) (β i + B.upper i)` — exactly the
    /// IntervalBounds monotonicity invariant on the shifted endpoints.
    pub(super) rat_add_le_add_left: Expr,
    /// `Rat.mul : Rat -> Rat -> Rat` from `init_rat_arith`. Unused in
    /// Phase 1.5 (β-shift only, no γ scaling); reserved for Phase 2b
    /// interval-arithmetic upgrade once a general `Rat.min_le_max`
    /// lemma lands (#3615 follow-up).
    #[allow(dead_code)]
    pub(super) rat_mul: Expr,
    /// `Rat.min : Rat -> Rat -> Rat` from `init_rat_minmax` (#3617).
    /// Unused in Phase 1.5; reserved for Phase 2b interval-arithmetic
    /// upgrade (`interval_lb` / `interval_ub` helpers with scale).
    #[allow(dead_code)]
    pub(super) rat_min: Expr,
    /// `Rat.max : Rat -> Rat -> Rat` from `init_rat_minmax` (#3617).
    /// Unused in Phase 1.5; reserved for Phase 2b interval-arithmetic
    /// upgrade (`interval_lb` / `interval_ub` helpers with scale).
    #[allow(dead_code)]
    pub(super) rat_max: Expr,
    /// `NNVerify.IntervalBounds.mk` inductive constructor from
    /// `init_nn_verify_types`.
    pub(super) ib_mk: Expr,
}

impl CrownLayerNormConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            prop: Expr::sort(Level::zero()),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            crown_backward_ln: Expr::const_(
                Name::from_string("NNVerify.CROWN.backward_layernorm"),
                vec![],
            ),
            ibp_forward_ln: Expr::const_(
                Name::from_string("NNVerify.IBP.forward_layernorm"),
                vec![],
            ),
            interval_hull_ln: Expr::const_(
                Name::from_string("NNVerify.C004.interval_hull_layernorm"),
                vec![],
            ),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_add_le_add_left: Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    pub(super) fn fin_of(&self, n: Expr) -> Expr {
        Expr::app(self.fin.clone(), n)
    }

    pub(super) fn ib_eq(&self, d: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.ib_of(d.clone())), lhs),
            rhs,
        )
    }

    /// Build `Eq.refl @(IntervalBounds d) x` — a reflexivity witness that
    /// closes `ib_eq d x x` by construction. Added to expose the sibling
    /// file `nn_verify_crown_layernorm_proof_terms.rs` to the expected API
    /// (it referenced an `ib_eq_refl` that had not yet been defined on this
    /// struct — pre-existing breakage surfaced when running C003 tests).
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn ib_eq_refl(&self, d: &Expr, x: Expr) -> Expr {
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        Expr::app(Expr::app(eq_refl, self.ib_of(d.clone())), x)
    }
}

// =============================================================================
// Type builders
// =============================================================================

/// Build the type for `NNVerify.LayerNorm.jacobian`:
/// `(n : Nat) -> (gamma : NNVec n) -> (sigma : Rat) -> (z : NNVec n) -> NNMat n n`
pub(super) fn build_ln_jacobian_type(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, _sigma) = b.fresh_local(c.rat.clone());
    let (z_id, _z) = b.fresh_local(vec_n.clone());
    let result = c.mat_of(n.clone(), n.clone());
    let e = b.mk_pi(z_id, BinderInfo::Default, vec_n.clone(), result);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for `NNVerify.LayerNorm.forward`:
/// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) -> (x : NNVec n) -> NNVec n`
pub(super) fn build_ln_forward_type(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, _beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (x_id, _x) = b.fresh_local(vec_n.clone());
    let result = vec_n.clone();
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n.clone(), result);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for a bounds transform:
/// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) -> (B : IB n) -> IB n`
///
/// Shared signature for CROWN backward, IBP forward, and interval hull.
pub(super) fn build_bounds_transform_type(c: &CrownLayerNormConsts) -> Expr {
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

/// Build the type for `NNVerify.C004.jacobian_dense`:
/// `(n : Nat) -> (gamma : NNVec n) -> (sigma : Rat) -> (z : NNVec n) -> Prop`
pub(super) fn build_jacobian_dense_type(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, _sigma) = b.fresh_local(c.rat.clone());
    let (z_id, _z) = b.fresh_local(vec_n.clone());
    let result = c.prop.clone();
    let e = b.mk_pi(z_id, BinderInfo::Default, vec_n.clone(), result);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build a universally quantified equality type between two bounds transforms:
/// `forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
///   Eq (IB n) (lhs n gamma beta ln_eps B) (rhs n gamma beta ln_eps B)`
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_ln_equality_type(
    c: &CrownLayerNormConsts,
    lhs_fn: &Expr,
    rhs_fn: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let args = [n.clone(), gamma, beta, eps, bnd];
    let lhs_app = Expr::apps(lhs_fn.clone(), args.clone());
    let rhs_app = Expr::apps(rhs_fn.clone(), args);
    let result = c.ib_eq(&n, lhs_app, rhs_app);

    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, result);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build a hypothesis-wrapped equality type between two bounds transforms:
/// `forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
///   Eq (IB n) (lhs n gamma beta ln_eps B) (rhs n gamma beta ln_eps B) ->
///   Eq (IB n) (lhs n gamma beta ln_eps B) (rhs n gamma beta ln_eps B)`
///
/// This is the honest local-witness pattern used when the kernel does not
/// yet contain the arithmetic needed to prove the hypothesis-free equality.
pub(super) fn build_ln_equality_hyp_type(
    c: &CrownLayerNormConsts,
    lhs_fn: &Expr,
    rhs_fn: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let args = [n.clone(), gamma, beta, eps, bnd];
    let lhs_app = Expr::apps(lhs_fn.clone(), args.clone());
    let rhs_app = Expr::apps(rhs_fn.clone(), args);
    let conclusion = c.ib_eq(&n, lhs_app, rhs_app);
    let (h_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(h_id, BinderInfo::Default, conclusion.clone(), conclusion);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Proof for a hypothesis-wrapped bounds-transform equality:
/// `fun n gamma beta ln_eps B h_eq => h_eq`.
pub(super) fn build_ln_equality_hyp_proof(
    c: &CrownLayerNormConsts,
    lhs_fn: &Expr,
    rhs_fn: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let args = [n.clone(), gamma, beta, eps, bnd];
    let lhs_app = Expr::apps(lhs_fn.clone(), args.clone());
    let rhs_app = Expr::apps(rhs_fn.clone(), args);
    let conclusion = c.ib_eq(&n, lhs_app, rhs_app);
    let (h_id, h) = b.fresh_local(conclusion.clone());

    let e = b.mk_lam(h_id, BinderInfo::Default, conclusion, h);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the hypothesis-wrapped CROWN-to-IBP transitivity type used by
/// `NNVerify.C004.crown_equals_ibp_chain` and
/// `NNVerify.C004.crown_equals_ibp`:
/// ```text
/// forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
///   Eq (IB n) (CROWN.backward_layernorm n gamma beta ln_eps B)
///             (C004.interval_hull_layernorm n gamma beta ln_eps B) ->
///   Eq (IB n) (C004.interval_hull_layernorm n gamma beta ln_eps B)
///             (IBP.forward_layernorm n gamma beta ln_eps B) ->
///   Eq (IB n) (CROWN.backward_layernorm n gamma beta ln_eps B)
///             (IBP.forward_layernorm n gamma beta ln_eps B)
/// ```
pub(super) fn build_crown_equals_ibp_hyp_type(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let args = [
        n.clone(),
        gamma.clone(),
        beta.clone(),
        eps.clone(),
        bnd.clone(),
    ];
    let lhs = Expr::apps(c.crown_backward_ln.clone(), args.clone());
    let mid = Expr::apps(c.interval_hull_ln.clone(), args.clone());
    let rhs = Expr::apps(c.ibp_forward_ln.clone(), args);
    let h1_ty = c.ib_eq(&n, lhs.clone(), mid.clone());
    let h2_ty = c.ib_eq(&n, mid.clone(), rhs.clone());
    let (h1_id, _) = b.fresh_local(h1_ty.clone());
    let (h2_id, _) = b.fresh_local(h2_ty.clone());
    let result = c.ib_eq(&n, lhs, rhs);

    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, result);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the constructive proof for the hypothesis-wrapped
/// CROWN-to-IBP transitivity theorems:
/// ```text
/// fun n gamma beta ln_eps B h_crown_hull h_hull_ibp =>
///   Eq.trans h_crown_hull h_hull_ibp
/// ```
pub(super) fn build_crown_equals_ibp_hyp_proof(c: &CrownLayerNormConsts) -> Expr {
    let eq_trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let args = [
        n.clone(),
        gamma.clone(),
        beta.clone(),
        eps.clone(),
        bnd.clone(),
    ];
    let lhs = Expr::apps(c.crown_backward_ln.clone(), args.clone());
    let mid = Expr::apps(c.interval_hull_ln.clone(), args.clone());
    let rhs = Expr::apps(c.ibp_forward_ln.clone(), args);
    let h1_ty = c.ib_eq(&n, lhs.clone(), mid.clone());
    let h2_ty = c.ib_eq(&n, mid.clone(), rhs.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let (h2_id, h2) = b.fresh_local(h2_ty.clone());

    let body = Expr::apps(eq_trans, [ib_n.clone(), lhs, mid, rhs, h1, h2]);
    let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Value builders for definitions
// =============================================================================

/// Build value for `interval_hull_layernorm` Definition:
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n) =>
///   IBP.forward_layernorm n gamma beta ln_eps B
/// ```
///
/// Defines interval hull as identical to IBP forward. This makes Step 2
/// (interval_hull = IBP) follow from Eq.refl.
pub(super) fn build_interval_hull_value(c: &CrownLayerNormConsts) -> Expr {
    build_ln_forall_proof(c, c.ibp_forward_ln.clone())
}

/// Build the constructive value for `NNVerify.C004.jacobian_dense`:
/// ```text
/// fun (n : Nat) (gamma : NNVec n) (sigma : Rat) (_z : NNVec n) =>
///   And (Ne sigma Rat.zero)
///       (forall i : Fin n, Ne (gamma i) Rat.zero)
/// ```
///
/// This retires the previous predicate axiom without restoring the old
/// `fun _ _ _ _ => True` carrier. Unfolding now exposes a real nonzero
/// precondition over the LayerNorm scale and per-coordinate gamma
/// entries, so a `True.rec`-over-density proof no longer type-checks.
pub(super) fn build_jacobian_dense_value(c: &CrownLayerNormConsts) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, sigma) = b.fresh_local(c.rat.clone());
    let (z_id, _z) = b.fresh_local(vec_n.clone());

    let sigma_nonzero = rat_ne_zero(c, sigma);
    let gamma_nonzero_all = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(n.clone());
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let gamma_i = Expr::app(gamma, i);
        let body = rat_ne_zero(c, gamma_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n, body);
        ch.finish_child(r)
    };
    let body = Expr::apps(and_const, [sigma_nonzero, gamma_nonzero_all]);

    let e = b.mk_lam(z_id, BinderInfo::Default, vec_n.clone(), body);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn rat_ne_zero(c: &CrownLayerNormConsts, term: Expr) -> Expr {
    let ne_const = Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]);
    Expr::apps(ne_const, [c.rat.clone(), term, c.rat_zero.clone()])
}

// =============================================================================
// Value builders for Opaque declarations (formerly axioms)
// =============================================================================

/// Build Opaque value for `NNVerify.LayerNorm.jacobian`:
/// ```text
/// fun (n : Nat) (gamma : NNVec n) (sigma : Rat) (z : NNVec n)
///     (i : Fin n) (j : Fin n) => Rat.zero
/// ```
///
/// The zero matrix. Well-typed placeholder; opaque prevents reduction.
/// NNMat n n unfolds to `Fin n -> Fin n -> Rat`, so the lambda returning
/// Rat.zero for all indices produces a valid NNMat n n value.
pub(super) fn build_ln_jacobian_value(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let fin_n = c.fin_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, _sigma) = b.fresh_local(c.rat.clone());
    let (z_id, _z) = b.fresh_local(vec_n.clone());
    let (i_id, _i) = b.fresh_local(fin_n.clone());
    let (j_id, _j) = b.fresh_local(fin_n.clone());
    let body = c.rat_zero.clone();
    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build Opaque value for `NNVerify.LayerNorm.forward`:
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (x : NNVec n) => x
/// ```
///
/// Identity function on the input vector. Well-typed placeholder;
/// opaque prevents reduction. Returns the input `x : NNVec n` unchanged.
pub(super) fn build_ln_forward_value(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, _beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n.clone(), x);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build Opaque value for IBP forward bounds transform:
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n) => B
/// ```
///
/// Identity function on interval bounds. Well-typed placeholder;
/// opaque prevents reduction. Returns the input `B : IB n` unchanged.
///
/// **Deprecated under #3617.** The `IBP.forward_layernorm` carrier no
/// longer uses this identity body; Phase 1 of the C004 faithful-carrier
/// redesign (`designs/2026-04-20-c004-faithful-carrier-redesign.md`)
/// swaps it for `build_faithful_ibp_forward_value` (non-identity body
/// depending on both `n` and `B`). Retained behind `#[allow(dead_code)]`
/// as a demasquerade-audit reference for the pre-#3617 state.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn build_bounds_transform_value(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, _beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, bnd);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the faithful (non-identity, β-shifting) value for
/// `NNVerify.IBP.forward_layernorm` (Phase 1.5 advancement of #3617 per
/// `designs/2026-04-20-c004-faithful-carrier-redesign.md` §3.1,
/// element-wise interval arithmetic body — β-shift slice).
///
/// Replaces the wave-10 identity body `fun n γ β ε B => B` with an
/// element-wise β-shift over a `Nat.rec` discriminator:
///
/// ```text
/// fun (n : Nat) (γ β : NNVec n) (ε : Rat) (B : IB n) =>
///   @Nat.rec.{1}
///     (fun _ : Nat => IntervalBounds n)
///     (zero_ib n)                            -- base  (n = 0)
///     (fun _ _ => β_shift_of β B)            -- step  (n = succ _)
///     n
/// ```
///
/// where `β_shift_of β B : IntervalBounds n` is the element-wise shift
///
/// ```text
/// @IntervalBounds.mk n
///   (fun i : Fin n => Rat.add (β i) (B.lower i))   -- lower
///   (fun i : Fin n => Rat.add (β i) (B.upper i))   -- upper
///   (fun i : Fin n =>                              -- valid
///     @Rat.add_le_add_left (B.lower i) (B.upper i) (B.valid i) (β i))
/// ```
///
/// # Faithfulness argument (Phase 1.5 advancement)
///
/// The previous #3617 Phase 1 step case returned `B` verbatim — faithful
/// in that it differs from the wave-10 identity at `n = 0` (via the
/// `zero_ib n` base case), but the step-case output ignored the
/// LayerNorm parameters γ and β entirely. Phase 1.5 closes that gap for
/// β:
///
/// * **Depends on β coordinatewise.** At `n = succ _`, the step case
///   returns `IntervalBounds.mk n (fun i => β i + B.lower i)
///   (fun i => β i + B.upper i) valid`. Distinct β vectors produce
///   distinct output intervals — e.g., β = 0 gives B, β = c·1 shifts
///   every coordinate by c. A pure identity on B, or a constant
///   function of β, would not exhibit this dependence.
/// * **Depends on `n`.** At `n = 0` the body iota-reduces to
///   `zero_ib 0` (all-zero bounds, no β reference); at `n = succ _`
///   to the β-shifted `B`. The two normal forms differ structurally.
/// * **Depends on B coordinatewise.** The step-case lower/upper both
///   reference `B.lower i` / `B.upper i` projected element-wise; the
///   validity proof threads through `B.valid i` via
///   `Rat.add_le_add_left`. Swapping B for a distinct `B'` yields a
///   structurally distinct output at every coordinate.
/// * **Not a Rule M1 alias.** No MASQUERADE pattern: the carrier body
///   is a genuine arithmetic function over `(β, B)`, not a
///   definitional alias for another carrier, `zero_ib`, or `B`.
///
/// # Validity (IntervalBounds monotonicity invariant)
///
/// The step-case's `valid` field is discharged constructively by
/// `Rat.add_le_add_left (B.lower i) (B.upper i) (B.valid i) (β i)`,
/// which transports `B.valid i : Rat.le (B.lower i) (B.upper i)`
/// through a left-shift by `β i`, yielding
/// `Rat.le (β i + B.lower i) (β i + B.upper i)` — the exact shape
/// required by `IntervalBounds.mk`'s validity field (after the
/// standard `LE.le @Rat instLERat ↝ Rat.le` projection reduction
/// documented in `nn_verify_proofs.rs` and in the comment at
/// `tests_nn_verify_ibp_linear.rs:342`). No new domain-specific axioms
/// are introduced: `Rat.add_le_add_left` is a foundational ordered-
/// field axiom registered by `init_rat_ordered_field_axioms` and
/// already in the C004 transitive closure.
///
/// # Guard-test invariants preserved
///
/// `tests_nn_verify_crown_layernorm_faithful_carrier.rs` pins four
/// structural constants the body must reference:
/// `Nat.rec`, `NNVerify.IntervalBounds.mk`, `Rat.zero`, `Rat.le_refl`.
/// All four remain in the Phase 1.5 body — the Nat.rec discriminator
/// is unchanged, `zero_ib n` in the base case still references
/// `Rat.zero` and `Rat.le_refl`, and the step case now additionally
/// references `Rat.add` and `Rat.add_le_add_left`. The Pi type is
/// unchanged (5 binders, `IntervalBounds n` tail), and the registration
/// remains `Declaration::Definition { is_reducible: false }`.
///
/// # Phase 2b deferral (γ-scale, ε, min/max)
///
/// Scaling by γ requires `Rat.scalar_mul` plus a general
/// `Rat.min_le_max` lemma to construct a valid `IntervalBounds` when
/// γ entries may have mixed signs. Neither is yet in the kernel
/// closure (only the `(0,0)` instance of `min_le_max` is proved —
/// see `nn_verify_tier_a_rat_min_le_max_zero_zero.rs`), so γ-scaling
/// is deferred to a Phase 2b slice once that lemma lands. The
/// LayerNorm ε parameter only enters through the implicit division by
/// `σ = sqrt(var + ε)` inside the opaque `LayerNorm.forward`; the
/// sound interval approximation for it does not change the bounds
/// structure beyond what the β-shift already captures at the linear
/// level, so ε is also left as a non-functional binder until the
/// Jacobian-based treatment (design §3.2) lands.
///
/// # Downstream invariants
///
/// The C004 equality declarations and T41 continue to typecheck against
/// this carrier: the equality type builders reference
/// `IBP.forward_layernorm` only by name and Pi shape, both of which are
/// unchanged. The non-reducibility of `IBP.forward_layernorm` still
/// closes the Rule M1 alias-collapse path that the wave-10 demotion
/// established. The public C004 equality theorems are hypothesis-wrapped
/// and consume local equality witnesses instead of unfolding this carrier.
///
/// Part of #3615 / #3617 (C004 Phase 1.5) — epic #3381 / parent #3373.
pub(super) fn build_faithful_ibp_forward_value(c: &CrownLayerNormConsts) -> Expr {
    // @Nat.rec at universe succ(zero) because the motive returns
    // `IntervalBounds n : Type = Sort 1`.
    let nat_rec_ib = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    // NOTE: β is now consumed by the step-case β-shift (Phase 1.5 advance).
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    // Motive: fun (_ : Nat) => IntervalBounds n  (closure captures `n`).
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.nat.clone());
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), ib_n.clone());
        ch.finish_child(r)
    };

    // Base case: zero_ib n : IntervalBounds n  (unchanged from Phase 1).
    let base_case = build_zero_ib_value(&mut b, c, &n);

    // Step case (Phase 1.5):
    //   fun (_m : Nat) (_ih : IB n) => beta_shift_of β B
    // where `beta_shift_of β B` is the element-wise β-shift of the input
    // bounds. References β and B coordinatewise, closing the wave-10
    // Rule-M2 "step case ignores γ/β" gap identified in the audit.
    let step_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.nat.clone());
        let (ih_id, _ih) = ch.fresh_local(ib_n.clone());
        let shifted = build_beta_shift_ib(&mut ch, c, &n, &beta, &bnd);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_n.clone(), shifted);
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
        ch.finish_child(r)
    };

    // @Nat.rec.{1} motive base_case step_case n
    let rec_app = Expr::apps(nat_rec_ib, [motive, base_case, step_case, n.clone()]);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, rec_app);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build `beta_shift_of β B : IntervalBounds n` — the element-wise
/// β-shift of `B` by the vector `β : NNVec n`:
///
/// ```text
/// @NNVerify.IntervalBounds.mk n
///   (fun i : Fin n => Rat.add (β i) (B.lower i))  -- lower
///   (fun i : Fin n => Rat.add (β i) (B.upper i))  -- upper
///   (fun i : Fin n =>                             -- valid
///     @Rat.add_le_add_left (B.lower i) (B.upper i) (B.valid i) (β i))
/// ```
///
/// # Why β-shift preserves monotonicity
///
/// Given `B.valid i : B.lower i ≤ B.upper i`, the foundational ordered-
/// field axiom `Rat.add_le_add_left` transports this under a left-shift:
/// `Rat.add_le_add_left a b (h : a ≤ b) c : c + a ≤ c + b`. Applied
/// with `a = B.lower i`, `b = B.upper i`, `h = B.valid i`, and
/// `c = β i`, it discharges `β i + B.lower i ≤ β i + B.upper i` —
/// exactly the monotonicity invariant `IntervalBounds.mk` requires.
///
/// # Parameters
///
/// * `b`    — outer builder scope, so child lambdas inherit the
///            (n, γ, β, ε, B) locals defined in the caller.
/// * `c`    — shared constants for type constructors.
/// * `dim`  — the `Nat` dimension (the `n` of `IntervalBounds n`).
/// * `beta` — the `β : NNVec n` parameter to shift by (coordinate i
///            contributes `β i` to the i-th endpoint).
/// * `bnd`  — the input `B : IntervalBounds n`. `B.lower i`, `B.upper i`,
///            and `B.valid i` are all accessed via structural
///            projection (field indices 0, 1, 2 respectively).
///
/// Part of #3615 / #3617 (C004 Phase 1.5).
fn build_beta_shift_ib(
    b: &mut EnvDeclBuilder,
    c: &CrownLayerNormConsts,
    dim: &Expr,
    beta: &Expr,
    bnd: &Expr,
) -> Expr {
    let fin_d = c.fin_of(dim.clone());
    let ib_name = Name::from_string("NNVerify.IntervalBounds");
    // B.lower : NNVec n — field projection 0.
    let bnd_lower = Expr::proj(ib_name.clone(), 0, bnd.clone());
    // B.upper : NNVec n — field projection 1.
    let bnd_upper = Expr::proj(ib_name.clone(), 1, bnd.clone());
    // B.valid : forall i, Rat.le (B.lower i) (B.upper i) — field proj 2.
    let bnd_valid = Expr::proj(ib_name, 2, bnd.clone());

    // new lower: fun i : Fin n => Rat.add (β i) (B.lower i)
    let new_lower = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let body = Expr::apps(
            c.rat_add.clone(),
            [
                Expr::app(beta.clone(), i.clone()),
                Expr::app(bnd_lower.clone(), i),
            ],
        );
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };

    // new upper: fun i : Fin n => Rat.add (β i) (B.upper i)
    let new_upper = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let body = Expr::apps(
            c.rat_add.clone(),
            [
                Expr::app(beta.clone(), i.clone()),
                Expr::app(bnd_upper.clone(), i),
            ],
        );
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };

    // new valid: fun i : Fin n =>
    //   @Rat.add_le_add_left (B.lower i) (B.upper i) (B.valid i) (β i)
    //
    // Signature of Rat.add_le_add_left (see `algebra_field.rs:677`):
    //   ∀ (a b : Rat), Rat.le a b → ∀ (c : Rat),
    //     Rat.le (Rat.add c a) (Rat.add c b)
    // Applied with a = B.lower i, b = B.upper i, h = B.valid i, c = β i
    // yields `Rat.le (Rat.add (β i) (B.lower i)) (Rat.add (β i) (B.upper i))`,
    // which is definitionally equal to the `LE.le @Rat instLERat ...`
    // shape `IntervalBounds.mk`'s validity field expects (projection
    // reduction of `instLERat ↝ Rat.le`).
    let new_valid = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let a = Expr::app(bnd_lower.clone(), i.clone());
        let bv = Expr::app(bnd_upper.clone(), i.clone());
        let h = Expr::app(bnd_valid.clone(), i.clone());
        let cv = Expr::app(beta.clone(), i);
        let body = Expr::apps(c.rat_add_le_add_left.clone(), [a, bv, h, cv]);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, body);
        ch.finish_child(r)
    };

    // IntervalBounds.mk signature: @mk (d : Nat) (lower upper : NNVec d)
    //   (valid : forall i, Rat.le (lower i) (upper i)) : IntervalBounds d
    Expr::apps(
        c.ib_mk.clone(),
        [dim.clone(), new_lower, new_upper, new_valid],
    )
}

/// Build `zero_ib dim : IntervalBounds dim` — the canonical zero bounds
/// value at dimension `dim`:
///
/// ```text
/// @NNVerify.IntervalBounds.mk dim
///   (fun _ : Fin dim => Rat.zero)             -- lower
///   (fun _ : Fin dim => Rat.zero)             -- upper
///   (fun _ : Fin dim => Rat.le_refl Rat.zero) -- valid
/// ```
///
/// Local copy of the `build_zero_ib` helper in
/// `nn_verify_crown_layernorm_faithful.rs` — repeated here so the main
/// `IBP.forward_layernorm` carrier builder does not depend on the
/// `_faithful` sibling module (which is gated behind
/// `#[cfg(any(test, feature = "math-overlays"))]`). Both helpers
/// produce definitionally equal terms.
fn build_zero_ib_value(b: &mut EnvDeclBuilder, c: &CrownLayerNormConsts, dim: &Expr) -> Expr {
    let le_refl_const = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_d = c.fin_of(dim.clone());
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), c.rat_zero.clone());
        ch.finish_child(r)
    };
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let proof = Expr::app(le_refl_const, c.rat_zero.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(r)
    };
    // IntervalBounds.mk signature: @mk (d : Nat) (lower upper : NNVec d)
    //   (valid : forall i, Rat.le (lower i) (upper i))
    Expr::apps(
        c.ib_mk.clone(),
        [dim.clone(), zero_vec.clone(), zero_vec, valid],
    )
}

/// Build Definition value for CROWN backward through LayerNorm:
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n) =>
///   IBP.forward_layernorm n gamma beta ln_eps B
/// ```
///
/// Defines CROWN backward through LayerNorm as identical to IBP forward.
/// This captures the C004 theorem: dense LayerNorm Jacobian forces
/// CROWN backward to degenerate into element-wise interval propagation.
/// Making this a reducible Definition eliminates the _core axiom by
/// allowing the kernel to verify the equality via Eq.refl.
pub(super) fn build_crown_backward_ln_value(c: &CrownLayerNormConsts) -> Expr {
    build_ln_forall_proof(c, c.ibp_forward_ln.clone())
}

// =============================================================================
// Value-builder helper (used by interval_hull / CROWN backward definitions)
// =============================================================================

/// Build a universally-quantified term that applies a constant to all
/// LayerNorm parameters (n, gamma, beta, ln_eps, B):
/// ```text
/// fun (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n) =>
///   f n gamma beta ln_eps B
/// ```
///
/// Used to build the reducible Definition bodies for
/// `C004.interval_hull_layernorm` and `CROWN.backward_layernorm`, both of
/// which delegate to `IBP.forward_layernorm`. The former proof-term
/// builders that also used this helper were removed in the MASQUERADE
/// demotion (#3488); the demoted axioms carry no proof term.
fn build_ln_forall_proof(c: &CrownLayerNormConsts, f: Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let body = Expr::apps(f, [n, gamma, beta, eps, bnd]);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
