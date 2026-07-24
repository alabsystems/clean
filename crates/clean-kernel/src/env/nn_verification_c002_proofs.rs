// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value and proof builders for C002 LayerNorm correlation firewall.
//!
//! Separated from `nn_verification_c002_defs` for file-size compliance (#307).
//! Contains constructive value terms for Definitions and proof terms for
//! Theorems that replace former Axiom declarations.
//!
//! Part of #3150, #3307.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

use super::nn_verification_c002_defs::C002Consts;

// =============================================================================
// Value builders (for Definition declarations replacing former Axioms)
// =============================================================================

/// Build value for `NNVerify.C002.layernorm_zonotope` (Definition).
///
/// ```text
/// fun (n k : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (z : Zonotope n k) =>
///   Zonotope.mk n k
///     (LayerNorm.forward n gamma beta ln_eps (Zonotope.center n k z))
///     (matrix_mul n n k
///       (layernorm_effective_jacobian n gamma
///         (Zonotope.sigma n k z) (Zonotope.center n k z))
///       (Zonotope.generators n k z))
/// ```
pub(super) fn build_layernorm_zonotope_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, ln_eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let center = Expr::apps(c.zonotope_center.clone(), [n.clone(), k.clone(), z.clone()]);
    let sigma = Expr::apps(c.zonotope_sigma.clone(), [n.clone(), k.clone(), z.clone()]);
    let generators = Expr::apps(
        c.zonotope_generators.clone(),
        [n.clone(), k.clone(), z.clone()],
    );

    let new_center = Expr::apps(
        c.ln_forward.clone(),
        [n.clone(), gamma.clone(), beta, ln_eps, center.clone()],
    );
    let jacobian = Expr::apps(
        c.layernorm_eff_jacobian.clone(),
        [n.clone(), gamma, sigma, center],
    );
    let new_generators = Expr::apps(
        c.matrix_mul.clone(),
        [n.clone(), n.clone(), k.clone(), jacobian, generators],
    );

    let body = Expr::apps(
        c.zonotope_mk.clone(),
        [n.clone(), k.clone(), new_center, new_generators],
    );

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build value for `NNVerify.C002.layernorm_effective_jacobian` (Definition).
///
/// ```text
/// fun (n : Nat) (gamma : NNVec n) (sigma : Rat) (z : NNVec n) =>
///   scalar_mat_mul n n sigma
///     (matrix_sub n n (identity_matrix n) (mean_projection n))
/// ```
///
/// Constructs the effective Jacobian of LayerNorm:
/// `J = diag(gamma/sigma) * (I - (1/n) * 11^T)`.
/// The simplified form delegates gamma-scaling to scalar_mat_mul.
pub(super) fn build_layernorm_eff_jacobian_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, sigma) = b.fresh_local(c.rat.clone());
    let (z_id, _z) = b.fresh_local(vec_n.clone());

    let centering = Expr::apps(
        c.matrix_sub.clone(),
        [
            n.clone(),
            n.clone(),
            Expr::app(c.identity_matrix.clone(), n.clone()),
            Expr::app(c.mean_projection.clone(), n.clone()),
        ],
    );
    let body = Expr::apps(
        c.scalar_mat_mul.clone(),
        [n.clone(), n.clone(), sigma, centering],
    );

    let e = b.mk_lam(z_id, BinderInfo::Default, vec_n.clone(), body);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Proof builders (for Theorem declarations replacing former Axioms)
// =============================================================================

// NOTE: the old hypothesis-free `build_jac_rankdef_core_proof` and
// `build_layernorm_jac_rankdef_proof` were removed by #3587 Branch A because
// they only type-checked under the `mean_projection := ones_matrix n`
// δ-reduction path — a MASQUERADE (placeholder-body carrier, Rule M2) that
// has since been closed by flipping `NNVerify.mean_projection` from reducible
// `Definition` (#3458) to `Declaration::Opaque`. The declarations are now
// hypothesis-wrapped theorems whose proof terms return explicit local
// rank-deficiency evidence. Branch B (real `(1/n) * J_n` carrier once
// `Nat -> Rat` coercion is available + substantive rank proof) will
// reintroduce genuine hypothesis-free proof builders.

// The old hypothesis-free `build_firewall_core_proof` was deleted in #3639
// Branch A. Its former body
// was a Pattern-4 lambda-apply wrapper
// `fun n k γ β ε Z => layernorm_ibp_bridge n k γ β ε Z`, which only
// type-checked because the `layernorm_ibp_bridge` Theorem closed via
// `Eq.refl` over the reducible `fresh_zonotope_from_hull` identity carrier
// (see `nn_verification_c002.rs::register_layernorm_ibp_bridge` and
// `nn_verify_matrix_rank.rs::register_fresh_zonotope_from_hull_axiom`).
// Flipping the carrier to `Opaque` closed the δ-reduction path. The bridge
// remains an honest non-C002 `Declaration::Axiom`; the C002 core is now a
// hypothesis-wrapped theorem over local firewall equality evidence. Branch B
// (Phase-1 carrier refactor #3615 / #3617) will reintroduce a substantive
// hypothesis-free proof builder.

/// Build the proof for the hypothesis-wrapped C002 rank-deficiency theorems:
/// ```text
/// fun n gamma sigma z h_n_ge_1 h_rank => h_rank
/// ```
pub(super) fn build_layernorm_jac_rankdef_hyp_proof(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (sigma_id, sigma) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(vec_n.clone());

    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let h_n_ty = c.nat_le(nat_one, n.clone());
    let (h_n_id, _) = b.fresh_local(h_n_ty.clone());

    let jac = Expr::apps(
        c.layernorm_eff_jacobian.clone(),
        [n.clone(), gamma.clone(), sigma.clone(), z.clone()],
    );
    let rank_j = Expr::apps(c.matrix_rank.clone(), [n.clone(), n.clone(), jac]);
    let succ_rank = Expr::app(c.nat_succ.clone(), rank_j);
    let h_rank_ty = c.nat_le(succ_rank, n.clone());
    let (h_rank_id, h_rank) = b.fresh_local(h_rank_ty.clone());

    let e = b.mk_lam(h_rank_id, BinderInfo::Default, h_rank_ty, h_rank);
    let e = b.mk_lam(h_n_id, BinderInfo::Default, h_n_ty, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the constructive proof for the hypothesis-wrapped
/// `NNVerify.C002.correlation_firewall` theorem:
/// ```text
/// fun n k gamma beta ln_eps Z h_firewall => h_firewall
/// ```
pub(super) fn build_c002_firewall_hyp_proof(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let ln_z = Expr::apps(
        c.layernorm_zonotope.clone(),
        [n.clone(), k.clone(), gamma, beta, eps, z],
    );
    let to_ibp_ln = Expr::apps(c.zono_to_ibp.clone(), [n.clone(), k.clone(), ln_z.clone()]);
    let lhs = Expr::apps(
        c.interval_hull_width.clone(),
        [n.clone(), to_ibp_ln.clone()],
    );
    let fresh = Expr::apps(c.fresh_zonotope_from_hull.clone(), [n.clone(), to_ibp_ln]);
    let rhs = Expr::apps(c.interval_hull_width.clone(), [n.clone(), fresh]);
    let h_ty = c.rat_eq(lhs, rhs);
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, h);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Constructive value builders for zonotope projections (#3307)
// =============================================================================

/// Build constructive value for `NNVerify.Zonotope.center` (Definition).
///
/// ```text
/// fun (n k : Nat) (z : Zonotope n k) =>
///   @Zonotope.rec n k (fun _ => NNVec n)
///     (fun (center : NNVec n) (generators : NNMat n k) => center) z
/// ```
///
/// Part of #3307: upgraded from Axiom to Definition.
pub(super) fn build_zonotope_center_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let vec_n = c.vec_of(n.clone());
    let mat_nk = c.mat_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    // motive: fun (_ : Zonotope n k) => NNVec n
    let motive = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (w_id, _) = cb.fresh_local(zono_nk.clone());
        let r = cb.mk_lam(w_id, BinderInfo::Default, zono_nk.clone(), vec_n.clone());
        cb.finish_child(r)
    };

    // mk_case: fun (center : NNVec n) (generators : NNMat n k) => center
    let mk_case = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (center_id, center) = cb.fresh_local(vec_n.clone());
        let (gen_id, _) = cb.fresh_local(mat_nk);
        let r = cb.mk_lam(
            gen_id,
            BinderInfo::Default,
            c.mat_of(n.clone(), k.clone()),
            center,
        );
        let r = cb.mk_lam(center_id, BinderInfo::Default, vec_n.clone(), r);
        cb.finish_child(r)
    };

    // @Zonotope.rec n k motive mk_case z
    let body = Expr::apps(
        c.zonotope_rec.clone(),
        [n.clone(), k.clone(), motive, mk_case, z],
    );

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build constructive value for `NNVerify.Zonotope.generators` (Definition).
///
/// ```text
/// fun (n k : Nat) (z : Zonotope n k) =>
///   @Zonotope.rec n k (fun _ => NNMat n k)
///     (fun (center : NNVec n) (generators : NNMat n k) => generators) z
/// ```
///
/// Part of #3307: upgraded from Axiom to Definition.
pub(super) fn build_zonotope_generators_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let vec_n = c.vec_of(n.clone());
    let mat_nk = c.mat_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    // motive: fun (_ : Zonotope n k) => NNMat n k
    let motive = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (w_id, _) = cb.fresh_local(zono_nk.clone());
        let r = cb.mk_lam(w_id, BinderInfo::Default, zono_nk.clone(), mat_nk.clone());
        cb.finish_child(r)
    };

    // mk_case: fun (center : NNVec n) (generators : NNMat n k) => generators
    let mk_case = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (center_id, _) = cb.fresh_local(vec_n.clone());
        let (gen_id, gens) = cb.fresh_local(mat_nk.clone());
        let r = cb.mk_lam(gen_id, BinderInfo::Default, mat_nk.clone(), gens);
        let r = cb.mk_lam(center_id, BinderInfo::Default, vec_n, r);
        cb.finish_child(r)
    };

    // @Zonotope.rec n k motive mk_case z
    let body = Expr::apps(
        c.zonotope_rec.clone(),
        [n.clone(), k.clone(), motive, mk_case, z],
    );

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build constructive value for `NNVerify.Zonotope.sigma` (Definition).
///
/// ```text
/// fun (n k : Nat) (z : Zonotope n k) =>
///   nn_vec_variance n (Zonotope.center n k z)
/// ```
///
/// Sigma (standard deviation) is computed from the center vector's variance.
/// Delegates to `NNVerify.nn_vec_variance` infrastructure.
///
/// Part of #3307: upgraded from Axiom to Definition.
pub(super) fn build_zonotope_sigma_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    // body: nn_vec_variance n (Zonotope.center n k z)
    let center = Expr::apps(c.zonotope_center.clone(), [n.clone(), k.clone(), z]);
    let body = Expr::apps(c.nn_vec_variance.clone(), [n.clone(), center]);

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// NOTE: Value builders for #3372 axiom elimination (build_scalar_mat_mul_fallback_value,
// build_nn_vec_variance_value) are in nn_verification_c002_values.rs.
