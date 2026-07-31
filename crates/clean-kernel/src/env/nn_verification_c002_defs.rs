// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type and value builders for C002 LayerNorm correlation firewall.
//!
//! Separated from `nn_verification_c002` for file-size compliance (#307).
//! All `build_*` functions return well-formed `Expr` types/values for
//! kernel declaration registration.
//!
//! Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// Additional constants used for constructive proof terms.
// These reference existing infrastructure registered by dependency init calls.

/// Shared constants for C002 theorem construction.
///
/// Uses the properly typed `NNVerify.*` infrastructure (zonotope types,
/// LayerNorm definitions, matrix rank operations) rather than the
/// placeholder `NNVerification.*` axioms.
pub(super) struct C002Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    #[cfg(test)]
    pub(super) ib: Expr,
    pub(super) eq: Expr,
    pub(super) zonotope: Expr,
    pub(super) zono_to_ibp: Expr,
    pub(super) interval_hull_width: Expr,
    pub(super) fresh_zonotope_from_hull: Expr,
    pub(super) layernorm_zonotope: Expr,
    pub(super) layernorm_eff_jacobian: Expr,
    #[cfg(test)]
    pub(super) firewall_core: Expr,
    pub(super) matrix_rank: Expr,
    pub(super) nat_succ: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_nat: Expr,
    // Infrastructure for constructive proof/value terms
    pub(super) ln_forward: Expr,
    pub(super) zonotope_center: Expr,
    pub(super) zonotope_generators: Expr,
    pub(super) zonotope_mk: Expr,
    pub(super) zonotope_sigma: Expr,
    pub(super) matrix_mul: Expr,
    pub(super) identity_matrix: Expr,
    pub(super) mean_projection: Expr,
    pub(super) matrix_sub: Expr,
    pub(super) scalar_mat_mul: Expr,
    // Infrastructure for constructive jac_rankdef_core proof (#3307)
    #[cfg(test)]
    pub(super) identity_minus_projection_rank: Expr,
    #[cfg(test)]
    pub(super) scalar_mat_rank_le: Expr,
    #[cfg(test)]
    pub(super) nat_eq_pred_succ_le: Expr,
    #[cfg(test)]
    pub(super) le_trans_nat: Expr,
    #[cfg(test)]
    pub(super) nat_succ_le_succ: Expr,
    #[cfg(test)]
    pub(super) nat_sub: Expr,
    #[cfg(test)]
    pub(super) nat_zero: Expr,
    // Infrastructure for constructive firewall_algebraic proof (#3307)
    #[cfg(test)]
    pub(super) zonotope_rankdef_width_eq: Expr,
    #[cfg(test)]
    pub(super) linear_image_zonotope: Expr,
    #[cfg(test)]
    pub(super) layernorm_jac_rankdef: Expr,
    // Infrastructure for constructive zonotope projection values (#3307)
    pub(super) zonotope_rec: Expr,
    // Infrastructure for constructive firewall_algebraic proof (#3307 — bridge)
    #[cfg(test)]
    pub(super) layernorm_ibp_bridge: Expr,
    pub(super) nn_vec_variance: Expr,
}

impl C002Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            #[cfg(test)]
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
            interval_hull_width: Expr::const_(
                Name::from_string("NNVerify.interval_hull_width"),
                vec![],
            ),
            fresh_zonotope_from_hull: Expr::const_(
                Name::from_string("NNVerify.fresh_zonotope_from_hull"),
                vec![],
            ),
            layernorm_zonotope: Expr::const_(
                Name::from_string("NNVerify.C002.layernorm_zonotope"),
                vec![],
            ),
            layernorm_eff_jacobian: Expr::const_(
                Name::from_string("NNVerify.C002.layernorm_effective_jacobian"),
                vec![],
            ),
            #[cfg(test)]
            firewall_core: Expr::const_(
                Name::from_string("NNVerify.C002.correlation_firewall_core"),
                vec![],
            ),
            matrix_rank: Expr::const_(Name::from_string("NNVerify.matrix_rank"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            // Infrastructure for constructive proof/value terms
            ln_forward: Expr::const_(Name::from_string("NNVerify.LayerNorm.forward"), vec![]),
            zonotope_center: Expr::const_(Name::from_string("NNVerify.Zonotope.center"), vec![]),
            zonotope_generators: Expr::const_(
                Name::from_string("NNVerify.Zonotope.generators"),
                vec![],
            ),
            zonotope_mk: Expr::const_(Name::from_string("NNVerify.Zonotope.mk"), vec![]),
            zonotope_sigma: Expr::const_(Name::from_string("NNVerify.Zonotope.sigma"), vec![]),
            matrix_mul: Expr::const_(Name::from_string("NNVerify.matrix_mul"), vec![]),
            identity_matrix: Expr::const_(Name::from_string("NNVerify.identity_matrix"), vec![]),
            mean_projection: Expr::const_(Name::from_string("NNVerify.mean_projection"), vec![]),
            matrix_sub: Expr::const_(Name::from_string("NNVerify.matrix_sub"), vec![]),
            scalar_mat_mul: Expr::const_(Name::from_string("NNVerify.scalar_mat_mul"), vec![]),
            // Infrastructure for constructive jac_rankdef_core proof (#3307)
            #[cfg(test)]
            identity_minus_projection_rank: Expr::const_(
                Name::from_string("NNVerify.identity_minus_projection_rank"),
                vec![],
            ),
            #[cfg(test)]
            scalar_mat_rank_le: Expr::const_(
                Name::from_string("NNVerify.scalar_mat_rank_le"),
                vec![],
            ),
            #[cfg(test)]
            nat_eq_pred_succ_le: Expr::const_(
                Name::from_string("NNVerify.nat_eq_pred_succ_le"),
                vec![],
            ),
            #[cfg(test)]
            le_trans_nat: Expr::const_(Name::from_string("NNVerify.le_trans_nat"), vec![]),
            #[cfg(test)]
            nat_succ_le_succ: Expr::const_(Name::from_string("NNVerify.nat_succ_le_succ"), vec![]),
            #[cfg(test)]
            nat_sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            #[cfg(test)]
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            // Infrastructure for constructive firewall_algebraic proof (#3307)
            #[cfg(test)]
            zonotope_rankdef_width_eq: Expr::const_(
                Name::from_string("NNVerify.zonotope_rankdef_width_eq"),
                vec![],
            ),
            #[cfg(test)]
            linear_image_zonotope: Expr::const_(
                Name::from_string("NNVerify.linear_image_zonotope"),
                vec![],
            ),
            #[cfg(test)]
            layernorm_jac_rankdef: Expr::const_(
                Name::from_string("NNVerify.C002.layernorm_jacobian_rank_deficient"),
                vec![],
            ),
            // Infrastructure for constructive zonotope projection values (#3307)
            zonotope_rec: Expr::const_(
                Name::from_string("NNVerify.Zonotope.rec"),
                vec![Level::succ(Level::zero())],
            ),
            // Infrastructure for constructive firewall_algebraic proof (#3307 — bridge)
            #[cfg(test)]
            layernorm_ibp_bridge: Expr::const_(
                Name::from_string("NNVerify.layernorm_ibp_bridge"),
                vec![],
            ),
            nn_vec_variance: Expr::const_(Name::from_string("NNVerify.nn_vec_variance"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    pub(super) fn zono_of(&self, n: Expr, k: Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n), k)
    }

    pub(super) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    pub(super) fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.nat.clone(), self.inst_le_nat.clone(), a, b],
        )
    }
}

// =============================================================================
// Type builders
// =============================================================================

/// Build type for `NNVerify.C002.layernorm_zonotope`:
/// `(n k : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) ->
///   Zonotope n k -> Zonotope n k`
pub(super) fn build_layernorm_zonotope_type(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (gamma_id, _) = b.fresh_local(vec_n.clone());
    let (beta_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (z_id, _) = b.fresh_local(zono_nk.clone());
    let e = b.mk_pi(z_id, BinderInfo::Default, zono_nk.clone(), zono_nk);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C002.layernorm_effective_jacobian`:
/// `(n : Nat) -> (gamma : NNVec n) -> (sigma : Rat) -> (z : NNVec n) -> NNMat n n`
pub(super) fn build_layernorm_eff_jacobian_type(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let mat_nn = c.mat_of(n.clone(), n.clone());
    let (gamma_id, _) = b.fresh_local(vec_n.clone());
    let (sigma_id, _) = b.fresh_local(c.rat.clone());
    let (z_id, _) = b.fresh_local(vec_n.clone());
    let e = b.mk_pi(z_id, BinderInfo::Default, vec_n.clone(), mat_nn);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the hypothesis-wrapped type for the C002 rank-deficiency claims.
///
/// The original hypothesis-free rank claim remains as the conclusion, but
/// callers must now provide it explicitly as local evidence after the `1 <= n`
/// premise. The proof terms return that local evidence.
pub(super) fn build_layernorm_jac_rankdef_hyp_type(c: &C002Consts) -> Expr {
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
    let hyp_n_ge_1 = c.nat_le(nat_one, n.clone());
    let (h_n_id, _) = b.fresh_local(hyp_n_ge_1.clone());

    let jac = Expr::apps(
        c.layernorm_eff_jacobian.clone(),
        [n.clone(), gamma, sigma, z],
    );
    let rank_j = Expr::apps(c.matrix_rank.clone(), [n.clone(), n.clone(), jac]);
    let succ_rank = Expr::app(c.nat_succ.clone(), rank_j);
    let conclusion = c.nat_le(succ_rank, n.clone());
    let (h_rank_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(
        h_rank_id,
        BinderInfo::Default,
        conclusion.clone(),
        conclusion,
    );
    let e = b.mk_pi(h_n_id, BinderInfo::Default, hyp_n_ge_1, e);
    let e = b.mk_pi(z_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for the main C002 theorem (correlation firewall equality).
pub(super) fn build_c002_firewall_type(c: &C002Consts) -> Expr {
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
    let conclusion = c.rat_eq(lhs, rhs);

    let e = b.mk_pi(z_id, BinderInfo::Default, zono_nk, conclusion);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the hypothesis-wrapped type for `NNVerify.C002.correlation_firewall`:
/// ```text
/// forall (n k : Nat) (gamma beta : NNVec n) (ln_eps : Rat)
///        (Z : Zonotope n k),
///   Eq Rat
///     (interval_hull_width n
///       (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z)))
///     (interval_hull_width n
///       (fresh_zonotope_from_hull n
///         (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z)))) ->
///   Eq Rat
///     (interval_hull_width n
///       (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z)))
///     (interval_hull_width n
///       (fresh_zonotope_from_hull n
///         (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z))))
/// ```
pub(super) fn build_c002_firewall_hyp_type(c: &C002Consts) -> Expr {
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
    let conclusion = c.rat_eq(lhs, rhs);
    let (h_id, _) = b.fresh_local(conclusion.clone());

    let e = b.mk_pi(h_id, BinderInfo::Default, conclusion.clone(), conclusion);
    let e = b.mk_pi(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.layernorm_ibp_bridge`:
/// ```text
/// forall (n k : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (Z : Zonotope n k),
///   Eq Rat
///     (interval_hull_width n (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z)))
///     (interval_hull_width n (fresh_zonotope_from_hull n
///       (Zonotope.to_ibp n k (layernorm_zonotope n k gamma beta ln_eps Z))))
/// ```
///
/// Infrastructure theorem bridging zonotope/interval formulations for C002.
/// Registered in C002 init (after layernorm_zonotope) because it references C002 names.
///
/// Part of #3307, #3371.
pub(super) fn build_layernorm_ibp_bridge_type(c: &C002Consts) -> Expr {
    // This is the hypothesis-free firewall equality. The public
    // `C002.correlation_firewall` headline is now hypothesis-wrapped; this
    // bridge keeps the unwrapped obligation visible as an honest Axiom.
    build_c002_firewall_type(c)
}

// `build_layernorm_ibp_bridge_proof` and `build_c002_firewall_proof` were
// deleted in #3639 Branch A. Their former bodies built an `Eq.refl`-rooted
// lambda that type-checked only because `NNVerify.fresh_zonotope_from_hull`
// was a reducible `Declaration::Definition` with identity body
// `fun (n : Nat) (B : IntervalBounds n) => B`. Flipping that carrier to
// `Declaration::Opaque` (see `nn_verify_matrix_rank.rs`) closed the
// δ-reduction path; the proofs no longer type-check under the honest
// carrier. `NNVerify.layernorm_ibp_bridge` and
// `NNVerify.C002.correlation_firewall_core` remain `Declaration::Axiom`
// entries on their original Pi types. `NNVerify.C002.correlation_firewall`
// is now a hypothesis-wrapped theorem over local equality evidence. Branch
// B (faithful zonotope→IBP translator; Phase-1 carrier refactor #3615 /
// #3617) will reintroduce substantive proof builders.
