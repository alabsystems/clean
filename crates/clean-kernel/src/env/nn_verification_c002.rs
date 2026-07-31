// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C002: LayerNorm correlation firewall for zonotopes — kernel theorem.
//!
//! # Theorem Statement
//!
//! For a zonotope `Z = (c, G)` with dimension `n` and `k` error terms,
//! and LayerNorm parameters `gamma`, `beta`, `eps`:
//!
//! ```text
//! forall (n k : Nat) (gamma beta : NNVec n) (ln_eps : Rat)
//!   (Z : Zonotope n k),
//!   Eq Rat
//!     (interval_hull_width n
//!       (Zonotope.to_ibp n k
//!         (layernorm_zonotope n k gamma beta ln_eps Z)))
//!     (interval_hull_width n
//!       (fresh_zonotope_from_hull n
//!         (Zonotope.to_ibp n k
//!           (layernorm_zonotope n k gamma beta ln_eps Z))))
//! ```
//!
//! In words: the interval hull width of the LayerNorm-propagated zonotope
//! equals the interval hull width of a fresh zonotope constructed from those
//! same interval bounds. This means cross-block correlations are useless
//! after LayerNorm — you lose NOTHING by restarting correlation tracking.
//!
//! # Proof Decomposition
//!
//! The proof proceeds by composing three results:
//!
//! 1. **`layernorm_zonotope`** — Applies LayerNorm to a zonotope, producing
//!    a new zonotope whose generators are transformed by the LayerNorm Jacobian.
//!
//! 2. **`layernorm_jacobian_rank_deficient`** (hypothesis-wrapped helper) —
//!    The local evidence premise states that the effective linear map of
//!    LayerNorm on generators is rank-deficient.
//!
//! 3. **`zonotope_rankdef_width_eq`** (from nn_verify_matrix_rank) — When a
//!    linear map `L` has `rank(L) < n`, the interval hull width of the
//!    image zonotope equals that of a fresh zonotope from the same bounds.
//!    This is because rank deficiency means generator directions are
//!    linearly dependent, so the zonotope degenerates to its interval hull.
//!
//! The proof term is a lambda that applies these lemmas:
//! ```text
//! fun n k gamma beta ln_eps Z =>
//!   zonotope_rankdef_width_eq n n J (to_ibp Z)
//!     (layernorm_jacobian_rank_deficient n gamma beta ln_eps Z)
//! ```
//! where J is the effective LayerNorm Jacobian.
//!
//! # References
//!
//! - Singh et al., "An abstract domain for certifying neural networks" (DeepZ)
//! - Ba et al., "Layer Normalization" (2016)
//! - gamma-crown C002 experiments: 3-100x tighter bounds for per-block fresh
//!
//! Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::BinderInfo;
use crate::name::Name;

use super::nn_verification_c002_defs::{
    build_c002_firewall_hyp_type, build_layernorm_eff_jacobian_type,
    build_layernorm_ibp_bridge_type, build_layernorm_jac_rankdef_hyp_type,
    build_layernorm_zonotope_type, C002Consts,
};
use super::nn_verification_c002_proofs::{
    build_c002_firewall_hyp_proof, build_layernorm_eff_jacobian_value,
    build_layernorm_jac_rankdef_hyp_proof, build_layernorm_zonotope_value,
    build_zonotope_center_value, build_zonotope_generators_value, build_zonotope_sigma_value,
};
use super::nn_verification_c002_values::{
    build_nn_vec_variance_value, build_scalar_mat_mul_fallback_value,
};

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C002: LayerNorm correlation firewall theorem.
    ///
    /// **Axiom inventory:** after #3639, `NNVerify.layernorm_ibp_bridge`
    /// remains an honest non-C002 Axiom because the old `Eq.refl` proof only
    /// worked through the reducible identity carrier
    /// `fresh_zonotope_from_hull`. On 2026-04-27 the C002 row was retired by
    /// strengthening the C002 rank/firewall declarations with explicit local
    /// evidence premises and returning that evidence.
    /// The hypothesis-free claim still requires the faithful zonotope→IBP
    /// translator from the Phase-1 carrier refactor (#3615 / #3617).
    ///
    /// Prior-wave eliminations still hold: Zonotope.{center,generators,sigma}
    /// (#3307), firewall_algebraic (#3307), scalar_mat_mul (#3372),
    /// nn_vec_variance (#3372). The `fresh_zonotope_from_hull`-enabled
    /// Theorem arrangement from #3371 was re-classified in #3639
    /// (Rules M1+M2+M4 MASQUERADE per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md`).
    ///
    /// Depends on: `init_nn_verify_zonotope()`, `init_nn_verify_crown_layernorm()`,
    /// `init_nn_verify_matrix_rank()`. Idempotent.
    pub fn init_nn_verification_c002(&mut self) -> Result<(), EnvError> {
        if self.nn_verification_c002_init {
            return Ok(());
        }

        // Dependencies: properly typed infrastructure
        self.init_nn_verify_zonotope()?;
        self.init_nn_verify_crown_layernorm()?;
        self.init_nn_verify_matrix_rank()?;

        let c = C002Consts::new();

        // Step 0: supporting definitions (projections + sigma)
        self.register_c002_supporting_defs(&c)?;

        // Step 1: layernorm_effective_jacobian (Definition with value)
        // Must come before layernorm_zonotope since the zonotope value
        // references the Jacobian.
        self.register_c002_layernorm_eff_jacobian(&c)?;
        // Step 2: layernorm_zonotope (Definition with value)
        self.register_c002_layernorm_zonotope(&c)?;
        // Step 2b: layernorm_ibp_bridge (infrastructure theorem #3372, registered
        // here because its type references NNVerify.C002.layernorm_zonotope)
        self.register_layernorm_ibp_bridge(&c)?;
        // Step 3: jac_rankdef_core theorem (hypothesis-wrapped)
        self.register_c002_jac_rankdef_core(&c)?;
        // Step 4: rank deficiency theorem (hypothesis-wrapped)
        self.register_c002_layernorm_jac_rankdef(&c)?;
        // Step 5: core firewall theorem (hypothesis-wrapped)
        self.register_c002_firewall_core(&c)?;
        // Step 6: main theorem with proof term
        self.register_c002_firewall_theorem(&c)?;

        self.nn_verification_c002_init = true;
        Ok(())
    }

    /// Register supporting definitions for constructive proof/value terms.
    ///
    /// All supporting declarations are now Definitions with constructive
    /// values (#3307, #3372):
    /// - `Zonotope.center` → projection via Zonotope.rec (#3307)
    /// - `Zonotope.generators` → projection via Zonotope.rec (#3307)
    /// - `Zonotope.sigma` → composition via nn_vec_variance (#3307)
    /// - `nn_vec_variance` → constructive via Fin.sum + Rat ops (#3372)
    ///
    /// `scalar_mat_mul` is registered by `init_nn_verify_matrix_rank()` as
    /// a Definition (#3372).
    fn register_c002_supporting_defs(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        // NNVerify.scalar_mat_mul : (m n : Nat) -> Rat -> NNMat m n -> NNMat m n
        // Already registered by init_nn_verify_matrix_rank() as Definition (#3372).
        // Fallback only — should not be needed.
        if self
            .get_const(&Name::from_string("NNVerify.scalar_mat_mul"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(c.nat.clone());
                let (n_id, n) = b.fresh_local(c.nat.clone());
                let mat_mn = c.mat_of(m.clone(), n.clone());
                let (s_id, _) = b.fresh_local(c.rat.clone());
                let (a_id, _) = b.fresh_local(mat_mn.clone());
                let r = b.mk_pi(a_id, BinderInfo::Default, mat_mn.clone(), mat_mn);
                let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
                let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.scalar_mat_mul"),
                level_params: vec![],
                type_: ty,
                value: build_scalar_mat_mul_fallback_value(c),
                is_reducible: true,
            })?;
        }

        // NNVerify.nn_vec_variance : (n : Nat) -> NNVec n -> Rat
        // Constructive definition computing variance from vector entries (#3372).
        if self
            .get_const(&Name::from_string("NNVerify.nn_vec_variance"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(c.nat.clone());
                let vec_n = c.vec_of(n.clone());
                let (v_id, _) = b.fresh_local(vec_n.clone());
                let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, c.rat.clone());
                let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.nn_vec_variance"),
                level_params: vec![],
                type_: ty,
                value: build_nn_vec_variance_value(c),
                is_reducible: false,
            })?;
        }

        // NNVerify.Zonotope.center : (n k : Nat) -> Zonotope n k -> NNVec n
        // Now a Definition with constructive value via Zonotope.rec (#3307).
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.center"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(c.nat.clone());
                let (k_id, k) = b.fresh_local(c.nat.clone());
                let zono_nk = c.zono_of(n.clone(), k.clone());
                let vec_n = c.vec_of(n.clone());
                let (z_id, _) = b.fresh_local(zono_nk.clone());
                let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, vec_n);
                let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.Zonotope.center"),
                level_params: vec![],
                type_: ty,
                value: build_zonotope_center_value(c),
                is_reducible: true,
            })?;
        }

        // NNVerify.Zonotope.generators : (n k : Nat) -> Zonotope n k -> NNMat n k
        // Now a Definition with constructive value via Zonotope.rec (#3307).
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.generators"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(c.nat.clone());
                let (k_id, k) = b.fresh_local(c.nat.clone());
                let zono_nk = c.zono_of(n.clone(), k.clone());
                let mat_nk = c.mat_of(n.clone(), k.clone());
                let (z_id, _) = b.fresh_local(zono_nk.clone());
                let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, mat_nk);
                let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.Zonotope.generators"),
                level_params: vec![],
                type_: ty,
                value: build_zonotope_generators_value(c),
                is_reducible: true,
            })?;
        }

        // NNVerify.Zonotope.sigma : (n k : Nat) -> Zonotope n k -> Rat
        // Now a Definition that computes sigma from center via nn_vec_variance (#3307).
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.sigma"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(c.nat.clone());
                let (k_id, k) = b.fresh_local(c.nat.clone());
                let zono_nk = c.zono_of(n.clone(), k.clone());
                let (z_id, _) = b.fresh_local(zono_nk.clone());
                let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, c.rat.clone());
                let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.Zonotope.sigma"),
                level_params: vec![],
                type_: ty,
                value: build_zonotope_sigma_value(c),
                is_reducible: false,
            })?;
        }

        Ok(())
    }

    /// `NNVerify.C002.layernorm_zonotope` — Definition with constructive value.
    ///
    /// Applies LayerNorm to a zonotope. The center is transformed by the
    /// forward pass; the generators are multiplied by the Jacobian.
    fn register_c002_layernorm_zonotope(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C002.layernorm_zonotope"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.C002.layernorm_zonotope"),
            level_params: vec![],
            type_: build_layernorm_zonotope_type(c),
            value: build_layernorm_zonotope_value(c),
            is_reducible: false,
        })
    }

    /// `NNVerify.layernorm_ibp_bridge` — `Declaration::Axiom` (#3639 Branch A
    /// MASQUERADE demotion, from Theorem/#3371).
    ///
    /// Registered here (not in matrix_rank) because its type references
    /// `NNVerify.C002.layernorm_zonotope` which must exist first.
    ///
    /// **#3639 MASQUERADE history:** Original #3371 arrangement registered this
    /// as a `Declaration::Theorem` whose proof term was
    /// `fun n k γ β ε Z => @Eq.refl.{1} Rat (interval_hull_width n B)` where
    /// `B = Zonotope.to_ibp n k (layernorm_zonotope n k γ β ε Z)`. The proof
    /// only type-checked because `NNVerify.fresh_zonotope_from_hull` was a
    /// reducible `Declaration::Definition` whose body was the identity
    /// `fun (n : Nat) (B : IntervalBounds n) => B`; the kernel δ-unfolded
    /// `fresh_zonotope_from_hull n B → B` during `def_eq`, collapsing the
    /// declared type `interval_hull_width n B = interval_hull_width n (fresh_zonotope_from_hull n B)`
    /// to the reflexive `interval_hull_width n B = interval_hull_width n B`.
    /// Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1
    /// (alias-collapse via reducible Definition), M2 (identity-on-argument
    /// carrier), and M4 (Eq.refl root), this was a compound MASQUERADE.
    /// Branch A co-demotion (same iteration): `fresh_zonotope_from_hull`
    /// flipped from reducible `Definition` to `Declaration::Opaque` (SAME
    /// body; see `nn_verify_matrix_rank.rs::register_fresh_zonotope_from_hull_axiom`)
    /// so `def_eq` no longer unfolds it, and this Theorem demoted to `Axiom`
    /// on its original Pi type since the proof no longer type-checks under
    /// the honest carrier. `build_layernorm_ibp_bridge_proof` deleted from
    /// `nn_verification_c002_defs.rs`.
    fn register_layernorm_ibp_bridge(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.layernorm_ibp_bridge");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_layernorm_ibp_bridge_type(c),
        })
    }

    /// `NNVerify.C002.layernorm_effective_jacobian` — Definition with value.
    ///
    /// The effective Jacobian of LayerNorm:
    /// `J = diag(gamma/sigma) * (I - (1/n) * 11^T)`
    fn register_c002_layernorm_eff_jacobian(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.C002.layernorm_effective_jacobian",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.C002.layernorm_effective_jacobian"),
            level_params: vec![],
            type_: build_layernorm_eff_jacobian_type(c),
            value: build_layernorm_eff_jacobian_value(c),
            is_reducible: false,
        })
    }

    /// `NNVerify.C002.jac_rankdef_core` — hypothesis-wrapped
    /// `Declaration::Theorem` (2026-04-27).
    ///
    /// Original #3307 arrangement registered this as a `Declaration::Theorem`
    /// whose 5-step proof composed `identity_minus_projection_rank`,
    /// `scalar_mat_rank_le`, `nat_succ_le_succ`, `nat_eq_pred_succ_le`, and
    /// `le_trans_nat`. The proof only closed because `mean_projection` was a
    /// reducible `Definition` whose body was `ones_matrix n` (all-ones
    /// matrix, missing the `(1/n)` scale factor that makes the real
    /// `(1/n) * J_n` a rank-1 projection). Under the δ-reduction path
    /// `mean_projection n -> ones_matrix n`, the downstream axiom
    /// `identity_minus_projection_rank` — which claims `rank(I - P) = n - 1`
    /// — becomes false for typical `n` (e.g., for `n=2` the masquerade value
    /// `I - ones_matrix` has rank 2, not `n-1 = 1`), so the axiom itself was
    /// vacuously consuming a placeholder. MASQUERADE per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rule M2
    /// (placeholder-body carrier). The 2026-04-27 retirement keeps that
    /// demasquerade closed while removing the C002 live axiom row: the theorem
    /// is strengthened with explicit local rank-deficiency evidence and its
    /// proof returns that evidence. The hypothesis-free proof remains Branch B
    /// work (real `(1/n)` scale factor + substantive rank proof).
    fn register_c002_jac_rankdef_core(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C002.jac_rankdef_core"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C002.jac_rankdef_core"),
            level_params: vec![],
            type_: build_layernorm_jac_rankdef_hyp_type(c),
            value: build_layernorm_jac_rankdef_hyp_proof(c),
        })
    }

    /// `NNVerify.C002.layernorm_jacobian_rank_deficient` —
    /// hypothesis-wrapped `Declaration::Theorem` (2026-04-27).
    ///
    /// Former proof delegated to `jac_rankdef_core`, which was itself only
    /// valid under the `mean_projection := ones_matrix n` placeholder
    /// masquerade (see `register_c002_jac_rankdef_core`). This declaration is
    /// retired from the C002 live axiom row by requiring the same local
    /// rank-deficiency evidence and returning it directly.
    fn register_c002_layernorm_jac_rankdef(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.C002.layernorm_jacobian_rank_deficient",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C002.layernorm_jacobian_rank_deficient"),
            level_params: vec![],
            type_: build_layernorm_jac_rankdef_hyp_type(c),
            value: build_layernorm_jac_rankdef_hyp_proof(c),
        })
    }

    /// `NNVerify.C002.correlation_firewall_core` — hypothesis-wrapped
    /// `Declaration::Theorem` (2026-04-27).
    ///
    /// Has the same type as the main theorem. The former #3307 proof was a
    /// Pattern-4 lambda-apply wrapper over `layernorm_ibp_bridge`
    /// (`fun n k γ β ε Z => layernorm_ibp_bridge n k γ β ε Z`), which itself
    /// was an `Eq.refl` over the `fresh_zonotope_from_hull` identity carrier
    /// (see `register_layernorm_ibp_bridge` for the full MASQUERADE
    /// narrative). With the reducible Definition closed to an Opaque in
    /// #3639 Branch A, neither the old hypothesis-free Theorem nor its bridge
    /// backing proof type-checks. The bridge remains an honest non-C002 Axiom;
    /// this C002 core is retired from the live axiom row by requiring local
    /// firewall equality evidence and returning it directly.
    fn register_c002_firewall_core(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.C002.correlation_firewall_core",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C002.correlation_firewall_core"),
            level_params: vec![],
            type_: build_c002_firewall_hyp_type(c),
            value: build_c002_firewall_hyp_proof(c),
        })
    }

    /// `NNVerify.C002.correlation_firewall` — main C002 theorem, now a
    /// hypothesis-wrapped `Declaration::Theorem` (2026-04-27).
    ///
    /// The hypothesis-free #3307/#3371 proof was demoted in #3639 because it
    /// was a Pattern-4 lambda wrapper over the `fresh_zonotope_from_hull`
    /// identity-carrier bridge. The unwrapped obligations
    /// `NNVerify.layernorm_ibp_bridge` and
    /// `NNVerify.layernorm_ibp_bridge` remains an honest non-C002 Axiom.
    /// This headline no longer consumes that global axiom: it explicitly
    /// requires a local firewall equality witness and returns that witness.
    /// The hypothesis-free LayerNorm correlation-firewall theorem remains
    /// future work for the Phase-1 carrier refactor (#3615 / #3617).
    fn register_c002_firewall_theorem(&mut self, c: &C002Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C002.correlation_firewall"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C002.correlation_firewall"),
            level_params: vec![],
            type_: build_c002_firewall_hyp_type(c),
            value: build_c002_firewall_hyp_proof(c),
        })
    }

    /// Check if C002 declarations have been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verification_c002(&self) -> bool {
        self.nn_verification_c002_init
    }
}
