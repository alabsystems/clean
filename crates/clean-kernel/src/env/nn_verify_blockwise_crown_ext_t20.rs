// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T20 `LayerNorm.zonotope_reset` — MASQUERADE RETIRED via a FAITHFUL
//! LAYERNORM-TRANSFER RESTATEMENT (Branch B, supersedes the #3509 Branch A
//! honest demotion).
//!
//! **Status:** Contains 2 `Declaration::Theorem` entries
//! (`NNVerify.LayerNorm.zonotope_reset` — lower-bound per-component equation;
//! `NNVerify.LayerNorm.zonotope_reset_upper` — the upper-bound companion) and 2
//! supporting reducible `Declaration::Definition` carriers
//! (`NNVerify.LayerNorm.layernorm_zono` — the faithful LN affine transfer on a
//! zonotope; `NNVerify.LayerNorm.zonotope_output` — its interval hull). All
//! GENUINELY consume the LayerNorm gain `γ` and bias `β`; none reduces to a
//! vacuous `Eq.refl` over a γ/β-discarding carrier. The former axiom is RETIRED.
//!
//! Split out of `nn_verify_blockwise_crown_ext.rs` (mirroring the T22 split in
//! `nn_verify_blockwise_crown_ext_t22.rs`) to stay under the 500-line file-size
//! cap and to localise the MASQUERADE history so future audits can see the
//! before/after in one place.
//!
//! ### MASQUERADE history (carrier `zonotope_output` discarded γ, β, ε)
//!
//! The 2026-04-19 `clean-native.mathverse` shard audit
//! (`reports/audit/2026-04-19-clean-native-shard-audit.md`, entry 9) flagged
//! T20 as trivial-by-construction. The original `zonotope_output n k γ β ε z`
//! was a reducible Definition whose body was `to_ibp n k z` — it DISCARDED `γ`,
//! `β`, and `ε`, so the registered theorem
//! `zonotope_output n k γ β ε z = to_ibp n k z` collapsed both sides to the
//! same `to_ibp n k z` normal form and closed by `Eq.refl`. With the historical
//! FAKE zero-interval `to_ibp` body, both sides were additionally the zero
//! interval — a textbook M2 (argument-discarding carrier) + M1 (alias collapse)
//! MASQUERADE (`designs/2026-04-19-demasquerade-cxxx-pattern.md`). #3509 Branch A
//! demoted the theorem to a body-less `Declaration::Axiom` on its current Pi
//! type. That closed the alias-collapse loophole but left a body-less axiom in
//! the trusted base — the count was honest but the content was absent.
//!
//! ### Branch B retirement (FAITHFUL LAYERNORM-TRANSFER RESTATEMENT, this file)
//!
//! `to_ibp` is now the FAITHFUL element-wise range
//! `[center_i − Σⱼ|G_ij|, center_i + Σⱼ|G_ij|]`
//! (`nn_verify_zonotope_to_ibp_faithful`). On top of it, the LayerNorm OUTPUT
//! AFFINE TRANSFER `x ↦ γ ⊙ x + β` applied to a zonotope is the faithful
//! `layernorm_zono`:
//!
//! ```text
//! layernorm_zono (n k : Nat) (γ β : NNVec n) (ε : Rat) (z : Zonotope n k)
//!   : Zonotope n k :=
//!   Zonotope.mk n k
//!     (center'    := fun (i : Fin n) => γ i * z.center i + β i)
//!     (generators':= fun (i : Fin n) (j : Fin k) => γ i * z.generators i j)
//! ```
//!
//! i.e. each output row is scaled by the gain `γ_i` and shifted by the bias
//! `β_i`; the per-row generator columns are gain-scaled. This GENUINELY consumes
//! `γ` and `β` — the parameters whose discarding was the original M2 violation.
//!
//! `zonotope_output` is then the interval hull of the LN-transferred zonotope:
//!
//! ```text
//! zonotope_output n k γ β ε z := to_ibp n k (layernorm_zono n k γ β ε z)
//! ```
//!
//! Both carriers are reducible so the two T20 proofs can δ-unfold them to the
//! `IntervalBounds.mk … .lower/.upper i` form their `Eq.refl` proofs match.
//!
//! **Why the OLD statement `zonotope_output = to_ibp z` is now FALSE (so we
//! restate, per Branch B, NOT prove the old equality).** With a faithful
//! `layernorm_zono`, `to_ibp (layernorm_zono γ β ε z) ≠ to_ibp z` in general:
//! gain `γ_i` scales the radius `Σⱼ|γ_i·G_ij| = |γ_i|·Σⱼ|G_ij|` and bias `β_i`
//! shifts the center, so the LN-output box differs from the input box whenever
//! `γ_i ≠ 1` or `β_i ≠ 0`. (This is exactly the width-change that made the
//! UNCONDITIONAL T21 `zonotope_width_preserved` axiom FALSE-as-written — see
//! `designs/2026-06-13-nnverify-5axiom-retirement-roadmap.md` Tranche B #4. T21
//! is now RETIRED to a kernel-checked GAIN-BOUND Theorem under `|γ_i| ≤ 1` in
//! `nn_verify_blockwise_crown_ext_t21.rs`, #3509 Branch B.) The honest
//! restatement here is a per-component characterisation of the faithful
//! LN-output box.
//!
//! ### The two restated theorems
//!
//! 1. **`zonotope_reset`** (lower-bound per-component equation):
//!    ```text
//!    ∀ (n k : Nat) (γ β : NNVec n) (ε : Rat) (z : Zonotope n k) (i : Fin n),
//!      (zonotope_output n k γ β ε z).lower i
//!        = (γ i * z.center i + β i)
//!            − Fin.sum k (fun j => Rat.abs (γ i * z.generators i j))
//!    ```
//!    The lower bound of the LN-output box is `(γ_i·c_i + β_i) − radius'_i`,
//!    where `radius'_i = Σⱼ|γ_i·G_ij|` is the gain-scaled per-row L1 radius. The
//!    RHS GENUINELY consumes `γ`, `β`, and `k` (it is `Fin.sum k …` over
//!    `γ i * G_ij`), so it is NOT a count/alias tautology and would FAIL to
//!    type-check against the retired γ/β-discarding carrier.
//! 2. **`zonotope_reset_upper`** (upper-bound companion): same with `+ radius'_i`
//!    and `.upper`. Together the two pin the LN-output box exactly.
//!
//! **On `ε`.** The post-affine box geometry `[γ·c+β ∓ Σ|γ·G|]` does NOT depend
//! on the LayerNorm epsilon `ε` (which stabilises the normalisation scale
//! `1/√(σ²+ε)` UPSTREAM of the output affine map; modelling that scale is the
//! C002 effective-Jacobian path — `nn_verification_c002`, out of T20's minimal
//! scope). `ε` stays in the signature (the registered type is unchanged) and is
//! quantified over in both theorems; the RHS being ε-independent is a TRUE,
//! kernel-checked fact, not a discard-masquerade: the M2 violation #3509 flagged
//! was discarding the gain `γ` and bias `β` (which collapsed the box to the
//! input box), and those are now genuinely consumed.
//!
//! Both proofs are `Declaration::Theorem`s closed by `Eq.refl` after δ/ι/β
//! reduction of the reducible carriers — the SAME proof technique the faithful
//! T22 `zonotope_generators_reset` uses (a genuine equation over a faithful
//! carrier, not a `def = def` alias). Their transitive axiom closure is
//! `⊆ {propext, Quot.sound, Classical.choice}` (the carriers reuse `Rat.mul`,
//! `Rat.add`, `Rat.sub`, `Rat.abs`, `Fin.sum`, `Zonotope.mk`, all axiom-free
//! constructive definitions over the faithful `Fin`/`Rat`-quotient carriers, and
//! `to_ibp`'s `valid` proof which is itself foundational). NO `sorry`, NO
//! `add_decl_structural`, NO `native_decide`.
//!
//! Mirrors the faithful-carrier technique of
//! `nn_verify_zonotope_to_ibp_faithful` (the `radius` row sum),
//! `nn_verify_blockwise_crown_ext_t22` (the genuine per-entry equation over a
//! faithful matrix), and `nn_verification_c002_proofs::build_layernorm_zonotope_value`
//! (the heavyweight effective-Jacobian LN transfer this minimal affine carrier
//! abstracts).
//!
//! Part of #3509 (Branch B). Tranche A #3 of
//! `designs/2026-06-13-nnverify-5axiom-retirement-roadmap.md`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants for the faithful T20 carriers + their two proofs.
struct T20Consts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nn_vec: Expr,
    ib: Expr,
    zonotope: Expr,
    zonotope_mk: Expr,
    zono_to_ibp: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul: Expr,
    rat_abs: Expr,
    fin_sum: Expr,
    /// `Eq.{1}` (`Rat : Sort 1`).
    eq: Expr,
    /// `Eq.refl.{1}`.
    eq_refl: Expr,
}

impl T20Consts {
    fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        Self {
            nat: c("Nat"),
            rat: c("Rat"),
            fin: c("Fin"),
            nn_vec: c("NNVerify.NNVec"),
            ib: c("NNVerify.IntervalBounds"),
            zonotope: c("NNVerify.Zonotope"),
            zonotope_mk: c("NNVerify.Zonotope.mk"),
            zono_to_ibp: c("NNVerify.Zonotope.to_ibp"),
            rat_add: c("Rat.add"),
            rat_sub: c("Rat.sub"),
            rat_mul: c("Rat.mul"),
            rat_abs: c("Rat.abs"),
            fin_sum: c("Fin.sum"),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    /// `@Fin n`.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// `@NNVerify.NNVec n`.
    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    /// `@NNVerify.IntervalBounds n`.
    fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    /// `@NNVerify.Zonotope n k`.
    fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.zonotope.clone(), [n.clone(), k.clone()])
    }

    /// `@Eq.{1} Rat lhs rhs : Prop`.
    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), lhs, rhs])
    }

    /// `Rat.mul a b`.
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    /// `Rat.add a b`.
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    /// `Rat.sub a b`.
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }

    /// The gain-scaled per-row L1 radius
    /// `radius'_i := Fin.sum k (fun (j : Fin k) => Rat.abs (γ i * G_ij))`.
    /// GENUINELY consumes the gain `γ_i` and every one of the `k` input columns.
    fn radius_scaled(
        &self,
        parent: &EnvDeclBuilder,
        fin_k: &Expr,
        k: &Expr,
        gamma_i: &Expr,
        gens_i: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = ch.fresh_local(fin_k.clone());
        let g_ij = Expr::app(gens_i.clone(), j);
        let scaled = self.mul(gamma_i.clone(), g_ij);
        let abs_scaled = Expr::app(self.rat_abs.clone(), scaled);
        let summand =
            ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), abs_scaled));
        Expr::apps(self.fin_sum.clone(), [k.clone(), summand])
    }
}

impl Environment {
    /// T20: `NNVerify.LayerNorm.zonotope_reset`
    ///
    /// FAITHFUL LAYERNORM-TRANSFER RESTATEMENT (Branch B). Registers the faithful
    /// `layernorm_zono` + `zonotope_output` carriers and the two per-component
    /// theorems pinning the LN-output box. See the module docs for the full
    /// statements, the FALSE-as-written justification for the restatement, and
    /// the `ε`-independence discussion.
    ///
    /// Part of #3509 (Branch B).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_t20_layernorm_zonotope_reset_ext(&mut self) -> Result<(), EnvError> {
        self.register_layernorm_zono_ext()?;
        self.register_layernorm_zonotope_output_ext()?;
        self.register_t20_zonotope_reset_lower()?;
        self.register_t20_zonotope_reset_upper()
    }

    /// `NNVerify.LayerNorm.layernorm_zono`
    /// `: (n k : Nat) -> (γ β : NNVec n) -> (ε : Rat) -> Zonotope n k -> Zonotope n k`
    ///
    /// FAITHFUL LayerNorm output affine transfer `x ↦ γ ⊙ x + β` on a zonotope
    /// (reducible `Declaration::Definition`):
    /// ```text
    /// fun n k γ β ε z =>
    ///   Zonotope.mk n k
    ///     (fun (i : Fin n) => γ i * z.center i + β i)
    ///     (fun (i : Fin n) (j : Fin k) => γ i * z.generators i j)
    /// ```
    /// The center' GENUINELY consumes `γ` and `β`; the generators' genuinely
    /// consume `γ`. It is registered reducible so the two T20 proofs can
    /// δ-unfold `to_ibp (layernorm_zono …)` to the per-component range terms
    /// their `Eq.refl` motives match against.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_layernorm_zono_ext(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.layernorm_zono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T20Consts::new();
        let zono_name = Name::from_string("NNVerify.Zonotope");

        // type : (n k : Nat) -> (γ β : NNVec n) -> (ε : Rat) -> Zonotope n k -> Zonotope n k.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let (gamma_id, _) = b.fresh_local(vec_n.clone());
            let (beta_id, _) = b.fresh_local(vec_n.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk.clone(), zono_nk);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value : fun n k γ β ε z => Zonotope.mk n k center' gens'.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, _eps) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let center = Expr::proj(zono_name.clone(), 0, z.clone());
            let gens = Expr::proj(zono_name.clone(), 1, z);

            // center' : NNVec n := fun (i : Fin n) => γ i * center i + β i.
            let center_fn = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let gamma_i = Expr::app(gamma.clone(), i.clone());
                let center_i = Expr::app(center.clone(), i.clone());
                let beta_i = Expr::app(beta.clone(), i);
                let scaled = c.mul(gamma_i, center_i);
                let body = c.add(scaled, beta_i);
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body))
            };
            // gens' : NNMat n k := fun (i : Fin n) (j : Fin k) => γ i * G_ij.
            let gens_fn = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let gamma_i = Expr::app(gamma.clone(), i.clone());
                let gens_i = Expr::app(gens.clone(), i);
                let row = {
                    let mut jb = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = jb.fresh_local(fin_k.clone());
                    let g_ij = Expr::app(gens_i.clone(), j);
                    let body = c.mul(gamma_i.clone(), g_ij);
                    jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
                };
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), row))
            };

            let body = Expr::apps(
                c.zonotope_mk.clone(),
                [n.clone(), k.clone(), center_fn, gens_fn],
            );
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
            let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.LayerNorm.zonotope_output`
    /// `: (n k : Nat) -> (γ β : NNVec n) -> (ε : Rat) -> Zonotope n k -> IntervalBounds n`
    ///
    /// The interval hull of the LN-transferred zonotope (reducible
    /// `Declaration::Definition`):
    /// ```text
    /// fun n k γ β ε z => to_ibp n k (layernorm_zono n k γ β ε z)
    /// ```
    ///
    /// ### History
    ///
    /// - #3435: reducible `Definition`, body `to_ibp n k z` — DISCARDED γ, β, ε
    ///   (M2), so T20/T21 closed by `Eq.refl` (M1 alias collapse over the FAKE
    ///   zero-interval `to_ibp`).
    /// - Branch B (this change): the body is the interval hull of the FAITHFUL
    ///   `layernorm_zono n k γ β ε z`, which genuinely consumes γ and β. M2 is
    ///   closed structurally: the body now depends on `γ`/`β` via
    ///   `layernorm_zono`'s `Zonotope.mk … (γ i * c i + β i) (γ i * G_ij)`.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_layernorm_zonotope_output_ext(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.zonotope_output");
        // Replace the legacy γ/β/ε-discarding Definition; only short-circuit when
        // the faithful body (citing `layernorm_zono`) is already in place.
        if self.get_const(&name).is_some_and(|ci| {
            ci.value
                .as_ref()
                .is_some_and(|v| expr_mentions(v, "NNVerify.LayerNorm.layernorm_zono"))
        }) {
            return Ok(());
        }
        let c = T20Consts::new();

        // type : (n k : Nat) -> (γ β : NNVec n) -> (ε : Rat) -> Zonotope n k -> IB n.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let ib_n = c.ib_of(&n);
            let (gamma_id, _) = b.fresh_local(vec_n.clone());
            let (beta_id, _) = b.fresh_local(vec_n.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, ib_n);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value : fun n k γ β ε z => to_ibp n k (layernorm_zono n k γ β ε z).
        let layernorm_zono = Expr::const_(
            Name::from_string("NNVerify.LayerNorm.layernorm_zono"),
            vec![],
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let ln_z = Expr::apps(
                layernorm_zono.clone(),
                [n.clone(), k.clone(), gamma, beta, eps, z],
            );
            let body = Expr::apps(c.zono_to_ibp.clone(), [n.clone(), k.clone(), ln_z]);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
            let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.LayerNorm.zonotope_reset` — the lower-bound per-component
    /// equation. See the module docs for the statement and the FALSE-as-written
    /// justification.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t20_zonotope_reset_lower(&mut self) -> Result<(), EnvError> {
        self.register_t20_zonotope_reset_bound(
            "NNVerify.LayerNorm.zonotope_reset",
            BoundSide::Lower,
        )
    }

    /// `NNVerify.LayerNorm.zonotope_reset_upper` — the upper-bound companion.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t20_zonotope_reset_upper(&mut self) -> Result<(), EnvError> {
        self.register_t20_zonotope_reset_bound(
            "NNVerify.LayerNorm.zonotope_reset_upper",
            BoundSide::Upper,
        )
    }

    /// Shared builder for the two per-component bound equations.
    ///
    /// For `side = Lower` (proj 0) / `Upper` (proj 1):
    /// ```text
    /// ∀ (n k : Nat) (γ β : NNVec n) (ε : Rat) (z : Zonotope n k) (i : Fin n),
    ///   (zonotope_output n k γ β ε z).<side> i
    ///     = (γ i * z.center i + β i) ∓ Fin.sum k (fun j => Rat.abs (γ i * z.generators i j))
    /// ```
    /// Proof: `Eq.refl Rat RHS`. The reducible `zonotope_output` δ-unfolds to
    /// `to_ibp n k (layernorm_zono …)`, which δ-unfolds to
    /// `IntervalBounds.mk n lower' upper' valid'`; the `.lower/.upper`
    /// projection ι-reduces to `lower'/upper'`, applied at `i` and β-reduced to
    /// the RHS. So both sides share a normal form and `Eq.refl` closes.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t20_zonotope_reset_bound(
        &mut self,
        thm_name: &str,
        side: BoundSide,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(thm_name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T20Consts::new();
        let zono_name = Name::from_string("NNVerify.Zonotope");
        let ib_name = Name::from_string("NNVerify.IntervalBounds");
        let zonotope_output = Expr::const_(
            Name::from_string("NNVerify.LayerNorm.zonotope_output"),
            vec![],
        );

        // RHS builder, shared between type and proof: the gain/bias-shifted
        // center ∓ the gain-scaled radius.
        let build_rhs = |b: &EnvDeclBuilder,
                         fin_k: &Expr,
                         k: &Expr,
                         gamma_i: &Expr,
                         center_i: &Expr,
                         beta_i: &Expr,
                         gens_i: &Expr| {
            let shifted_center = c.add(c.mul(gamma_i.clone(), center_i.clone()), beta_i.clone());
            let radius = c.radius_scaled(b, fin_k, k, gamma_i, gens_i);
            match side {
                BoundSide::Lower => c.sub(shifted_center, radius),
                BoundSide::Upper => c.add(shifted_center, radius),
            }
        };
        let proj_idx = match side {
            BoundSide::Lower => 0u32,
            BoundSide::Upper => 1u32,
        };

        // type : ∀ n k γ β ε z i, (zonotope_output …).<side> i = RHS.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            let out = Expr::apps(
                zonotope_output.clone(),
                [
                    n.clone(),
                    k.clone(),
                    gamma.clone(),
                    beta.clone(),
                    eps,
                    z.clone(),
                ],
            );
            let bound_vec = Expr::proj(ib_name.clone(), proj_idx, out);
            let lhs = Expr::app(bound_vec, i.clone());

            let gamma_i = Expr::app(gamma.clone(), i.clone());
            let center_i = Expr::app(Expr::proj(zono_name.clone(), 0, z.clone()), i.clone());
            let beta_i = Expr::app(beta.clone(), i.clone());
            let gens_i = Expr::app(Expr::proj(zono_name.clone(), 1, z.clone()), i.clone());
            let rhs = build_rhs(&b, &fin_k, &k, &gamma_i, &center_i, &beta_i, &gens_i);

            let concl = c.rat_eq(lhs, rhs);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n, concl);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value : fun n k γ β ε z i => Eq.refl Rat RHS.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let zono_nk = c.zono_of(&n, &k);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, _eps) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            let gamma_i = Expr::app(gamma.clone(), i.clone());
            let center_i = Expr::app(Expr::proj(zono_name.clone(), 0, z.clone()), i.clone());
            let beta_i = Expr::app(beta.clone(), i.clone());
            let gens_i = Expr::app(Expr::proj(zono_name.clone(), 1, z.clone()), i.clone());
            let rhs = build_rhs(&b, &fin_k, &k, &gamma_i, &center_i, &beta_i, &gens_i);
            let refl = Expr::apps(c.eq_refl.clone(), [c.rat.clone(), rhs]);

            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, refl);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
            let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Which interval bound the per-component equation pins.
#[derive(Clone, Copy)]
enum BoundSide {
    Lower,
    Upper,
}

/// Recursively check whether `e` mentions the const named `target`.
fn expr_mentions(e: &Expr, target: &str) -> bool {
    use crate::expr::ExprKind;
    let t = Name::from_string(target);
    fn go(e: &Expr, t: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == t,
            ExprKind::App(f, a) => go(f, t) || go(a, t),
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => go(ty, t) || go(b, t),
            ExprKind::Let(_, ty, v, b, _) => go(ty, t) || go(v, t) || go(b, t),
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => go(x, t),
            _ => false,
        }
    }
    go(e, &t)
}
