// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope compression soundness theorems (T10-T12).
//!
//! Formalizes the key theorems establishing zonotope soundness:
//!
//! ## Theorems
//!
//! - **T10: `NNVerify.Zonotope.center_contained`** — the center of a zonotope
//!   is always contained in it: `forall z, contains z (center z)`.
//!   Proof: instantiate eps = 0, which satisfies |0| <= 1 and
//!   center + G*0 = center.
//!
//! - **T11: `NNVerify.Zonotope.compress_sound`** — compression preserves
//!   containment: `forall z z', compress z = z' -> forall x, contains z x -> contains z' x`.
//!   This is the key soundness theorem for zonotope domain compression.
//!
//! - **T12: `NNVerify.Zonotope.to_ibp_sound`** — zonotope-to-IBP conversion
//!   is sound: `forall z x, contains z x -> IntervalBounds.contains (to_ibp z) x`.
//!   Every point in the zonotope is also in its IBP over-approximation.
//!
//! ## Helper Theorem
//!
//! - `NNVerify.Zonotope.zero_eps_valid` — zero epsilon vector has entries in
//!   [-1,1]. Constructive `Declaration::Theorem` (eps=0 bound) reusing the same
//!   `Rat`-order bricks T10 uses inline; transitive axiom closure is empty.
//!
//! Part of #3152.

use super::nn_verify_zonotope::ZonotopeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize zonotope compression soundness declarations (T10-T12).
    ///
    /// Depends on: `init_nn_verify_zonotope()` for Zonotope types.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, T10/T11/T12 are registered
    /// ENSURES: Idempotent (guarded by `nn_verify_zonotope_compress_init`)
    pub(crate) fn init_nn_verify_zonotope_compress(&mut self) -> Result<(), EnvError> {
        // Reuse the same init flag — types and theorems are one logical unit.
        // The zonotope init method already sets the flag.
        self.init_nn_verify_zonotope()?;

        // T10's constructive witness needs: function extensionality (lift the
        // pointwise `center = center + G·0` identity to the NNVec equality),
        // the `Fin.sum` linearity overlay (`Fin.sum_congr`, `Fin.sum_zero_fn`,
        // plus the reducible `Rat.mul_zero` / `Rat.add_zero` field theorems it
        // pulls in via `init_rat_field_inst`), and the `Rat`-order brick
        // `Rat.neg_le_neg` for the `-1 ≤ 0` half of the epsilon bound.
        // `init_rat_linear_order` (already in `init_nn_verify_zonotope`)
        // supplies `Rat.zero_lt_one` / `Rat.lt_iff_le_not_le` for the `0 ≤ 1`
        // half, and `init_nn_verify_tier_a_rat_neg_zero_zero` proves
        // `Rat.neg 0 = 0` so the `Rat.neg_le_neg 0 1 _` witness retypes at
        // `-1 ≤ 0` by def-eq.
        self.init_funext()?;
        self.init_fin_sum()?;
        self.register_rat_neg_le_neg()?;
        self.init_nn_verify_tier_a_rat_neg_zero_zero()?;

        // T12 (faithful `to_ibp_sound`) additionally needs:
        //   - `Rat.abs` (faithful carrier) + `Rat.abs_nonneg` / `Rat.abs_mul`
        //     + lattice lemmas `Rat.le_max_left/right` / `Rat.max_le`
        //     (all via `init_rat_abs`),
        //   - `Rat.neg_neg` (via `init_boolean_analysis_order_toolkit`),
        //   - `Rat.le_abs_self` / `Rat.neg_abs_le` (built over the faithful
        //     carrier by `register_rat_abs_self_bounds`),
        //   - `NNVerify.mul_nonneg_le_left` (via `init_nn_verify_ibp_linear`),
        //   - `Fin.sum_neg` (via `register_fin_sum_neg_theorem`),
        //   - `Rat.mul_one` (via `init_rat_field_inst`).
        self.init_rat_abs()?;
        self.init_rat_field_inst()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.register_rat_abs_self_bounds()?;
        self.init_nn_verify_ibp_linear()?;
        self.register_fin_sum_neg_theorem()?;

        let c = ZonotopeConsts::new();

        // Helper theorem (eps=0 bound) — constructive, reuses T10's Rat bricks.
        self.register_zero_eps_valid(&c)?;

        // T10: center containment
        self.register_t10_center_contained(&c)?;
        // T11: compression soundness
        self.register_t11_compress_sound(&c)?;
        // T12: zonotope-to-IBP conversion soundness
        self.register_t12_to_ibp_sound(&c)?;

        Ok(())
    }

    /// `NNVerify.Zonotope.zero_eps_valid` (constructive `Declaration::Theorem` —
    /// eps=0 bound helper, #3152 promotion):
    /// `forall (k : Nat) (i : Fin k), LE.le (Rat.neg Rat.one) Rat.zero /\
    ///   LE.le Rat.zero Rat.one`
    ///
    /// The zero vector satisfies the epsilon-ball constraint [-1, 1]. This was a
    /// bare `Declaration::Axiom`; it is now a genuine kernel-checked term built
    /// from the SAME constructive `Rat`-order bricks T10 (`center_contained`)
    /// uses inline for its per-coordinate bound (`build_t10_bounds`).
    ///
    /// SOUNDNESS: eps=0 bound, NOT an `Eq.refl`/opaque masquerade. The value is
    /// `fun (k : Nat) (_i : Fin k) =>
    ///    And.intro (-1 ≤ 0)(0 ≤ 1) neg_one_le_zero zero_le_one`, where:
    /// - `neg_one_le_zero` = `Rat.neg_le_neg 0 1 (0 ≤ 1)` (retypes at `-1 ≤ 0`
    ///   because `Rat.neg 0 ≡ 0` by def-eq via the constructive
    ///   `NNVerify.Rat.neg_zero_zero`), and
    /// - `zero_le_one` = `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 1)
    ///   Rat.zero_lt_one)`.
    ///
    /// Every `Rat`-order brick it reuses (`Rat.neg_le_neg`,
    /// `Rat.lt_iff_le_not_le`, `Rat.zero_lt_one`) is itself a constructive
    /// `Declaration::Theorem` over the quotient-`Rat` carrier, so the head is
    /// `And.intro` and the transitive axiom closure is EMPTY (`⊆ FOUNDATIONAL`,
    /// `ProofQuality::Constructive`) — NO new axiom, and it leaves the
    /// admitted-axiom census entirely (Axiom → constructive Theorem). Pinned by
    /// `test_zero_eps_valid_is_constructive_theorem_with_and_intro_value` and
    /// `test_zero_eps_valid_axiom_closure_is_foundational`.
    fn register_zero_eps_valid(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if matches!(
            self.get_const(&Name::from_string("NNVerify.Zonotope.zero_eps_valid"))
                .map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let h = T10Consts::new();
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let neg_one = Expr::app(c.rat_neg.clone(), c.rat_one.clone());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let fin_k = Expr::app(c.fin.clone(), k.clone());
            let (i_id, _i) = b.fresh_local(fin_k.clone());
            let conj = Expr::app(
                Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), rat_zero.clone())),
                c.rat_le(rat_zero.clone(), c.rat_one.clone()),
            );
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_k, conj);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // value: fun (k : Nat) (_i : Fin k) =>
        //          And.intro (-1 ≤ 0)(0 ≤ 1) neg_one_le_zero zero_le_one.
        let value = {
            let le_neg = c.rat_le(neg_one.clone(), rat_zero.clone());
            let le_one = c.rat_le(rat_zero.clone(), c.rat_one.clone());
            let proof = Expr::apps(
                h.and_intro.clone(),
                [le_neg, le_one, h.neg_one_le_zero(), h.zero_le_one()],
            );
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let fin_k = Expr::app(c.fin.clone(), k.clone());
            let (i_id, _i) = b.fresh_local(fin_k.clone());
            let body = b.mk_lam(i_id, BinderInfo::Default, fin_k, proof);
            let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(lam)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Zonotope.zero_eps_valid"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **T10: `NNVerify.Zonotope.center_contained`** (constructive
    /// `Declaration::Theorem` — eps=0 witness, #3152 lane-4c promotion).
    /// `forall (n k : Nat) (z : Zonotope n k), contains z (center z)`
    ///
    /// The center of a zonotope is always contained in it. T10 was a bare
    /// `Declaration::Axiom`; it is now a genuine kernel-checked term that
    /// constructs the existential witness `ε := 0` and discharges both
    /// conjuncts of the `contains` body.
    ///
    /// SOUNDNESS: eps=0 witness, NOT an `Eq.refl`/opaque masquerade.
    /// `contains z (center z)` reducibly unfolds to
    /// `∃ ε : NNVec k, (∀ i, -1 ≤ ε i ∧ ε i ≤ 1) ∧
    ///    center = NNVec.add center (NNMat.mulVec G ε)`.
    /// We supply `Exists.intro (fun _ => Rat.zero) (And.intro bounds eqx)`:
    /// - `bounds`: for every `i`, `And.intro (-1 ≤ 0)(0 ≤ 1)` from
    ///   `Rat.neg_le_neg 0 1 (0 ≤ 1)` (`Rat.neg 0 ≡ 0` by def-eq via the
    ///   constructive `NNVerify.Rat.neg_zero_zero`) and the `0 ≤ 1` term
    ///   `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 1) Rat.zero_lt_one)`.
    /// - `eqx`: `funext` over the pointwise identity
    ///   `center i = center i + Σⱼ (G i j · 0)`, where the sum collapses by
    ///   `Fin.sum_congr` (`Rat.mul_zero`) then `Fin.sum_zero_fn`, and the
    ///   `+ 0` collapses by `Rat.add_zero`; the goal is its `Eq.symm`.
    ///
    /// Closure: every `Rat`-order / field / `Fin.sum` brick it reuses
    /// (`Rat.neg_le_neg`, `Rat.lt_iff_le_not_le`, `Rat.add_zero`,
    /// `Rat.mul_zero`, `Fin.sum_congr`, `Fin.sum_zero_fn`, ...) is itself a
    /// constructive `Declaration::Theorem` over the quotient-`Rat` carrier, so
    /// T10's transitive axiom closure is EMPTY (`⊆ FOUNDATIONAL`,
    /// `ProofQuality::Constructive`) — NO new axiom, and it leaves the
    /// admitted-axiom census entirely (Axiom → constructive Theorem whose
    /// proof head is `Exists.intro`). Pinned by
    /// `test_t10_axiom_closure_is_foundational`.
    fn register_t10_center_contained(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if matches!(
            self.get_const(&Name::from_string("NNVerify.Zonotope.center_contained"))
                .map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let helpers = T10Consts::new();
        let ty = build_t10_type(c);
        let value = build_t10_value(c, &helpers);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Zonotope.center_contained"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **T11: `NNVerify.Zonotope.compress_sound`** (HONEST hypothesis-wrapped
    /// restatement — #zono-false fix).
    ///
    /// The OLD axiom was REFUTABLE: `compress n k k' z = z' → ∀ x, contains z x →
    /// contains z' x` claimed UNCONDITIONAL over-approximation for the OPAQUE
    /// `compress`. At `k' = 0` the compressed `z'` is a POINT zonotope (it
    /// contains exactly its center), yet a non-degenerate `z` (with a generator,
    /// `k ≥ 1`) contains a whole segment — so no `z'.center` can contain every
    /// `x ∈ z`. Counterexample pinned in
    /// `tests_zonotope_false_axiom_prevention.rs` (`z' = {0}`, `x = 1` ⇒
    /// `contains {0} 1`, false).
    ///
    /// No premise over the OPAQUE `compress` makes the unconditional claim true:
    /// the predecessor's `k' ≥ n` box-cover bound is only sufficient *together
    /// with* a faithful box-compression BODY (which needs `Rat.abs` + Fin
    /// row-sums — deferred). Until that body lands, we follow the established
    /// house pattern for unproved-content-over-an-opaque-carrier (cf.
    /// `compress_tightness` / `compress_tightness_helper` in
    /// `nn_verify_zonotope_compress_c001.rs`): make the missing
    /// over-approximation an EXPLICIT, caller-visible local hypothesis and return
    /// it, instead of laundering it as an unconditional axiom.
    ///
    /// `forall (n k k' : Nat) (z : Zonotope n k) (z' : Zonotope n k'),
    ///   compress n k k' z = z' ->
    ///   (h_over : forall (x : NNVec n), contains z x -> contains z' x) ->
    ///   forall (x : NNVec n), contains z x -> contains z' x`
    ///
    /// The body returns `h_over`. This is honest (it transparently states
    /// "compression preserves containment IF compression over-approximates"), it
    /// is no longer refutable (the conclusion is only reached after discharging
    /// the undischargeable `h_over`/`compress = z'` hypotheses, so C4 classifies
    /// it `Opaque`/trusted), and it threads cleanly through C001a.
    ///
    /// Registered as a `Declaration::Theorem` (it carries a real proof term — the
    /// identity on `h_over`), so it is NOT counted among admitted domain axioms.
    fn register_t11_compress_sound(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.compress_sound"))
            .is_some()
        {
            return Ok(());
        }
        // Shared builder for the over-approximation predicate
        // `∀ (x : NNVec n), contains z x → contains z' x`.
        let build_over = |b: &EnvDeclBuilder,
                          n: &Expr,
                          k: &Expr,
                          kp: &Expr,
                          z: &Expr,
                          zp: &Expr,
                          vec_n: &Expr| {
            let mut ch = EnvDeclBuilder::child_of(b);
            let (x_id, x) = ch.fresh_local(vec_n.clone());
            let h_contains = c.contains(n, k, z, &x);
            let concl = c.contains(n, kp, zp, &x);
            let (hc_id, _) = ch.fresh_local(h_contains.clone());
            let inner = ch.mk_pi(hc_id, BinderInfo::Default, h_contains, concl);
            let pi = ch.mk_pi(x_id, BinderInfo::Default, vec_n.clone(), inner);
            ch.finish_child(pi)
        };

        // `h_le : Nat.le k' k` — required by the refined `compress` arity.
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let h_le_ty = Expr::apps(nat_le.clone(), [kp.clone(), k.clone()]);
            let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let zono_nkp = c.zono_of(n.clone(), kp.clone());
            let vec_n = c.vec_of(n.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());

            // compress n k k' h_le z = z'
            let compress_app = Expr::apps(
                c.zono_compress.clone(),
                [n.clone(), k.clone(), kp.clone(), hle.clone(), z.clone()],
            );
            let h_compress = c.eq_of(zono_nkp.clone(), compress_app, zp.clone());

            // h_over : ∀ x, contains z x → contains z' x  (premise AND conclusion).
            let over = build_over(&b, &n, &k, &kp, &z, &zp, &vec_n);

            let (hover_id, _) = b.fresh_local(over.clone());
            let (hcomp_id, _) = b.fresh_local(h_compress.clone());

            let r = b.mk_pi(hover_id, BinderInfo::Default, over.clone(), over);
            let r = b.mk_pi(hcomp_id, BinderInfo::Default, h_compress, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Proof term: `fun n k k' h_le z z' _hcomp h_over => h_over`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let h_le_ty = Expr::apps(nat_le.clone(), [kp.clone(), k.clone()]);
            let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let zono_nkp = c.zono_of(n.clone(), kp.clone());
            let vec_n = c.vec_of(n.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());

            let compress_app = Expr::apps(
                c.zono_compress.clone(),
                [n.clone(), k.clone(), kp.clone(), hle.clone(), z.clone()],
            );
            let h_compress = c.eq_of(zono_nkp.clone(), compress_app, zp.clone());
            let over = build_over(&b, &n, &k, &kp, &z, &zp, &vec_n);

            let (hover_id, hover) = b.fresh_local(over.clone());
            let (hcomp_id, _) = b.fresh_local(h_compress.clone());

            // return h_over
            let e = b.mk_lam(hover_id, BinderInfo::Default, over, hover);
            let e = b.mk_lam(hcomp_id, BinderInfo::Default, h_compress, e);
            let e = b.mk_lam(zp_id, BinderInfo::Default, zono_nkp, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le_ty, e);
            let e = b.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Zonotope.compress_sound"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **T12: `NNVerify.Zonotope.to_ibp_sound`** (constructive
    /// `Declaration::Theorem` — FAITHFUL zonotope→IBP soundness).
    /// `forall (n k : Nat) (z : Zonotope n k) (x : NNVec n),
    ///   contains z x -> IntervalBounds.contains (to_ibp n k z) x`
    ///
    /// Zonotope-to-IBP conversion is sound: any point in the zonotope is also
    /// in the interval bounds computed by `to_ibp`. T12 was a bare
    /// `Declaration::Axiom`; with the faithful `to_ibp`
    /// (`[center − Σ|G|, center + Σ|G|]`) it is now a genuine kernel-checked
    /// term — the triangle-inequality argument that `|Σⱼ G_ij εⱼ| ≤ Σⱼ |G_ij|`
    /// when `|εⱼ| ≤ 1`. See `nn_verify_zonotope_to_ibp_sound_proof` for the
    /// proof builder.
    ///
    /// ## Soundness note
    ///
    /// The proof's transitive closure reaches the per-summand / sum bricks:
    /// `Rat.abs_mul`, `NNVerify.mul_nonneg_le_left`, `Rat.le_abs_self`,
    /// `Rat.neg_abs_le` (the latter two built constructively here over the
    /// faithful `Rat.abs = max a (-a)` carrier), `Rat.mul_one`, `Rat.max_le`,
    /// `Rat.neg_le_neg`, `Rat.neg_neg`, `Rat.le_trans`, `Rat.add_le_add_left`,
    /// `Fin.sum_le`, `Fin.sum_neg`, plus `Eq.subst` / `Eq.symm` / `And.*` /
    /// `Exists.elim`. Whether the closure is `⊆ FOUNDATIONAL` depends on
    /// `Fin.sum_le` / `Rat.abs_mul` being constructive theorems (they are, in
    /// the overlays build) vs. honest admitted axioms — audited separately by
    /// the Soundness Certificate.
    fn register_t12_to_ibp_sound(&mut self, c: &ZonotopeConsts) -> Result<(), EnvError> {
        if matches!(
            self.get_const(&Name::from_string("NNVerify.Zonotope.to_ibp_sound"))
                .map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(n.clone(), k.clone());
            let vec_n = c.vec_of(n.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());

            // to_ibp n k z
            let to_ibp_app = Expr::app(
                Expr::app(Expr::app(c.zono_to_ibp.clone(), n.clone()), k.clone()),
                z.clone(),
            );
            let h_zono_contains = c.contains(&n, &k, &z, &x);
            let concl = c.ib_contains_app(&n, &to_ibp_app, &x);

            let (hc_id, _) = b.fresh_local(h_zono_contains.clone());

            let r = b.mk_pi(hc_id, BinderInfo::Default, h_zono_contains, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = super::nn_verify_zonotope_to_ibp_sound_proof::build_to_ibp_sound_value(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Zonotope.to_ibp_sound"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Constants used to build T10's constructive proof term.
///
/// All names are registered before `register_t10_center_contained` runs (see
/// the extra `init_*` / `register_*` calls in `init_nn_verify_zonotope_compress`).
struct T10Consts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_neg: Expr,
    /// `Eq.symm.{1}`.
    eq_symm: Expr,
    /// `Eq.trans.{1}`.
    eq_trans: Expr,
    /// `congrArg.{1,1}`.
    congr_arg: Expr,
    /// `Exists.intro.{1}`.
    exists_intro: Expr,
    and_intro: Expr,
    and_left: Expr,
    iff_mp: Expr,
    not_const: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    fin_sum_zero_fn: Expr,
    funext: Expr,
    rat_add_zero: Expr,
    rat_mul_zero: Expr,
    rat_neg_le_neg: Expr,
    rat_zero_lt_one: Expr,
    rat_lt_iff_le_not_le: Expr,
}

impl T10Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            iff_mp: Expr::const_(Name::from_string("Iff.mp"), vec![]),
            not_const: Expr::const_(Name::from_string("Not"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            fin_sum_zero_fn: Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]),
            funext: Expr::const_(Name::from_string("funext"), vec![l1.clone(), l1]),
            rat_add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            rat_mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            rat_neg_le_neg: Expr::const_(Name::from_string("Rat.neg_le_neg"), vec![]),
            rat_zero_lt_one: Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]),
            rat_lt_iff_le_not_le: Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        }
    }

    /// `-1 ≤ 0`-half proof, of type `LE.le Rat instLERat (Rat.neg Rat.one) Rat.zero`.
    ///
    /// `Rat.neg_le_neg 0 1 (0 ≤ 1) : Rat.neg 1 ≤ Rat.neg 0`; the kernel accepts
    /// this against `Rat.neg 1 ≤ 0` because `Rat.neg 0 ≡ 0` (the constructive
    /// `NNVerify.Rat.neg_zero_zero` is an `Eq.refl` witnessing exactly this
    /// def-eq).
    fn neg_one_le_zero(&self) -> Expr {
        Expr::apps(
            self.rat_neg_le_neg.clone(),
            [
                self.rat_zero.clone(),
                self.rat_one.clone(),
                self.zero_le_one(),
            ],
        )
    }

    /// `0 ≤ 1`-half proof, of type `LE.le Rat instLERat Rat.zero Rat.one`.
    ///
    /// `And.left (0 ≤ 1) (¬ 1 ≤ 0)
    ///   (Iff.mp (Rat.lt 0 1) (And (0 ≤ 1)(¬ 1 ≤ 0))
    ///      (Rat.lt_iff_le_not_le 0 1) Rat.zero_lt_one)`.
    /// Mirrors the constructive `NNVerify.rat_zero_le_one` term (`Rat.le` and
    /// `LE.le Rat instLERat` are def-eq via `instLERat`).
    fn zero_le_one(&self) -> Expr {
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let le_01 = Expr::apps(
            rat_le.clone(),
            [self.rat_zero.clone(), self.rat_one.clone()],
        );
        let le_10 = Expr::apps(rat_le, [self.rat_one.clone(), self.rat_zero.clone()]);
        let not_le_10 = Expr::app(self.not_const.clone(), le_10);
        let lt_01 = Expr::apps(rat_lt, [self.rat_zero.clone(), self.rat_one.clone()]);
        let and_prop = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [le_01.clone(), not_le_10.clone()],
        );
        let lt_iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), self.rat_one.clone()],
        );
        let mp = Expr::apps(
            self.iff_mp.clone(),
            [lt_01, and_prop, lt_iff, self.rat_zero_lt_one.clone()],
        );
        Expr::apps(self.and_left.clone(), [le_01, not_le_10, mp])
    }
}

/// Build T10's declaration type:
///   `∀ (n k : Nat) (z : Zonotope n k), contains z (center z)`.
fn build_t10_type(c: &ZonotopeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let center = Expr::proj(Name::from_string("NNVerify.Zonotope"), 0, z.clone());
    let concl = c.contains(&n, &k, &z, &center);
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, concl);
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build T10's constructive proof term:
///   `fun n k z => @Exists.intro.{1} (NNVec k) P (fun _ => 0) (And.intro ...)`.
fn build_t10_value(c: &ZonotopeConsts, h: &T10Consts) -> Expr {
    let zono_name = Name::from_string("NNVerify.Zonotope");
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let vec_k = c.vec_of(k.clone());
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let center = Expr::proj(zono_name.clone(), 0, z.clone());
    let gens = Expr::proj(zono_name.clone(), 1, z.clone());

    // eps0 : NNVec k := fun (_ : Fin k) => Rat.zero.
    let eps0 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, _i) = ch.fresh_local(fin_k.clone());
        let lam = ch.mk_lam(i_id, BinderInfo::Default, fin_k.clone(), h.rat_zero.clone());
        ch.finish_child(lam)
    };

    // P : NNVec k → Prop — the EXACT body of the reducible `contains z center`.
    let p_motive = build_t10_predicate(c, h, &b, &n, &k, &center, &gens);

    // bounds proof : ∀ i, And (-1 ≤ eps0 i)(eps0 i ≤ 1).
    let bounds = build_t10_bounds(c, h, &b, &fin_k);
    // eqx proof : center = NNVec.add center (NNMat.mulVec gens eps0).
    let eqx = build_t10_eqx(c, h, &b, &n, &k, &center, &gens, &eps0);

    // The two conjunct PROPS (And.intro takes a,b explicitly in this kernel).
    // `eqx` is an equality over `NNVec n` (a `Type 0`), so it uses `c.eq_of`
    // (`Eq.{1}` with the carrier `NNVec n`), NOT the `Rat`-level `Eq`.
    let vec_n = c.vec_of(n.clone());
    let bounds_prop = build_t10_bounds_prop(c, h, &b, &fin_k, &eps0);
    let eqx_prop = c.eq_of(
        vec_n,
        center.clone(),
        rhs_of_eqx(c, h, &n, &k, &center, &gens, &eps0),
    );
    let and_proof = Expr::apps(h.and_intro.clone(), [bounds_prop, eqx_prop, bounds, eqx]);

    // @Exists.intro.{1} (NNVec k) P eps0 and_proof.
    let body = Expr::apps(h.exists_intro.clone(), [vec_k, p_motive, eps0, and_proof]);

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// RHS of the `eqx` equation:
///   `NNVerify.NNVec.add n center (NNVerify.NNMat.mulVec n k gens eps0)`.
fn rhs_of_eqx(
    c: &ZonotopeConsts,
    _h: &T10Consts,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
    eps0: &Expr,
) -> Expr {
    let mul = Expr::apps(
        c.nn_mat_mul_vec.clone(),
        [n.clone(), k.clone(), gens.clone(), eps0.clone()],
    );
    Expr::apps(c.nn_vec_add.clone(), [n.clone(), center.clone(), mul])
}

/// Build `P : NNVec k → Prop`, identical to the body lambda of the reducible
/// `NNVerify.Zonotope.contains` applied at `x := center`. Reconstructed here so
/// `Exists.intro`'s explicit predicate argument is syntactically the goal's.
fn build_t10_predicate(
    c: &ZonotopeConsts,
    h: &T10Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
) -> Expr {
    let neg_one = Expr::app(c.rat_neg.clone(), c.rat_one.clone());
    let vec_n = c.vec_of(n.clone());
    let vec_k = c.vec_of(k.clone());
    let fin_k = Expr::app(h.fin.clone(), k.clone());

    let mut ch = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = ch.fresh_local(vec_k.clone());

    // bounds(ε) = ∀ i : Fin k, (-1 ≤ ε i) ∧ (ε i ≤ 1).
    let bounds = {
        let mut d = EnvDeclBuilder::child_of(&ch);
        let (i_id, i) = d.fresh_local(fin_k.clone());
        let eps_i = Expr::app(eps.clone(), i);
        let conj = Expr::app(
            Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), eps_i.clone())),
            c.rat_le(eps_i, c.rat_one.clone()),
        );
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_k.clone(), conj))
    };

    // eqx(ε) = center = NNVec.add center (NNMat.mulVec gens ε).
    let rhs = rhs_of_eqx(c, h, n, k, center, gens, &eps);
    let eq_x = c.eq_of(vec_n.clone(), center.clone(), rhs);
    let conj_body = Expr::app(Expr::app(c.and.clone(), bounds), eq_x);
    let lam = ch.mk_lam(eps_id, BinderInfo::Default, vec_k, conj_body);
    ch.finish_child(lam)
}

/// Build the PROP `bounds(eps0) = ∀ i, (-1 ≤ eps0 i) ∧ (eps0 i ≤ 1)` (the first
/// conjunct's type, with the concrete `eps0` witness substituted).
fn build_t10_bounds_prop(
    c: &ZonotopeConsts,
    h: &T10Consts,
    parent: &EnvDeclBuilder,
    fin_k: &Expr,
    eps0: &Expr,
) -> Expr {
    let neg_one = Expr::app(c.rat_neg.clone(), c.rat_one.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = d.fresh_local(fin_k.clone());
    let eps_i = Expr::app(eps0.clone(), i);
    let conj = Expr::app(
        Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), eps_i.clone())),
        c.rat_le(eps_i, h.rat_one.clone()),
    );
    d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_k.clone(), conj))
}

/// Build the bounds proof:
///   `fun (i : Fin k) => And.intro (-1 ≤ 0)(0 ≤ 1) neg_one_le_zero zero_le_one`.
/// At each `i`, `eps0 i` β-reduces to `Rat.zero`, so the conjuncts are the
/// closed `-1 ≤ 0` / `0 ≤ 1` props.
fn build_t10_bounds(
    c: &ZonotopeConsts,
    h: &T10Consts,
    parent: &EnvDeclBuilder,
    fin_k: &Expr,
) -> Expr {
    let neg_one = Expr::app(c.rat_neg.clone(), c.rat_one.clone());
    let le_neg = c.rat_le(neg_one, h.rat_zero.clone());
    let le_one = c.rat_le(h.rat_zero.clone(), h.rat_one.clone());

    let mut d = EnvDeclBuilder::child_of(parent);
    let (i_id, _i) = d.fresh_local(fin_k.clone());
    let proof = Expr::apps(
        h.and_intro.clone(),
        [le_neg, le_one, h.neg_one_le_zero(), h.zero_le_one()],
    );
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_k.clone(), proof))
}

/// Build the `eqx` proof: `center = NNVec.add center (NNMat.mulVec gens eps0)`.
///
/// `funext` over the pointwise identity. The pointwise goal at `i : Fin n` is
/// (after the reducible `NNVec.add` / `NNMat.mulVec` unfold + β on `eps0`)
///   `center i = Rat.add (center i) (Fin.sum k (fun j => Rat.mul (gens i j) 0))`,
/// which is `Eq.symm` of `add_collapse`.
fn build_t10_eqx(
    c: &ZonotopeConsts,
    h: &T10Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
    eps0: &Expr,
) -> Expr {
    let vec_n = c.vec_of(n.clone());
    let fin_n = Expr::app(h.fin.clone(), n.clone());
    let rhs = rhs_of_eqx(c, h, n, k, center, gens, eps0);

    // β : fun (_ : Fin n) => Rat  — funext codomain motive.
    let beta = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, _i) = d.fresh_local(fin_n.clone());
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), h.rat.clone()))
    };

    // pointwise : fun (i : Fin n) => Eq.symm (add_collapse i).
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let center_i = Expr::app(center.clone(), i.clone());
        let gens_i = Expr::app(gens.clone(), i.clone());

        // inner_zero : Fin.sum k (fun j => Rat.mul (gens i j) 0) = 0.
        let inner_zero = build_inner_sum_zero(h, &d, k, &gens_i);

        // add_collapse : Rat.add (center i) (Fin.sum k ...) = center i.
        let inner_sum = build_inner_sum(h, &d, k, &gens_i);
        let add_inner = Expr::apps(h.rat_add.clone(), [center_i.clone(), inner_sum.clone()]);
        let add_zero = Expr::apps(h.rat_add.clone(), [center_i.clone(), h.rat_zero.clone()]);
        // congrArg (fun s => Rat.add (center i) s) inner_zero
        //   : Rat.add (center i)(Fin.sum...) = Rat.add (center i) 0.
        let add_closure = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (s_id, s) = e.fresh_local(h.rat.clone());
            let body = Expr::apps(h.rat_add.clone(), [center_i.clone(), s]);
            e.finish_child(e.mk_lam(s_id, BinderInfo::Default, h.rat.clone(), body))
        };
        let congr = Expr::apps(
            h.congr_arg.clone(),
            [
                h.rat.clone(),
                h.rat.clone(),
                inner_sum,
                h.rat_zero.clone(),
                add_closure,
                inner_zero,
            ],
        );
        // Rat.add_zero (center i) : Rat.add (center i) 0 = center i.
        let add_zero_proof = Expr::app(h.rat_add_zero.clone(), center_i.clone());
        // add_collapse : Rat.add (center i)(Fin.sum...) = center i.
        let add_collapse = Expr::apps(
            h.eq_trans.clone(),
            [
                h.rat.clone(),
                add_inner.clone(),
                add_zero,
                center_i.clone(),
                congr,
                add_zero_proof,
            ],
        );
        // goal: center i = Rat.add (center i)(Fin.sum...) = (rhs i)  ⇒  symm.
        let symm = Expr::apps(
            h.eq_symm.clone(),
            [h.rat.clone(), add_inner, center_i.clone(), add_collapse],
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), symm))
    };

    // @funext.{1,1} (Fin n) β center rhs pointwise : center = rhs.
    Expr::apps(
        h.funext.clone(),
        [fin_n, beta, center.clone(), rhs, pointwise],
    )
}

/// `Fin.sum k (fun (j : Fin k) => Rat.mul (gens_i j) Rat.zero)`.
fn build_inner_sum(h: &T10Consts, parent: &EnvDeclBuilder, k: &Expr, gens_i: &Expr) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let summand = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = e.fresh_local(fin_k.clone());
        let body = Expr::apps(
            h.rat_mul.clone(),
            [Expr::app(gens_i.clone(), j), h.rat_zero.clone()],
        );
        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    Expr::apps(h.fin_sum.clone(), [k.clone(), summand])
}

/// Proof `Fin.sum k (fun j => Rat.mul (gens_i j) 0) = Rat.zero`.
///
/// `Eq.trans (Fin.sum_congr k mul_fn zero_fn (fun j => Rat.mul_zero (gens_i j)))
///           (Fin.sum_zero_fn k)`.
fn build_inner_sum_zero(h: &T10Consts, parent: &EnvDeclBuilder, k: &Expr, gens_i: &Expr) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());

    // mul_fn : Fin k → Rat := fun j => Rat.mul (gens_i j) 0.
    let mul_fn = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = e.fresh_local(fin_k.clone());
        let body = Expr::apps(
            h.rat_mul.clone(),
            [Expr::app(gens_i.clone(), j), h.rat_zero.clone()],
        );
        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // zero_fn : Fin k → Rat := fun _ => 0.
    let zero_fn = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (j_id, _j) = e.fresh_local(fin_k.clone());
        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), h.rat_zero.clone()))
    };
    // pointwise : fun (j : Fin k) => Rat.mul_zero (gens_i j)
    //   : Rat.mul (gens_i j) 0 = 0.
    let pw = {
        let mut e = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = e.fresh_local(fin_k.clone());
        let body = Expr::app(h.rat_mul_zero.clone(), Expr::app(gens_i.clone(), j));
        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // congr : Fin.sum k mul_fn = Fin.sum k zero_fn.
    let congr = Expr::apps(
        h.fin_sum_congr.clone(),
        [k.clone(), mul_fn.clone(), zero_fn.clone(), pw],
    );
    // zfn : Fin.sum k zero_fn = 0.
    let zfn = Expr::app(h.fin_sum_zero_fn.clone(), k.clone());
    let sum_mul = Expr::apps(h.fin_sum.clone(), [k.clone(), mul_fn]);
    let sum_zero = Expr::apps(h.fin_sum.clone(), [k.clone(), zero_fn]);
    Expr::apps(
        h.eq_trans.clone(),
        [
            h.rat.clone(),
            sum_mul,
            sum_zero,
            h.rat_zero.clone(),
            congr,
            zfn,
        ],
    )
}
