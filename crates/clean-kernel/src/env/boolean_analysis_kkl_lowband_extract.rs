// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL spectral extraction — RUNG A: the low-band Fourier-mass extraction.
//!
//! ## What this rung proves
//!
//! The hypercontractive-bridge half of the KKL finish needs to bound the
//! UNWEIGHTED level-`≤k` Fourier mass by the NOISE-weighted full mass
//! `Σ_S (ρ²)^{|S|}·w S` (`= ‖T_ρ a‖₂²` un-normalized). This rung is the genuine
//! purely-rational spectral extraction, stated GENERALLY over a base `b ∈ [0,1]`
//! and a nonnegative weight `w` (no fractional-power / real carrier — the
//! `(ρ²)^{|S|}` weights are `Rat.powNat`):
//!
//! ```text
//! BoolAnalysis.subsetSum_low_band_extract :
//!   ∀ (n k : Nat) (b : Rat) (w : HCPoint n → Rat),
//!     Rat.le Rat.zero b → Rat.le b Rat.one → (∀ S, Rat.le Rat.zero (w S)) →
//!       Rat.le
//!         (Rat.mul (Rat.powNat b k)
//!                  (subsetSum n (fun S => Rat.mul (ind (Nat.ble (setSizeNat n S) k)) (w S))))
//!         (subsetSum n (fun S => Rat.mul (Rat.powNat b (setSizeNat n S)) (w S)))
//! ```
//!
//! i.e. `b^k · W^{≤k}_b[w]  ≤  Σ_S b^{|S|}·w S`, where
//!   * `W^{≤k}_b[w] := Σ_S [|S| ≤ k]·w S` is the un-weighted level-`≤k` mass
//!     (the `Nat.ble (setSizeNat n S) k` mask is the `|S| ≤ k` low-band bit), and
//!   * `Σ_S b^{|S|}·w S` is the noise-weighted full mass.
//!
//! **At `b := ρ² = 1/9` (`ρ = 1/3`) and `w S := f̂(S)²`**, the RHS is the
//! un-normalized `‖T_{1/3} g‖₂² = Σ_S (1/9)^{|S|}·f̂(S)²` (the `noise_spectral_level`
//! interface), so this is exactly the `(1/9)^k · W^{≤k}[g] ≤ ‖T_{1/3} g‖₂²`
//! low-band extraction the bridge consumes — the `9^k · ‖T_{1/3} g‖₂²` form is the
//! one further rational step away (multiply through by `9^k` and clear
//! `9^k·(1/9)^k = 1`), but the inverse-free `b^k·…` form proven here is the
//! load-bearing rational primitive (it needs NO `b⁻ᵏ` inverse identity).
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. **Per-`S`** (`Rat.threshold_term_le`, the on-branch per-term core): at
//!    `(k := b^k, size := b^{|S|}, w := w S, bit := [|S| ≤ k])` it gives
//!    `b^k·(ind bit·w S) ≤ b^{|S|}·w S`, once its three hypotheses are
//!    discharged:
//!      - `0 ≤ w S` — the lemma's own `hw` argument;
//!      - `0 ≤ b^{|S|}` — `Rat.powNat_nonneg b (setSizeNat n S) hb0`;
//!      - `bit = true → b^k ≤ b^{|S|}` — from `Nat.le_of_ble_eq_true |S| k`
//!        (`|S| ≤ k`) fed to the LANDED antitone power lemma
//!        `Rat.powNat_le_powNat_right_antitone b |S| k hb0 hb1 (|S| ≤ k)`
//!        (`0 ≤ b ≤ 1 ∧ |S| ≤ k → b^k ≤ b^{|S|}`).
//! 2. **Lift** (`subsetSum_le_of_pointwise`): the per-`S` core, applied
//!    pointwise, lifts to
//!    `Σ_S b^k·(ind bit·w S) ≤ Σ_S b^{|S|}·w S`.
//! 3. **Pull the scalar OUT** (`subsetSum_smul`):
//!    `Σ_S b^k·(ind bit·w S) = b^k · Σ_S ind bit·w S`; `Eq.subst`
//!    (motive `t ↦ t ≤ Σ_S b^{|S|}·w S`) transports (2) along it to the stated
//!    `b^k · W^{≤k}_b[w] ≤ Σ_S b^{|S|}·w S`.
//!
//! Every leaf (`Rat.threshold_term_le`, `Rat.powNat_nonneg`,
//! `Rat.powNat_le_powNat_right_antitone`, `Nat.le_of_ble_eq_true`,
//! `subsetSum_le_of_pointwise`, `subsetSum_smul`, `Eq.subst`/`Eq.symm`) is
//! `Constructive` with empty closure, so this rung is too. No axiom is added or
//! removed. Idempotent.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the low-band-extraction rung. The `ind` / `Nat.ble` /
/// `setSizeNat` / `subsetSum` builds are byte-for-byte the on-branch
/// `dyadic_level_sum` / `K2b` spellings so all terms stay def-eq to the bricks
/// they reuse.
struct LowBandExtractConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    hcpoint: Expr,
    ind: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    pow_nat: Expr,
    nat_ble: Expr,
    u1: Level,
}

impl LowBandExtractConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Rat.powNat b k`.
    fn pow(&self, b: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), k.clone()])
    }
    /// `Nat.ble a m`.
    fn ble(&self, a: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, m])
    }
    /// `bit = Bool.true`.
    fn bit_eq_true(&self, bit: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), bit, self.bool_true.clone()],
        )
    }
    /// The low-band mask integrand `fun S => ind (ble |S| k) · w S` —
    /// `ble (setSizeNat n S) k` is the `|S| ≤ k` low-band bit.
    fn mask_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(self.set_size_nat_of(n, &s), k.clone());
        let body = self.mul(self.ind_of(bit), Expr::app(w.clone(), s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The scaled LHS integrand `fun S => b^k · (ind (ble |S| k) · w S)` — the
    /// `subsetSum_smul` / `threshold_term_le` LHS shape `b^k · mask S`.
    fn scaled_mask_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        k: &Expr,
        b: &Expr,
        w: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(self.set_size_nat_of(n, &s), k.clone());
        let body = self.mul(
            self.pow(b, k),
            self.mul(self.ind_of(bit), Expr::app(w.clone(), s)),
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The RHS integrand `fun S => b^{|S|} · w S`.
    fn weighted_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, w: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.mul(
            self.pow(b, &self.set_size_nat_of(n, &s)),
            Expr::app(w.clone(), s),
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the RUNG-A low-band spectral-extraction rung. Idempotent.
    pub fn init_boolean_analysis_kkl_lowband_extract(&mut self) -> Result<(), EnvError> {
        self.register_subset_sum_low_band_extract()?;
        Ok(())
    }

    /// `BoolAnalysis.subsetSum_low_band_extract :
    ///   ∀ (n k : Nat) (b : Rat) (w : HCPoint n → Rat),
    ///     0 ≤ b → b ≤ 1 → (∀ S, 0 ≤ w S) →
    ///       Rat.le (b^k · subsetSum n (fun S => ind (ble |S| k) · w S))
    ///              (subsetSum n (fun S => b^{|S|} · w S))`.
    ///
    /// The low-band Fourier-mass extraction `b^k·W^{≤k}_b[w] ≤ Σ_S b^{|S|}·w S`.
    /// See module docs for the proof and the `ρ²=1/9 / w=f̂²` specialization.
    pub fn register_subset_sum_low_band_extract(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_low_band_extract");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Pull the Boolean-analysis aggregate FIRST. It is the transitive
        // dependency of every brick below (`Rat.threshold_term_le` etc. each
        // re-enter it). Because this rung is now wired INTO the aggregate, the
        // call below registers the whole chain — including this very theorem — so
        // the post-init guard then short-circuits, avoiding a re-entrant
        // double-`add_decl` of any shared brick.
        self.init_boolean_analysis()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_threshold_term_le()?; // Rat.threshold_term_le (per-S core)
        self.register_subset_sum_le_of_pointwise()?; // subsetSum_le_of_pointwise
        self.register_subset_sum_smul_theorem()?; // subsetSum_smul
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.register_rat_pow_nat_le_pow_nat_right_antitone()?; // antitone exponent bound
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true
        self.register_subset_sum()?;
        self.register_set_size_nat()?;

        // Re-check the guard: the dependency inits above (transitively
        // `init_boolean_analysis`) may have re-entered this registrar via the
        // always-on wiring chain and already registered the theorem.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = LowBandExtractConsts::new();
        let threshold_term_le = Expr::const_(Name::from_string("Rat.threshold_term_le"), vec![]);
        let pow_nat_nonneg = Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]);
        let antitone = Expr::const_(
            Name::from_string("Rat.powNat_le_powNat_right_antitone"),
            vec![],
        );
        let le_of_ble = Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]);
        let subset_sum_le_pw = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        );
        let subset_sum_smul =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);

        let ty = {
            let mut bld = EnvDeclBuilder::new();
            let (n_id, n) = bld.fresh_local(c.nat.clone());
            let (k_id, k) = bld.fresh_local(c.nat.clone());
            let (b_id, bv) = bld.fresh_local(c.rat.clone());
            let w_ty = c.hcpoint_to_rat(&n);
            let (w_id, w) = bld.fresh_local(w_ty.clone());

            // hb0 : 0 ≤ b ; hb1 : b ≤ 1
            let hb0_ty = c.rat_le(c.order.rat_zero.clone(), bv.clone());
            let hb1_ty = c.rat_le(bv.clone(), c.order.rat_one.clone());
            // hw : ∀ S, 0 ≤ w S
            let hw_ty = {
                let mut ch = EnvDeclBuilder::child_of(&bld);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c.rat_le(c.order.rat_zero.clone(), Expr::app(w.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };

            let mass = c.subset_sum_of(&n, c.mask_fn(&bld, &n, &k, &w));
            let lhs = c.mul(c.pow(&bv, &k), mass);
            let rhs = c.subset_sum_of(&n, c.weighted_fn(&bld, &n, &bv, &w));
            let concl = c.rat_le(lhs, rhs);

            let (hb0_id, _) = bld.fresh_local(hb0_ty.clone());
            let (hb1_id, _) = bld.fresh_local(hb1_ty.clone());
            let (hw_id, _) = bld.fresh_local(hw_ty.clone());
            let e = bld.mk_pi(hw_id, BinderInfo::Default, hw_ty, concl);
            let e = bld.mk_pi(hb1_id, BinderInfo::Default, hb1_ty, e);
            let e = bld.mk_pi(hb0_id, BinderInfo::Default, hb0_ty, e);
            let e = bld.mk_pi(w_id, BinderInfo::Default, w_ty, e);
            let e = bld.mk_pi(b_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bld.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = bld.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            bld.finish(e)
        };

        let value = {
            let mut bld = EnvDeclBuilder::new();
            let (n_id, n) = bld.fresh_local(c.nat.clone());
            let (k_id, k) = bld.fresh_local(c.nat.clone());
            let (b_id, bv) = bld.fresh_local(c.rat.clone());
            let w_ty = c.hcpoint_to_rat(&n);
            let (w_id, w) = bld.fresh_local(w_ty.clone());

            let hb0_ty = c.rat_le(c.order.rat_zero.clone(), bv.clone());
            let hb1_ty = c.rat_le(bv.clone(), c.order.rat_one.clone());
            let hw_ty = {
                let mut ch = EnvDeclBuilder::child_of(&bld);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c.rat_le(c.order.rat_zero.clone(), Expr::app(w.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let (hb0_id, hb0) = bld.fresh_local(hb0_ty.clone());
            let (hb1_id, hb1) = bld.fresh_local(hb1_ty.clone());
            let (hw_id, hw) = bld.fresh_local(hw_ty.clone());

            let pow_b_k = c.pow(&bv, &k);
            let mask = c.mask_fn(&bld, &n, &k, &w);
            let scaled = c.scaled_mask_fn(&bld, &n, &k, &bv, &w);
            let weighted = c.weighted_fn(&bld, &n, &bv, &w);
            let rhs = c.subset_sum_of(&n, weighted.clone());

            // pointwise : ∀ S, (scaled S) ≤ (weighted S)
            //   := fun S => Rat.threshold_term_le (b^k) (b^{|S|}) (w S) (ble |S| k)
            //                 (hw S)                         -- 0 ≤ w S
            //                 (powNat_nonneg b |S| hb0)      -- 0 ≤ b^{|S|}
            //                 (hthr S)                       -- bit=true → b^k ≤ b^{|S|}
            let pointwise = {
                let mut ch = EnvDeclBuilder::child_of(&bld);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let size_nat = c.set_size_nat_of(&n, &s); // |S|
                let pow_b_size = c.pow(&bv, &size_nat); // b^{|S|}
                let w_s = Expr::app(w.clone(), s.clone());
                let bit = c.ble(size_nat.clone(), k.clone()); // [|S| ≤ k]

                // h_w_s : 0 ≤ w S
                let h_w_s = Expr::app(hw.clone(), s.clone());
                // h_size_nn : 0 ≤ b^{|S|}   := powNat_nonneg b |S| hb0
                let h_size_nn = Expr::apps(
                    pow_nat_nonneg.clone(),
                    [bv.clone(), size_nat.clone(), hb0.clone()],
                );
                // hthr : (ble |S| k = true) → b^k ≤ b^{|S|}
                //   := fun (h : ble |S| k = true) =>
                //        antitone b |S| k hb0 hb1 (Nat.le_of_ble_eq_true |S| k h)
                //   (antitone b m n h0 h1 (m≤n) : b^n ≤ b^m, here m:=|S|, n:=k ⇒ b^k ≤ b^{|S|}).
                let hthr = {
                    let mut hb = EnvDeclBuilder::child_of(&ch);
                    let ante = c.bit_eq_true(bit.clone());
                    let (h_id, h) = hb.fresh_local(ante.clone());
                    // |S| ≤ k
                    let h_le = Expr::apps(le_of_ble.clone(), [size_nat.clone(), k.clone(), h]);
                    // b^k ≤ b^{|S|}
                    let body = Expr::apps(
                        antitone.clone(),
                        [
                            bv.clone(),
                            size_nat.clone(),
                            k.clone(),
                            hb0.clone(),
                            hb1.clone(),
                            h_le,
                        ],
                    );
                    hb.finish_child(hb.mk_lam(h_id, BinderInfo::Default, ante, body))
                };

                // Rat.threshold_term_le (b^k) (b^{|S|}) (w S) (bit) (h_w_s) (h_size_nn) (hthr)
                let term = Expr::apps(
                    threshold_term_le.clone(),
                    [
                        pow_b_k.clone(),
                        pow_b_size,
                        w_s,
                        bit,
                        h_w_s,
                        h_size_nn,
                        hthr,
                    ],
                );
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, term))
            };

            // h_pw : Σ_S (scaled S) ≤ Σ_S (weighted S)
            //   := subsetSum_le_of_pointwise n scaled weighted pointwise
            let h_pw = Expr::apps(
                subset_sum_le_pw.clone(),
                [n.clone(), scaled.clone(), weighted.clone(), pointwise],
            );

            // h_smul : Σ_S (b^k · mask S) = b^k · Σ_S (mask S)
            //   := subsetSum_smul n (b^k) mask
            //   (the `scaled` integrand IS `fun S => b^k · mask S`, def-eq).
            let h_smul = Expr::apps(
                subset_sum_smul.clone(),
                [n.clone(), pow_b_k.clone(), mask.clone()],
            );
            let scaled_sum = c.subset_sum_of(&n, scaled); // Σ_S (b^k · mask S)
            let pulled = c.mul(pow_b_k.clone(), c.subset_sum_of(&n, mask)); // b^k · Σ_S mask S

            // body : pulled ≤ rhs
            //   := subst (motive t => t ≤ rhs) (a := scaled_sum) (b := pulled) h_smul h_pw
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&bld);
                let (t_id, t) = m.fresh_local(c.rat_ty());
                let mbody = c.rat_le(t, rhs.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat_ty(), mbody))
            };
            let body = c.order.subst(motive, scaled_sum, pulled, h_smul, h_pw);

            let e = bld.mk_lam(hw_id, BinderInfo::Default, hw_ty, body);
            let e = bld.mk_lam(hb1_id, BinderInfo::Default, hb1_ty, e);
            let e = bld.mk_lam(hb0_id, BinderInfo::Default, hb0_ty, e);
            let e = bld.mk_lam(w_id, BinderInfo::Default, w_ty, e);
            let e = bld.mk_lam(b_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bld.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = bld.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            bld.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_lowband_extract()
            .expect("init_boolean_analysis_kkl_lowband_extract");
        env.init_boolean_analysis_kkl_lowband_extract()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_subset_sum_low_band_extract_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.subsetSum_low_band_extract");
    }

    /// REFUTE GATE. `refute_conjecture` must NOT refute the low-band extraction
    /// (it is a true, kernel-PROVEN inequality) when probed over the canonical
    /// Boolean-function battery (constants + dictators + parity — the functions
    /// that killed the false `deriv_level_mass_lower`). A refutation would mean
    /// the statement is FALSE and must not be built.
    #[test]
    fn test_subset_sum_low_band_extract_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.subsetSum_low_band_extract",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the low-band extraction is a true inequality; it must NOT refute on \
             the dictator/parity/constant battery"
        );
    }

    /// THE WIRING GATE. The audit found the low-band-extract / deriv-4norm /
    /// pownat-mono / level-split rungs orphaned (referenced only by their own
    /// `#[cfg(test)]` sites). The census-NEUTRAL ones are now wired into the
    /// always-on aggregate `init_boolean_analysis`, so they must be reachable from
    /// `init_boolean_analysis` alone (the entry point
    /// `init_fourier_boolean → soundness_certificate_env` uses) — without any
    /// KKL-specific registrar called by the test — and each must remain a
    /// kernel-checked, `Constructive`, empty-closure Theorem in that env.
    #[test]
    fn test_kkl_low_band_chain_wired_into_init_boolean_analysis() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        for name in [
            "BoolAnalysis.subsetSum_low_band_extract",      // RUNG A
            "Rat.powNat_le_powNat_right_antitone",          // antitone primitive
            "Rat.powNat_le_powNat_right",                   // monotone primitive
            "BoolAnalysis.noise_spectral_level",            // spectral ‖T_ρ a‖₂² interface
            "BoolAnalysis.derivative_4norm_eq_4_influence", // deriv-4norm chain
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} must be reachable through init_boolean_analysis (wiring)"
            );
            check_constructive(&env, name);
        }
    }

    /// `variance_low_band_influence` (the audit-named KKL-finish target) is a
    /// PROVEN, kernel-checked, `Constructive`, empty-closure Theorem and is
    /// reachable in any overlay env via its own registrar — but it is
    /// intentionally NOT auto-wired into the always-on `init_boolean_analysis`
    /// (its `kkl_threshold_mass_le` dependency transitively registers the abstract
    /// `Trans` instance axioms `instTransNatLt` / `instTransNatLtLtLe`, which would
    /// grow the live soundness-certificate census by 2). This test pins both
    /// facts: it is reachable + empty-closure through its own registrar.
    #[test]
    fn test_variance_low_band_influence_reachable_via_own_registrar() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_lowband()
            .expect("init_boolean_analysis_kkl_lowband");
        check_constructive(&env, "BoolAnalysis.variance_low_band_influence");
    }
}
