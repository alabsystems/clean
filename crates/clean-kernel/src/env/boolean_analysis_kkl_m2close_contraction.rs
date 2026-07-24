// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 M2-close component **H2**, the
//! spectral-side **2-norm CONTRACTION** of the noise operator.
//!
//! # What this discharges
//!
//! `BoolAnalysis.m2_from_contraction`
//! (`boolean_analysis_kkl_dualres_m2.rs`) reduces M2
//! (`f4 = Σ_x pow4(z x) ≤ 16·count³`, `z := T_{1/9}g`) to two genuine facts:
//! **H1** `f4 ≤ s2 := (Σz²)²` (the `‖·‖₄ ≤ ‖·‖₂` shadow) and **H2** `s2 ≤
//! 16·count²` (the squared 2-norm contraction). H2's analytic core is the
//! **2-norm contraction** `Σ_x sq(T_{1/9}g x) ≤ Σ_x sq(g x)` — the noise
//! operator never *increases* the 2-norm; it only damps. This module builds that
//! contraction at the SPECTRAL level, axiom-free, with NO hypercontractivity and
//! NO irrationals.
//!
//! # The spectral route (no hypercontractivity, no `8^n`)
//!
//! `BoolAnalysis.noise_spectral_level` (`boolean_analysis_kkl_levelsplit.rs`)
//! is the kernel-checked identity (un-normalized, `A a S := Σ_x a x·χ_S x`):
//!
//! ```text
//!   Σ_x Σ_y (a x·a y)·noiseDensityW (ρ·ρ) n x y
//!     = Σ_S levelWt ρ n S · (A a S · A a S)
//! ```
//!
//! The LHS is the un-normalized `‖T_ρ a‖₂²` (the noise-operator 2-norm); the RHS
//! is its spectral form with the per-level damping weight `levelWt ρ n S =
//! (ρ·ρ)^{|S|}` (`levelWt_eq_powNat`). Parseval is the SAME identity at `ρ = 1`
//! (`levelWt 1 n S ≡ 1^{|S|}`), giving the un-damped `‖a‖₂² = Σ_S A(S)²`. The
//! contraction is therefore the term-wise domination
//!
//! ```text
//!   Σ_S levelWt ρ n S · A(S)²  ≤  Σ_S A(S)²        [each levelWt ρ n S ≤ 1]
//! ```
//!
//! which is what this module proves over abstract `(ρ, n, a)` (given `0 ≤ ρ·ρ`
//! and `ρ·ρ ≤ 1`, both trivially true at `ρ = 1/9`: `0 ≤ 1/81 ≤ 1`). At
//! `ρ := 1/9`, `a := pm∘D_i f` it IS `Σ_x sq(T_{1/9}g) ≤ Σ_x sq(g) = 4·count`
//! (`deriv_sq_sum_eq_four_disagree`); squaring closes H2 of `m2_from_contraction`.
//!
//! # What this module proves (axiom-free, kernel-checked)
//!
//! ```text
//! BoolAnalysis.spectral_level_two_norm_contraction :
//!   ∀ (ρ : Rat) (n : Nat) (a : HCPoint n → Rat),
//!     Rat.le Rat.zero (Rat.mul ρ ρ) →          -- 0 ≤ ρ²
//!     Rat.le (Rat.mul ρ ρ) Rat.one →           -- ρ² ≤ 1
//!     Rat.le
//!       (subsetSum n (fun S => Rat.mul (levelWt ρ n S) (Rat.mul (A a S) (A a S))))
//!       (subsetSum n (fun S =>                  (Rat.mul (A a S) (A a S))))
//! ```
//!
//! where `A a S := subsetSum n (fun x => Rat.mul (a x) (chi n S x))`. The LHS
//! integrand is byte-for-byte `noise_spectral_level`'s RHS integrand
//! (`rhs_lvl_fn`), so this lemma composes directly with that identity to bound
//! the spatial double-sum 2-norm `Σ_x Σ_y …` by the unweighted Parseval mass.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! `subsetSum_le_of_pointwise n G_lvl G_one pointwise`, where the per-`S`
//! pointwise bound `levelWt ρ n S · (A·A) ≤ A·A` is:
//!
//! 1. `h_lvl_le_1 : levelWt ρ n S ≤ 1`:
//!    - `ep : levelWt ρ n S = (ρ·ρ)^{setSizeNat n S}`  (`levelWt_eq_powNat`)
//!    - `anti : (ρ·ρ)^{setSizeNat n S} ≤ (ρ·ρ)^0`
//!      (`Rat.powNat_le_powNat_right_antitone (ρ·ρ) 0 (setSizeNat n S) h0 h1
//!         (Nat.zero_le (setSizeNat n S))`)
//!    - `pz : (ρ·ρ)^0 = 1`  (`Rat.powNat_zero`); subst the RHS of `anti` →
//!      `(ρ·ρ)^{setSizeNat n S} ≤ 1`; subst the LHS along `Eq.symm ep` →
//!      `levelWt ρ n S ≤ 1`.
//! 2. `h_AA_nonneg : 0 ≤ A·A`  (`Rat.sq_nonneg (A a S)`).
//! 3. `mlr : levelWt ρ n S · (A·A) ≤ 1·(A·A)`
//!    (`Rat.mul_le_mul_of_nonneg_right (A·A) (levelWt) 1 h_lvl_le_1 h_AA_nonneg`);
//!    subst the RHS `1·(A·A) → A·A` along `Rat.one_mul (A·A)` →
//!    `levelWt ρ n S · (A·A) ≤ A·A`.
//!
//! Every leaf (`subsetSum_le_of_pointwise`, `levelWt_eq_powNat`,
//! `Rat.powNat_le_powNat_right_antitone`, `Rat.powNat_zero`, `Nat.zero_le`,
//! `Rat.sq_nonneg`, `Rat.mul_le_mul_of_nonneg_right`, `Rat.one_mul`, `Eq.subst`,
//! `Eq.symm`) is `Constructive` with empty admitted-axiom closure, so this
//! contraction is too. No axiom is added or removed. Idempotent.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the spectral-level 2-norm contraction.
struct ContractionConsts {
    o: OrderConsts,
    nat: Expr,
    nat_zero: Expr,
    chi: Expr,
    hcpoint: Expr,
    subset_sum: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    pow_nat: Expr,
}

impl ContractionConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            chi: k("BoolAnalysis.chi"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            pow_nat: k("Rat.powNat"),
        }
    }

    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn one(&self) -> Expr {
        self.o.rat_one.clone()
    }
    fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    fn rho_sq(&self, rho: &Expr) -> Expr {
        self.mul(rho.clone(), rho.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn level_wt(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn set_size_nat(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn pow(&self, base: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [base.clone(), k.clone()])
    }

    /// `A a S = subsetSum n (fun x => a x · χ_S x)` — the un-normalized Fourier
    /// coefficient, byte-for-byte `LevelSplitConsts::a_coeff` (the
    /// `noise_spectral_level` inner sum).
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), self.chi_(n, s, &x));
        let g = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    /// RHS `S`-integrand with the `levelWt` weight:
    /// `fun S => levelWt ρ n S · (A a S · A a S)`. Byte-for-byte
    /// `LevelSplitConsts::rhs_lvl_fn` (so this composes with `noise_spectral_level`).
    fn lvl_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let w = self.level_wt(rho, n, &s);
        let inner = self.a_coeff(&b, n, a, &s);
        let body = self.mul(w, self.mul(inner.clone(), inner));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Unweighted `S`-integrand `fun S => A a S · A a S` (the Parseval mass,
    /// `= levelWt 1 n S · (A·A)`).
    fn sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let inner = self.a_coeff(&b, n, a, &s);
        let body = self.mul(inner.clone(), inner);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `levelWt_eq_powNat ρ n S : levelWt ρ n S = powNat (ρ·ρ) (setSizeNat n S)`.
    fn levelwt_eq_pownat(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.levelWt_eq_powNat"), vec![]),
            [rho.clone(), n.clone(), s.clone()],
        )
    }

    /// `Rat.powNat_le_powNat_right_antitone b m n h0 h1 hmn : b^n ≤ b^m`
    /// (`0 ≤ b`, `b ≤ 1`, `m ≤ n`).
    fn pow_antitone(&self, b: &Expr, m: &Expr, n: &Expr, h0: Expr, h1: Expr, hmn: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Rat.powNat_le_powNat_right_antitone"),
                vec![],
            ),
            [b.clone(), m.clone(), n.clone(), h0, h1, hmn],
        )
    }

    /// `Rat.powNat_zero b : b^0 = 1`.
    fn pow_zero(&self, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_zero"), vec![]),
            [b.clone()],
        )
    }

    /// `Nat.zero_le k : Nat.le Nat.zero k`.
    fn nat_zero_le(&self, k: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            [k.clone()],
        )
    }

    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            [a.clone()],
        )
    }

    /// `Rat.mul_le_mul_of_nonneg_right a b c (h:b≤c)(h0:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            [a, b, cc, h, h0],
        )
    }

    /// `Rat.one_mul a : Rat.one · a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), [a])
    }

    /// `Eq.symm.{1} @Rat l r h : Eq r l`.
    fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        self.o.symm(l, r, h)
    }

    /// `Eq.subst.{1} @Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        self.o.subst(motive, a, b, h_eq, h)
    }

    /// `BoolAnalysis.subsetSum_le_of_pointwise n g h hyp : subsetSum n g ≤ subsetSum n h`.
    fn ssum_le_of_pointwise(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
                vec![],
            ),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.spectral_level_two_norm_contraction` — the
    /// spectral-side 2-norm contraction `Σ_S levelWt ρ n S·A(S)² ≤ Σ_S A(S)²`
    /// (under `0 ≤ ρ²` and `ρ² ≤ 1`), the analytic core of H2 of
    /// `m2_from_contraction`. The noise operator damps (never amplifies) the
    /// 2-norm: each per-level weight `levelWt ρ n S = (ρ²)^{|S|} ≤ 1`. NO
    /// hypercontractivity, NO irrationals. Kernel-checked,
    /// `ProofQuality::Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_spectral_level_two_norm_contraction(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.spectral_level_two_norm_contraction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_le()?; // Nat.le, Nat.zero_le surface
        self.init_boolean_analysis()?; // HCPoint, chi, subsetSum, powNat
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_le_of_pointwise()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_levelwt_eq_pow_nat()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_le_pow_nat_right_antitone()?;
        self.register_nat_le_total_proof()?; // Nat.zero_le
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg, mul_le_mul_of_nonneg_right
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.one_mul
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ContractionConsts::new();
        let (ty, value) = build_contraction(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `spectral_level_two_norm_contraction`.
fn build_contraction(c: &ContractionConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let a_ty = c.hcpoint_to_rat(&n);
        let (a_id, a) = b.fresh_local(a_ty.clone());

        let rho_sq = c.rho_sq(&rho);
        let h0_ty = c.le(c.zero(), rho_sq.clone()); // 0 ≤ ρ²
        let h1_ty = c.le(rho_sq, c.one()); // ρ² ≤ 1

        let lhs = c.ssum(&n, c.lvl_fn(&b, &rho, &n, &a));
        let rhs = c.ssum(&n, c.sq_fn(&b, &n, &a));
        let concl = c.le(lhs, rhs);

        let (h1_id, _) = b.fresh_local(h1_ty.clone());
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
        let (h0_id, _) = b.fresh_local(h0_ty.clone());
        let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let a_ty = c.hcpoint_to_rat(&n);
        let (a_id, a) = b.fresh_local(a_ty.clone());

        let rho_sq = c.rho_sq(&rho);
        let h0_ty = c.le(c.zero(), rho_sq.clone());
        let h1_ty = c.le(rho_sq.clone(), c.one());
        let (h0_id, h0) = b.fresh_local(h0_ty.clone());
        let (h1_id, h1) = b.fresh_local(h1_ty.clone());

        let g_lvl = c.lvl_fn(&b, &rho, &n, &a);
        let g_one = c.sq_fn(&b, &n, &a);

        // pointwise : ∀ S, levelWt ρ n S·(A·A) ≤ (A·A)
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = d.fresh_local(hcp.clone());

            let lvl = c.level_wt(&rho, &n, &s);
            let aa = {
                let inner = c.a_coeff(&d, &n, &a, &s);
                (inner.clone(), c.mul(inner.clone(), inner))
            };
            let (a_s, aa) = aa; // a_s := A a S ; aa := A·A
            let ssz = c.set_size_nat(&n, &s);
            let pow_ssz = c.pow(&rho_sq, &ssz); // (ρ²)^{|S|}
            let pow_zero = c.pow(&rho_sq, &c.nat_zero.clone()); // (ρ²)^0

            // h_lvl_le_1 : levelWt ρ n S ≤ 1
            let h_lvl_le_1 = {
                // anti : (ρ²)^{|S|} ≤ (ρ²)^0
                let anti = c.pow_antitone(
                    &rho_sq,
                    &c.nat_zero.clone(),
                    &ssz,
                    h0.clone(),
                    h1.clone(),
                    c.nat_zero_le(&ssz),
                );
                // subst RHS (ρ²)^0 → 1 via Rat.powNat_zero (ρ²), motive z ↦ (ρ²)^{|S|} ≤ z
                let pz = c.pow_zero(&rho_sq); // (ρ²)^0 = 1
                let pow_ssz_le_1 = {
                    let motive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (z_id, z) = e.fresh_local(c.rat());
                        let body = c.le(pow_ssz.clone(), z);
                        e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
                    };
                    c.subst(motive, pow_zero.clone(), c.one(), pz, anti)
                };
                // subst LHS levelWt → via Eq.symm (levelWt_eq_powNat), motive z ↦ z ≤ 1
                let ep = c.levelwt_eq_pownat(&rho, &n, &s); // levelWt = (ρ²)^{|S|}
                let ep_sym = c.symm(lvl.clone(), pow_ssz.clone(), ep); // (ρ²)^{|S|} = levelWt
                let motive = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (z_id, z) = e.fresh_local(c.rat());
                    let body = c.le(z, c.one());
                    e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
                };
                c.subst(motive, pow_ssz.clone(), lvl.clone(), ep_sym, pow_ssz_le_1)
            };

            // h_aa_nonneg : 0 ≤ A·A
            let h_aa_nonneg = c.sq_nonneg(&a_s);

            // mlr : levelWt·(A·A) ≤ 1·(A·A)
            //   Rat.mul_le_mul_of_nonneg_right (A·A) (levelWt) 1 h_lvl_le_1 h_aa_nonneg
            let one_aa = c.mul(c.one(), aa.clone()); // 1·(A·A)
            let mlr = c.mul_le_right(aa.clone(), lvl.clone(), c.one(), h_lvl_le_1, h_aa_nonneg);
            // subst RHS 1·(A·A) → A·A via Rat.one_mul (A·A), motive z ↦ levelWt·(A·A) ≤ z
            let lvl_aa = c.mul(lvl.clone(), aa.clone()); // levelWt·(A·A)
            let one_mul_eq = c.one_mul(aa.clone()); // 1·(A·A) = A·A
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = e.fresh_local(c.rat());
                let body = c.le(lvl_aa.clone(), z);
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
            };
            let body = c.subst(motive, one_aa, aa.clone(), one_mul_eq, mlr);
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        let proof = c.ssum_le_of_pointwise(&n, &g_lvl, &g_one, pointwise);

        let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, proof);
        let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_lam(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_spectral_level_two_norm_contraction()
            .expect("register_spectral_level_two_norm_contraction");
        env
    }

    #[test]
    fn test_contraction_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.spectral_level_two_norm_contraction");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_spectral_level_two_norm_contraction()
            .expect("first");
        env.register_spectral_level_two_norm_contraction()
            .expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE. The spectral 2-norm contraction is a TRUE
    /// implication: from `0 ≤ ρ²` and `ρ² ≤ 1`, EVERY per-level weight
    /// `levelWt ρ n S = (ρ²)^{|S|} ≤ 1`, so `Σ_S levelWt·A² ≤ Σ_S A²` for ALL
    /// `(ρ, n, a)` — no carrier instance can break it; `refute_conjecture` must
    /// NOT manufacture a counterexample.
    ///
    /// By hand: at `ρ² = 1` every weight is `1` (equality edge, NOT a
    /// refutation); for `ρ² < 1` weights shrink — the LHS strictly contracts.
    /// The implication never fails.
    #[test]
    fn test_contraction_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.spectral_level_two_norm_contraction",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the spectral 2-norm contraction is a TRUE implication; must NOT refute"
        );
    }
}
