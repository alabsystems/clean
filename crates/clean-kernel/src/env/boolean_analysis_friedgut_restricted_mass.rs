// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP 4 ASSEMBLE: `friedgut_restricted_mass_le`
//! — the faithful O'Donnell §9.6 L2 charging bound
//! `Σ_{S⊄J, |S|≤d} f̂(S)² ≤ 9^d·(dr·I[f])`.
//!
//! Chains the four banked masked bricks (no new proof content — pure transport +
//! constant cancellation):
//!
//! ```text
//! BoolAnalysis.friedgut_restricted_mass_le :
//!   ∀ (n d : Nat) (f : BoolFn n) (J : HCPoint n) (dr : Rat),
//!     0 ≤ dr → 0 ≤ dr·dr → dr·dr < 1 →
//!     (∀ i, 0 ≤ Influence n f i) →
//!     (∀ i, Bool.not (J i) = Bool.true → Influence n f i ≤ dr·dr) →
//!       Rat.le
//!         (subsetSum n (fun S =>
//!            ind (notSubsetMask n S J)
//!              · (ind (Nat.ble (setSizeNat n S) d)
//!                  · (FourierCoefficient n f S · FourierCoefficient n f S))))   -- Σ_{S⊄J,|S|≤d} f̂²
//!         (Rat.mul (Rat.powNat (Rat.ofNat 9) d) (Rat.mul dr (TotalInfluence n f)))  -- 9^d·(dr·I[f])
//! ```
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Write `M := Σ_{S⊄J,|S|≤d} f̂²` (the conclusion's LHS), `b := pm∘f`,
//! `Q9 := 9^d`, `P4 := 4^n`, `I := TotalInfluence n f`.
//!
//! 1. **STEP 3 charge** at `b := pm∘f` (`friedgut_masked_deg_band_charge n d (pm∘f) J`):
//!    `LHS_charge := Σ_{S⊄J,|S|≤d} 4·A_{pm∘f}² ≤ Σ_{i∉J} W^{≤d}[D_i(pm∘f)] =: RHS_charge`.
//! 2. **STEP 4a** (`kkl_summed_deriv_le_wnorm_sum_masked n d f J`):
//!    `RHS_charge ≤ Q9·(P4·Σ_{i∉J} W_norm_i)`.
//! 3. **STEP 2 masked** (`kkl_wnorm_sum_le_rat_masked n f m dr … `, `m := ¬J`):
//!    `Σ_{i∉J} W_norm_i ≤ 4·(dr·I)`. Scaled on the left by the nonneg `P4`
//!    (`mul_le_mul_of_nonneg_left`) then by `Q9`: `Q9·(P4·Σ_{i∉J} W_norm_i) ≤ Q9·(P4·(4·(dr·I)))`.
//! 4. **STEP 4b** (`deg_band_rhs_eq_pow4_mass_masked n d f J`):
//!    `LHS_charge = (4·P4)·M`. Subst rewrites the chain's far-left to `(4·P4)·M`.
//! 5. **constant reshape** (pure `Rat` assoc/comm): `Q9·(P4·(4·(dr·I))) = (4·P4)·(Q9·(dr·I))`.
//!    Subst rewrites the chain's far-right.
//! 6. **cancel** `Rat.le_of_mul_le_mul_left_pos M (Q9·(dr·I)) (4·P4) (0<4·P4)`:
//!    from `(4·P4)·M ≤ (4·P4)·(Q9·(dr·I))`, with `0 < 4·P4`
//!    (`mul_pos 4 P4 (0<4) (powNat_pos 4 n (0<4))`), conclude `M ≤ Q9·(dr·I)`.
//!
//! All four bricks + the order/positivity leaves (`Rat.mul_le_mul_of_nonneg_left`,
//! `Rat.le_of_mul_le_mul_left_pos`, `Rat.mul_pos`, `Rat.powNat_pos`,
//! `Rat.mul_assoc`/`mul_comm`, `Eq.*`, `congrArg`) are landed `Constructive`
//! empty-closure Theorems, so this assembly is too. NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Real`. No axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the STEP 4 assembly. Carrier spellings byte-match the four
/// consumed masked bricks (STEP 3 / 4a / 4b / STEP 2 masked) + the positivity /
/// cancel leaves.
struct RestrictedMassConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
    rat_mul: Expr,
    rat_zero: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_: Expr,
    bool_not: Expr,
    bool_true: Expr,
    bool_fn: Expr,
    pm: Expr,
    chi: Expr,
    fourier: Expr,
    subset_sum: Expr,
    fin: Expr,
    fin_sum: Expr,
    ind: Expr,
    set_size_nat: Expr,
    not_subset_mask: Expr,
    nat_ble: Expr,
    influence: Expr,
    total_influence: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    rat_lt: Expr,
    mul_le_left: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    #[cfg(test)]
    l0: Level,
    l1: Level,
}

impl RestrictedMassConsts {
    fn new() -> Self {
        #[cfg(test)]
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_of_nat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_zero: k("Rat.zero"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_: k("Bool"),
            bool_not: k("Bool.not"),
            bool_true: k("Bool.true"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            pm: k("BoolAnalysis.pm"),
            chi: k("BoolAnalysis.chi"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            nat_ble: k("Nat.ble"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            rat_lt: k("Rat.lt"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            #[cfg(test)]
            l0,
            l1,
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `(4 : Rat) := mk(ofNat 4) 1`.
    fn four(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(4)),
                self.nat_one(),
            ],
        )
    }
    /// `Rat.ofNat 4` — the masked aggregate's RHS constant base.
    fn ofnat4(&self) -> Expr {
        Expr::app(self.rat_of_nat.clone(), self.nat_lit(4))
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `4^n := powNat 4 n` (byte-match STEP 4b's `pow4`).
    fn pow4(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.four(), n.clone()])
    }
    /// `9^d := powNat (Rat.ofNat 9) d` (byte-match STEP 4a's `pow9`).
    fn pow9(&self, d: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                d.clone(),
            ],
        )
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn low_bit(&self, n: &Expr, d: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.nat_ble.clone(),
            [self.set_size_nat_of(n, s), d.clone()],
        )
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }

    // ── order / eq plumbing ───────────────────────────────────────────────────
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn trans_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        // `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_eq(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }

    /// `0 < 4` := `@Int.NonNeg.mk 3` at the `Rat.lt 0 (mk(ofNat 4)1)` type
    /// (byte-match KKL `four_pos`).
    fn four_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(3),
        )
    }
    /// `0 ≤ (mk(ofNat v)1)` := `Rat.le_of_ble_eq_true 0 v (refl true)` — the
    /// closed nonneg witness for a positive numeral base.
    fn nonneg_lit(&self, lit: Expr) -> Expr {
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl_btrue = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.bool_.clone(), btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [self.rat_zero.clone(), lit, refl_btrue],
        )
    }

    /// `pm∘f := fun (x : HCPoint n) => pm (f x)`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Z S := A_S(pm∘f) := subsetSum n (fun x => pm(f x)·χ_S x)`.
    fn z_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let body = self.mul(pm_fx, self.chi_(n, s, &x));
        let g = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
}

/// The OUTSIDE-`J` mask `m := fun i => Bool.not (J i)`.
fn mask_fn(c: &RestrictedMassConsts, parent: &EnvDeclBuilder, n: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.bnot(Expr::app(j.clone(), i.clone()));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// Conclusion LHS integrand `fun S => ind(notSubsetMask)·(ind(ble |S| d)·(f̂·f̂))`
/// — BYTE-IDENTICAL to STEP 4b's `mass_x_fn` (the masked low-band f̂² mass).
fn mass_x_fn(
    c: &RestrictedMassConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    d: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let xx = c.x_sq(n, f, &s);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, d, &s));
    let body = c.mul(r, c.mul(p, xx));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// STEP 3 charge LHS integrand `fun S => ind(notSubsetMask)·(ind(ble |S| d)·(4·(Z·Z)))`
/// (≡ STEP 3 `mass_fn` at `b := pm∘f` ≡ STEP 4b `mass_in_fn`).
fn mass_in_fn(
    c: &RestrictedMassConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    d: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let z = c.z_coeff(&b, n, f, &s);
    let zz = c.mul(z.clone(), z);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, d, &s));
    let body = c.mul(r, c.mul(p, c.mul(c.four(), zz)));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `lhs_i := fun i => ind(¬J i)·W^{≤d}[D_i(pm∘f)]` — STEP 3's `lhs_i_fn` at
/// `b := pm∘f` ≡ STEP 4a's `masked_l_fn`. Built via the STEP-3 deg-band-masked
/// builder so the byte-spelling matches the charge's RHS exactly.
fn masked_l_fn(
    c: &RestrictedMassConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    d: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    // We do not re-spell W^{≤d}; instead, the chain ties the charge's RHS and 4a's
    // LHS by their shared `Fin.sum n (lhs_i_fn …)` head, which the kernel matches
    // definitionally. This helper is only needed to anchor the masked-noise LHS
    // term in the trans chain; we re-derive it from the deriv/lowband carriers.
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    // D_i (pm∘f) := fun x => pm(f x) − pm(f(hcFlip n x i)).
    let g = {
        let mut dd = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(n);
        let (x_id, x) = dd.fresh_local(hcp.clone());
        let fx = Expr::app(c.pm.clone(), Expr::app(f.clone(), x.clone()));
        let flip = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]),
            [n.clone(), x.clone(), i.clone()],
        );
        let fflip = Expr::app(c.pm.clone(), Expr::app(f.clone(), flip));
        let body = Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [fx, fflip],
        );
        dd.finish_child(dd.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    // W^{≤d}[g] := subsetSum n (fun S => ind(ble |S| d)·(A_g·A_g)).
    let lowband = {
        let mut dd = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(n);
        let (s_id, s) = dd.fresh_local(hcp.clone());
        let a = {
            let mut e = EnvDeclBuilder::child_of(&dd);
            let (x_id, x) = e.fresh_local(hcp.clone());
            let body = c.mul(Expr::app(g.clone(), x.clone()), c.chi_(n, &s, &x));
            let lam = e.finish_child(e.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            c.ssum(n, lam)
        };
        let bit = c.ind_of(c.low_bit(n, d, &s));
        let body = c.mul(bit, c.mul(a.clone(), a));
        let lam = dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, hcp, body));
        c.ssum(n, lam)
    };
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, lowband);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `masked_wn := fun i => ind(¬J i)·W_norm[D_i(pm∘f)]` — STEP 4a's `masked_wn_fn`
/// ≡ the masked aggregate's summand `fun i => ind(m i)·W_norm_i` at `m := ¬J`.
fn masked_wn_fn(
    c: &RestrictedMassConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let g = {
        let mut dd = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(n);
        let (x_id, x) = dd.fresh_local(hcp.clone());
        let fx = Expr::app(c.pm.clone(), Expr::app(f.clone(), x.clone()));
        let flip = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]),
            [n.clone(), x.clone(), i.clone()],
        );
        let fflip = Expr::app(c.pm.clone(), Expr::app(f.clone(), flip));
        let body = Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [fx, fflip],
        );
        dd.finish_child(dd.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    let w_norm = {
        let third = Expr::apps(
            c.rat_mk.clone(),
            [Expr::app(c.int_of_nat.clone(), c.nat_one()), c.nat_lit(3)],
        );
        let tg = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]),
            [third, n.clone(), g.clone()],
        );
        let mut dd = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(n);
        let (y_id, y) = dd.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        let lam = dd.finish_child(dd.mk_lam(y_id, BinderInfo::Default, hcp, body));
        let w = c.ssum(n, lam);
        // inv(8^n) with 8 := mk(ofNat 8) 1.
        let eight = Expr::apps(
            c.rat_mk.clone(),
            [Expr::app(c.int_of_nat.clone(), c.nat_lit(8)), c.nat_one()],
        );
        let pow8 = Expr::apps(c.pow_nat.clone(), [eight, n.clone()]);
        let inv8 = Expr::app(Expr::const_(Name::from_string("Rat.inv"), vec![]), pow8);
        c.mul(w, inv8)
    };
    let mask = c.ind_of(c.bnot(Expr::app(j.clone(), i.clone())));
    let body = c.mul(mask, w_norm);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

fn restricted_mass_type(c: &RestrictedMassConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());
    let (dr_id, dr) = b.fresh_local(c.rat.clone());

    let dd = c.mul(dr.clone(), dr.clone());
    let hd_ty = c.le(c.rat_zero.clone(), dr.clone());
    let (hd_id, _) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone());
    let (hdd0_id, _) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.lt(dd.clone(), {
        // `1 : Rat` := mk(ofNat 1) 1.
        Expr::apps(
            c.rat_mk.clone(),
            [Expr::app(c.int_of_nat.clone(), c.nat_one()), c.nat_one()],
        )
    });
    let (hdd1_id, _) = b.fresh_local(hdd1_ty.clone());

    // h0 : ∀ i, 0 ≤ Inf_i.
    let h0_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let body = c.le(c.rat_zero.clone(), c.influence_of(&n, &f, &i));
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h0_id, _) = b.fresh_local(h0_ty.clone());

    // h1m : ∀ i, Bool.not (J i) = true → Inf_i ≤ dr·dr.
    let h1m_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let prem = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![c.l1.clone()]),
            [
                c.bool_.clone(),
                c.bnot(Expr::app(j.clone(), i.clone())),
                c.bool_true.clone(),
            ],
        );
        let concl = c.le(c.influence_of(&n, &f, &i), dd.clone());
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h1m_id, _) = b.fresh_local(h1m_ty.clone());

    let lhs = c.ssum(&n, mass_x_fn(c, &b, &n, &d, &f, &j));
    let rhs = c.mul(c.pow9(&d), c.mul(dr.clone(), c.total_influence_of(&n, &f)));
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(h1m_id, BinderInfo::Default, h1m_ty, concl);
    let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_pi(hdd1_id, BinderInfo::Default, hdd1_ty, e);
    let e = b.mk_pi(hdd0_id, BinderInfo::Default, hdd0_ty, e);
    let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
    let e = b.mk_pi(dr_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn restricted_mass_value(c: &RestrictedMassConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());
    let (dr_id, dr) = b.fresh_local(c.rat.clone());

    let dd = c.mul(dr.clone(), dr.clone());
    let one_rat = Expr::apps(
        c.rat_mk.clone(),
        [Expr::app(c.int_of_nat.clone(), c.nat_one()), c.nat_one()],
    );
    let hd_ty = c.le(c.rat_zero.clone(), dr.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.lt(dd.clone(), one_rat.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let h0_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let body = c.le(c.rat_zero.clone(), c.influence_of(&n, &f, &i));
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1m_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let prem = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![c.l1.clone()]),
            [
                c.bool_.clone(),
                c.bnot(Expr::app(j.clone(), i.clone())),
                c.bool_true.clone(),
            ],
        );
        let concl = c.le(c.influence_of(&n, &f, &i), dd.clone());
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h1m_id, h1m) = b.fresh_local(h1m_ty.clone());

    let pmf = c.pm_f(&b, &n, &f);
    let m = mask_fn(c, &b, &n, &j);

    // ── key terms ──
    let q9 = c.pow9(&d);
    let p4 = c.pow4(&n);
    let four = c.four();
    let four_p4 = c.mul(four.clone(), p4.clone()); // 4·4^n
    let infl = c.total_influence_of(&n, &f);
    let dr_i = c.mul(dr.clone(), infl.clone()); // dr·I
    let ofnat4 = c.ofnat4();
    let four_dr_i = c.mul(ofnat4.clone(), dr_i.clone()); // (ofNat 4)·(dr·I) — masked-agg RHS

    let mass_x = mass_x_fn(c, &b, &n, &d, &f, &j); // f̂² masked mass integrand
    let m_mass = c.ssum(&n, mass_x.clone()); // M = conclusion LHS
    let mass_in = mass_in_fn(c, &b, &n, &d, &f, &j); // 4·A² masked mass integrand
    let lhs_charge = c.ssum(&n, mass_in.clone()); // Σ 4·A²
    let masked_l = masked_l_fn(c, &b, &n, &d, &f, &j);
    let rhs_charge = c.fsum(&n, masked_l.clone()); // Σ_{i∉J} W^{≤d}
    let masked_wn = masked_wn_fn(c, &b, &n, &f, &j);
    let masked_wn_sum = c.fsum(&n, masked_wn.clone()); // Σ_{i∉J} W_norm

    let p4_wn = c.mul(p4.clone(), masked_wn_sum.clone()); // 4^n·Σ_{i∉J} W_norm
    let q9_p4_wn = c.mul(q9.clone(), p4_wn.clone()); // 9^d·(4^n·Σ W_norm) = 4a RHS
    let p4_fdi = c.mul(p4.clone(), four_dr_i.clone()); // 4^n·((ofNat4)·(dr·I))
    let q9_p4_fdi = c.mul(q9.clone(), p4_fdi.clone()); // 9^d·(4^n·((ofNat4)·(dr·I)))
    let fp4_m = c.mul(four_p4.clone(), m_mass.clone()); // (4·4^n)·M
    let fp4_q9di = c.mul(four_p4.clone(), c.mul(q9.clone(), dr_i.clone())); // (4·4^n)·(9^d·(dr·I))

    // (1) STEP 3 charge at b := pm∘f.
    let charge = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_masked_deg_band_charge"),
            vec![],
        ),
        [n.clone(), d.clone(), pmf.clone(), j.clone()],
    ); // : lhs_charge ≤ rhs_charge

    // (2) STEP 4a.
    let noise = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.kkl_summed_deriv_le_wnorm_sum_masked"),
            vec![],
        ),
        [n.clone(), d.clone(), f.clone(), j.clone()],
    ); // : rhs_charge ≤ q9_p4_wn

    // (3) STEP 2 masked aggregate.
    let agg = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.kkl_wnorm_sum_le_rat_masked"),
            vec![],
        ),
        [
            n.clone(),
            f.clone(),
            m.clone(),
            dr.clone(),
            hd.clone(),
            hdd0.clone(),
            hdd1.clone(),
            h0.clone(),
            h1m.clone(),
        ],
    ); // : masked_wn_sum ≤ four_dr_i   (= (ofNat4)·(dr·I))

    //   scale by P4 on the left: mul_le_mul_of_nonneg_left (four_dr_i) (masked_wn_sum) P4 agg (0≤P4).
    //   `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    let p4_nonneg = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
        [four.clone(), n.clone(), c.nonneg_lit(four.clone())],
    ); // 0 ≤ 4^n
    let agg_p4 = Expr::apps(
        c.mul_le_left.clone(),
        [
            p4.clone(),
            masked_wn_sum.clone(),
            four_dr_i.clone(),
            agg,
            p4_nonneg.clone(),
        ],
    ); // : P4·masked_wn_sum ≤ P4·four_dr_i
       //   scale by Q9: mul_le_mul_of_nonneg_left (p4_fdi) (p4_wn) Q9 agg_p4 (0≤Q9).
    let ofnat9 = Expr::app(c.rat_of_nat.clone(), c.nat_lit(9));
    let q9_nonneg = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
        [ofnat9.clone(), d.clone(), c.nonneg_lit(ofnat9.clone())],
    ); // 0 ≤ 9^d
    let agg_q9p4 = Expr::apps(
        c.mul_le_left.clone(),
        [q9.clone(), p4_wn.clone(), p4_fdi.clone(), agg_p4, q9_nonneg],
    ); // : q9_p4_wn ≤ q9_p4_fdi

    // chain inequalities: lhs_charge ≤ rhs_charge ≤ q9_p4_wn ≤ q9_p4_fdi.
    let c12 = c.trans_le(
        lhs_charge.clone(),
        rhs_charge.clone(),
        q9_p4_wn.clone(),
        charge,
        noise,
    );
    let chain = c.trans_le(
        lhs_charge.clone(),
        q9_p4_wn.clone(),
        q9_p4_fdi.clone(),
        c12,
        agg_q9p4,
    );
    // chain : lhs_charge ≤ q9_p4_fdi.

    // (4) STEP 4b : lhs_charge = (4·4^n)·M.  Rewrite chain's LHS to (4·4^n)·M.
    let recon = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass_masked"),
            vec![],
        ),
        [n.clone(), d.clone(), f.clone(), j.clone()],
    ); // : lhs_charge = (4·4^n)·M
       //   subst (motive t => t ≤ q9_p4_fdi) along recon : lhs_charge → (4·4^n)·M.
    let motive_l = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.le(t, q9_p4_fdi.clone());
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let chain_l = c.subst(motive_l, lhs_charge.clone(), fp4_m.clone(), recon, chain);
    // chain_l : (4·4^n)·M ≤ q9_p4_fdi.

    // (5) constant reshape : q9_p4_fdi = (4·4^n)·(9^d·(dr·I)).
    //   q9_p4_fdi = Q9·(P4·((ofNat4)·(dr·I)))
    //   STEP a: (ofNat4)·(dr·I) = 4·(dr·I)   [ofNat4 = mk(ofNat4)1 = 4 def-eq; congr_r (dr·I) refl?]
    //   Actually `Rat.ofNat 4` and `mk(ofNat 4)1` are DEF-EQ (ofNat n ≡ mk(ofNat n)1),
    //   so four_dr_i ≡ 4·(dr·I) and p4_fdi ≡ P4·(4·(dr·I)) definitionally — no rewrite
    //   needed; we reshape the def-eq form Q9·(P4·(4·(dr·I))) → (4·P4)·(Q9·(dr·I)).
    let four_dr_i_def = c.mul(four.clone(), dr_i.clone()); // 4·(dr·I)  (def-eq to four_dr_i)
    let p4_4di = c.mul(p4.clone(), four_dr_i_def.clone()); // P4·(4·(dr·I))
    let q9_p4_4di = c.mul(q9.clone(), p4_4di.clone()); // Q9·(P4·(4·(dr·I)))
    let reshape = const_reshape(c, &b, &q9, &p4, &four, &dr_i);
    // reshape : Q9·(P4·(4·(dr·I))) = (4·P4)·(Q9·(dr·I)).
    //   subst (motive t => (4·4^n)·M ≤ t) along reshape : Q9·(P4·(4·(dr·I))) → (4·P4)·(Q9·(dr·I)).
    let motive_r = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.le(fp4_m.clone(), t);
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // chain_l has RHS q9_p4_fdi which is def-eq to q9_p4_4di; subst needs the `a` to be q9_p4_4di.
    let chain_r = c.subst(
        motive_r,
        q9_p4_4di.clone(),
        fp4_q9di.clone(),
        reshape,
        chain_l,
    );
    // chain_r : (4·4^n)·M ≤ (4·4^n)·(9^d·(dr·I)).

    // (6) cancel : le_of_mul_le_mul_left_pos M (Q9·(dr·I)) (4·4^n) (0 < 4·4^n) chain_r.
    let four_p4_pos = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
        [
            four.clone(),
            p4.clone(),
            c.four_pos(),
            Expr::apps(
                Expr::const_(Name::from_string("Rat.powNat_pos"), vec![]),
                [four.clone(), n.clone(), c.four_pos()],
            ),
        ],
    ); // 0 < 4·4^n
    let q9_dri = c.mul(q9.clone(), dr_i.clone());
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
        [
            m_mass.clone(),
            q9_dri.clone(),
            four_p4.clone(),
            four_p4_pos,
            chain_r,
        ],
    );
    // proof : M ≤ Q9·(dr·I) = conclusion.

    let e = b.mk_lam(h1m_id, BinderInfo::Default, h1m_ty, proof);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(hdd1_id, BinderInfo::Default, hdd1_ty, e);
    let e = b.mk_lam(hdd0_id, BinderInfo::Default, hdd0_ty, e);
    let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
    let e = b.mk_lam(dr_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// Pure-`Rat` rearrangement
/// `const_reshape Q9 P4 4 X : Q9·(P4·(4·X)) = (4·P4)·(Q9·X)`,
/// built only from `mul_assoc`/`mul_comm`. (Here `X := dr·I`.) Chain:
/// ```text
///   Q9·(P4·(4·X))
///     = Q9·((P4·4)·X)      congr_l Q9 (symm (mul_assoc P4 4 X))
///     = Q9·(((4·P4))·X)    congr_l Q9 (congr_r X (mul_comm P4 4))
///     = (Q9·(4·P4))·X      symm (mul_assoc Q9 (4·P4) X)
///     = ((4·P4)·Q9)·X      congr_r X (mul_comm Q9 (4·P4))
///     = (4·P4)·(Q9·X)      mul_assoc (4·P4) Q9 X
/// ```
fn const_reshape(
    c: &RestrictedMassConsts,
    parent: &EnvDeclBuilder,
    q9: &Expr,
    p4: &Expr,
    four: &Expr,
    xx: &Expr,
) -> Expr {
    let four_x = c.mul(four.clone(), xx.clone()); // 4·X
    let p4_4 = c.mul(p4.clone(), four.clone()); // P4·4
    let four_p4 = c.mul(four.clone(), p4.clone()); // 4·P4
    let p4_4x = c.mul(p4.clone(), four_x.clone()); // P4·(4·X)
    let p4_4_then_x = c.mul(p4_4.clone(), xx.clone()); // (P4·4)·X
    let four_p4_x = c.mul(four_p4.clone(), xx.clone()); // (4·P4)·X
    let q9_x = c.mul(q9.clone(), xx.clone()); // Q9·X

    let q9_p4_4x = c.mul(q9.clone(), p4_4x.clone()); // Q9·(P4·(4·X)) = LHS
    let q9_p4_4_then_x = c.mul(q9.clone(), p4_4_then_x.clone()); // Q9·((P4·4)·X)
    let q9_four_p4_x = c.mul(q9.clone(), four_p4_x.clone()); // Q9·((4·P4)·X)
    let q9_four_p4 = c.mul(q9.clone(), four_p4.clone()); // Q9·(4·P4)
    let q9_four_p4_then_x = c.mul(q9_four_p4.clone(), xx.clone()); // (Q9·(4·P4))·X
    let four_p4_q9 = c.mul(four_p4.clone(), q9.clone()); // (4·P4)·Q9
    let four_p4_q9_then_x = c.mul(four_p4_q9.clone(), xx.clone()); // ((4·P4)·Q9)·X
    let four_p4_q9x = c.mul(four_p4.clone(), q9_x.clone()); // (4·P4)·(Q9·X) = RHS

    // e1 : P4·(4·X) = (P4·4)·X   symm (mul_assoc P4 4 X).
    let e1 = c.symm(
        p4_4_then_x.clone(),
        p4_4x.clone(),
        c.assoc(p4.clone(), four.clone(), xx.clone()),
    );
    // s1 : Q9·(P4·(4·X)) = Q9·((P4·4)·X)   congr_l Q9 e1.
    let s1 = c.congr_l(parent, q9, p4_4x.clone(), p4_4_then_x.clone(), e1);
    // e2 : (P4·4)·X = (4·P4)·X   congr_r X (mul_comm P4 4).
    let e2 = c.congr_r(
        parent,
        xx,
        p4_4.clone(),
        four_p4.clone(),
        c.comm(p4.clone(), four.clone()),
    );
    // s2 : Q9·((P4·4)·X) = Q9·((4·P4)·X)   congr_l Q9 e2.
    let s2 = c.congr_l(parent, q9, p4_4_then_x.clone(), four_p4_x.clone(), e2);
    // s3 : Q9·((4·P4)·X) = (Q9·(4·P4))·X   symm (mul_assoc Q9 (4·P4) X).
    let s3 = c.symm(
        q9_four_p4_then_x.clone(),
        q9_four_p4_x.clone(),
        c.assoc(q9.clone(), four_p4.clone(), xx.clone()),
    );
    // s4 : (Q9·(4·P4))·X = ((4·P4)·Q9)·X   congr_r X (mul_comm Q9 (4·P4)).
    let s4 = c.congr_r(
        parent,
        xx,
        q9_four_p4.clone(),
        four_p4_q9.clone(),
        c.comm(q9.clone(), four_p4.clone()),
    );
    // s5 : ((4·P4)·Q9)·X = (4·P4)·(Q9·X)   mul_assoc (4·P4) Q9 X.
    let s5 = c.assoc(four_p4.clone(), q9.clone(), xx.clone());

    let c12 = c.trans_eq(
        q9_p4_4x.clone(),
        q9_p4_4_then_x.clone(),
        q9_four_p4_x.clone(),
        s1,
        s2,
    );
    let c123 = c.trans_eq(
        q9_p4_4x.clone(),
        q9_four_p4_x.clone(),
        q9_four_p4_then_x.clone(),
        c12,
        s3,
    );
    let c1234 = c.trans_eq(
        q9_p4_4x.clone(),
        q9_four_p4_then_x.clone(),
        four_p4_q9_then_x.clone(),
        c123,
        s4,
    );
    c.trans_eq(q9_p4_4x, four_p4_q9_then_x, four_p4_q9x, c1234, s5)
}

impl RestrictedMassConsts {
    fn fsum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
}

impl Environment {
    /// Register `BoolAnalysis.friedgut_restricted_mass_le` (STEP 4 assembly) —
    /// `Σ_{S⊄J,|S|≤d} f̂(S)² ≤ 9^d·(dr·I[f])`. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn init_boolean_analysis_friedgut_restricted_mass(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_restricted_mass_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.le_of_ble_eq_true
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left, LE.le
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.register_rat_le_of_mul_le_mul_left_pos()?; // the positive-left cancel
        self.register_rat_le_trans_proof()?; // Rat.le_trans
                                             // the four masked bricks (each idempotent, constructive, empty closure):
        self.init_boolean_analysis_friedgut_deg_band_masked()?; // STEP 3
        self.init_boolean_analysis_friedgut_masked_noise()?; // STEP 4a
        self.init_boolean_analysis_friedgut_masked_reconcile()?; // STEP 4b
        self.init_boolean_analysis_kkl_dualhc_masked()?; // STEP 2 masked aggregate
                                                         // positivity leaves: Rat.mul_pos, Rat.powNat_pos.
        self.register_rat_pow_nat_mul_base()?; // Rat.powNat_pos + Rat.powNat_mul_base
        self.register_rat_order_proofs()?; // Rat.mul_pos

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = RestrictedMassConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: restricted_mass_type(&c),
            value: restricted_mass_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_friedgut_restricted_mass_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_restricted_mass()
            .expect("init_boolean_analysis_friedgut_restricted_mass");
        let nm = Name::from_string("BoolAnalysis.friedgut_restricted_mass_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("STEP 4 assembly proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_restricted_mass_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_restricted_mass()
            .expect("first");
        env.init_boolean_analysis_friedgut_restricted_mass()
            .expect("idempotent");
    }
}
