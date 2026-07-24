// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP 4b: the `Jᶜ`-MASKED normalization
//! reconciliation (faithful O'Donnell §9.6 L2 chain, banked toward retiring the
//! `friedgut_boolean(+_helper)` admitted axioms).
//!
//! The OUTSIDE-`J`-masked variant of the rung-2 normalization bridge
//! [`BoolAnalysis.deg_band_rhs_eq_pow4_mass`], restated against STEP 3's CHARGING
//! LHS integrand (`mass_fn` at `b := pm∘f`): it converts the un-normalized
//! `4·A_{pm∘f}²` carrier of the masked degree-band charge into the normalized
//! `f̂²` carrier, with the `4·4^n` scalar pulled out EXACTLY.
//!
//! ```text
//! BoolAnalysis.deg_band_rhs_eq_pow4_mass_masked :
//!   ∀ (n k : Nat) (f : BoolFn n) (J : HCPoint n),
//!     subsetSum n (fun S =>
//!         ind (notSubsetMask n S J)                                    -- S ⊄ J
//!           · (ind (Nat.ble (setSizeNat n S) k)                        -- |S| ≤ k
//!               · (Rat.mul 4 (A_S(pm∘f) · A_S(pm∘f)))))                -- · 4·A_{pm∘f}(S)²
//!       = Rat.mul (Rat.mul 4 (Rat.powNat 4 n))
//!                 (subsetSum n (fun S =>
//!                     ind (notSubsetMask n S J)
//!                       · (ind (Nat.ble (setSizeNat n S) k)
//!                           · (f̂ S · f̂ S))))                          -- (4·4^n)·Σ_{S⊄J,|S|≤k} f̂(S)²
//! ```
//!
//! where `A_S(pm∘f) := subsetSum n (fun x => pm(f x)·χ_S x)` (byte-identical to
//! `Acoeff n (pm∘f) S`, i.e. STEP 3's `mass_fn` integrand at `b := pm∘f`),
//! `f̂ S := FourierCoefficient n f S`, and
//! `notSubsetMask n S J = Nat.ble 1 (setSizeNat n (fun i => S i ∧ ¬J i))`.
//!
//! The LHS is BYTE-IDENTICAL to STEP 3's `friedgut_masked_deg_band_charge` LHS
//! `subsetSum_S(ind(notSubsetMask)·w S)` at `b := pm∘f` (`w S := ind(ble |S| k)·
//! (4·A_{pm∘f}(S)²)`), so STEP 4 chains the masked charge directly through this
//! equality with no β/δ adjustment.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! Write `Z S := A_S(pm∘f)`, `X S := f̂(S)·f̂(S)`, `p S := ind (ble |S| k)`,
//! `r S := ind (notSubsetMask n S J)`, `P4 := 4^n`.
//!
//! 1. **per-S normalize + reshape** — for each `S`,
//!    ```text
//!      r·(p·(4·(Z·Z)))  =  r·(p·(4·(P4·X)))      congr, via step-1-squared (Z·Z = P4·X)
//!                       =  (4·P4)·(r·(p·X))       masked_reshape (pure Rat assoc/comm)
//!    ```
//!    `masked_reshape r p P4 X` is a pure-`Rat` rearrangement built only from
//!    `mul_assoc`/`mul_comm` (NO field facts).
//! 2. **subsetSum_congr** lifts (1):
//!    `LHS = subsetSum n (fun S => (4·P4)·(r·(p·X)))`.
//! 3. **subsetSum_smul** pulls the scalar:
//!    `= (4·P4)·subsetSum n (fun S => r·(p·X))` = the conclusion's RHS.
//!
//! `Eq.trans` of (2),(3) closes. The `|S|=0`/empty-band bookkeeping of the
//! unmasked `deg_band_rhs_eq_pow4_mass` is NOT needed here: STEP 3's charging LHS
//! has NO `setSize` factor (the `setSize`-weighted RHS is the EQUALITY's RHS, not
//! the charge's), so the band masks `(r, p)` are carried through verbatim — no
//! `setsize_band_mask_collapse`.
//!
//! Every leaf (`subsetSum_pm_sq_eq_pow4_fourier`, `subsetSum_congr`,
//! `subsetSum_smul`, `notSubsetMask`, `Rat.mul_assoc`, `Rat.mul_comm`, `congrArg`,
//! `Eq.*`) is `Constructive` with empty admitted-axiom closure, so this brick is
//! too. NO `sorry` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real`. No axiom added/removed. Idempotent. Gated
//! behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the masked normalization-reconciliation. Carrier spellings
/// (`subsetSum`, `chi`, `pm`, `FourierCoefficient`, `powNat`, `setSizeNat`,
/// `notSubsetMask`, `ind`, `Nat.ble`, `4 := mk(ofNat 4) 1`) byte-match STEP 3's
/// `mass_fn` carriers and step-1-squared's `Z`.
struct MaskedReconcileConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    chi: Expr,
    pm: Expr,
    subset_sum: Expr,
    fourier: Expr,
    ind: Expr,
    set_size_nat: Expr,
    not_subset_mask: Expr,
    nat_ble: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    l1: Level,
}

impl MaskedReconcileConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            chi: k("BoolAnalysis.chi"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            nat_ble: k("Nat.ble"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
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
    /// `(4 : Rat) := mk(ofNat 4) 1` (byte-match STEP 3's `four`).
    fn four(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(4)),
                self.nat_one(),
            ],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `4^n := powNat 4 n` (byte-match step-1-squared's `pow4`).
    fn pow4(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.four(), n.clone()])
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
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
    /// `Nat.ble (setSizeNat n S) k` — the `|S| ≤ k` low-band bit.
    fn low_bit(&self, n: &Expr, k: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.nat_ble.clone(),
            [self.set_size_nat_of(n, s), k.clone()],
        )
    }
    /// `Z S := A_S(pm∘f) := subsetSum n (fun x => pm(f x)·χ_S x)` — BYTE-IDENTICAL
    /// to step-1-squared's `Z` and to `Acoeff n (pm∘f) S` (STEP 3 at `b:=pm∘f`).
    fn z_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let body = self.mul(pm_fx, self.chi_(n, s, &x));
        let g = d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }
    /// `f̂(S)·f̂(S)`.
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }

    // ── Eq.{1} plumbing ───────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
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
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
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

    /// Pure-`Rat` rearrangement
    /// `masked_reshape r p P4 X : r·(p·(4·(P4·X))) = (4·P4)·(r·(p·X))`,
    /// built only from `mul_assoc`/`mul_comm` (NO field facts). Chain:
    /// ```text
    ///   r·(p·(4·(P4·X)))
    ///     = r·(p·((4·P4)·X))     congr_l r (congr_l p (symm (mul_assoc 4 P4 X)))
    ///     = r·((p·(4·P4))·X)     congr_l r (symm (mul_assoc p (4·P4) X))
    ///     = r·(((4·P4)·p)·X)     congr_l r (congr_r X (mul_comm p (4·P4)))
    ///     = r·((4·P4)·(p·X))     congr_l r (mul_assoc (4·P4) p X)
    ///     = (r·(4·P4))·(p·X)     symm (mul_assoc r (4·P4) (p·X))
    ///     = ((4·P4)·r)·(p·X)     congr_r (p·X) (mul_comm r (4·P4))
    ///     = (4·P4)·(r·(p·X))     mul_assoc (4·P4) r (p·X)
    /// ```
    fn masked_reshape(
        &self,
        parent: &EnvDeclBuilder,
        r: &Expr,
        p: &Expr,
        p4: &Expr,
        xx: &Expr,
    ) -> Expr {
        let four = self.four();
        let four_p4 = self.mul(four.clone(), p4.clone()); // 4·P4
        let p4_x = self.mul(p4.clone(), xx.clone()); // P4·X
        let four_p4x = self.mul(four.clone(), p4_x.clone()); // 4·(P4·X)
        let fp4_x = self.mul(four_p4.clone(), xx.clone()); // (4·P4)·X
        let p_x = self.mul(p.clone(), xx.clone()); // p·X
        let p_fp4 = self.mul(p.clone(), four_p4.clone()); // p·(4·P4)
        let fp4_p = self.mul(four_p4.clone(), p.clone()); // (4·P4)·p

        // terms
        let p_four_p4x = self.mul(p.clone(), four_p4x.clone()); // p·(4·(P4·X))
        let p_fp4_x = self.mul(p.clone(), fp4_x.clone()); // p·((4·P4)·X)
        let p_fp4_then_x = self.mul(p_fp4.clone(), xx.clone()); // (p·(4·P4))·X
        let fp4_p_then_x = self.mul(fp4_p.clone(), xx.clone()); // ((4·P4)·p)·X
        let fp4_px = self.mul(four_p4.clone(), p_x.clone()); // (4·P4)·(p·X)

        let r_p_four_p4x = self.mul(r.clone(), p_four_p4x.clone()); // r·(p·(4·(P4·X)))
        let r_p_fp4_x = self.mul(r.clone(), p_fp4_x.clone()); // r·(p·((4·P4)·X))
        let r_p_fp4_then_x = self.mul(r.clone(), p_fp4_then_x.clone()); // r·((p·(4·P4))·X)
        let r_fp4_p_then_x = self.mul(r.clone(), fp4_p_then_x.clone()); // r·(((4·P4)·p)·X)
        let r_fp4_px = self.mul(r.clone(), fp4_px.clone()); // r·((4·P4)·(p·X))
        let r_fp4 = self.mul(r.clone(), four_p4.clone()); // r·(4·P4)
        let r_fp4_then_px = self.mul(r_fp4.clone(), p_x.clone()); // (r·(4·P4))·(p·X)
        let fp4_r = self.mul(four_p4.clone(), r.clone()); // (4·P4)·r
        let fp4_r_then_px = self.mul(fp4_r.clone(), p_x.clone()); // ((4·P4)·r)·(p·X)
        let r_p_x = self.mul(r.clone(), p_x.clone()); // r·(p·X)
        let fp4_rpx = self.mul(four_p4.clone(), r_p_x.clone()); // (4·P4)·(r·(p·X)) = target RHS

        // e1 : 4·(P4·X) = (4·P4)·X  := symm (mul_assoc 4 P4 X).
        let e1 = self.symm(
            fp4_x.clone(),
            four_p4x.clone(),
            self.assoc(four.clone(), p4.clone(), xx.clone()),
        );
        // s1 : r·(p·(4·(P4·X))) = r·(p·((4·P4)·X))  := congr_l r (congr_l p e1).
        let pe1 = self.congr_l(parent, p, four_p4x.clone(), fp4_x.clone(), e1);
        let s1 = self.congr_l(parent, r, p_four_p4x.clone(), p_fp4_x.clone(), pe1);
        // e2 : p·((4·P4)·X) = (p·(4·P4))·X  := symm (mul_assoc p (4·P4) X).
        let e2 = self.symm(
            p_fp4_then_x.clone(),
            p_fp4_x.clone(),
            self.assoc(p.clone(), four_p4.clone(), xx.clone()),
        );
        // s2 : r·(p·((4·P4)·X)) = r·((p·(4·P4))·X)  := congr_l r e2.
        let s2 = self.congr_l(parent, r, p_fp4_x.clone(), p_fp4_then_x.clone(), e2);
        // e3 : (p·(4·P4))·X = ((4·P4)·p)·X  := congr_r X (mul_comm p (4·P4)).
        let e3 = self.congr_r(
            parent,
            xx,
            p_fp4.clone(),
            fp4_p.clone(),
            self.comm(p.clone(), four_p4.clone()),
        );
        // s3 : r·((p·(4·P4))·X) = r·(((4·P4)·p)·X)  := congr_l r e3.
        let s3 = self.congr_l(parent, r, p_fp4_then_x.clone(), fp4_p_then_x.clone(), e3);
        // e4 : ((4·P4)·p)·X = (4·P4)·(p·X)  := mul_assoc (4·P4) p X.
        let e4 = self.assoc(four_p4.clone(), p.clone(), xx.clone());
        // s4 : r·(((4·P4)·p)·X) = r·((4·P4)·(p·X))  := congr_l r e4.
        let s4 = self.congr_l(parent, r, fp4_p_then_x.clone(), fp4_px.clone(), e4);
        // s5 : r·((4·P4)·(p·X)) = (r·(4·P4))·(p·X)  := symm (mul_assoc r (4·P4) (p·X)).
        let s5 = self.symm(
            r_fp4_then_px.clone(),
            r_fp4_px.clone(),
            self.assoc(r.clone(), four_p4.clone(), p_x.clone()),
        );
        // s6 : (r·(4·P4))·(p·X) = ((4·P4)·r)·(p·X)  := congr_r (p·X) (mul_comm r (4·P4)).
        let s6 = self.congr_r(
            parent,
            &p_x,
            r_fp4.clone(),
            fp4_r.clone(),
            self.comm(r.clone(), four_p4.clone()),
        );
        // s7 : ((4·P4)·r)·(p·X) = (4·P4)·(r·(p·X))  := mul_assoc (4·P4) r (p·X).
        let s7 = self.assoc(four_p4.clone(), r.clone(), p_x.clone());

        // chain s1..s7.
        let c12 = self.trans(
            r_p_four_p4x.clone(),
            r_p_fp4_x.clone(),
            r_p_fp4_then_x.clone(),
            s1,
            s2,
        );
        let c123 = self.trans(
            r_p_four_p4x.clone(),
            r_p_fp4_then_x.clone(),
            r_fp4_p_then_x.clone(),
            c12,
            s3,
        );
        let c1234 = self.trans(
            r_p_four_p4x.clone(),
            r_fp4_p_then_x.clone(),
            r_fp4_px.clone(),
            c123,
            s4,
        );
        let c12345 = self.trans(
            r_p_four_p4x.clone(),
            r_fp4_px.clone(),
            r_fp4_then_px.clone(),
            c1234,
            s5,
        );
        let c123456 = self.trans(
            r_p_four_p4x.clone(),
            r_fp4_then_px.clone(),
            fp4_r_then_px.clone(),
            c12345,
            s6,
        );
        self.trans(r_p_four_p4x, fp4_r_then_px, fp4_rpx, c123456, s7)
    }
}

// ───────────── the per-S / band-integrand lambdas (for subsetSum_congr) ─────────

/// CHARGING LHS integrand `fun S => r·(p·(4·(Z·Z)))` (≡ STEP 3's `mass_fn` at
/// `b := pm∘f`), where `r = ind(notSubsetMask n S J)`, `p = ind(ble |S| k)`,
/// `Z = A_S(pm∘f)`.
fn mass_in_fn(
    c: &MaskedReconcileConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let z = c.z_coeff(&d, n, f, &s);
    let zz = c.mul(z.clone(), z);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, k, &s));
    let body = c.mul(r, c.mul(p, c.mul(c.four(), zz)));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// scaled middle integrand `fun S => (4·4^n) · (r·(p·(f̂·f̂)))`.
fn mid_in_fn(
    c: &MaskedReconcileConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let four_p4 = c.mul(c.four(), c.pow4(n));
    let xx = c.x_sq(n, f, &s);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, k, &s));
    let r_px = c.mul(r, c.mul(p, xx));
    let body = c.mul(four_p4, r_px);
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// the masked low-band mass integrand `fun S => r·(p·(f̂·f̂))` — the conclusion
/// RHS subsetSum integrand.
fn mass_x_fn(
    c: &MaskedReconcileConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    j: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let xx = c.x_sq(n, f, &s);
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, k, &s));
    let body = c.mul(r, c.mul(p, xx));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn masked_reconcile_type(c: &MaskedReconcileConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, mass_in_fn(c, &b, &n, &k, &f, &j));
    let four_p4 = c.mul(c.four(), c.pow4(&n));
    let rhs = c.mul(four_p4, c.ssum(&n, mass_x_fn(c, &b, &n, &k, &f, &j)));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn masked_reconcile_value(c: &MaskedReconcileConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());

    let mass_in = mass_in_fn(c, &b, &n, &k, &f, &j);
    let mid_in = mid_in_fn(c, &b, &n, &k, &f, &j);
    let mass_x = mass_x_fn(c, &b, &n, &k, &f, &j);

    let four_p4 = c.mul(c.four(), c.pow4(&n));
    let mass_sum = c.ssum(&n, mass_in.clone()); // LHS of conclusion
    let mid_sum = c.ssum(&n, mid_in.clone());
    let mass_x_sum = c.ssum(&n, mass_x.clone());
    let scaled = c.mul(four_p4.clone(), mass_x_sum.clone()); // RHS of conclusion

    // ── per-S : mass_in S = mid_in S ──
    let per_s = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());

        let z = c.z_coeff(&d, &n, &f, &s); // Z = A_S(pm∘f)
        let zz = c.mul(z.clone(), z.clone());
        let xx = c.x_sq(&n, &f, &s); // f̂·f̂
        let p4 = c.pow4(&n);
        let p4_x = c.mul(p4.clone(), xx.clone()); // P4·X
        let r = c.ind_of(c.not_subset_mask_of(&n, &s, &j));
        let p = c.ind_of(c.low_bit(&n, &k, &s));
        let four = c.four();

        // h_sq : Z·Z = P4·X   (subsetSum_pm_sq_eq_pow4_fourier n f S).
        let h_sq = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_pm_sq_eq_pow4_fourier"),
                vec![],
            ),
            [n.clone(), f.clone(), s.clone()],
        );

        // h_norm : r·(p·(4·(Z·Z))) = r·(p·(4·(P4·X)))
        //   congr_l r (congr_l p (congr_l 4 h_sq)).
        let inner = c.congr_l(&d, &four, zz.clone(), p4_x.clone(), h_sq);
        let four_zz = c.mul(four.clone(), zz.clone());
        let four_p4x = c.mul(four.clone(), p4_x.clone());
        let inner_p = c.congr_l(&d, &p, four_zz.clone(), four_p4x.clone(), inner);
        let p_4zz = c.mul(p.clone(), four_zz.clone());
        let p_4p4x = c.mul(p.clone(), four_p4x.clone());
        let h_norm = c.congr_l(&d, &r, p_4zz.clone(), p_4p4x.clone(), inner_p);

        // h_reshape : r·(p·(4·(P4·X))) = (4·P4)·(r·(p·X))   masked_reshape.
        let h_reshape = c.masked_reshape(&d, &r, &p, &p4, &xx);

        // chain : mass_in S = mid_in S
        let lhs_term = c.mul(r.clone(), p_4zz.clone()); // r·(p·(4·(Z·Z)))
        let mid_term0 = c.mul(r.clone(), p_4p4x.clone()); // r·(p·(4·(P4·X)))
        let p_x = c.mul(p.clone(), xx.clone());
        let r_px = c.mul(r.clone(), p_x.clone());
        let mid_term = c.mul(four_p4.clone(), r_px.clone()); // (4·P4)·(r·(p·X))
        let body = c.trans(lhs_term, mid_term0, mid_term, h_norm, h_reshape);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    // (1) eq1 : mass_sum = mid_sum   subsetSum_congr n mass_in mid_in per_s.
    let ss_congr = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
    let eq1 = Expr::apps(
        ss_congr,
        [n.clone(), mass_in.clone(), mid_in.clone(), per_s],
    );

    // (2) eq2 : mid_sum = (4·P4)·mass_x_sum   subsetSum_smul n (4·P4) mass_x.
    //   `mid_in` is `fun S => (4·P4)·(mass_x S)` by β, so its sum is the smul LHS.
    let ss_smul = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);
    let eq2 = Expr::apps(ss_smul, [n.clone(), four_p4.clone(), mass_x.clone()]);

    // chain : mass_sum = mid_sum = (4·P4)·mass_x_sum.
    let proof = c.trans(mass_sum, mid_sum, scaled, eq1, eq2);

    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.deg_band_rhs_eq_pow4_mass_masked` (STEP 4b) — the
    /// `Jᶜ`-masked normalization reconciliation
    /// `Σ_{S⊄J,|S|≤k} 4·A_{pm∘f}(S)² = (4·4^n)·Σ_{S⊄J,|S|≤k} f̂(S)²`. See module
    /// docs. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent; no axiom added/removed.
    pub fn init_boolean_analysis_friedgut_masked_reconcile(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass_masked");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, chi, FourierCoefficient, ind, setSizeNat
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_subset_sum_pm_sq_eq_pow4_fourier()?; // step-1-squared bridge
        self.init_boolean_analysis_friedgut_cheap_rungs()?; // notSubsetMask

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MaskedReconcileConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: masked_reconcile_type(&c),
            value: masked_reconcile_value(&c),
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
    fn test_deg_band_rhs_eq_pow4_mass_masked_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_masked_reconcile()
            .expect("init_boolean_analysis_friedgut_masked_reconcile");
        let nm = Name::from_string("BoolAnalysis.deg_band_rhs_eq_pow4_mass_masked");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("masked norm-reconcile proof must check: {e:?}"));
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
    fn test_masked_reconcile_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_masked_reconcile()
            .expect("first");
        env.init_boolean_analysis_friedgut_masked_reconcile()
            .expect("idempotent");
    }
}
