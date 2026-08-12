// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `influence_fourier` assembly — leg lemmas toward
//! `Inf_i[f] = Σ_{S∋i} f̂(S)²` (O'Donnell Thm. 2.20).
//!
//! Every piece is already proven (`subsetSum_inversion_core{,_flip}`,
//! `chi_flip_spectral`, `flip_coeff_absorb`, `disagree_sq_bridge`,
//! `subsetSum_xside_core`, the `subsetSum` linearity lemmas); this module is the
//! multi-stage `Eq.trans` regrouping that glues them. Mirrors the leg/chain
//! engineering style of `boolean_analysis_xside_core_chain.rs`.
//!
//! Notation (at fixed `n, f, i`):
//!   * `A_S := subsetSum n (fun y => pm(f y)·χ_S(y))`  (un-normalized; `f̂(S) = A_S/2^n`)
//!   * `a(S) := (2·ind(S i))·A_S`  — the modified-derivative coefficient.
//!
//! Leg lemmas registered here:
//!   * `subsetSum_flip_spectral_split` — at a fixed sign point `x`,
//!     `Σ_S a(S)·χ_S(x) = (Σ_S A_S·χ_S(x)) − (Σ_S A_S·χ_S(hcFlip n x i))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) struct InflConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_one: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    hc_decode: Expr,
    hc_flip: Expr,
    chi: Expr,
    pm: Expr,
    ind: Expr,
    flip_sign: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_sub: Expr,
    subset_sum_smul: Expr,
    ind_mul_self: Expr,
    rat_mmmc: Expr,
    #[cfg(test)]
    influence: Expr,
    fourier_coeff: Expr,
    inversion_core: Expr,
    inversion_core_flip: Expr,
    xside_core: Expr,
    disagree_sq_bridge: Expr,
    flip_coeff_absorb: Expr,
    chi_flip_spectral: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_sub: Expr,
    rat_mul_one: Expr,
    rat_one_mul: Expr,
    rat_inv: Expr,
    rat_mul_inv_cancel: Expr,
    natcast_ne_zero: Expr,
    one_le_two_pow: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    fin: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fin_sum: Expr,
    fin_sum_congr: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl InflConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            hc_flip: Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            flip_sign: Expr::const_(Name::from_string("BoolAnalysis.flipSign"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_sub: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_sub"), vec![]),
            subset_sum_smul: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
            ind_mul_self: Expr::const_(Name::from_string("BoolAnalysis.ind_mul_self"), vec![]),
            rat_mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            #[cfg(test)]
            influence: Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]),
            fourier_coeff: Expr::const_(
                Name::from_string("BoolAnalysis.FourierCoefficient"),
                vec![],
            ),
            inversion_core: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_inversion_core"),
                vec![],
            ),
            inversion_core_flip: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_inversion_core_flip"),
                vec![],
            ),
            xside_core: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_xside_core"),
                vec![],
            ),
            disagree_sq_bridge: Expr::const_(
                Name::from_string("BoolAnalysis.disagree_sq_bridge"),
                vec![],
            ),
            flip_coeff_absorb: Expr::const_(
                Name::from_string("BoolAnalysis.flip_coeff_absorb"),
                vec![],
            ),
            chi_flip_spectral: Expr::const_(
                Name::from_string("BoolAnalysis.chi_flip_spectral"),
                vec![],
            ),
            bool_beq: Expr::const_(Name::from_string("Bool.beq"), vec![]),
            bool_not: Expr::const_(Name::from_string("Bool.not"), vec![]),
            rat_mul_assoc: Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            rat_mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            rat_mul_sub: Expr::const_(Name::from_string("Rat.mul_sub"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            rat_one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            rat_inv: Expr::const_(Name::from_string("Rat.inv"), vec![]),
            rat_mul_inv_cancel: Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]),
            natcast_ne_zero: Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]),
            one_le_two_pow: Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            nat_le_step: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            #[cfg(test)]
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── numeral / type helpers ─────────────────────────────────────────────
    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    /// `(k/1) : Rat` for a Nat `k`.
    fn rat_of_nat(&self, k: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), k), self.one_nat()],
        )
    }
    /// `2 : Rat`.
    fn rat_two(&self) -> Expr {
        self.rat_of_nat(self.two_nat())
    }
    /// `2^n : Nat`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `(2^n)/1 : Rat`.
    fn cube(&self, n: &Expr) -> Expr {
        self.rat_of_nat(self.pow2(n))
    }
    fn hc_decode_(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `fun (x : HCPoint n) => pm (f x)` — the un-normalized amplitude `pm∘f`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pm_(Expr::app(f.clone(), x.clone()));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    // ── term builders ──────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn flip_sign_(&self, b: Expr) -> Expr {
        Expr::app(self.flip_sign.clone(), b)
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `congrArg (g : Rat → Rat) (h : a = b) : g a = g b`.
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `congrArg (fun z => left·z) h : left·a = left·bb`.
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    /// `congrArg (fun z => z·right) h : a·right = bb·right`.
    fn mul_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }

    /// `A_S := subsetSum n (fun y => pm(b y)·χ_S(y))` (inner correlation), where
    /// `b : HCPoint n → Rat` is the un-normalized amplitude `pm∘f`.
    fn amp(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(b.clone(), y.clone()), self.chi_(n, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn fsum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    /// `Fin.sum_congr n f g h : Fin.sum n f = Fin.sum n g`.
    fn fin_sum_congr_apply(&self, n: &Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n.clone(), f, g, h])
    }
    /// `m·m` (square).
    fn sq(&self, m: Expr) -> Expr {
        self.mul(m.clone(), m)
    }
    /// Given `h : p = q`, produce `p·p = q·q` (square both sides).
    /// `p·p = q·p` (mul_right_congr) then `q·p = q·q` (mul_left_congr).
    fn sq_congr(&self, parent: &EnvDeclBuilder, p: Expr, q: Expr, h: Expr) -> Expr {
        let h2 = h.clone();
        let r = self.mul_right_congr(parent, &p, p.clone(), q.clone(), h);
        let l = self.mul_left_congr(parent, &q, p.clone(), q.clone(), h2);
        let pp = self.mul(p.clone(), p.clone());
        let qp = self.mul(q.clone(), p);
        let qq = self.mul(q.clone(), q);
        self.trans(pp, qp, qq, r, l)
    }
    /// `disagree x := Bool.not (Bool.beq (f x) (f (hcFlip n x i)))`.
    fn disagree(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        Expr::app(
            self.bool_not.clone(),
            Expr::apps(self.bool_beq.clone(), [fx, fflip]),
        )
    }
    /// `disagree_sq_bridge a b : 4·ind(not(beq a b)) = (pm a − pm b)·(pm a − pm b)`.
    fn disagree_bridge(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.disagree_sq_bridge.clone(), [a, bb])
    }
    /// `subsetSum_smul n c f : Σ_S c·f(S) = c·Σ_S f(S)`.
    fn smul(&self, n: &Expr, cc: Expr, f: Expr) -> Expr {
        Expr::apps(self.subset_sum_smul.clone(), [n.clone(), cc, f])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, bb: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, bb, cc, d])
    }
    /// `4 : Rat`.
    fn rat_four(&self) -> Expr {
        let four = {
            let mut k = self.nat_zero.clone();
            for _ in 0..4 {
                k = Expr::app(self.nat_succ.clone(), k);
            }
            k
        };
        self.rat_of_nat(four)
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    /// `Rat.mul_inv_cancel a hne : a·a⁻¹ = 1`.
    fn mul_inv_cancel(&self, a: Expr, hne: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, hne])
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_e(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Influence n f i`.
    #[cfg(test)]
    fn influence_(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `FourierCoefficient n f S` (the normalized `f̂(S)`).
    fn fcoeff(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            self.fourier_coeff.clone(),
            [n.clone(), f.clone(), s.clone()],
        )
    }
}

include!("boolean_analysis_influence_legs.rs");
include!("boolean_analysis_influence_master.rs");
include!("boolean_analysis_influence_bridge.rs");
include!("boolean_analysis_influence_cancel.rs");
include!("boolean_analysis_influence_final.rs");
include!("boolean_analysis_acoeff_fourier.rs");
