// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut v3 — the THRESHOLD (`C-thr`) case of `friedgut_boolean`.
//!
//! This module assembles the final `n > B` branch of the v3 junta theorem,
//! `BoolAnalysis.friedgut_boolean_case_threshold`, plus the small bounded
//! sub-bricks it needs. Every declaration is a genuine `Declaration::Theorem`,
//! `Constructive`, with an EMPTY admitted-axiom closure (⊆ FOUNDATIONAL_AXIOMS).
//! Hand-constructed `Expr` (no tactics). Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.
//!
//! # Goal
//!
//! ```text
//! BoolAnalysis.friedgut_boolean_case_threshold :
//!   ∀ (n : Nat) (f : BoolFn n) (K eps : Rat) (e : Nat),
//!     Rat.le (TotalInfluence n f) K →
//!     Rat.lt Rat.zero eps → Rat.lt eps 1 →
//!     And (Rat.le (natCast (2^e) · eps) K) (Rat.le K (natCast (2^(e+1)) · eps)) →
//!     Nat.lt (Nat.pow 2 (48·2^e)) n →
//!       Exists (fun (J : HCPoint n) =>
//!         And (Nat.le (setSizeNat n J) (Nat.pow 2 (48·2^e)))
//!             (Rat.le (subsetSum n (fun S =>
//!                        ind (notSubsetMask n S J) · (f̂ S · f̂ S))) eps))
//! ```
//!
//! whose `Exists` predicate is BYTE-IDENTICAL to `friedgut_l2_faithful_body_v3`.
//! The witness is the threshold junta `J := thresholdJ n f (dr·dr)`, with
//! `dr := lowDr (2^(e+2)) K eps = eps / (2·(natCast(9^(2^(e+2)))·K))`.
//!
//! # Sub-bricks (each its own commit)
//!
//! 1. `BoolAnalysis.influence_nonneg : ∀ n f i, 0 ≤ Influence n f i`
//!    — per-coordinate influence is nonneg. `Influence ≡ Expect (ind∘differ)
//!    ≡ Rat.div (Σ ind) (natCast 2^n) ≡ (Σ ind)·inv(natCast 2^n)`; `Σ ind ≥ 0`
//!    (`Fin.sum_nonneg`+`ind_nonneg`), `inv(natCast 2^n) ≥ 0` (`inv_pos` of the
//!    positive cast, then `le_of_lt`), combined by `mul_nonneg`.
//!
//! 2. `Rat.powNat_nine_eq_natCast : ∀ d, Rat.powNat (Rat.ofNat 9) d
//!      = natCast (Nat.pow 9 d)` — the LOW-band `9^d` two-spellings bridge
//!    (l2-core writes `9^d` as `Rat.powNat (Rat.ofNat 9) d`; the LOW-budget
//!    cancel writes it as `natCast (Nat.pow 9 d)`). `Nat.rec` on `d`, mirroring
//!    `Rat.powNat_two_eq_natCast`.
//!
//! 3. `BoolAnalysis.friedgut_threshold_high_pre : ∀ K eps (e:Nat),
//!      Rat.le 0 eps → Rat.le K (natCast(2^(e+1))·eps) →
//!        Rat.le K (natCast(2^(e+2)+1)·(eps/2))` — the HIGH-band budget
//!    precondition `I ≤ (d+1)·eH` reshaped from the upper guard (`d := 2^(e+2)`,
//!    `eH := eps/2`).
//!
//! 4. `dr² < 1` is built inline in the assembly from the LOWER guard.
//!
//! NO `sorry` / `sorryAx` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real` / `Rat.dist` / new `Axiom`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms for the threshold-case bricks. Spellings byte-match the
/// banked friedgut bricks (`L2Consts`, `ProofConsts`, the LOW band).
struct ThrConsts {
    nat: Expr,
    rat: Expr,
    #[cfg(test)]
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_div: Expr,
    rat_of_nat: Expr,
    rat_pow_nat: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    hc_decode: Expr,
    hc_flip: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    ind: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    l0: Level,
    l1: Level,
}

impl ThrConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            #[cfg(test)]
            bool_: k("Bool"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_div: k("Rat.div"),
            rat_of_nat: k("Rat.ofNat"),
            rat_pow_nat: k("Rat.powNat"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            ind: k("BoolAnalysis.ind"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            l0,
            l1,
        }
    }

    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn nat_one(&self) -> Expr {
        self.nat_lit(1)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n.clone()])
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.nat_one(),
            ],
        )
    }
    /// `LE.le.{0} Rat instLERat a b`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![self.l0.clone()]),
            [
                self.rat.clone(),
                Expr::const_(Name::from_string("instLERat"), vec![]),
                a,
                b,
            ],
        )
    }
    /// `Rat.lt a b`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    /// `Eq.{2} Rat a b`.
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.rat.clone(), a],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg.{1,1} A B a b f h : f a = f b`.
    fn congr_arg(&self, dom: Expr, cod: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [dom, cod, a, b, f, h],
        )
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    /// `Nat.add a b`.
    fn nmul_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.add"), vec![]), [a, b])
    }
    /// `Eq.symm.{2} Rat a b h : Eq Rat b a`.
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `Eq.subst.{2} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `congrArg (fun (z : Rat) => left·z) h : left·a = left·b`.
    fn congr_mul_l(&self, parent: &EnvDeclBuilder, left: Expr, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, bb, f, h)
    }
    /// `congrArg (fun (z : Rat) => z·right) h : a·right = b·right`.
    fn congr_mul_r(
        &self,
        parent: &EnvDeclBuilder,
        right: Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, bb, f, h)
    }
    fn trans3_rat(
        &self,
        a: Expr,
        b: Expr,
        cc: Expr,
        dd: Expr,
        h1: Expr,
        h2: Expr,
        h3: Expr,
    ) -> Expr {
        let t1 = self.trans_rat(a.clone(), b.clone(), cc.clone(), h1, h2);
        self.trans_rat(a, cc, dd, t1, h3)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    /// `Rat.mul_pos a b ha hb : 0 < a·b`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.le_trans a b c h1 h2 : a ≤ c`.
    #[cfg(test)]
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.le_of_mul_le_mul_left_pos a b c hpos hle : a ≤ b`  (from `c·a ≤ c·b`, `0<c`).
    fn le_of_mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hpos: Expr, hle: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
            [a, b, cc, hpos, hle],
        )
    }
    /// `natCast(9^d)` (LOW-band `a := natCast(Nat.pow 9 d)`).
    fn cast_pow9(&self, d: &Expr) -> Expr {
        self.natcast(&self.nat_pow9(d))
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c hbc h0 : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, hbc, h0],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c hbc h0 : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            [a, b, cc, hbc, h0],
        )
    }
    /// `Rat.le_of_lt a b h : a ≤ b`.
    fn le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]),
            [a, b, h],
        )
    }
    /// `Rat.inv_pos b h : 0 < inv b`.
    fn inv_pos(&self, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.inv_pos"), vec![]),
            [b, h],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.lt_of_lt_of_le a b c h1 h2 : a < c`.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.lt_of_le_of_lt a b c h1 h2 : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_lt_add_left"), vec![]),
            [a, b, cc, h],
        )
    }
    /// `Rat.mul_lt_mul a b c d h0a hab h0c hcd : (a·c) < (b·d)`.
    fn mul_lt_mul(
        &self,
        a: Expr,
        b: Expr,
        cc: Expr,
        dd: Expr,
        h0a: Expr,
        hab: Expr,
        h0c: Expr,
        hcd: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_lt_mul"), vec![]),
            [a, b, cc, dd, h0a, hab, h0c, hcd],
        )
    }
    /// `Rat.add a b`.
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.add"), vec![]), [a, b])
    }
    #[cfg(test)]
    fn rat_add(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.add"), vec![])
    }
    /// Bare `Rat.le a b` (the spelling `Rat.lt_iff_le_not_le` uses internally).
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    /// `mul_lt_mul_of_pos_left a b cc (hab : a < b) (hc : 0 < cc) : cc·a < cc·b`.
    /// Built from the LEFT le-cancel + `lt_iff_le_not_le` (no native strict-mul
    /// lemma exists on branch). `cc·a ≤ cc·b` (mul_le_of_nonneg_left of `a≤b`),
    /// and `¬(cc·b ≤ cc·a)` (else le_of_mul_le_mul_left_pos contradicts ¬b≤a).
    /// All order atoms use bare `Rat.lt`/`Rat.le` to byte-match `lt_iff_le_not_le`.
    fn mul_lt_mul_of_pos_left(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        cc: &Expr,
        hab: Expr,
        hc: Expr,
    ) -> Expr {
        let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
        let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_c = Expr::const_(Name::from_string("And"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let le_cancel = Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]);
        // P_ab := Rat.lt a b ; Q_ab := (a≤b ∧ ¬b≤a). pair := (lt_iff a b).mp hab : Q_ab.
        let lt_ab = self.lt(a.clone(), b.clone());
        let le_ab = self.rle(a.clone(), b.clone());
        let le_ba = self.rle(b.clone(), a.clone());
        let not_le_ba = Expr::app(not_c.clone(), le_ba.clone());
        let q_ab = Expr::apps(and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let iff_ab = Expr::apps(lt_iff.clone(), [a.clone(), b.clone()]);
        let pair = Expr::apps(iff_mp.clone(), [lt_ab.clone(), q_ab.clone(), iff_ab, hab]);
        let h_le_ab = Expr::apps(
            and_left.clone(),
            [le_ab.clone(), not_le_ba.clone(), pair.clone()],
        );
        let h_nba = Expr::apps(and_right.clone(), [le_ab.clone(), not_le_ba.clone(), pair]);
        let h0c = self.le_of_lt(self.rat_zero.clone(), cc.clone(), hc.clone());
        // cca ≤ ccb (mul_le_left produces bare Rat.le).
        let cca = self.mul(cc.clone(), a.clone());
        let ccb = self.mul(cc.clone(), b.clone());
        let h_cca_ccb = self.mul_le_left(cc.clone(), a.clone(), b.clone(), h_le_ab, h0c);
        // ¬(ccb ≤ cca) : fun h => h_nba (le_cancel b a cc hc h).
        let not_ccb_cca = {
            let mut g = EnvDeclBuilder::child_of(parent);
            let ccb_cca_ty = self.rle(ccb.clone(), cca.clone());
            let (hh_id, hh) = g.fresh_local(ccb_cca_ty.clone());
            let ba = Expr::apps(
                le_cancel.clone(),
                [b.clone(), a.clone(), cc.clone(), hc.clone(), hh],
            );
            let body = Expr::app(h_nba, ba);
            g.finish_child(g.mk_lam(hh_id, BinderInfo::Default, ccb_cca_ty, body))
        };
        // cca < ccb := (lt_iff cca ccb).mpr ⟨h_cca_ccb, not_ccb_cca⟩.
        let lt_cc = self.lt(cca.clone(), ccb.clone());
        let le_cc = self.rle(cca.clone(), ccb.clone());
        let not_le_cc = Expr::app(not_c.clone(), self.rle(ccb.clone(), cca.clone()));
        let q_cc = Expr::apps(and_c.clone(), [le_cc.clone(), not_le_cc.clone()]);
        let and_pair = Expr::apps(
            and_intro.clone(),
            [le_cc.clone(), not_le_cc.clone(), h_cca_ccb, not_ccb_cca],
        );
        let iff_cc = Expr::apps(lt_iff.clone(), [cca.clone(), ccb.clone()]);
        Expr::apps(iff_mpr.clone(), [lt_cc, q_cc, iff_cc, and_pair])
    }
    fn rat_one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.one"), vec![])
    }
    /// `Nat.pow 2 m` (alias of pow2 for already-built exponents).
    fn pow2_at(&self, m: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), m.clone()])
    }
    /// `Nat.pow 9 m`.
    fn nat_pow9_exp(&self, m: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(9), m.clone()])
    }
    /// `Eq.symm.{1} Nat a b h : Eq Nat b a`.
    fn nat_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nat.clone(), a, b, h],
        )
    }
    /// `Eq.trans.{1} Nat a b c h1 h2 : Eq Nat a c`.
    fn nat_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.nat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg (fun (z : Nat) => Nat.add left z) h : Nat.add left a = Nat.add left b`.
    fn nat_congr_add_l(
        &self,
        parent: &EnvDeclBuilder,
        left: Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.nat.clone());
            let body = self.nmul_add(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.nat.clone(), body))
        };
        self.congr_arg(self.nat.clone(), self.nat.clone(), a, bb, f, h)
    }
    /// `congrArg (fun (z : Nat) => Nat.pow 9 z) h : Nat.pow 9 a = Nat.pow 9 b`.
    fn nat_congr_pow9(&self, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.nat.clone());
            let body = self.nat_pow9_exp(&z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.nat.clone(), body))
        };
        self.congr_arg(self.nat.clone(), self.nat.clone(), a, bb, f, h)
    }
    /// Proof of `(u·v)·(u·v) = (u·u)·(v·v)` via assoc/comm.
    fn sq_prod(&self, parent: &EnvDeclBuilder, u: &Expr, v: &Expr) -> Expr {
        let uv = self.mul(u.clone(), v.clone());
        let uu = self.mul(u.clone(), u.clone());
        let vv = self.mul(v.clone(), v.clone());
        // s1 : (u·v)·(u·v) = ((u·v)·u)·v   [symm (assoc (u·v) u v)].
        let uv_u = self.mul(uv.clone(), u.clone());
        let s1 = self.symm_rat(
            self.mul(uv_u.clone(), v.clone()),
            self.mul(uv.clone(), uv.clone()),
            self.mul_assoc(uv.clone(), u.clone(), v.clone()),
        );
        // p : (u·v)·u = (u·u)·v.
        //   (u·v)·u = u·(v·u)   [assoc u v u]
        //   u·(v·u) = u·(u·v)   [congr u· (comm v u)]
        //   u·(u·v) = (u·u)·v   [symm (assoc u u v)]
        let uu_v = self.mul(uu.clone(), v.clone());
        let u_vu = self.mul(u.clone(), self.mul(v.clone(), u.clone()));
        let u_uv = self.mul(u.clone(), uv.clone());
        let p1 = self.mul_assoc(u.clone(), v.clone(), u.clone());
        let p2 = self.congr_mul_l(
            parent,
            u.clone(),
            self.mul(v.clone(), u.clone()),
            uv.clone(),
            self.mul_comm(v.clone(), u.clone()),
        );
        let p3 = self.symm_rat(
            uu_v.clone(),
            u_uv.clone(),
            self.mul_assoc(u.clone(), u.clone(), v.clone()),
        );
        let p = self.trans3_rat(
            uv_u.clone(),
            u_vu.clone(),
            u_uv.clone(),
            uu_v.clone(),
            p1,
            p2,
            p3,
        );
        // s2 : ((u·v)·u)·v = ((u·u)·v)·v   [congr (·v) p].
        let s2 = self.congr_mul_r(parent, v.clone(), uv_u.clone(), uu_v.clone(), p);
        // s3 : ((u·u)·v)·v = (u·u)·(v·v)   [assoc (u·u) v v].
        let s3 = self.mul_assoc(uu.clone(), v.clone(), v.clone());
        // chain s1;s2;s3.
        let lhs = self.mul(uv.clone(), uv.clone());
        let r = self.mul(uu_v.clone(), v.clone());
        self.trans3_rat(
            lhs,
            self.mul(uv_u.clone(), v.clone()),
            r,
            self.mul(uu.clone(), vv.clone()),
            s1,
            s2,
            s3,
        )
    }
    /// `Nat.pow 9 d`.
    fn nat_pow9(&self, d: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(9), d.clone()])
    }
    /// `Rat.ofNat 9` — the LOW-band / l2-core `9^d` base.
    fn rat_nine(&self) -> Expr {
        Expr::app(self.rat_of_nat.clone(), self.nat_lit(9))
    }
    /// `Rat.powNat (Rat.ofNat 9) d` — l2-core's `pow9` spelling of `9^d`.
    fn pow9_rat(&self, d: &Expr) -> Expr {
        Expr::apps(self.rat_pow_nat.clone(), [self.rat_nine(), d.clone()])
    }
    /// `Rat.mul_natCast a b : mk(ofNat a) 1 · mk(ofNat b) 1 = mk(ofNat (a·b)) 1`.
    fn mul_natcast_at(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_natCast"), vec![]),
            [a, b],
        )
    }
    /// `congrArg (fun (z : Nat) => natCast z) h : natCast a = natCast b`.
    fn natcast_congr(&self, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.nat.clone());
            let body = self.natcast(&z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.nat.clone(), body))
        };
        self.congr_arg(self.nat.clone(), self.rat.clone(), a, bb, f, h)
    }
    /// `congrArg (fun (z : Rat) => 9·z) h : 9·a = 9·b` (left congruence at base 9).
    fn nine_congr_l(&self, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let nine = self.rat_nine();
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(nine.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, bb, f, h)
    }

    /// `fun (k : Fin (2^n)) => ind (Bool.not (Bool.beq (f (hcDecode n k))
    ///                                       (f (hcFlip n (hcDecode n k) i))))`
    /// — the decoded summand of `Influence n f i ≡ Expect n (ind∘differ)`.
    fn influence_summand(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_pow = self.fin_of(&self.pow2(n));
        let (k_id, k) = b.fresh_local(fin_pow.clone());
        let x = Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()]);
        let f_x = Expr::app(f.clone(), x.clone());
        let flipped = Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
        let f_flip = Expr::app(f.clone(), flipped);
        let beq = Expr::apps(self.bool_beq.clone(), [f_x, f_flip]);
        let differ = Expr::app(self.bool_not.clone(), beq);
        let body = self.ind_of(differ);
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_pow, body))
    }
}

impl Environment {
    /// `BoolAnalysis.influence_nonneg : ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
    ///   Rat.le Rat.zero (Influence n f i)`.
    ///
    /// Per-coordinate influence is nonnegative. `Influence n f i` reducibly
    /// unfolds to `Expect n (fun x => ind (differ x))
    /// ≡ Rat.div (Fin.sum (2^n) summand) (natCast (2^n))
    /// ≡ Rat.mul (Fin.sum (2^n) summand) (Rat.inv (natCast (2^n)))`, where each
    /// `summand k = ind (…) ≥ 0`. The numerator is nonneg (`Fin.sum_nonneg` of
    /// `ind_nonneg`); `Rat.inv (natCast (2^n)) ≥ 0` (`Rat.inv_pos` of the cast
    /// `0 < natCast (2^n)`, then `Rat.le_of_lt`); their product is nonneg
    /// (`Rat.mul_nonneg`). Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent. No axiom added/removed.
    pub fn register_influence_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.influence_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Influence, Expect, ind, hcFlip, hcDecode
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_beq()?; // Bool.beq
        self.init_fin_sum()?; // Fin.sum, Fin.sum_nonneg
        self.register_ind_nonneg()?; // BoolAnalysis.ind_nonneg
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.init_algebra_rat_inv_pos()?; // Rat.inv_pos, Rat.le_of_lt
        self.init_rat_linear_order()?; // Rat.mul_nonneg, le_antisymm, lt_iff_le_not_le
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow, natCast_ne_zero_of_pos
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ThrConsts::new();
        let fin_sum_nonneg = Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]);
        let ind_nonneg = Expr::const_(Name::from_string("BoolAnalysis.ind_nonneg"), vec![]);
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let natcast_ne_zero = Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
        let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let inv_pos = Expr::const_(Name::from_string("Rat.inv_pos"), vec![]);
        let le_of_lt = Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]);
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());

            let infl = c.influence_of(&n, &f, &i);
            let concl = c.le(c.rat_zero.clone(), infl.clone());

            if !for_value {
                let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, concl);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // num := Fin.sum (2^n) summand ; denom := natCast (2^n).
            let pow2n = c.pow2(&n);
            let summand = c.influence_summand(&b, &n, &f, &i);
            let num = Expr::apps(
                Expr::const_(Name::from_string("Fin.sum"), vec![]),
                [pow2n.clone(), summand.clone()],
            );
            let denom = c.natcast(&pow2n);

            // h_num : 0 ≤ num  via  Fin.sum_nonneg (2^n) summand h_each.
            let h_each = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let fin_pow = c.fin_of(&pow2n);
                let (k_id, k) = g.fresh_local(fin_pow.clone());
                // summand k ≡ ind (differ k); its nonneg is ind_nonneg (differ k).
                // Build (differ k) by applying summand and peeling `ind`: easiest is
                // ind_nonneg applied to the SAME bit `summand` uses. Re-derive bit:
                let x = Expr::apps(c.hc_decode.clone(), [n.clone(), k.clone()]);
                let f_x = Expr::app(f.clone(), x.clone());
                let flipped = Expr::apps(c.hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
                let f_flip = Expr::app(f.clone(), flipped);
                let beq = Expr::apps(c.bool_beq.clone(), [f_x, f_flip]);
                let differ = Expr::app(c.bool_not.clone(), beq);
                let body = Expr::app(ind_nonneg.clone(), differ);
                g.finish_child(g.mk_lam(k_id, BinderInfo::Default, fin_pow, body))
            };
            let h_num = Expr::apps(
                fin_sum_nonneg.clone(),
                [pow2n.clone(), summand.clone(), h_each],
            );

            // h_denom_pos : 0 < natCast (2^n).
            //   one_le : Nat.le 1 (2^n) := Nat.one_le_two_pow n.
            //   h0d : 0 ≤ denom := natCast_nonneg (2^n).
            //   d_ne : denom ≠ 0 := natCast_ne_zero_of_pos (2^n) one_le.
            //   not_d_le0 : ¬(denom ≤ 0) := fun hle => d_ne (le_antisymm denom 0 hle h0d).
            //   ha_pos : 0 < denom := Iff.mpr (lt_iff_le_not_le 0 denom)
            //                                 (And.intro h0d not_d_le0).
            let one_le = Expr::app(one_le_two_pow.clone(), n.clone());
            let h0d = Expr::app(natcast_nonneg.clone(), pow2n.clone());
            let d_ne = Expr::apps(natcast_ne_zero.clone(), [pow2n.clone(), one_le]);
            let not_d_le0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let d_le0_ty = c.le(denom.clone(), c.rat_zero.clone());
                let (hle_id, hle) = g.fresh_local(d_le0_ty.clone());
                let d_eq0 = Expr::apps(
                    le_antisymm.clone(),
                    [denom.clone(), c.rat_zero.clone(), hle, h0d.clone()],
                );
                let body = Expr::app(d_ne.clone(), d_eq0);
                g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, d_le0_ty, body))
            };
            let lt0d = c.lt(c.rat_zero.clone(), denom.clone());
            let le0d = c.le(c.rat_zero.clone(), denom.clone());
            let not_le_d0 = Expr::app(not_c.clone(), c.le(denom.clone(), c.rat_zero.clone()));
            let and_ty = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [le0d.clone(), not_le_d0.clone()],
            );
            let and_pair = Expr::apps(
                and_intro.clone(),
                [le0d.clone(), not_le_d0.clone(), h0d.clone(), not_d_le0],
            );
            let iff_ld = Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), denom.clone()]);
            let h_denom_pos = Expr::apps(
                iff_mpr.clone(),
                [lt0d.clone(), and_ty.clone(), iff_ld, and_pair],
            );

            // h_inv : 0 ≤ inv denom := le_of_lt 0 (inv denom)
            //            (inv_pos denom h_denom_pos).
            let inv_denom = c.inv(denom.clone());
            let inv_pos_pf = Expr::apps(inv_pos.clone(), [denom.clone(), h_denom_pos]);
            let h_inv = Expr::apps(
                le_of_lt.clone(),
                [c.rat_zero.clone(), inv_denom.clone(), inv_pos_pf],
            );

            // proof : 0 ≤ mul num (inv denom)  := mul_nonneg num (inv denom) h_num h_inv.
            // The goal `0 ≤ Influence n f i` is def-eq to this
            // (Influence ≡ Expect ≡ div num denom ≡ mul num (inv denom)).
            let proof = Expr::apps(
                mul_nonneg.clone(),
                [num.clone(), inv_denom.clone(), h_num, h_inv],
            );

            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, proof);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.powNat_nine_eq_natCast : ∀ (d : Nat),
    ///   Rat.powNat (Rat.ofNat 9) d = Rat.mk (Int.ofNat (Nat.pow 9 d)) 1`.
    ///
    /// The LOW-band `9^d` two-spellings bridge: `friedgut_l2_core`'s `hlow`
    /// hypothesis writes `9^d` as `Rat.powNat (Rat.ofNat 9) d`, while
    /// `friedgut_low_budget_cancel` (and the v3 SIZE brick) write it as
    /// `natCast (Nat.pow 9 d)`. `Nat.rec` on `d`, mirroring
    /// `Rat.powNat_two_eq_natCast`. Base `d=0`: both sides ≡ `mk(ofNat 1) 1`
    /// (`powNat _ 0 ≡ Rat.one`, `Nat.pow 9 0 ≡ 1`), `Eq.refl`. Step `d+1`, ih
    /// `9^d = natCast(Nat.pow 9 d)`: the goal ι-reduces to
    /// `9·9^d = natCast(Nat.mul (Nat.pow 9 d) 9)` (powNat multiplies LEFT,
    /// Nat.pow RIGHT) via
    ///   `9·9^d = 9·natCast(Nat.pow 9 d)`          [congr (9·_) ih]
    ///         ≡ natCast(9)·natCast(Nat.pow 9 d)    [Rat.ofNat 9 ≡ mk(ofNat 9) 1]
    ///         = natCast(Nat.mul 9 (Nat.pow 9 d))   [Rat.mul_natCast 9 (9^d)]
    ///         = natCast(Nat.mul (Nat.pow 9 d) 9)   [congr natCast (Nat.mul_comm)]
    /// whose last term is the goal RHS (def-eq to `natCast(Nat.pow 9 (d+1))`).
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    /// No axiom added/removed.
    pub fn register_rat_pow_nat_nine_eq_natcast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_nine_eq_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_ofnat()?; // Rat.ofNat (the LOW-band / l2-core 9^d base)
        self.register_rat_pow_nat()?; // Rat.powNat (+ powNat_succ ι-reduction)
        self.register_rat_mul_natcast()?; // Rat.mul_natCast (the step's natCast product)
        self.register_nat_mul_comm_proof()?; // Nat.mul_comm (factor-order swap)
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ThrConsts::new();
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let nmul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let concl = c.eq_rat(c.pow9_rat(&d), c.natcast(&c.nat_pow9(&d)));
            b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), concl))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());

            // motive : fun (k : Nat) => 9^k = natCast(Nat.pow 9 k).
            let motive = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = g.fresh_local(c.nat.clone());
                let body = c.eq_rat(c.pow9_rat(&k), c.natcast(&c.nat_pow9(&k)));
                g.finish_child(g.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base : 9^0 = natCast(Nat.pow 9 0).  Both ≡ mk(ofNat 1) 1; Eq.refl.
            let base = c.refl_rat(c.pow9_rat(&c.nat_zero.clone()));

            // succ_case : fun (k) (ih : 9^k = natCast(Nat.pow 9 k)) => <proof>.
            let succ_case = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = g.fresh_local(c.nat.clone());
                let pow9k = c.nat_pow9(&k); // Nat.pow 9 k
                let ih_ty = c.eq_rat(c.pow9_rat(&k), c.natcast(&pow9k));
                let (ih_id, ih) = g.fresh_local(ih_ty.clone());

                let rpk = c.pow9_rat(&k); // 9^k (Rat)
                let cast_pow9k = c.natcast(&pow9k); // natCast(Nat.pow 9 k)
                let nine = c.rat_nine();

                // goal LHS ≡ 9·9^k (Rat.powNat 9 (succ k) ι-reduces to Rat.mul 9 (9^k)).
                let nine_rpk = c.mul(nine.clone(), rpk.clone());
                let nine_cast = c.mul(nine.clone(), cast_pow9k.clone());
                // s1 : 9·9^k = 9·natCast(9^k)   congr (9·_) ih.
                let s1 = c.nine_congr_l(&g, rpk.clone(), cast_pow9k.clone(), ih);
                // s2 : natCast(9)·natCast(9^k) = natCast(Nat.mul 9 (9^k)).
                //   (9·natCast(9^k) ≡ natCast(9)·natCast(9^k) since 9 ≡ mk(ofNat 9) 1.)
                let s2 = c.mul_natcast_at(c.nat_lit(9), pow9k.clone());
                let cast_9_pow9k = c.natcast(&c.nmul(c.nat_lit(9), pow9k.clone()));
                // s3 : natCast(Nat.mul 9 (9^k)) = natCast(Nat.mul (9^k) 9)
                //   congr natCast (Nat.mul_comm 9 (9^k)).
                let comm = Expr::apps(nmul_comm.clone(), [c.nat_lit(9), pow9k.clone()]);
                let cast_pow9k_9 = c.natcast(&c.nmul(pow9k.clone(), c.nat_lit(9)));
                let s3 = c.natcast_congr(
                    &g,
                    c.nmul(c.nat_lit(9), pow9k.clone()),
                    c.nmul(pow9k.clone(), c.nat_lit(9)),
                    comm,
                );

                // chain: 9·9^k = 9·cast = natCast(9·9^k) = natCast(9^k·9).
                let ch = c.trans_rat(
                    nine_rpk.clone(),
                    nine_cast.clone(),
                    cast_9_pow9k.clone(),
                    s1,
                    s2,
                );
                let proof = c.trans_rat(
                    nine_rpk.clone(),
                    cast_9_pow9k.clone(),
                    cast_pow9k_9.clone(),
                    ch,
                    s3,
                );
                // proof : 9·9^k = natCast(Nat.mul (9^k) 9), def-eq to goal RHS
                // natCast(Nat.pow 9 (k+1)) (Nat.pow 9 (succ k) ≡ Nat.mul (Nat.pow 9 k) 9).
                let r = g.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
                g.finish_child(g.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
            };

            let rec_app = Expr::apps(nat_rec.clone(), [motive, base, succ_case, d.clone()]);
            b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), rec_app))
        };

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.friedgut_threshold_high_pre : ∀ (K eps : Rat) (e : Nat),
    ///   Rat.lt Rat.zero eps →
    ///   @LE.le Rat instLERat K (Rat.mul (natCast (2^(e+1))) eps) →
    ///     @LE.le Rat instLERat K
    ///       (Rat.mul (natCast (Nat.succ (2^(e+2)))) (Rat.div eps Rat.two))`.
    ///
    /// The HIGH-band budget precondition reshape: the upper guard `K ≤ 2^(e+1)·eps`
    /// lifts to `K ≤ (2^(e+2)+1)·(eps/2)`, the `hi` that `friedgut_high_mass_budget`
    /// consumes at `d := 2^(e+2)`, `eH := eps/2`. The core identity
    /// `EQ : natCast(2^(e+2))·(eps/2) = natCast(2^(e+1))·eps` is
    ///   natCast(2^(e+2)) = natCast(2^(e+1)) + natCast(2^(e+1))   [add_natCast∘pow_two_succ]
    ///   (A+A)·(eps/2) = A·(eps/2) + A·(eps/2)                    [right_distrib]
    ///   A·(eps/2) + A·(eps/2) = A·((eps/2)+(eps/2))              [left_distrib⁻¹]
    ///   A·((eps/2)+(eps/2)) = A·eps                              [congr (A·_) add_halves]
    /// with `A := natCast(2^(e+1))`. Then `natCast(2^(e+2))·(eps/2)
    /// ≤ natCast(2^(e+2)+1)·(eps/2)` (`mul_le_mul_of_nonneg_right`, the Nat-step
    /// `2^(e+2) ≤ 2^(e+2)+1` cast in, `0 ≤ eps/2` via `half_pos`), chained by
    /// `le_trans` and `Eq.subst`. Kernel-checked, `Constructive`, empty
    /// admitted-axiom closure. Idempotent. No axiom added/removed.
    pub fn register_friedgut_threshold_high_pre(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_threshold_high_pre");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_nat()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.div
        self.init_rat_field_inst()?; // Rat.left_distrib, Rat.right_distrib
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_algebra_rat_half_pos()?; // Rat.half_pos, Rat.add_halves
        self.init_algebra_rat_inv_pos()?; // Rat.le_of_lt
        self.register_rat_add_natcast()?; // Rat.add_natCast
        self.register_nat_pow_two_succ_proof()?; // Nat.pow_two_succ
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble
        self.register_nat_ble_le_lemmas()?; // Nat.ble_refl, Nat.ble_succ_right_eq_true
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ThrConsts::new();
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_two = Expr::const_(Name::from_string("Rat.two"), vec![]);
        let rat_div = c.rat_div.clone();
        let left_distrib = Expr::const_(Name::from_string("Rat.left_distrib"), vec![]);
        let right_distrib = Expr::const_(Name::from_string("Rat.right_distrib"), vec![]);
        let add_natcast = Expr::const_(Name::from_string("Rat.add_natCast"), vec![]);
        let add_halves = Expr::const_(Name::from_string("Rat.add_halves"), vec![]);
        let half_pos = Expr::const_(Name::from_string("Rat.half_pos"), vec![]);
        let le_of_lt = Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let mul_le_right =
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
        let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
        let ble_refl = Expr::const_(Name::from_string("Nat.ble_refl"), vec![]);
        let ble_succ_right = Expr::const_(Name::from_string("Nat.ble_succ_right_eq_true"), vec![]);
        let pow_two_succ = Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]);
        let nat_succ = c.nat_succ.clone();

        let div2 = |a: Expr| Expr::apps(rat_div.clone(), [a, rat_two.clone()]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (k_id, kk) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (e_id, e) = b.fresh_local(c.nat.clone());

            // e+1, e+2, 2^(e+1), 2^(e+2), succ(2^(e+2)).
            let e1 = Expr::app(nat_succ.clone(), e.clone()); // e+1
            let e2 = Expr::app(nat_succ.clone(), e1.clone()); // e+2
            let pow_e1 = c.pow2(&e1); // 2^(e+1)
            let pow_e2 = c.pow2(&e2); // 2^(e+2)
            let succ_pow_e2 = Expr::app(nat_succ.clone(), pow_e2.clone()); // 2^(e+2)+1
            let aa = c.natcast(&pow_e1); // A := natCast(2^(e+1))
            let cast_pe2 = c.natcast(&pow_e2); // natCast(2^(e+2))
            let cast_spe2 = c.natcast(&succ_pow_e2); // natCast(2^(e+2)+1)
            let half = div2(eps.clone()); // eps/2

            let guard_rhs = c.mul(aa.clone(), eps.clone()); // A·eps
            let goal_rhs = c.mul(cast_spe2.clone(), half.clone()); // (2^(e+2)+1)·(eps/2)

            let heps_ty = c.lt(c.rat_zero.clone(), eps.clone()); // 0 < eps
            let hguard_ty = c.le(kk.clone(), guard_rhs.clone()); // K ≤ A·eps
            let concl = c.le(kk.clone(), goal_rhs.clone()); // K ≤ (2^(e+2)+1)·(eps/2)

            if !for_value {
                let (heps_id, _) = b.fresh_local(heps_ty.clone());
                let (hguard_id, _) = b.fresh_local(hguard_ty.clone());
                let r = b.mk_pi(hguard_id, BinderInfo::Default, hguard_ty, concl);
                let r = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, r);
                let r = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), r);
                let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
                return b.finish(b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), r));
            }

            let (heps_id, heps) = b.fresh_local(heps_ty.clone());
            let (hguard_id, hguard) = b.fresh_local(hguard_ty.clone());

            // ── EQ : natCast(2^(e+2))·(eps/2) = A·eps ──
            // q1 : natCast(2^(e+2)) = A + A.
            //   pow_two_succ (e+1) : Nat.pow 2 (succ (e+1)) = Nat.add (2^(e+1)) (2^(e+1)),
            //   i.e. 2^(e+2) = 2^(e+1) + 2^(e+1) (def-eq succ(e+1) ≡ e+2).
            //   add_natCast (2^(e+1)) (2^(e+1)) :
            //     natCast(2^(e+1) + 2^(e+1)) = natCast(2^(e+1)) + natCast(2^(e+1)) = A + A.
            //   congrArg natCast (pow_two_succ (e+1)) :
            //     natCast(2^(e+2)) = natCast(2^(e+1)+2^(e+1)); chain with add_natCast.
            let h_pts = Expr::apps(pow_two_succ.clone(), [e1.clone()]); // 2^(e+2) = (2^(e+1))+(2^(e+1))
            let sum_nat = c.nmul_add(pow_e1.clone(), pow_e1.clone()); // Nat.add (2^(e+1)) (2^(e+1))
            let cast_sum = c.natcast(&sum_nat); // natCast(2^(e+1)+2^(e+1))
            let q1a = c.natcast_congr(&b, pow_e2.clone(), sum_nat.clone(), h_pts);
            // q1a : natCast(2^(e+2)) = natCast(2^(e+1)+2^(e+1)).
            let q1b = Expr::apps(add_natcast.clone(), [pow_e1.clone(), pow_e1.clone()]);
            // q1b : natCast(2^(e+1)+2^(e+1)) = A + A.
            let a_plus_a = add(aa.clone(), aa.clone());
            let q1 = c.trans_rat(
                cast_pe2.clone(),
                cast_sum.clone(),
                a_plus_a.clone(),
                q1a,
                q1b,
            );
            // q1 : natCast(2^(e+2)) = A + A.

            // q2 : natCast(2^(e+2))·(eps/2) = (A + A)·(eps/2).
            //   congrArg (·(eps/2)) q1.
            let q2 = c.congr_mul_r(&b, half.clone(), cast_pe2.clone(), a_plus_a.clone(), q1);
            // q3 : (A + A)·(eps/2) = A·(eps/2) + A·(eps/2)   [right_distrib A A (eps/2)].
            let a_half = c.mul(aa.clone(), half.clone());
            let q3 = Expr::apps(
                right_distrib.clone(),
                [aa.clone(), aa.clone(), half.clone()],
            );
            // q4 : A·(eps/2) + A·(eps/2) = A·((eps/2)+(eps/2))   [symm (left_distrib A (eps/2)(eps/2))].
            let half_plus_half = add(half.clone(), half.clone());
            let a_hph = c.mul(aa.clone(), half_plus_half.clone());
            let ld = Expr::apps(
                left_distrib.clone(),
                [aa.clone(), half.clone(), half.clone()],
            ); // A·((eps/2)+(eps/2)) = A·(eps/2)+A·(eps/2)
            let q4 = c.symm_rat(a_hph.clone(), add(a_half.clone(), a_half.clone()), ld);
            // q5 : A·((eps/2)+(eps/2)) = A·eps   [congr (A·_) (add_halves eps)].
            let hadd = Expr::app(add_halves.clone(), eps.clone()); // (eps/2)+(eps/2) = eps
            let q5 = c.congr_mul_l(&b, aa.clone(), half_plus_half.clone(), eps.clone(), hadd);
            // EQ : natCast(2^(e+2))·(eps/2) = A·eps  (chain q2;q3;q4;q5).
            let lhs_eq = c.mul(cast_pe2.clone(), half.clone());
            let ap_half = add(a_half.clone(), a_half.clone());
            let eqc1 = c.trans_rat(
                lhs_eq.clone(),
                c.mul(a_plus_a.clone(), half.clone()),
                ap_half.clone(),
                q2,
                q3,
            );
            let eqc2 = c.trans_rat(lhs_eq.clone(), ap_half.clone(), a_hph.clone(), eqc1, q4);
            let eq_full = c.trans_rat(lhs_eq.clone(), a_hph.clone(), guard_rhs.clone(), eqc2, q5);
            // eq_full : natCast(2^(e+2))·(eps/2) = A·eps.

            // h_half_nonneg : 0 ≤ eps/2 := le_of_lt 0 (eps/2) (half_pos eps heps).
            let hp = Expr::apps(half_pos.clone(), [eps.clone(), heps.clone()]);
            let h_half_nn = Expr::apps(le_of_lt.clone(), [c.rat_zero.clone(), half.clone(), hp]);

            // h_nat_le : natCast(2^(e+2)) ≤ natCast(2^(e+2)+1).
            //   ble (2^(e+2)) (succ (2^(e+2))) = true
            //     := ble_succ_right_eq_true (2^(e+2)) (2^(e+2)) (ble_refl (2^(e+2))).
            //   Nat.cast_le_of_ble (2^(e+2)) (succ (2^(e+2))) that.
            let h_ble_refl = Expr::app(ble_refl.clone(), pow_e2.clone());
            let h_ble = Expr::apps(
                ble_succ_right.clone(),
                [pow_e2.clone(), pow_e2.clone(), h_ble_refl],
            );
            let h_nat_le = Expr::apps(
                cast_le_of_ble.clone(),
                [pow_e2.clone(), succ_pow_e2.clone(), h_ble],
            );

            // h_mul : natCast(2^(e+2))·(eps/2) ≤ natCast(2^(e+2)+1)·(eps/2).
            //   mul_le_mul_of_nonneg_right (eps/2) (natCast 2^(e+2)) (natCast 2^(e+2)+1)
            //                               h_nat_le h_half_nn.
            let h_mul = Expr::apps(
                mul_le_right.clone(),
                [
                    half.clone(),
                    cast_pe2.clone(),
                    cast_spe2.clone(),
                    h_nat_le,
                    h_half_nn,
                ],
            );
            // h_mul : natCast(2^(e+2))·(eps/2) ≤ goal_rhs.

            // Transport guard's RHS A·eps back to natCast(2^(e+2))·(eps/2) via eq_full:
            //   subst (motive t => K ≤ t) (a := A·eps) (b := natCast(2^(e+2))·(eps/2))
            //         (symm eq_full) hguard : K ≤ natCast(2^(e+2))·(eps/2).
            let motive = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.le(kk.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let eq_symm = c.symm_rat(lhs_eq.clone(), guard_rhs.clone(), eq_full);
            // eq_symm : A·eps = natCast(2^(e+2))·(eps/2).
            let hk_lhs = c.subst_rat(motive, guard_rhs.clone(), lhs_eq.clone(), eq_symm, hguard);
            // hk_lhs : K ≤ natCast(2^(e+2))·(eps/2).

            // proof : K ≤ goal_rhs := le_trans K (natCast(2^(e+2))·(eps/2)) goal_rhs hk_lhs h_mul.
            let proof = Expr::apps(
                le_trans.clone(),
                [kk.clone(), lhs_eq.clone(), goal_rhs.clone(), hk_lhs, h_mul],
            );

            let r = b.mk_lam(hguard_id, BinderInfo::Default, hguard_ty, proof);
            let r = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, r);
            let r = b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), r))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.friedgut_threshold_size_rearrange :
    ///   ∀ (e : Nat) (K eps : Rat),
    ///     Rat.lt Rat.zero K → Rat.lt Rat.zero eps → Rat.lt eps Rat.one →
    ///     @LE.le Rat instLERat K (Rat.mul (natCast (2^(e+1))) eps) →
    ///       @LE.le Rat instLERat K (Rat.mul (Rat.mul dr dr) (natCast (2^(48·2^e))))`,
    ///   where `dr := Rat.div eps (Rat.mul Rat.two (Rat.mul (natCast (Nat.pow 9 (2^(e+2)))) K))`
    ///   (= `lowDr (2^(e+2)) K eps`).
    ///
    /// The SIZE-bound rearrangement: `friedgut_size_poly_bound`'s cleared form
    /// `4·9^(2d)·K³ ≤ eps²·B` (`d := 2^(e+2)`, `B := 2^(48·2^e)`) is exactly
    /// `K ≤ dr²·B` after restoring the `dr²` denominator. With
    /// `den := 2·(natCast(9^d)·K)` (so `dr = eps/den`):
    ///   E1 : (den·den)·K = natCast(4·9^(2d))·(K·(K·K))      [den² = 4·9^(2d)·K²]
    ///   E2 : (den·den)·(dr²·B) = (eps·eps)·B                [den·dr = eps twice]
    ///   size_poly : natCast(4·9^(2d))·(K·(K·K)) ≤ (eps·eps)·B
    ///     ⟹ (den·den)·K ≤ (den·den)·(dr²·B)   [Eq.subst E1, E2]
    ///     ⟹ K ≤ dr²·B   [le_of_mul_le_mul_left_pos, 0 < den·den].
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    /// No axiom added/removed.
    pub fn register_friedgut_threshold_size_rearrange(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_threshold_size_rearrange");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_nat()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.div
        self.init_rat_field_inst()?; // mul_assoc, mul_comm
        self.init_rat_linear_order()?; // mul_pos, zero_lt_one
        self.init_algebra_rat_div_mul_cancel()?; // Rat.div_mul_cancel_pos
        self.init_boolean_analysis_order_toolkit()?; // mul_le order surface
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_le_of_mul_le_mul_left_pos()?; // Rat.le_of_mul_le_mul_left_pos
        self.register_rat_mul_natcast()?; // Rat.mul_natCast
        self.register_natcast_nonneg()?; // natCast_nonneg
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow, natCast_ne_zero_of_pos
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right (0<a via pow≥1)
        self.register_nat_pow_add_proof()?; // Nat.pow_add (9^d·9^d = 9^(2d))
        self.register_nat_succ_mul_proof()?; // Nat.succ_mul (2·d = d+d)
        self.register_nat_one_mul_proof()?; // Nat.one_mul (1·d = d)
        self.register_fin_sum_const_one_theorems()?; // Rat.add_natCast_one (Rat.two = nc2)
        self.register_rat_zero_lt_two()?; // 0 < Rat.two
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_friedgut_size_poly_bound()?; // the cleared poly bound
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ThrConsts::new();
        let nat_succ = c.nat_succ.clone();
        let two_rat = c.rat_two.clone();
        let div_mul_cancel = Expr::const_(Name::from_string("Rat.div_mul_cancel_pos"), vec![]);
        let mul_natcast = Expr::const_(Name::from_string("Rat.mul_natCast"), vec![]);
        let pow_add = Expr::const_(Name::from_string("Nat.pow_add"), vec![]);
        let zero_lt_two = Expr::const_(Name::from_string("Rat.zero_lt_two"), vec![]);
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let natcast_ne_zero = Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]);
        let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
        let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
        let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let size_poly = Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_size_poly_bound"),
            vec![],
        );

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(c.nat.clone());
            let (k_id, kk) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());

            // d := 2^(e+2); a := natCast(9^d); den := 2·(a·K); dr := eps/den.
            let e1 = Expr::app(nat_succ.clone(), e.clone()); // e+1
            let e2 = Expr::app(nat_succ.clone(), e1.clone()); // e+2
            let dexp = c.pow2(&e2); // d = 2^(e+2)
            let a = c.cast_pow9(&dexp); // a = natCast(9^d)
            let ak = c.mul(a.clone(), kk.clone()); // a·K
            let den = c.mul(two_rat.clone(), ak.clone()); // den = 2·(a·K)
            let dr = Expr::apps(c.rat_div.clone(), [eps.clone(), den.clone()]); // eps/den
            let drdr = c.mul(dr.clone(), dr.clone()); // dr·dr
            let ee48 = c.nmul(c.nat_lit(48), c.pow2(&e)); // 48·2^e
            let bnat = c.pow2_at(&ee48); // 2^(48·2^e)
            let bcast = c.natcast(&bnat); // natCast(B)
            let goal_rhs = c.mul(drdr.clone(), bcast.clone()); // dr²·B

            let q_e1 = c.natcast(&c.pow2(&e1)); // natCast(2^(e+1))
            let guard_rhs = c.mul(q_e1.clone(), eps.clone()); // natCast(2^(e+1))·eps

            let hkpos_ty = c.lt(c.rat_zero.clone(), kk.clone()); // 0 < K
            let hepspos_ty = c.lt(c.rat_zero.clone(), eps.clone()); // 0 < eps
            let hlt1_ty = c.lt(eps.clone(), c.rat_one()); // eps < 1
            let hguard_ty = c.le(kk.clone(), guard_rhs.clone()); // K ≤ natCast(2^(e+1))·eps
            let concl = c.le(kk.clone(), goal_rhs.clone()); // K ≤ dr²·B

            if !for_value {
                let (hkpos_id, _) = b.fresh_local(hkpos_ty.clone());
                let (hepspos_id, _) = b.fresh_local(hepspos_ty.clone());
                let (hlt1_id, _) = b.fresh_local(hlt1_ty.clone());
                let (hguard_id, _) = b.fresh_local(hguard_ty.clone());
                let r = b.mk_pi(hguard_id, BinderInfo::Default, hguard_ty, concl);
                let r = b.mk_pi(hlt1_id, BinderInfo::Default, hlt1_ty, r);
                let r = b.mk_pi(hepspos_id, BinderInfo::Default, hepspos_ty, r);
                let r = b.mk_pi(hkpos_id, BinderInfo::Default, hkpos_ty, r);
                let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), r);
                return b.finish(b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), r));
            }

            let (hkpos_id, hkpos) = b.fresh_local(hkpos_ty.clone());
            let (hepspos_id, hepspos) = b.fresh_local(hepspos_ty.clone());
            let (hlt1_id, hlt1) = b.fresh_local(hlt1_ty.clone());
            let (hguard_id, hguard) = b.fresh_local(hguard_ty.clone());

            // ── 0 < a := natCast(9^d) ── (mirror of friedgut_low_budget_cancel) ──
            let one = c.nat_lit(1);
            let mut h_1le9 = Expr::app(nat_le_refl.clone(), one.clone());
            {
                let mut cur = one.clone();
                for _ in 0..8 {
                    let nxt = Expr::app(nat_succ.clone(), cur.clone());
                    h_1le9 = Expr::apps(nat_le_step.clone(), [one.clone(), cur.clone(), h_1le9]);
                    cur = nxt;
                }
            }
            let zero_le_d = Expr::app(nat_zero_le.clone(), dexp.clone());
            let nine_d = c.nat_pow9(&dexp); // Nat.pow 9 d
            let one_le_9pow = Expr::apps(
                pow_le_pow_right.clone(),
                [
                    c.nat_lit(9),
                    c.nat_zero.clone(),
                    dexp.clone(),
                    h_1le9,
                    zero_le_d,
                ],
            );
            let h0a = Expr::app(natcast_nonneg.clone(), nine_d.clone()); // 0 ≤ a
            let ha_ne = Expr::apps(natcast_ne_zero.clone(), [nine_d.clone(), one_le_9pow]); // a ≠ 0
            let not_a_le0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let a_le0_ty = c.le(a.clone(), c.rat_zero.clone());
                let (hle_id, hle) = g.fresh_local(a_le0_ty.clone());
                let a_eq0 = Expr::apps(
                    le_antisymm.clone(),
                    [a.clone(), c.rat_zero.clone(), hle, h0a.clone()],
                );
                let body = Expr::app(ha_ne.clone(), a_eq0);
                g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, a_le0_ty, body))
            };
            let le0a = c.le(c.rat_zero.clone(), a.clone());
            let not_le_a0 = Expr::app(not_c.clone(), c.le(a.clone(), c.rat_zero.clone()));
            let and_ty_a = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [le0a.clone(), not_le_a0.clone()],
            );
            let and_pair_a = Expr::apps(
                and_intro.clone(),
                [le0a.clone(), not_le_a0.clone(), h0a.clone(), not_a_le0],
            );
            let iff_la = Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), a.clone()]);
            let ha_pos = Expr::apps(
                iff_mpr.clone(),
                [
                    c.lt(c.rat_zero.clone(), a.clone()),
                    and_ty_a.clone(),
                    iff_la,
                    and_pair_a,
                ],
            ); // 0 < a

            // 0 < a·K, 0 < den = 2·(a·K), 0 < den·den.
            let h_ak_pos = c.mul_pos(a.clone(), kk.clone(), ha_pos.clone(), hkpos.clone());
            let h_den_pos = c.mul_pos(two_rat.clone(), ak.clone(), zero_lt_two.clone(), h_ak_pos);
            let h_dd_pos = c.mul_pos(
                den.clone(),
                den.clone(),
                h_den_pos.clone(),
                h_den_pos.clone(),
            );

            // ── E1 : (den·den)·K = natCast(4·9^(2d))·(K·(K·K)) ──
            // den·den = (2·(a·K))·(2·(a·K)). Regroup to (2·2)·((a·a)·(K·K)).
            // Helper square-of-product: prove den·den = nc4·(nc(9^2d)·(K·K)),
            // then = nc(4·9^2d)·(K·K), then ·K and assoc.
            // a·a = nc(9^d)·nc(9^d) = nc(9^d·9^d) = nc(9^(d+d)) ; and 2·2 = nc4.
            // First: aa_eq : a·a = nc(9^(2d)).
            let aa = c.mul(a.clone(), a.clone());
            let nine_dd = c.nat_pow9_exp(&c.nmul_add(dexp.clone(), dexp.clone())); // 9^(d+d)
            let nine_2d = c.nat_pow9_exp(&c.nmul(c.nat_lit(2), dexp.clone())); // 9^(2·d)
            let cast_nine_dd = c.natcast(&nine_dd);
            let cast_nine_2d = c.natcast(&nine_2d);
            // mul_natCast (9^d) (9^d) : nc(9^d)·nc(9^d) = nc(9^d·9^d)... but RHS is nc(Nat.mul (9^d)(9^d)).
            let aa_mn = Expr::apps(mul_natcast.clone(), [nine_d.clone(), nine_d.clone()]);
            // aa_mn : a·a = nc(Nat.mul (9^d) (9^d)).
            let nmul_nine = c.nmul(nine_d.clone(), nine_d.clone());
            let cast_nmul_nine = c.natcast(&nmul_nine);
            // pow_add 9 d d : 9^(d+d) = (9^d)·(9^d) = Nat.mul (9^d)(9^d) ... pow_add gives
            //   Nat.pow 9 (d+d) = Nat.mul (Nat.pow 9 d)(Nat.pow 9 d).
            let h_powadd = Expr::apps(pow_add.clone(), [c.nat_lit(9), dexp.clone(), dexp.clone()]);
            // h_powadd : 9^(d+d) = Nat.mul (9^d)(9^d). congr natCast (symm h_powadd):
            //   nc(Nat.mul (9^d)(9^d)) = nc(9^(d+d)).
            let h_powadd_symm = c.nat_symm(nine_dd.clone(), nmul_nine.clone(), h_powadd);
            let cast_powadd =
                c.natcast_congr(&b, nmul_nine.clone(), nine_dd.clone(), h_powadd_symm);
            // aa_eq1 : a·a = nc(9^(d+d)) := trans aa_mn cast_powadd.
            let aa_eq1 = c.trans_rat(
                aa.clone(),
                cast_nmul_nine.clone(),
                cast_nine_dd.clone(),
                aa_mn,
                cast_powadd,
            );
            // two_mul_d : Nat.mul 2 d = Nat.add d d  (succ_mul 1 d ; one_mul d).
            //   succ_mul 1 d : Nat.mul (succ 1) d = Nat.add d (Nat.mul 1 d)   (2 ≡ succ 1).
            //   one_mul d    : Nat.mul 1 d = d.
            //   congr (Nat.add d ·) one_mul : Nat.add d (Nat.mul 1 d) = Nat.add d d.
            let succ_mul = Expr::const_(Name::from_string("Nat.succ_mul"), vec![]);
            let one_mul = Expr::const_(Name::from_string("Nat.one_mul"), vec![]);
            let two_d = c.nmul(c.nat_lit(2), dexp.clone()); // Nat.mul 2 d
            let mul1_d = c.nmul(c.nat_lit(1), dexp.clone()); // Nat.mul 1 d
            let add_d_mul1d = c.nmul_add(dexp.clone(), mul1_d.clone());
            let add_dd = c.nmul_add(dexp.clone(), dexp.clone());
            let h_succ_mul = Expr::apps(succ_mul.clone(), [c.nat_lit(1), dexp.clone()]);
            // h_succ_mul : Nat.mul 2 d = Nat.add d (Nat.mul 1 d).
            let h_one_mul = Expr::app(one_mul.clone(), dexp.clone()); // Nat.mul 1 d = d
            let h_add_congr =
                c.nat_congr_add_l(&b, dexp.clone(), mul1_d.clone(), dexp.clone(), h_one_mul);
            // h_add_congr : Nat.add d (Nat.mul 1 d) = Nat.add d d.
            let two_mul_d = c.nat_trans(
                two_d.clone(),
                add_d_mul1d.clone(),
                add_dd.clone(),
                h_succ_mul,
                h_add_congr,
            );
            // two_mul_d : Nat.mul 2 d = Nat.add d d.
            let h_pow9_2d_eq_dd = c.nat_congr_pow9(&b, two_d.clone(), add_dd.clone(), two_mul_d);
            // h_pow9_2d_eq_dd : 9^(2d) = 9^(d+d). congr natCast :
            let cast_2d_eq_dd =
                c.natcast_congr(&b, nine_2d.clone(), nine_dd.clone(), h_pow9_2d_eq_dd);
            // aa_eq : a·a = nc(9^(2d)) := trans aa_eq1 (symm cast_2d_eq_dd).
            let cast_dd_eq_2d =
                c.symm_rat(cast_nine_2d.clone(), cast_nine_dd.clone(), cast_2d_eq_dd);
            let aa_eq = c.trans_rat(
                aa.clone(),
                cast_nine_dd.clone(),
                cast_nine_2d.clone(),
                aa_eq1,
                cast_dd_eq_2d,
            );
            // aa_eq : a·a = nc(9^(2d)).

            // ── two_sq : Rat.two·Rat.two = nc4 ──
            // `Rat.two ≡ Rat.add Rat.one Rat.one` does NOT whnf-reduce to the literal
            // `mk(ofNat 2) 1` (Rat is a quotient), so we bridge propositionally:
            //   two_eq : Rat.two = nc2  := Rat.add_natCast_one 1
            //     (its LHS Rat.add (mk(ofNat 1) 1) Rat.one is def-eq to Rat.two).
            //   Rat.two·Rat.two = nc2·Rat.two = nc2·nc2 = nc(2·2) = nc4.
            let nc2 = c.natcast(&c.nat_lit(2));
            let nc4 = c.natcast(&c.nat_lit(4));
            let two_two = c.mul(two_rat.clone(), two_rat.clone());
            let two_eq = Expr::apps(
                Expr::const_(Name::from_string("Rat.add_natCast_one"), vec![]),
                [c.nat_lit(1)],
            ); // Rat.two = nc2  (by def-eq on the LHS)
            let nc2_two = c.mul(nc2.clone(), two_rat.clone());
            let nc2_nc2 = c.mul(nc2.clone(), nc2.clone());
            let ts1 = c.congr_mul_r(
                &b,
                two_rat.clone(),
                two_rat.clone(),
                nc2.clone(),
                two_eq.clone(),
            );
            let ts2 = c.congr_mul_l(
                &b,
                nc2.clone(),
                two_rat.clone(),
                nc2.clone(),
                two_eq.clone(),
            );
            let ts3 = Expr::apps(mul_natcast.clone(), [c.nat_lit(2), c.nat_lit(2)]);
            // ts3 : nc2·nc2 = nc(Nat.mul 2 2) (= nc4 by def-eq).
            let two_sq = c.trans3_rat(
                two_two.clone(),
                nc2_two.clone(),
                nc2_nc2.clone(),
                nc4.clone(),
                ts1,
                ts2,
                ts3,
            );
            // two_sq : Rat.two·Rat.two = nc4.

            // ── den2_eq : den·den = nc(4·9^(2d))·(K·K) ──
            // den·den = (2·(a·K))·(2·(a·K)) = (2·2)·((a·K)·(a·K))   [sq_prod 2 (a·K)]
            //         = (2·2)·((a·a)·(K·K))                         [congr ((2·2)·_) (sq_prod a K)]
            //         = nc4·(nc(9^2d)·(K·K))                        [congr along two_sq, aa_eq]
            //         = (nc4·nc(9^2d))·(K·K)                        [symm assoc]
            //         = nc(4·9^2d)·(K·K)                            [congr (·(K·K)) (mul_natCast 4 (9^2d))]
            let kk_sq = c.mul(kk.clone(), kk.clone());
            let ak_sq = c.mul(ak.clone(), ak.clone());
            let aa_kk = c.mul(aa.clone(), kk_sq.clone());
            // d1 : den·den = (2·2)·((a·K)·(a·K)).
            let d1 = c.sq_prod(&b, &two_rat, &ak);
            // d2 : (a·K)·(a·K) = (a·a)·(K·K).
            let d2 = c.sq_prod(&b, &a, &kk);
            // d3 : (2·2)·((a·K)·(a·K)) = (2·2)·((a·a)·(K·K))   [congr ((2·2)·_) d2].
            let d3 = c.congr_mul_l(&b, two_two.clone(), ak_sq.clone(), aa_kk.clone(), d2);
            // d4 : (2·2)·((a·a)·(K·K)) = nc4·((a·a)·(K·K))    [congr (·((a·a)·(K·K))) two_sq].
            let nc9_kk = c.mul(cast_nine_2d.clone(), kk_sq.clone());
            let d4 = c.congr_mul_r(&b, aa_kk.clone(), two_two.clone(), nc4.clone(), two_sq);
            // d5 : nc4·((a·a)·(K·K)) = nc4·(nc(9^2d)·(K·K))    [congr (nc4·_) (congr (·(K·K)) aa_eq)].
            let inner_eq =
                c.congr_mul_r(&b, kk_sq.clone(), aa.clone(), cast_nine_2d.clone(), aa_eq);
            let d5 = c.congr_mul_l(&b, nc4.clone(), aa_kk.clone(), nc9_kk.clone(), inner_eq);
            // d6 : nc4·(nc(9^2d)·(K·K)) = (nc4·nc(9^2d))·(K·K)   [symm (assoc nc4 nc(9^2d)(K·K))].
            let nc4_nc9 = c.mul(nc4.clone(), cast_nine_2d.clone());
            let d6 = c.symm_rat(
                c.mul(nc4_nc9.clone(), kk_sq.clone()),
                c.mul(nc4.clone(), nc9_kk.clone()),
                c.mul_assoc(nc4.clone(), cast_nine_2d.clone(), kk_sq.clone()),
            );
            // d7 : (nc4·nc(9^2d))·(K·K) = nc(4·9^2d)·(K·K)   [congr (·(K·K)) (mul_natCast 4 (9^2d))].
            let head = c.natcast(&c.nmul(c.nat_lit(4), nine_2d.clone())); // nc(4·9^2d)
            let mn_4_9 = Expr::apps(mul_natcast.clone(), [c.nat_lit(4), nine_2d.clone()]);
            // mn_4_9 : nc4·nc(9^2d) = nc(Nat.mul 4 (9^2d)).
            let d7 = c.congr_mul_r(&b, kk_sq.clone(), nc4_nc9.clone(), head.clone(), mn_4_9);
            // den2_eq := den·den = nc(4·9^2d)·(K·K)  (chain d1..d7).
            let den2 = c.mul(den.clone(), den.clone());
            let head_kksq = c.mul(head.clone(), kk_sq.clone());
            let de_a = c.trans_rat(
                den2.clone(),
                c.mul(two_two.clone(), ak_sq.clone()),
                c.mul(two_two.clone(), aa_kk.clone()),
                d1,
                d3,
            );
            let de_b = c.trans_rat(
                den2.clone(),
                c.mul(two_two.clone(), aa_kk.clone()),
                c.mul(nc4.clone(), aa_kk.clone()),
                de_a,
                d4,
            );
            let de_c = c.trans_rat(
                den2.clone(),
                c.mul(nc4.clone(), aa_kk.clone()),
                c.mul(nc4.clone(), nc9_kk.clone()),
                de_b,
                d5,
            );
            let de_d = c.trans_rat(
                den2.clone(),
                c.mul(nc4.clone(), nc9_kk.clone()),
                c.mul(nc4_nc9.clone(), kk_sq.clone()),
                de_c,
                d6,
            );
            let den2_eq = c.trans_rat(
                den2.clone(),
                c.mul(nc4_nc9.clone(), kk_sq.clone()),
                head_kksq.clone(),
                de_d,
                d7,
            );
            // den2_eq : den·den = nc(4·9^2d)·(K·K).

            // ── E1 : (den·den)·K = nc(4·9^2d)·(K·(K·K)) ──
            //   (den·den)·K = (nc(4·9^2d)·(K·K))·K   [congr (·K) den2_eq]
            //              = nc(4·9^2d)·((K·K)·K)     [assoc head (K·K) K]
            //              = nc(4·9^2d)·(K·(K·K))     [congr (head·_) (assoc K K K)]
            let e1a = c.congr_mul_r(&b, kk.clone(), den2.clone(), head_kksq.clone(), den2_eq);
            let kk_kk_k = c.mul(kk_sq.clone(), kk.clone()); // (K·K)·K
            let k_kk = c.mul(kk.clone(), kk_sq.clone()); // K·(K·K)  (the size_poly cube nesting)
            let head_kkk = c.mul(head.clone(), kk_kk_k.clone());
            let e1b = c.mul_assoc(head.clone(), kk_sq.clone(), kk.clone()); // (head·(K·K))·K = head·((K·K)·K)
            let e1c = c.congr_mul_l(
                &b,
                head.clone(),
                kk_kk_k.clone(),
                k_kk.clone(),
                c.mul_assoc(kk.clone(), kk.clone(), kk.clone()),
            );
            // chain e1a;e1b;e1c.
            let dd_k = c.mul(den2.clone(), kk.clone());
            let head_kksq_k = c.mul(head_kksq.clone(), kk.clone()); // (head·(K·K))·K
            let size_lhs = c.mul(head.clone(), k_kk.clone()); // nc(4·9^2d)·(K·(K·K)) = size_poly LHS
            let e1_x = c.trans_rat(
                dd_k.clone(),
                head_kksq_k.clone(),
                head_kkk.clone(),
                e1a,
                e1b,
            );
            let e1 = c.trans_rat(dd_k.clone(), head_kkk.clone(), size_lhs.clone(), e1_x, e1c);
            // e1 : (den·den)·K = nc(4·9^2d)·(K·(K·K)).

            // ── den·dr = eps  (div_mul_cancel + comm) ──
            //   div_mul_cancel_pos eps den h_den_pos : (eps/den)·den = eps  ; comm ⟹ den·(eps/den)=eps.
            let dr_den = c.mul(dr.clone(), den.clone()); // dr·den = (eps/den)·den
            let h_drden = Expr::apps(
                div_mul_cancel.clone(),
                [eps.clone(), den.clone(), h_den_pos.clone()],
            );
            // h_drden : (eps/den)·den = eps.  comm den dr : den·dr = dr·den.
            let h_comm_dendr = c.mul_comm(den.clone(), dr.clone()); // den·dr = dr·den
            let den_dr = c.mul(den.clone(), dr.clone());
            let h_den_dr = c.trans_rat(
                den_dr.clone(),
                dr_den.clone(),
                eps.clone(),
                h_comm_dendr,
                h_drden,
            );
            // h_den_dr : den·dr = eps.

            // ── E2 : (den·den)·(dr²·B) = (eps·eps)·B ──
            //   (den·den)·((dr·dr)·B) = (den·(den·((dr·dr)·B)))  ... easier:
            //   regroup (den·den)·((dr·dr)·B) → (den·dr)·(den·dr)·B → eps·eps·B.
            //   Use: (den·den)·((dr·dr)·B) = ((den·den)·(dr·dr))·B   [symm assoc (den·den)(dr·dr) B]
            //        (den·den)·(dr·dr) = (den·dr)·(den·dr)          [symm (sq_prod' ...)]  — via sq_prod on
            //          a 4-factor rearrange: (den·den)·(dr·dr) = (den·dr)·(den·dr).
            let drdr_b = c.mul(drdr.clone(), bcast.clone()); // (dr·dr)·B
            let dd_drdr = c.mul(den2.clone(), drdr.clone()); // (den·den)·(dr·dr)
                                                             // s4 : (den·den)·((dr·dr)·B) = ((den·den)·(dr·dr))·B   [symm (assoc (den·den)(dr·dr) B)].
            let s4 = c.symm_rat(
                c.mul(dd_drdr.clone(), bcast.clone()),
                c.mul(den2.clone(), drdr_b.clone()),
                c.mul_assoc(den2.clone(), drdr.clone(), bcast.clone()),
            );
            // sq4 : (den·den)·(dr·dr) = (den·dr)·(den·dr)   [symm (interchange)].
            //   prove (den·dr)·(den·dr) = (den·den)·(dr·dr) via sq_prod-style interchange:
            //   (den·dr)·(den·dr) = (den·den)·(dr·dr)  is `sq_interchange den den dr dr`? Use:
            //   (x·y)·(x·y) = (x·x)·(y·y) is sq_prod; here x=den,y=dr gives
            //   (den·dr)·(den·dr) = (den·den)·(dr·dr).  symm gives the needed direction.
            let dendr_sq = c.mul(den_dr.clone(), den_dr.clone());
            let sq_dendr = c.sq_prod(&b, &den, &dr); // (den·dr)·(den·dr) = (den·den)·(dr·dr)
            let sq4 = c.symm_rat(dendr_sq.clone(), dd_drdr.clone(), sq_dendr);
            // sq4 : (den·den)·(dr·dr) = (den·dr)·(den·dr).
            // e2c : (den·dr)·(den·dr) = eps·eps   [congr both sides via h_den_dr].
            //   congr (·(den·dr)) h_den_dr : (den·dr)·(den·dr) = eps·(den·dr)
            //   congr (eps·_) h_den_dr     : eps·(den·dr) = eps·eps
            let eps_dendr = c.mul(eps.clone(), den_dr.clone());
            let eps_eps = c.mul(eps.clone(), eps.clone());
            let e2c1 = c.congr_mul_r(
                &b,
                den_dr.clone(),
                den_dr.clone(),
                eps.clone(),
                h_den_dr.clone(),
            );
            let e2c2 = c.congr_mul_l(
                &b,
                eps.clone(),
                den_dr.clone(),
                eps.clone(),
                h_den_dr.clone(),
            );
            let e2c = c.trans_rat(
                dendr_sq.clone(),
                eps_dendr.clone(),
                eps_eps.clone(),
                e2c1,
                e2c2,
            );
            // dd_drdr_eq_eps2 : (den·den)·(dr·dr) = eps·eps   [trans sq4 e2c].
            let dd_drdr_eq =
                c.trans_rat(dd_drdr.clone(), dendr_sq.clone(), eps_eps.clone(), sq4, e2c);
            // sB : ((den·den)·(dr·dr))·B = (eps·eps)·B   [congr (·B) dd_drdr_eq].
            let s_b = c.congr_mul_r(
                &b,
                bcast.clone(),
                dd_drdr.clone(),
                eps_eps.clone(),
                dd_drdr_eq,
            );
            // E2 := (den·den)·((dr·dr)·B) = (eps·eps)·B   [trans s4 sB].
            let dd_drdrb = c.mul(den2.clone(), drdr_b.clone());
            let eps2_b = c.mul(eps_eps.clone(), bcast.clone());
            let e2 = c.trans_rat(
                dd_drdrb.clone(),
                c.mul(dd_drdr.clone(), bcast.clone()),
                eps2_b.clone(),
                s4,
                s_b,
            );
            // E2 : (den·den)·((dr·dr)·B) = (eps·eps)·B.

            // ── size_poly bound : nc(4·9^2d)·(K·(K·K)) ≤ (eps·eps)·B ──
            // 0 ≤ K from 0 < K (le_of_lt).
            let hk0 = Expr::apps(
                Expr::const_(Name::from_string("Rat.le_of_lt"), vec![]),
                [c.rat_zero.clone(), kk.clone(), hkpos.clone()],
            );
            let sp = Expr::apps(
                size_poly.clone(),
                [
                    e.clone(),
                    kk.clone(),
                    eps.clone(),
                    hk0,
                    hepspos.clone(),
                    hlt1.clone(),
                    hguard.clone(),
                ],
            );
            // sp : nc(4·9^2d)·(K·(K·K)) ≤ (eps·eps)·B.

            // ── transport sp's LHS to (den·den)·K and RHS to (den·den)·(dr²·B) ──
            // motive_l t => t ≤ (eps·eps)·B ; subst along (symm e1) gives (den·den)·K ≤ (eps·eps)·B.
            let motive_l = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.le(t, eps2_b.clone());
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let e1_symm = c.symm_rat(dd_k.clone(), size_lhs.clone(), e1);
            let sp_l = c.subst_rat(motive_l, size_lhs.clone(), dd_k.clone(), e1_symm, sp);
            // sp_l : (den·den)·K ≤ (eps·eps)·B.
            // motive_r t => (den·den)·K ≤ t ; subst along (symm E2) gives
            //   (den·den)·K ≤ (den·den)·((dr·dr)·B).
            let motive_r = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.le(dd_k.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let e2_symm = c.symm_rat(dd_drdrb.clone(), eps2_b.clone(), e2);
            let hle = c.subst_rat(motive_r, eps2_b.clone(), dd_drdrb.clone(), e2_symm, sp_l);
            // hle : (den·den)·K ≤ (den·den)·((dr·dr)·B).

            // ── cancel : K ≤ (dr·dr)·B  := le_of_mul_le_mul_left_pos K ((dr·dr)·B) (den·den) h_dd_pos hle ──
            let proof =
                c.le_of_mul_le_left(kk.clone(), drdr_b.clone(), den2.clone(), h_dd_pos, hle);
            // proof : K ≤ (dr·dr)·B = goal_rhs (drdr_b ≡ goal_rhs).

            let r = b.mk_lam(hguard_id, BinderInfo::Default, hguard_ty, proof);
            let r = b.mk_lam(hlt1_id, BinderInfo::Default, hlt1_ty, r);
            let r = b.mk_lam(hepspos_id, BinderInfo::Default, hepspos_ty, r);
            let r = b.mk_lam(hkpos_id, BinderInfo::Default, hkpos_ty, r);
            let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), r))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.friedgut_threshold_dr_sq_lt_one :
    ///   ∀ (e : Nat) (K eps : Rat),
    ///     Rat.lt Rat.zero eps →
    ///     @LE.le Rat instLERat (Rat.mul (natCast (2^e)) eps) K →
    ///       Rat.lt (Rat.mul dr dr) (Rat.mk (Int.ofNat 1) 1)`,
    ///   where `dr := Rat.div eps (Rat.mul Rat.two (Rat.mul (natCast (Nat.pow 9 (2^(e+2)))) K))`.
    ///
    /// `dr² < 1`, the l2-core `hdd1`. With `den := 2·(natCast(9^d)·K)`,
    /// `dr = eps/den`: from the LOWER guard `2^e·eps ≤ K` (and `eps>0`),
    /// `eps ≤ K ≤ a·K < 2·(a·K) = den` (`a := natCast(9^d) ≥ 1`, `2^e ≥ 1`), so
    /// `eps < den`, hence `dr = inv(den)·eps < inv(den)·den = 1`
    /// (`mul_lt_mul_of_pos_left`, `mul_inv_cancel`), and `0 ≤ dr`, so
    /// `dr·dr < 1·1 = 1` (`Rat.mul_lt_mul`, `mul_one`). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent. No axiom
    /// added/removed.
    pub fn register_friedgut_threshold_dr_sq_lt_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_threshold_dr_sq_lt_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_nat()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.div
        self.init_rat_field_inst()?; // mul_one, mul_inv_cancel, right_distrib, one_mul, add_zero
        self.init_rat_linear_order()?; // mul_pos, lt_iff_le_not_le, zero_lt_one
        self.init_algebra_rat_div_mul_cancel()?; // (not strictly needed but pulls Rat.div carrier)
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left/right
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_le_of_mul_le_mul_left_pos()?; // le-cancel (for mul_lt_mul_of_pos_left)
        self.init_algebra_rat_inv_pos()?; // Rat.inv_pos, Rat.le_of_lt
        self.init_algebra_rat_inv_dyadic()?; // Rat.ne_zero_of_pos
        self.init_algebra_rat_mul_strict()?; // Rat.mul_lt_mul
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.register_natcast_nonneg()?; // natCast_nonneg
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow, natCast_ne_zero_of_pos
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right
        self.register_rat_zero_lt_two()?; // 0 < Rat.two
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble (1 ≤ natCast m)
        self.register_nat_ble_le_lemmas()?; // ble_refl (for 1 ≤ ...)
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ThrConsts::new();
        let nat_succ = c.nat_succ.clone();
        let two_rat = c.rat_two.clone();
        let _mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
        let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        let right_distrib = Expr::const_(Name::from_string("Rat.right_distrib"), vec![]);
        let mul_inv_cancel = Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]);
        let ne_zero_of_pos = Expr::const_(Name::from_string("Rat.ne_zero_of_pos"), vec![]);
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let natcast_ne_zero = Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
        let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
        let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let zero_lt_two = Expr::const_(Name::from_string("Rat.zero_lt_two"), vec![]);
        let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(c.nat.clone());
            let (k_id, kk) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());

            let e1n = Expr::app(nat_succ.clone(), e.clone());
            let e2n = Expr::app(nat_succ.clone(), e1n.clone());
            let dexp = c.pow2(&e2n); // d = 2^(e+2)
            let a = c.cast_pow9(&dexp); // a = natCast(9^d)
            let ak = c.mul(a.clone(), kk.clone());
            let den = c.mul(two_rat.clone(), ak.clone());
            let dr = Expr::apps(c.rat_div.clone(), [eps.clone(), den.clone()]);
            let drdr = c.mul(dr.clone(), dr.clone());
            let one_lit = c.natcast(&c.nat_lit(1)); // mk(ofNat 1) 1 = l2-core's one
            let pow_e = c.pow2(&e); // 2^e
            let q_e = c.natcast(&pow_e); // natCast(2^e)

            let heps_ty = c.lt(c.rat_zero.clone(), eps.clone());
            let guard_lo_ty = c.le(c.mul(q_e.clone(), eps.clone()), kk.clone()); // 2^e·eps ≤ K
            let concl = c.lt(drdr.clone(), one_lit.clone());

            if !for_value {
                let (heps_id, _) = b.fresh_local(heps_ty.clone());
                let (hg_id, _) = b.fresh_local(guard_lo_ty.clone());
                let r = b.mk_pi(hg_id, BinderInfo::Default, guard_lo_ty, concl);
                let r = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, r);
                let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
                let r = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), r);
                return b.finish(b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), r));
            }

            let (heps_id, heps) = b.fresh_local(heps_ty.clone());
            let (hg_id, hg) = b.fresh_local(guard_lo_ty.clone());

            // ── 0 < a := natCast(9^d) ── (mirror) ──
            let one = c.nat_lit(1);
            let mut h_1le9 = Expr::app(nat_le_refl.clone(), one.clone());
            {
                let mut cur = one.clone();
                for _ in 0..8 {
                    let nxt = Expr::app(nat_succ.clone(), cur.clone());
                    h_1le9 = Expr::apps(nat_le_step.clone(), [one.clone(), cur.clone(), h_1le9]);
                    cur = nxt;
                }
            }
            let nine_d = c.nat_pow9(&dexp);
            let one_le_9pow = Expr::apps(
                pow_le_pow_right.clone(),
                [
                    c.nat_lit(9),
                    c.nat_zero.clone(),
                    dexp.clone(),
                    h_1le9,
                    Expr::app(nat_zero_le.clone(), dexp.clone()),
                ],
            );
            let h0a = Expr::app(natcast_nonneg.clone(), nine_d.clone());
            let ha_ne = Expr::apps(
                natcast_ne_zero.clone(),
                [nine_d.clone(), one_le_9pow.clone()],
            );
            let not_a_le0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let a_le0_ty = c.le(a.clone(), c.rat_zero.clone());
                let (hle_id, hle) = g.fresh_local(a_le0_ty.clone());
                let a_eq0 = Expr::apps(
                    le_antisymm.clone(),
                    [a.clone(), c.rat_zero.clone(), hle, h0a.clone()],
                );
                g.finish_child(g.mk_lam(
                    hle_id,
                    BinderInfo::Default,
                    a_le0_ty,
                    Expr::app(ha_ne.clone(), a_eq0),
                ))
            };
            let le0a = c.le(c.rat_zero.clone(), a.clone());
            let not_le_a0 = Expr::app(not_c.clone(), c.le(a.clone(), c.rat_zero.clone()));
            let ha_pos = Expr::apps(
                iff_mpr.clone(),
                [
                    c.lt(c.rat_zero.clone(), a.clone()),
                    Expr::apps(
                        Expr::const_(Name::from_string("And"), vec![]),
                        [le0a.clone(), not_le_a0.clone()],
                    ),
                    Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), a.clone()]),
                    Expr::apps(
                        and_intro.clone(),
                        [le0a.clone(), not_le_a0.clone(), h0a.clone(), not_a_le0],
                    ),
                ],
            ); // 0 < a

            // 0 < 2^e cast, 0 < K, 0 ≤ K.
            // 1 ≤ natCast(2^e) via cast_le_of_ble 1 (2^e) (ble 1 (2^e) = true).
            //   ble 1 (2^e) = true: 1 ≤ 2^e (one_le_two_pow) ⟹ but ble needs proof; use
            //   cast_le_of_ble with the ble-eq-true from one_le_two_pow? cast_le_of_ble wants
            //   Nat.ble 1 (2^e) = true.  Derive from Nat.one_le_two_pow via le→ble:
            //   simpler: 1 ≤ natCast(2^e) := cast_le_of_ble 1 (2^e) hble where hble : ble 1 (2^e)=true.
            //   Build hble from one_le_two_pow (Nat.le 1 (2^e)) is not directly ble; instead use
            //   natCast monotone of one_le_two_pow is unavailable. Use: 0 < natCast(2^e) like `a`.
            let pow_e_nat = c.pow2(&e); // 2^e
            let one_le_2powe = Expr::app(one_le_two_pow.clone(), e.clone()); // Nat.le 1 (2^e)
            let h0qe = Expr::app(natcast_nonneg.clone(), pow_e_nat.clone()); // 0 ≤ natCast(2^e)
            let hqe_ne = Expr::apps(
                natcast_ne_zero.clone(),
                [pow_e_nat.clone(), one_le_2powe.clone()],
            );
            let not_qe_le0 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let qe_le0_ty = c.le(q_e.clone(), c.rat_zero.clone());
                let (hle_id, hle) = g.fresh_local(qe_le0_ty.clone());
                let qe_eq0 = Expr::apps(
                    le_antisymm.clone(),
                    [q_e.clone(), c.rat_zero.clone(), hle, h0qe.clone()],
                );
                g.finish_child(g.mk_lam(
                    hle_id,
                    BinderInfo::Default,
                    qe_le0_ty,
                    Expr::app(hqe_ne.clone(), qe_eq0),
                ))
            };
            let le0qe = c.le(c.rat_zero.clone(), q_e.clone());
            let not_le_qe0 = Expr::app(not_c.clone(), c.le(q_e.clone(), c.rat_zero.clone()));
            let hqe_pos = Expr::apps(
                iff_mpr.clone(),
                [
                    c.lt(c.rat_zero.clone(), q_e.clone()),
                    Expr::apps(
                        Expr::const_(Name::from_string("And"), vec![]),
                        [le0qe.clone(), not_le_qe0.clone()],
                    ),
                    Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), q_e.clone()]),
                    Expr::apps(
                        and_intro.clone(),
                        [le0qe.clone(), not_le_qe0.clone(), h0qe.clone(), not_qe_le0],
                    ),
                ],
            ); // 0 < natCast(2^e)
               // 0 < natCast(2^e)·eps.
            let qe_eps = c.mul(q_e.clone(), eps.clone());
            let h_qe_eps_pos = c.mul_pos(q_e.clone(), eps.clone(), hqe_pos, heps.clone());
            // 0 < K := lt_of_lt_of_le 0 (qe·eps) K (0<qe·eps) hg.
            let hk_pos = c.lt_of_lt_of_le(
                c.rat_zero.clone(),
                qe_eps.clone(),
                kk.clone(),
                h_qe_eps_pos,
                hg.clone(),
            );
            let hk0 = c.le_of_lt(c.rat_zero.clone(), kk.clone(), hk_pos.clone()); // 0 ≤ K
                                                                                  // 0 < a·K, 0 < den.
            let h_ak_pos = c.mul_pos(a.clone(), kk.clone(), ha_pos.clone(), hk_pos.clone());
            let h_den_pos = c.mul_pos(
                two_rat.clone(),
                ak.clone(),
                zero_lt_two.clone(),
                h_ak_pos.clone(),
            );
            let _h0_ak = c.le_of_lt(c.rat_zero.clone(), ak.clone(), h_ak_pos.clone()); // 0 ≤ a·K

            // ── 1 ≤ natCast(2^e) and 1 ≤ a := natCast(9^d) ──
            //   ble_eq_true_of_le k m (Nat.le k m) : Nat.ble k m = true ;
            //   cast_le_of_ble k m that : natCast k ≤ natCast m  (natCast 1 ≡ one_lit).
            let ble_of_le = Expr::const_(Name::from_string("Nat.ble_eq_true_of_le"), vec![]);
            let hble_1_2e = Expr::apps(
                ble_of_le.clone(),
                [one.clone(), pow_e_nat.clone(), one_le_2powe.clone()],
            );
            let h1_le_qe = Expr::apps(
                cast_le_of_ble.clone(),
                [one.clone(), pow_e_nat.clone(), hble_1_2e],
            );
            // h1_le_qe : natCast 1 ≤ natCast(2^e)  (natCast 1 ≡ one_lit).
            let hble_1_9d = Expr::apps(
                ble_of_le.clone(),
                [one.clone(), nine_d.clone(), one_le_9pow.clone()],
            );
            let h1_le_a = Expr::apps(
                cast_le_of_ble.clone(),
                [one.clone(), nine_d.clone(), hble_1_9d],
            );
            // h1_le_a : natCast 1 ≤ a.

            // ── eps ≤ a·K ──
            //   eps = 1·eps ≤ natCast(2^e)·eps   [mul_le_right (1≤natCast(2^e)) (0≤eps)]
            //   1·eps ≡ eps (def-eq one_mul); natCast(2^e)·eps ≤ K (guard hg).
            //   So eps ≤ K (le_trans), and K = 1·K ≤ a·K [mul_le_right (1≤a)(0≤K)], 1·K ≡ K.
            let h0eps = c.le_of_lt(c.rat_zero.clone(), eps.clone(), heps.clone()); // 0 ≤ eps
                                                                                   // one_lit·eps ≤ q_e·eps ; rewrite LHS one_lit·eps → eps via one_mul eps.
            let one_eps = c.mul(one_lit.clone(), eps.clone()); // one_lit·eps
            let h_oneeps_le = c.mul_le_right(
                eps.clone(),
                one_lit.clone(),
                q_e.clone(),
                h1_le_qe,
                h0eps.clone(),
            );
            //  : one_lit·eps ≤ q_e·eps.
            let h_one_mul_eps = Expr::app(one_mul.clone(), eps.clone()); // Rat.one·eps = eps (≡ one_lit·eps)
            let motive_q = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.rle(t, qe_eps.clone());
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let h_eps_le_qeeps = c.subst_rat(
                motive_q,
                one_eps.clone(),
                eps.clone(),
                h_one_mul_eps,
                h_oneeps_le,
            );
            // h_eps_le_qeeps : eps ≤ q_e·eps.
            // eps ≤ K := le_trans eps (q_e·eps) K h_eps_le_qeeps hg.
            let h_eps_le_k = Expr::apps(
                le_trans.clone(),
                [
                    eps.clone(),
                    qe_eps.clone(),
                    kk.clone(),
                    h_eps_le_qeeps,
                    hg.clone(),
                ],
            );
            // one_lit·K ≤ a·K ; rewrite LHS one_lit·K → K via one_mul K.
            let one_k = c.mul(one_lit.clone(), kk.clone());
            let h_onek_le =
                c.mul_le_right(kk.clone(), one_lit.clone(), a.clone(), h1_le_a, hk0.clone());
            let h_one_mul_k = Expr::app(one_mul.clone(), kk.clone()); // Rat.one·K = K
            let motive_k = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.rle(t, ak.clone());
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let h_k_le_ak =
                c.subst_rat(motive_k, one_k.clone(), kk.clone(), h_one_mul_k, h_onek_le);
            // h_k_le_ak : K ≤ a·K.
            // eps ≤ a·K := le_trans eps K (a·K) h_eps_le_k h_k_le_ak.
            let h_eps_le_ak = Expr::apps(
                le_trans.clone(),
                [eps.clone(), kk.clone(), ak.clone(), h_eps_le_k, h_k_le_ak],
            );

            // ── a·K < den = 2·(a·K) ──
            //   a·K = (a·K)+0 < (a·K)+(a·K)   [add_lt_add_left 0 (a·K) (a·K) (0<a·K)]   (LHS ≡ a·K via add_zero)
            //   (a·K)+(a·K) = 2·(a·K) = den   [symm two_mul_eq_add: 2·x = x+x]
            // two_x_eq : Rat.two·(a·K) = (a·K)+(a·K)   via right_distrib 1 1 (a·K) (Rat.two ≡ 1+1) + one_mul.
            //   right_distrib 1 1 (a·K) : (1+1)·(a·K) = 1·(a·K) + 1·(a·K).  Rat.two ≡ 1+1, and
            //   1·(a·K) ≡ a·K (def-eq one_mul), so the RHS is def-eq (a·K)+(a·K); the equality
            //   `den = (a·K)+(a·K)` therefore holds by `right_distrib Rat.one Rat.one (a·K)`
            //   retyped against `den = (a·K)+(a·K)` (both ends def-eq).
            let ak_plus_ak = c.add(ak.clone(), ak.clone());
            let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
            // den_eq_sum : den = (a·K)+(a·K).
            //   rd : den = 1·(a·K) + 1·(a·K)   [right_distrib 1 1 (a·K); LHS (1+1)·(a·K) ≡ den]
            //   one_mul (a·K) : 1·(a·K) = a·K   ⟹ congr both summands.
            let one_ak = c.mul(rat_one.clone(), ak.clone()); // 1·(a·K)
            let one_ak_sum = c.add(one_ak.clone(), one_ak.clone());
            let rd = Expr::apps(
                right_distrib.clone(),
                [rat_one.clone(), rat_one.clone(), ak.clone()],
            );
            // rd : den = 1·(a·K) + 1·(a·K)  (LHS retyped to den by def-eq).
            let h_one_mul_ak = Expr::app(one_mul.clone(), ak.clone()); // 1·(a·K) = a·K
                                                                       // congrL : 1·(a·K)+1·(a·K) = a·K + (1·(a·K))   [congr (·+1·(a·K)) one_mul]
                                                                       //   then congrR : a·K + 1·(a·K) = a·K + a·K    [congr (a·K +·) one_mul]
            let congr_l = {
                let f = {
                    let mut g = EnvDeclBuilder::child_of(&b);
                    let (z_id, z) = g.fresh_local(c.rat.clone());
                    let body = c.add(z, one_ak.clone());
                    g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.congr_arg(
                    c.rat.clone(),
                    c.rat.clone(),
                    one_ak.clone(),
                    ak.clone(),
                    f,
                    h_one_mul_ak.clone(),
                )
            };
            let ak_plus_oneak = c.add(ak.clone(), one_ak.clone());
            let congr_r = {
                let f = {
                    let mut g = EnvDeclBuilder::child_of(&b);
                    let (z_id, z) = g.fresh_local(c.rat.clone());
                    let body = c.add(ak.clone(), z);
                    g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.congr_arg(
                    c.rat.clone(),
                    c.rat.clone(),
                    one_ak.clone(),
                    ak.clone(),
                    f,
                    h_one_mul_ak,
                )
            };
            // sum_simp : 1·(a·K)+1·(a·K) = (a·K)+(a·K).
            let sum_simp = c.trans_rat(
                one_ak_sum.clone(),
                ak_plus_oneak.clone(),
                ak_plus_ak.clone(),
                congr_l,
                congr_r,
            );
            // den_eq_sum : den = (a·K)+(a·K)  [trans rd sum_simp].
            let den_eq_sum = c.trans_rat(
                den.clone(),
                one_ak_sum.clone(),
                ak_plus_ak.clone(),
                rd,
                sum_simp,
            );
            // sum_eq_den : (a·K)+(a·K) = den.
            let sum_eq_den = c.symm_rat(den.clone(), ak_plus_ak.clone(), den_eq_sum);

            // ak_lt_sum : a·K < (a·K)+(a·K).
            //   add_lt_add_left 0 (a·K) (a·K) (0<a·K) : (a·K)+0 < (a·K)+(a·K).
            //   rewrite LHS (a·K)+0 → a·K via add_zero (a·K).
            let ak_plus_0 = c.add(ak.clone(), c.rat_zero.clone());
            let add_lt =
                c.add_lt_add_left(c.rat_zero.clone(), ak.clone(), ak.clone(), h_ak_pos.clone());
            let h_addzero = Expr::app(add_zero.clone(), ak.clone()); // (a·K)+0 = a·K
            let motive_lt = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.lt(t, ak_plus_ak.clone());
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let ak_lt_sum =
                c.subst_rat(motive_lt, ak_plus_0.clone(), ak.clone(), h_addzero, add_lt);
            // ak_lt_sum : a·K < (a·K)+(a·K).
            // ak_lt_den : a·K < den  [rewrite RHS sum→den via sum_eq_den].
            let motive_lt2 = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.lt(ak.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let ak_lt_den = c.subst_rat(
                motive_lt2,
                ak_plus_ak.clone(),
                den.clone(),
                sum_eq_den,
                ak_lt_sum,
            );
            // ak_lt_den : a·K < den.

            // ── eps < den := lt_of_le_of_lt eps (a·K) den (eps≤a·K) (a·K<den) ──
            let h_eps_lt_den =
                c.lt_of_le_of_lt(eps.clone(), ak.clone(), den.clone(), h_eps_le_ak, ak_lt_den);

            // ── dr < 1 ──
            //   0 < inv den ; mul_lt_mul_of_pos_left eps den (inv den) (eps<den)(0<inv den)
            //     : (inv den)·eps < (inv den)·den.
            //   (inv den)·eps = eps·inv den = dr (comm; dr ≡ eps·inv den) ;
            //   (inv den)·den = den·inv den = 1 (comm + mul_inv_cancel).
            let inv_den = c.inv(den.clone());
            let h_inv_pos = c.inv_pos(den.clone(), h_den_pos.clone()); // 0 < inv den
            let h_inv_nn = c.le_of_lt(c.rat_zero.clone(), inv_den.clone(), h_inv_pos.clone()); // 0 ≤ inv den
            let mul_lt =
                c.mul_lt_mul_of_pos_left(&b, &eps, &den, &inv_den, h_eps_lt_den, h_inv_pos);
            // mul_lt : (inv den)·eps < (inv den)·den.
            let invden_eps = c.mul(inv_den.clone(), eps.clone());
            let invden_den = c.mul(inv_den.clone(), den.clone());
            // (inv den)·eps = eps·(inv den) [comm] ; eps·inv den ≡ dr (Rat.div def). Use comm then
            //   the result is eps·inv den which is def-eq to dr; rewrite mul_lt's LHS.
            let comm_invden_eps = c.mul_comm(inv_den.clone(), eps.clone()); // (inv den)·eps = eps·(inv den)
            let eps_invden = c.mul(eps.clone(), inv_den.clone());
            // (inv den)·den = den·(inv den) [comm] = 1 [mul_inv_cancel den (den≠0)].
            let comm_invden_den = c.mul_comm(inv_den.clone(), den.clone()); // (inv den)·den = den·(inv den)
            let den_invden = c.mul(den.clone(), inv_den.clone());
            let hden_ne = Expr::apps(ne_zero_of_pos.clone(), [den.clone(), h_den_pos.clone()]); // den ≠ 0
            let den_inv_eq_one = Expr::apps(mul_inv_cancel.clone(), [den.clone(), hden_ne]); // den·inv den = 1
                                                                                             // chain (inv den)·den = den·inv den = 1.
            let invden_den_eq_one = c.trans_rat(
                invden_den.clone(),
                den_invden.clone(),
                one_lit.clone(),
                comm_invden_den,
                den_inv_eq_one,
            );
            // Rewrite mul_lt : (inv den)·eps < (inv den)·den  →  eps·inv den < 1.
            //   subst LHS (inv den)·eps → eps·inv den via comm_invden_eps ;
            //   subst RHS (inv den)·den → 1 via invden_den_eq_one.
            let motive_lhs = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.lt(t, invden_den.clone());
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let mul_lt_l = c.subst_rat(
                motive_lhs,
                invden_eps.clone(),
                eps_invden.clone(),
                comm_invden_eps,
                mul_lt,
            );
            // mul_lt_l : eps·inv den < (inv den)·den.
            let motive_rhs = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.lt(eps_invden.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let dr_lt_one = c.subst_rat(
                motive_rhs,
                invden_den.clone(),
                one_lit.clone(),
                invden_den_eq_one,
                mul_lt_l,
            );
            // dr_lt_one : eps·inv den < 1.  eps·inv den ≡ dr (Rat.div def-eq), so this is dr < 1.

            // ── 0 ≤ dr := mul_nonneg eps (inv den) (0≤eps)(0≤inv den) ──   (dr ≡ eps·inv den)
            let h_dr_nn = c.mul_nonneg(eps.clone(), inv_den.clone(), h0eps.clone(), h_inv_nn);
            // h_dr_nn : 0 ≤ eps·inv den (≡ 0 ≤ dr).

            // ── dr·dr < 1·1 ── mul_lt_mul dr 1 dr 1 (0≤dr)(dr<1)(0≤dr)(dr<1) ──
            //   stated at eps·inv den for dr to match h_dr_nn / dr_lt_one types.
            let drv = eps_invden.clone(); // = dr (def-eq)
            let drdr_v = c.mul(drv.clone(), drv.clone());
            let one_one = c.mul(one_lit.clone(), one_lit.clone());
            let mlm = c.mul_lt_mul(
                drv.clone(),
                one_lit.clone(),
                drv.clone(),
                one_lit.clone(),
                h_dr_nn.clone(),
                dr_lt_one.clone(),
                h_dr_nn,
                dr_lt_one,
            );
            // mlm : (eps·inv den)·(eps·inv den) < 1·1.
            // 1·1 = 1 [mul_one one_lit].   subst RHS 1·1 → 1.
            let one_one_eq_one = Expr::app(mul_one.clone(), one_lit.clone()); // one_lit·1 = one_lit ; 1 ≡ one_lit
            let motive_final = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = g.fresh_local(c.rat.clone());
                let body = c.lt(drdr_v.clone(), t);
                g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let proof = c.subst_rat(
                motive_final,
                one_one.clone(),
                one_lit.clone(),
                one_one_eq_one,
                mlm,
            );
            // proof : (eps·inv den)·(eps·inv den) < one_lit.  This is def-eq to dr·dr < one_lit
            // (dr ≡ eps·inv den ≡ Rat.div eps den), the goal `concl`.

            let r = b.mk_lam(hg_id, BinderInfo::Default, guard_lo_ty, proof);
            let r = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, r);
            let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), r))
        };

        let ty = mk(false);
        let value = mk(true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.friedgut_boolean_case_threshold` — the THRESHOLD (`n > B`)
    /// branch of the v3 Friedgut junta theorem. See the module docs for the full
    /// statement; its `Exists` predicate is BYTE-IDENTICAL to
    /// `friedgut_l2_faithful_body_v3`. Witness `J := thresholdJ n f (dr·dr)`,
    /// `dr := lowDr (2^(e+2)) K eps`. MASS via `friedgut_l2_core`, SIZE via
    /// `influence_threshold_card_le` + `setSize_eq_natCast` +
    /// `friedgut_threshold_size_rearrange` + `Rat.le_of_natCast_le_natCast`.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    /// No axiom added/removed.
    pub fn register_friedgut_boolean_case_threshold(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_boolean_case_threshold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.init_rat_field_inst()?;
        self.init_rat_linear_order()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.div, Rat.add_halves
        self.init_algebra_rat_inv_pos()?; // Rat.le_of_lt
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_lt_of_le
        self.register_rat_le_trans_proof()?;
        self.register_set_size_nat()?;
        self.register_not_subset_mask()?;
        self.register_subset_sum()?;
        self.register_natcast_nonneg()?;
        self.register_expect_one_theorems()?; // one_le_two_pow, natCast_ne_zero_of_pos
        self.register_nat_pow_le_pow_right_proof()?;
        self.register_rat_zero_lt_two()?;
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_nat_arith_order_proofs()?; // Nat.add_le_add_left, Nat.succ_le_succ
        self.register_nat_pow_two_succ_proof()?; // Nat.pow_two_succ
        self.register_nat_pow_add_proof()?; // Nat.pow_add (8·2^(e+2)=2^(e+5))
        self.register_nat_eight_mul_pow_two_add_two_le_proof()?; // 8·2^(e+2) ≤ 48·2^e
        self.register_nat_mul_comm_proof()?;
        // MASS bricks.
        self.init_boolean_analysis_friedgut_l2_core()?;
        self.init_boolean_analysis_friedgut_low_budget()?; // friedgut_low_budget_cancel
        self.register_friedgut_high_mass_budget()?;
        self.register_rat_pow_nat_nine_eq_natcast()?;
        self.register_friedgut_threshold_high_pre()?;
        self.register_influence_nonneg()?;
        self.init_boolean_analysis_friedgut_threshold_j()?; // thresholdJ + membership lemmas
        self.register_friedgut_threshold_dr_sq_lt_one()?;
        self.register_total_influence_nonneg()?; // 0 ≤ I[f]
                                                 // SIZE bricks.
        self.register_influence_threshold_card_le()?;
        self.register_set_size_eq_natcast()?;
        self.register_friedgut_threshold_size_rearrange()?;
        self.register_rat_le_of_natcast_le_natcast_proof()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let value = case_threshold_build(self, true)?;
        let type_ = case_threshold_build(self, false)?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// `fun S => ind(notSubsetMask n S J)·(f̂ S·f̂ S)` — the v3 masked-mass integrand
/// (byte-identical to `friedgut_l2_faithful_body_v3`'s `mass_fn` and
/// `friedgut_l2_core`'s `full_fn`).
fn ct_mass_fn(c: &ThrConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        n.clone(),
    );
    let (s_id, s) = b.fresh_local(hcp.clone());
    let mask = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.notSubsetMask"), vec![]),
        [n.clone(), s.clone(), j.clone()],
    );
    let coeff = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
        [n.clone(), f.clone(), s.clone()],
    );
    let body = c.mul(c.ind_of(mask), c.mul(coeff.clone(), coeff));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// Build the `friedgut_boolean_case_threshold` type (`for_value=false`) / proof
/// (`for_value=true`). Hand-constructed `Expr`, no tactics.
fn case_threshold_build(env: &Environment, for_value: bool) -> Result<Expr, EnvError> {
    let _ = env;
    let c = ThrConsts::new();
    let u1 = Level::succ(Level::zero());
    let nat_succ = c.nat_succ.clone();
    let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
    let bool_fn = c.bool_fn.clone();
    let total_influence = Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]);
    let set_size_nat = Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]);
    let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
    let threshold_j = Expr::const_(Name::from_string("BoolAnalysis.thresholdJ"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let exists_c = Expr::const_(Name::from_string("Exists"), vec![u1.clone()]);
    let exists_intro = Expr::const_(Name::from_string("Exists.intro"), vec![u1.clone()]);
    let and_c = Expr::const_(Name::from_string("And"), vec![]);
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
    let and_right = Expr::const_(Name::from_string("And.right"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = Expr::app(bool_fn.clone(), n.clone());
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (k_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (e_id, e) = b.fresh_local(c.nat.clone());

    let hcp_n = Expr::app(hcpoint.clone(), n.clone());
    let infl = Expr::apps(total_influence.clone(), [n.clone(), f.clone()]);
    let pow_e = c.pow2(&e); // 2^e
    let e1n = Expr::app(nat_succ.clone(), e.clone());
    let pow_e1 = c.pow2(&e1n); // 2^(e+1)
    let budget = c.nmul(c.nat_lit(48), pow_e.clone()); // 48·2^e
    let big_b = Expr::apps(
        Expr::const_(Name::from_string("Nat.pow"), vec![]),
        [c.nat_lit(2), budget.clone()],
    ); // 2^(48·2^e)

    let guard_lo = c.le(c.mul(c.natcast(&pow_e), eps.clone()), kk.clone());
    let guard_hi = c.le(kk.clone(), c.mul(c.natcast(&pow_e1), eps.clone()));
    let guard_ty = Expr::apps(and_c.clone(), [guard_lo.clone(), guard_hi.clone()]);

    let hi_ty = c.le(infl.clone(), kk.clone()); // I ≤ K
    let heps_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let heps1_ty = c.lt(eps.clone(), c.rat_one()); // eps < 1  (Rat.one spelling per v3? v3 uses Rat.lt eps 1)
    let hn_ty = Expr::apps(nat_lt.clone(), [big_b.clone(), n.clone()]); // 2^(48·2^e) < n

    // Exists predicate (byte-match v3 body).
    let pred = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = g.fresh_local(hcp_n.clone());
        let size_concl = Expr::apps(
            nat_le.clone(),
            [
                Expr::apps(set_size_nat.clone(), [n.clone(), j.clone()]),
                big_b.clone(),
            ],
        );
        let mass = Expr::apps(
            subset_sum.clone(),
            [n.clone(), ct_mass_fn(&c, &g, &n, &f, &j)],
        );
        let mass_concl = c.le(mass, eps.clone());
        let and = Expr::apps(and_c.clone(), [size_concl, mass_concl]);
        g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcp_n.clone(), and))
    };
    let exists_goal = Expr::apps(exists_c.clone(), [hcp_n.clone(), pred.clone()]);

    if !for_value {
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());
        let (heps1_id, _) = b.fresh_local(heps1_ty.clone());
        let (hg_id, _) = b.fresh_local(guard_ty.clone());
        let (hn_id, _) = b.fresh_local(hn_ty.clone());
        let r = b.mk_pi(hn_id, BinderInfo::Default, hn_ty, exists_goal);
        let r = b.mk_pi(hg_id, BinderInfo::Default, guard_ty, r);
        let r = b.mk_pi(heps1_id, BinderInfo::Default, heps1_ty, r);
        let r = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, r);
        let r = b.mk_pi(hi_id, BinderInfo::Default, hi_ty, r);
        let r = b.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), r);
        let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
        let r = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), r);
        let r = b.mk_pi(f_id, BinderInfo::Default, bf_ty, r);
        return Ok(b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r)));
    }

    // ── value ──
    let (hi_id, hi) = b.fresh_local(hi_ty.clone());
    let (heps_id, heps) = b.fresh_local(heps_ty.clone());
    let (heps1_id, heps1) = b.fresh_local(heps1_ty.clone());
    let (hg_id, hg) = b.fresh_local(guard_ty.clone());
    let (hn_id, hn) = b.fresh_local(hn_ty.clone());

    // d := 2^(e+2) ; a := natCast(9^d) ; den := 2·(a·K) ; dr := eps/den ; tau := dr·dr.
    let e2n = Expr::app(nat_succ.clone(), e1n.clone());
    let dexp = c.pow2(&e2n);
    let a = c.cast_pow9(&dexp);
    let ak = c.mul(a.clone(), kk.clone());
    let den = c.mul(c.rat_two.clone(), ak.clone());
    let dr = Expr::apps(c.rat_div.clone(), [eps.clone(), den.clone()]);
    let tau = c.mul(dr.clone(), dr.clone());
    let jj = Expr::apps(threshold_j.clone(), [n.clone(), f.clone(), tau.clone()]); // J = thresholdJ n f tau

    // guard projections.
    let g_lo = Expr::apps(
        and_left.clone(),
        [guard_lo.clone(), guard_hi.clone(), hg.clone()],
    ); // 2^e·eps ≤ K
    let g_hi = Expr::apps(
        and_right.clone(),
        [guard_lo.clone(), guard_hi.clone(), hg.clone()],
    ); // K ≤ 2^(e+1)·eps

    // Const handles for the assembly.
    let l2_core = Expr::const_(Name::from_string("BoolAnalysis.friedgut_l2_core"), vec![]);
    let low_cancel = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_low_budget_cancel"),
        vec![],
    );
    let high_budget = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_high_mass_budget"),
        vec![],
    );
    let high_pre = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_threshold_high_pre"),
        vec![],
    );
    let pow9_bridge = Expr::const_(Name::from_string("Rat.powNat_nine_eq_natCast"), vec![]);
    let influence_nonneg = Expr::const_(Name::from_string("BoolAnalysis.influence_nonneg"), vec![]);
    let thr_not_mem = Expr::const_(
        Name::from_string("BoolAnalysis.thresholdJ_not_mem_le"),
        vec![],
    );
    let thr_mem = Expr::const_(Name::from_string("BoolAnalysis.thresholdJ_mem_le"), vec![]);
    let dr_sq_lt_one = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_threshold_dr_sq_lt_one"),
        vec![],
    );
    let total_infl_nn = Expr::const_(
        Name::from_string("BoolAnalysis.total_influence_nonneg"),
        vec![],
    );
    let card_le = Expr::const_(
        Name::from_string("BoolAnalysis.influence_threshold_card_le"),
        vec![],
    );
    let setsize_natcast =
        Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]);
    let size_rearr = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_threshold_size_rearrange"),
        vec![],
    );
    let le_of_natcast = Expr::const_(Name::from_string("Rat.le_of_natCast_le_natCast"), vec![]);
    let add_halves = Expr::const_(Name::from_string("Rat.add_halves"), vec![]);
    let div_pos = Expr::const_(Name::from_string("Rat.div_pos"), vec![]);
    let zero_lt_two = Expr::const_(Name::from_string("Rat.zero_lt_two"), vec![]);
    let fin_c = c.fin.clone();
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
    let set_size = Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]);

    // half := Rat.div eps Rat.two = eL = eH (byte-match cancel's eps/2).
    let half = Expr::apps(c.rat_div.clone(), [eps.clone(), c.rat_two.clone()]);

    // ── basic positivity ──
    // 0 < a := natCast(9^d).
    let one_le_9pow = {
        let one = c.nat_lit(1);
        let mut h_1le9 = Expr::app(
            Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            one.clone(),
        );
        {
            let mut cur = one.clone();
            for _ in 0..8 {
                let nxt = Expr::app(nat_succ.clone(), cur.clone());
                h_1le9 = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                    [one.clone(), cur.clone(), h_1le9],
                );
                cur = nxt;
            }
        }
        Expr::apps(
            Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
            [
                c.nat_lit(9),
                c.nat_zero.clone(),
                dexp.clone(),
                h_1le9,
                Expr::app(
                    Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                    dexp.clone(),
                ),
            ],
        )
    };
    let pos_atom = |m_nat: &Expr, one_le: Expr, b: &EnvDeclBuilder| -> Expr {
        let m = c.natcast(m_nat);
        let h0m = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
            m_nat.clone(),
        );
        let hm_ne = Expr::apps(
            Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]),
            [m_nat.clone(), one_le],
        );
        let not_m_le0 = {
            let mut g = EnvDeclBuilder::child_of(b);
            let m_le0_ty = c.le(m.clone(), c.rat_zero.clone());
            let (hle_id, hle) = g.fresh_local(m_le0_ty.clone());
            let m_eq0 = Expr::apps(
                Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]),
                [m.clone(), c.rat_zero.clone(), hle, h0m.clone()],
            );
            g.finish_child(g.mk_lam(
                hle_id,
                BinderInfo::Default,
                m_le0_ty,
                Expr::app(hm_ne.clone(), m_eq0),
            ))
        };
        let le0m = c.le(c.rat_zero.clone(), m.clone());
        let not_le_m0 = Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            c.le(m.clone(), c.rat_zero.clone()),
        );
        Expr::apps(
            Expr::const_(Name::from_string("Iff.mpr"), vec![]),
            [
                c.lt(c.rat_zero.clone(), m.clone()),
                Expr::apps(and_c.clone(), [le0m.clone(), not_le_m0.clone()]),
                Expr::apps(
                    Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
                    [c.rat_zero.clone(), m.clone()],
                ),
                Expr::apps(
                    and_intro.clone(),
                    [le0m.clone(), not_le_m0.clone(), h0m.clone(), not_m_le0],
                ),
            ],
        )
    };
    let ha_pos = pos_atom(&c.nat_pow9(&dexp), one_le_9pow, &b); // 0 < a
    let one_le_2pe = Expr::app(
        Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
        e.clone(),
    );
    let hqe_pos = pos_atom(&pow_e, one_le_2pe, &b); // 0 < natCast(2^e)
                                                    // 0 < natCast(2^e)·eps  ⟹  0 < K.
    let qe_eps = c.mul(c.natcast(&pow_e), eps.clone());
    let h_qe_eps_pos = c.mul_pos(c.natcast(&pow_e), eps.clone(), hqe_pos, heps.clone());
    let hk_pos = c.lt_of_lt_of_le(
        c.rat_zero.clone(),
        qe_eps.clone(),
        kk.clone(),
        h_qe_eps_pos,
        g_lo.clone(),
    );
    let _hk0 = c.le_of_lt(c.rat_zero.clone(), kk.clone(), hk_pos.clone()); // 0 ≤ K
                                                                           // 0 < a·K, 0 < den.
    let h_ak_pos = c.mul_pos(a.clone(), kk.clone(), ha_pos, hk_pos.clone());
    let h_den_pos = c.mul_pos(c.rat_two.clone(), ak.clone(), zero_lt_two.clone(), h_ak_pos);
    let _ = (div_pos.clone(), zero_lt_two);
    // 0 < dr, 0 < tau = dr·dr, 0 ≤ dr, 0 ≤ tau.
    let h_dr_pos = Expr::apps(
        div_pos.clone(),
        [eps.clone(), den.clone(), heps.clone(), h_den_pos.clone()],
    ); // 0 < dr
    let h_tau_pos = c.mul_pos(dr.clone(), dr.clone(), h_dr_pos.clone(), h_dr_pos.clone()); // 0 < tau
    let h_dr_nn = c.le_of_lt(c.rat_zero.clone(), dr.clone(), h_dr_pos.clone()); // 0 ≤ dr
    let h_tau_nn = c.le_of_lt(c.rat_zero.clone(), tau.clone(), h_tau_pos.clone()); // 0 ≤ tau
                                                                                   // 0 ≤ I, I ≤ K.
    let h_infl_nn = Expr::apps(total_infl_nn.clone(), [n.clone(), f.clone()]); // 0 ≤ I

    // ════════ MASS via friedgut_l2_core ════════
    // hd : 0 ≤ dr ; hdd0 : 0 ≤ dr·dr ; hdd1 : dr·dr < 1 ; h0 : ∀i,0≤Inf ;
    // h1m : ∀i, bnot(J i)=true → Inf ≤ dr·dr ; hlow : 9^d·(dr·I)≤eL ;
    // hhigh : M≤eH ; hsum : eL+eH≤eps.
    let hd = h_dr_nn.clone();
    let hdd0 = h_tau_nn.clone();
    // hdd1 : dr·dr < 1 := dr_sq_lt_one e K eps heps g_lo.
    let hdd1 = Expr::apps(
        dr_sq_lt_one.clone(),
        [
            e.clone(),
            kk.clone(),
            eps.clone(),
            heps.clone(),
            g_lo.clone(),
        ],
    );
    // h0 : ∀ i, 0 ≤ Influence n f i := fun i => influence_nonneg n f i.
    let h0 = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let fin_n = Expr::app(fin_c.clone(), n.clone());
        let (i_id, i) = g.fresh_local(fin_n.clone());
        let body = Expr::apps(influence_nonneg.clone(), [n.clone(), f.clone(), i]);
        g.finish_child(g.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    // h1m : ∀ i, bnot(J i)=true → Inf ≤ tau := fun i => thresholdJ_not_mem_le n f tau i.
    let h1m = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let fin_n = Expr::app(fin_c.clone(), n.clone());
        let (i_id, i) = g.fresh_local(fin_n.clone());
        let body = Expr::apps(thr_not_mem.clone(), [n.clone(), f.clone(), tau.clone(), i]);
        g.finish_child(g.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    // hlow : 9^d·(dr·I) ≤ eL  (eL = half).
    //   cancel : natCast(9^d)·(dr·I) ≤ eps/2  := low_cancel d K eps I hk_pos heps h_infl_nn hi.
    let cancel = Expr::apps(
        low_cancel.clone(),
        [
            dexp.clone(),
            kk.clone(),
            eps.clone(),
            infl.clone(),
            hk_pos.clone(),
            heps.clone(),
            h_infl_nn.clone(),
            hi.clone(),
        ],
    );
    //   bridge : powNat(ofNat 9, d) = natCast(9^d).  subst LHS factor.
    //   l2-core's hlow LHS is (powNat(ofNat 9,d))·(dr·I); rewrite from natCast(9^d)·(dr·I).
    let pow9_rat_d = c.pow9_rat(&dexp); // powNat(ofNat 9) d
    let cast_pow9_d = c.cast_pow9(&dexp); // natCast(9^d)
    let dr_i = c.mul(dr.clone(), infl.clone());
    let bridge = Expr::apps(pow9_bridge.clone(), [dexp.clone()]); // powNat(ofNat 9,d) = natCast(9^d)
                                                                  // motive t => t·(dr·I) ≤ half ; subst (a := natCast(9^d), b := powNat...) along (symm bridge).
    let bridge_symm = c.symm_rat(pow9_rat_d.clone(), cast_pow9_d.clone(), bridge); // natCast(9^d) = powNat... ? bridge : powNat = natCast, symm : natCast = powNat
    let motive_low = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = g.fresh_local(c.rat.clone());
        let body = c.le(c.mul(t, dr_i.clone()), half.clone());
        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let hlow = c.subst_rat(
        motive_low,
        cast_pow9_d.clone(),
        pow9_rat_d.clone(),
        bridge_symm,
        cancel,
    );
    // hlow : powNat(ofNat 9,d)·(dr·I) ≤ half.

    // ════════ HIGH band : hhigh : M_{≥d+1} ≤ eH (= half) ════════
    let nle = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);
    let npow =
        |x: Expr, k: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.pow"), vec![]), [x, k]);
    let nmul =
        |x: Expr, y: Expr| Expr::apps(Expr::const_(Name::from_string("Nat.mul"), vec![]), [x, y]);
    let nat_le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
    let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let add_le_add_left = Expr::const_(Name::from_string("Nat.add_le_add_left"), vec![]);
    let mul_le_mul_right = Expr::const_(Name::from_string("Nat.mul_le_mul_right"), vec![]);
    let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
    let pow_two_succ = Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]);
    let eight_le = Expr::const_(
        Name::from_string("Nat.eight_mul_pow_two_add_two_le"),
        vec![],
    );
    let nat_mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
    let nat_subst = Expr::const_(Name::from_string("Eq.subst"), vec![u1.clone()]);
    let nat_symm = Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]);
    let two_n = c.nat_lit(2);
    let one_nat = c.nat_lit(1);
    let d_succ = Expr::app(nat_succ.clone(), dexp.clone()); // d+1 = succ(2^(e+2))
    let pow_d_succ = npow(two_n.clone(), d_succ.clone()); // 2^(d+1)
    let pow_budget = npow(two_n.clone(), budget.clone()); // 2^(48·2^e) = big_b
    let one_le_2pe2 = Expr::app(
        Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
        e2n.clone(),
    ); // 1 ≤ 2^(e+2)

    // 1 ≤ 8 (Nat.le.step^7 of refl 1) ; 2 ≤ 8 (step^6 of refl 2).
    let mk_le_lit = |lo_n: u64, hi_n: u64| -> Expr {
        let lo = c.nat_lit(lo_n);
        let mut h = Expr::app(nat_le_refl.clone(), lo.clone());
        let mut cur = lo.clone();
        for _ in 0..(hi_n - lo_n) {
            let nxt = Expr::app(nat_succ.clone(), cur.clone());
            h = Expr::apps(nat_le_step.clone(), [lo.clone(), cur.clone(), h]);
            cur = nxt;
        }
        h
    };
    let h_2_le_8 = mk_le_lit(2, 8); // 2 ≤ 8

    // STEP A : Nat.le (succ(2^(e+2))) (48·2^e).
    let pow_e2_plus_pe2 = nmul(c.nat_lit(2), dexp.clone()); // 2·2^(e+2)  (used as add-pair below)
    let _ = pow_e2_plus_pe2;
    let _add_pe2_1 = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [dexp.clone(), one_nat.clone()],
    ); // 2^(e+2)+1
    let add_pe2_pe2 = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [dexp.clone(), dexp.clone()],
    ); // 2^(e+2)+2^(e+2)
       // a1 : 2^(e+2)+1 ≤ 2^(e+2)+2^(e+2)  := add_le_add_left 1 (2^(e+2)) (1≤2^(e+2)) (2^(e+2)).
    let a1 = Expr::apps(
        add_le_add_left.clone(),
        [
            one_nat.clone(),
            dexp.clone(),
            one_le_2pe2.clone(),
            dexp.clone(),
        ],
    );
    // pts : 2^(e+3) = 2^(e+2)+2^(e+2)  := pow_two_succ (e+2).
    let exp_e3 = Expr::app(nat_succ.clone(), e2n.clone()); // e+3 = succ(e+2)
    let pow_e3 = npow(two_n.clone(), exp_e3.clone()); // 2^(e+3)
    let pts = Expr::apps(pow_two_succ.clone(), [e2n.clone()]); // 2^(e+3) = 2^(e+2)+2^(e+2)
    let pts_symm = Expr::apps(
        nat_symm.clone(),
        [c.nat.clone(), pow_e3.clone(), add_pe2_pe2.clone(), pts],
    ); // 2^(e+2)+2^(e+2) = 2^(e+3)
       // a2 : succ(2^(e+2)) ≤ 2^(e+3)  := subst (motive t => succ(2^(e+2)) ≤ t) (along pts_symm) a1.
       //   a1 : 2^(e+2)+1 ≤ 2^(e+2)+2^(e+2) ; (2^(e+2)+1 ≡ succ(2^(e+2)) def-eq).
    let motive_a2 = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = g.fresh_local(c.nat.clone());
        let body = nle(d_succ.clone(), t);
        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let a2 = Expr::apps(
        nat_subst.clone(),
        [
            c.nat.clone(),
            motive_a2,
            add_pe2_pe2.clone(),
            pow_e3.clone(),
            pts_symm,
            a1,
        ],
    );
    // a2 : Nat.le (succ(2^(e+2))) (2^(e+3)).
    // a3 : 2^(e+3) ≤ 8·2^(e+2).
    //   2^(e+3) ≡ 2^(e+2)·2 (Nat.pow mult on RIGHT) ; mul_comm (2^(e+2)) 2 : 2^(e+2)·2 = 2·2^(e+2).
    //   mul_le_mul_right 2 8 (2^(e+2)) (2≤8) : 2·2^(e+2) ≤ 8·2^(e+2).
    //   rewrite LHS 2·2^(e+2) → 2^(e+3) via (symm comm) and (def-eq 2^(e+3) ≡ 2^(e+2)·2).
    let pe2_mul_2 = nmul(dexp.clone(), c.nat_lit(2)); // 2^(e+2)·2  (≡ 2^(e+3))
    let two_mul_pe2 = nmul(c.nat_lit(2), dexp.clone()); // 2·2^(e+2)
    let eight_mul_pe2 = nmul(c.nat_lit(8), dexp.clone()); // 8·2^(e+2)
    let comm_pe2_2 = Expr::apps(nat_mul_comm.clone(), [dexp.clone(), c.nat_lit(2)]); // 2^(e+2)·2 = 2·2^(e+2)
    let mlr = Expr::apps(
        mul_le_mul_right.clone(),
        [c.nat_lit(2), c.nat_lit(8), dexp.clone(), h_2_le_8],
    ); // 2·2^(e+2) ≤ 8·2^(e+2)
       // a3pre : 2^(e+2)·2 ≤ 8·2^(e+2)  := subst (motive t => t ≤ 8·2^(e+2)) (along symm comm_pe2_2) mlr.
    let comm_symm = Expr::apps(
        nat_symm.clone(),
        [
            c.nat.clone(),
            pe2_mul_2.clone(),
            two_mul_pe2.clone(),
            comm_pe2_2,
        ],
    ); // 2·2^(e+2) = 2^(e+2)·2
    let motive_a3 = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = g.fresh_local(c.nat.clone());
        let body = nle(t, eight_mul_pe2.clone());
        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let a3pre = Expr::apps(
        nat_subst.clone(),
        [
            c.nat.clone(),
            motive_a3,
            two_mul_pe2.clone(),
            pe2_mul_2.clone(),
            comm_symm,
            mlr,
        ],
    );
    // a3pre : 2^(e+2)·2 ≤ 8·2^(e+2).  2^(e+3) ≡ 2^(e+2)·2 (def-eq), so a3pre : 2^(e+3) ≤ 8·2^(e+2).
    // a4 : succ(2^(e+2)) ≤ 8·2^(e+2)  := le_trans (a2) (a3pre).
    let a4 = Expr::apps(
        nat_le_trans.clone(),
        [
            d_succ.clone(),
            pow_e3.clone(),
            eight_mul_pe2.clone(),
            a2,
            a3pre,
        ],
    );
    // a5 : 8·2^(e+2) ≤ 48·2^e  := eight_le e.
    let a5 = Expr::apps(eight_le.clone(), [e.clone()]);
    // hdsucc_le_budget : succ(2^(e+2)) ≤ 48·2^e  := le_trans (a4) (a5).
    let hdsucc_le_budget = Expr::apps(
        nat_le_trans.clone(),
        [
            d_succ.clone(),
            eight_mul_pe2.clone(),
            budget.clone(),
            a4,
            a5,
        ],
    );

    // STEP B : 2^(d+1) ≤ 2^(48·2^e)  := pow_le_pow_right 2 (d+1) (48·2^e) (1≤2) hdsucc_le_budget.
    let h_1_le_2 = mk_le_lit(1, 2);
    let pow_dsucc_le_powbudget = Expr::apps(
        pow_le_pow_right.clone(),
        [
            two_n.clone(),
            d_succ.clone(),
            budget.clone(),
            h_1_le_2,
            hdsucc_le_budget,
        ],
    );
    // STEP C : 2^(48·2^e) ≤ n  := from hn : Nat.lt (2^(48·2^e)) n ≡ Nat.le (succ(2^(48·2^e))) n.
    //   2^(48·2^e) ≤ succ(2^(48·2^e))  := le.step (le.refl ..) ; then le_trans with hn.
    let pow_budget_succ = Expr::app(nat_succ.clone(), pow_budget.clone());
    let powbudget_le_succ = Expr::apps(
        nat_le_step.clone(),
        [
            pow_budget.clone(),
            pow_budget.clone(),
            Expr::app(nat_le_refl.clone(), pow_budget.clone()),
        ],
    ); // 2^B ≤ succ(2^B)
       // hn : Nat.lt (2^B) n ≡ Nat.le (succ(2^B)) n.
    let pow_budget_le_n = Expr::apps(
        nat_le_trans.clone(),
        [
            pow_budget.clone(),
            pow_budget_succ.clone(),
            n.clone(),
            powbudget_le_succ,
            hn,
        ],
    );
    // hk_n : 2^(d+1) ≤ n  := le_trans (B) (C).
    let hk_n = Expr::apps(
        nat_le_trans.clone(),
        [
            pow_d_succ.clone(),
            pow_budget.clone(),
            n.clone(),
            pow_dsucc_le_powbudget,
            pow_budget_le_n,
        ],
    );
    // hk_n : Nat.le (2^(d+1)) n  (matches high_budget's hk : Nat.le (Nat.pow 2 (d+1)) n).

    // hpos : 0 < natCast(d+1) := pos_atom (d+1) (1 ≤ d+1).
    //   1 ≤ succ(2^(e+2)) := Nat.succ_le_succ (Nat.zero_le (2^(e+2))).
    let succ_le_succ = Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]);
    let one_le_dsucc = Expr::apps(
        succ_le_succ.clone(),
        [
            c.nat_zero.clone(),
            dexp.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                dexp.clone(),
            ),
        ],
    ); // 1 ≤ succ(2^(e+2))
    let hpos = pos_atom(&d_succ, one_le_dsucc, &b); // 0 < natCast(d+1)

    // hi_pre : I ≤ natCast(d+1)·half.
    //   high_pre K eps e heps g_hi : K ≤ natCast(succ(2^(e+2)))·(eps/2).
    //   (high_pre's eps-hyp is 0 < eps.)
    let hi_high_pre = Expr::apps(
        high_pre.clone(),
        [
            kk.clone(),
            eps.clone(),
            e.clone(),
            heps.clone(),
            g_hi.clone(),
        ],
    );
    // hi_high_pre : K ≤ natCast(succ(2^(e+2)))·(eps/2) = natCast(d+1)·half.
    let dsucc_cast = c.natcast(&d_succ);
    let dsucc_half = c.mul(dsucc_cast.clone(), half.clone());
    let hi_pre = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [
            infl.clone(),
            kk.clone(),
            dsucc_half.clone(),
            hi.clone(),
            hi_high_pre,
        ],
    );
    // hi_pre : I ≤ natCast(d+1)·half.

    // hhigh : M_{≥d+1} ≤ half := high_budget n d f half hk_n hpos hi_pre.
    let hhigh = Expr::apps(
        high_budget.clone(),
        [
            n.clone(),
            dexp.clone(),
            f.clone(),
            half.clone(),
            hk_n,
            hpos,
            hi_pre,
        ],
    );

    // hsum : eL+eH ≤ eps.  eL=eH=half.  add_halves eps : half+half = eps ; then le_refl/subst.
    //   half+half = eps (add_halves) ⟹ half+half ≤ eps via le of eq (subst le_refl).
    let half_plus_half = c.add(half.clone(), half.clone());
    let h_add_halves = Expr::apps(add_halves.clone(), [eps.clone()]); // half+half = eps
    let le_refl_eps = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        [eps.clone()],
    ); // eps ≤ eps
       // subst (motive t => t ≤ eps) (along symm h_add_halves) le_refl_eps : (half+half) ≤ eps.
    let h_add_halves_symm = c.symm_rat(half_plus_half.clone(), eps.clone(), h_add_halves);
    let motive_sum = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = g.fresh_local(c.rat.clone());
        let body = c.le(t, eps.clone());
        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let hsum = c.subst_rat(
        motive_sum,
        eps.clone(),
        half_plus_half.clone(),
        h_add_halves_symm,
        le_refl_eps,
    );
    // hsum : half+half ≤ eps.

    // ── l2_core application : MASS := subsetSum n (full_fn J) ≤ eps ──
    let mass_proof = Expr::apps(
        l2_core.clone(),
        [
            n.clone(),
            dexp.clone(),
            f.clone(),
            jj.clone(),
            dr.clone(),
            half.clone(),
            half.clone(),
            eps.clone(),
            hd,
            hdd0,
            hdd1,
            h0,
            h1m,
            hlow,
            hhigh,
            hsum,
        ],
    );
    // mass_proof : subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂·f̂)) ≤ eps.

    // ════════ SIZE : setSizeNat n J ≤ 2^(48·2^e) ════════
    // hnn : ∀i,0≤Inf := h0 (rebuild) ; hb : ∀i, J i=true → tau≤Inf := fun i => thresholdJ_mem_le n f tau i.
    let hnn = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let fin_n = Expr::app(fin_c.clone(), n.clone());
        let (i_id, i) = g.fresh_local(fin_n.clone());
        g.finish_child(g.mk_lam(
            i_id,
            BinderInfo::Default,
            fin_n,
            Expr::apps(influence_nonneg.clone(), [n.clone(), f.clone(), i]),
        ))
    };
    let hb = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let fin_n = Expr::app(fin_c.clone(), n.clone());
        let (i_id, i) = g.fresh_local(fin_n.clone());
        g.finish_child(g.mk_lam(
            i_id,
            BinderInfo::Default,
            fin_n,
            Expr::apps(thr_mem.clone(), [n.clone(), f.clone(), tau.clone(), i]),
        ))
    };
    // card : tau · Fin.sum n (fun i => ind(J i)) ≤ I  := influence_threshold_card_le n f tau J hnn hb.
    let card = Expr::apps(
        card_le.clone(),
        [n.clone(), f.clone(), tau.clone(), jj.clone(), hnn, hb],
    );
    // Fin.sum n (fun i => ind(J i)) ≡ setSize n J (def-eq).  setSize_eq_natCast n J : setSize n J = natCast(|J|).
    let cardfn = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let fin_n = Expr::app(fin_c.clone(), n.clone());
        let (i_id, i) = g.fresh_local(fin_n.clone());
        let body = c.ind_of(Expr::app(jj.clone(), i));
        g.finish_child(g.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let fin_sum_card = Expr::apps(fin_sum.clone(), [n.clone(), cardfn]); // Fin.sum n (ind∘J) ≡ setSize n J
    let set_size_j = Expr::apps(set_size.clone(), [n.clone(), jj.clone()]); // setSize n J
    let setsize_nat_j = Expr::apps(set_size_nat.clone(), [n.clone(), jj.clone()]); // setSizeNat n J
    let cast_size = c.natcast(&setsize_nat_j); // natCast(setSizeNat n J)
    let h_setsize_eq = Expr::apps(setsize_natcast.clone(), [n.clone(), jj.clone()]); // setSize n J = natCast(|J|)
                                                                                     //   (setSize n J ≡ Fin.sum n (ind∘J) def-eq, so h_setsize_eq : Fin.sum(ind∘J) = natCast(|J|).)
                                                                                     // card2 : tau · natCast(|J|) ≤ I  := subst (motive t => tau·t ≤ I) (along h_setsize_eq) card.
    let tau_finsum = c.mul(tau.clone(), fin_sum_card.clone());
    let _ = (tau_finsum, set_size_j);
    let motive_card = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = g.fresh_local(c.rat.clone());
        let body = c.le(c.mul(tau.clone(), t), infl.clone());
        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let card2 = c.subst_rat(
        motive_card,
        fin_sum_card.clone(),
        cast_size.clone(),
        h_setsize_eq,
        card,
    );
    // card2 : tau · natCast(|J|) ≤ I.
    // tau·natCast(|J|) ≤ K  := le_trans (tau·natCast(|J|)) I K card2 hi.
    let tau_cast = c.mul(tau.clone(), cast_size.clone());
    let card3 = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [
            tau_cast.clone(),
            infl.clone(),
            kk.clone(),
            card2,
            hi.clone(),
        ],
    );
    // card3 : tau·natCast(|J|) ≤ K.
    // K ≤ tau·natCast(B)  := size_rearrange e K eps hk_pos heps heps1 g_hi.
    let cast_big_b = c.natcast(&pow_budget); // natCast(2^(48·2^e))
    let k_le_tau_b = Expr::apps(
        size_rearr.clone(),
        [
            e.clone(),
            kk.clone(),
            eps.clone(),
            hk_pos.clone(),
            heps.clone(),
            heps1.clone(),
            g_hi.clone(),
        ],
    );
    // k_le_tau_b : K ≤ (dr·dr)·natCast(B) = tau·natCast(B).
    let tau_b = c.mul(tau.clone(), cast_big_b.clone());
    // card4 : tau·natCast(|J|) ≤ tau·natCast(B)  := le_trans (tau·natCast(|J|)) K (tau·natCast(B)) card3 k_le_tau_b.
    let card4 = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [
            tau_cast.clone(),
            kk.clone(),
            tau_b.clone(),
            card3,
            k_le_tau_b,
        ],
    );
    // cancel tau>0 : natCast(|J|) ≤ natCast(B)  := le_of_mul_le_mul_left_pos natCast(|J|) natCast(B) tau h_tau_pos card4.
    let cast_le = c.le_of_mul_le_left(
        cast_size.clone(),
        cast_big_b.clone(),
        tau.clone(),
        h_tau_pos,
        card4,
    );
    // cast_le : natCast(|J|) ≤ natCast(B).
    // size : Nat.le (setSizeNat n J) (2^(48·2^e))  := le_of_natCast_le_natCast (|J|) B cast_le.
    let size_proof = Expr::apps(
        le_of_natcast.clone(),
        [setsize_nat_j.clone(), pow_budget.clone(), cast_le],
    );
    // size_proof : Nat.le (setSizeNat n J) (Nat.pow 2 (48·2^e)).

    // ── Exists.intro J (And.intro size_proof mass_proof) ──
    let size_concl = nle(setsize_nat_j.clone(), big_b.clone());
    let mass_fn_j = ct_mass_fn(&c, &b, &n, &f, &jj);
    let mass_concl = c.le(
        Expr::apps(subset_sum.clone(), [n.clone(), mass_fn_j]),
        eps.clone(),
    );
    let and_proof = Expr::apps(
        and_intro.clone(),
        [size_concl, mass_concl, size_proof, mass_proof],
    );
    let intro = Expr::apps(
        exists_intro.clone(),
        [hcp_n.clone(), pred.clone(), jj.clone(), and_proof],
    );

    // bind all hypothesis lambdas.
    let r = b.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
    let r = b.mk_lam(hg_id, BinderInfo::Default, guard_ty, r);
    let r = b.mk_lam(heps1_id, BinderInfo::Default, heps1_ty, r);
    let r = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, r);
    let r = b.mk_lam(hi_id, BinderInfo::Default, hi_ty, r);
    let r = b.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Default, bf_ty, r);
    Ok(b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
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
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_influence_nonneg_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_influence_nonneg()
            .expect("register_influence_nonneg");
        env.register_influence_nonneg().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.influence_nonneg");
    }

    #[test]
    fn test_pow_nat_nine_eq_natcast_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_nine_eq_natcast()
            .expect("register_rat_pow_nat_nine_eq_natcast");
        env.register_rat_pow_nat_nine_eq_natcast()
            .expect("idempotent");
        check_constructive(&env, "Rat.powNat_nine_eq_natCast");
    }

    #[test]
    fn test_friedgut_threshold_high_pre_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_threshold_high_pre()
            .expect("register_friedgut_threshold_high_pre");
        env.register_friedgut_threshold_high_pre()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_threshold_high_pre");
    }

    #[test]
    fn test_friedgut_threshold_size_rearrange_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_threshold_size_rearrange()
            .expect("register_friedgut_threshold_size_rearrange");
        env.register_friedgut_threshold_size_rearrange()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_threshold_size_rearrange");
    }

    #[test]
    fn test_friedgut_threshold_dr_sq_lt_one_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_threshold_dr_sq_lt_one()
            .expect("register_friedgut_threshold_dr_sq_lt_one");
        env.register_friedgut_threshold_dr_sq_lt_one()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_threshold_dr_sq_lt_one");
    }

    #[test]
    fn test_friedgut_boolean_case_threshold_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_boolean_case_threshold()
            .expect("register_friedgut_boolean_case_threshold");
        env.register_friedgut_boolean_case_threshold()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_boolean_case_threshold");
    }
}
