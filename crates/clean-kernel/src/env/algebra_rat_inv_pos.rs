// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.inv_pos` (strict positivity of the inverse).
//!
//! # Why this module exists
//!
//! `NNReal.mul`'s product-Cauchy tail tolerance is `δ = (ε/2)·B'⁻¹` with
//! `B' = bound + 1 ≥ 1` from `NNReal.IsCauchy_bounded`. The strict bound
//! `0 < δ` needs `0 < B'⁻¹`, i.e. inverse-positivity. That lemma is genuinely
//! absent from the live Rat order layer; this module proves it directly,
//! adding ZERO axioms.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.inv_pos : ∀ a : Rat, Rat.lt Rat.zero a → Rat.lt Rat.zero (Rat.inv a)`
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.
//!
//! # Proof sketch (mirrors `Rat.half_pos`)
//!
//! Write `ai := Rat.inv a`. The key lemma is `contra : (ai ≤ 0) → False`:
//!   `ai ≤ 0  ⟹  a·ai ≤ a·0`   (`mul_le_mul_of_nonneg_left a ai 0 (·) h0a`, with
//!                                `h0a : 0 ≤ a`)
//!          `⟹  a·ai ≤ 0`       (`a·0 = 0` via `Rat.mul_zero a`, `Eq.subst`)
//!          `⟹  1 ≤ 0`          (`a·ai = 1` via `Rat.mul_inv_cancel a h_ne`, `Eq.subst`)
//!          `⟹  False`          (`¬ 1 ≤ 0` from `Rat.zero_lt_one` through
//!                                `Rat.lt_iff_le_not_le`).
//! The nonzero hypothesis `h_ne : a = 0 → False` comes from `0 < a`: given
//! `heq : a = 0`, transport `a ≤ a` (`le_refl`) along `heq` to `a ≤ 0`, which
//! contradicts `¬ a ≤ 0` (from `0 < a`). Then `0 ≤ a` is `And.left` of
//! `Iff.mp (lt_iff_le_not_le 0 a) hpos`.
//!
//! Finally `0 < ai` is `Iff.mpr (lt_iff_le_not_le 0 ai) (And.intro p1 contra)`
//! with `p1 : 0 ≤ ai` from `Rat.le_total 0 ai` (the `ai ≤ 0` branch discharged
//! by `contra` ⟶ `False.elim`).
//!
//! Every cited lemma (`mul_le_mul_of_nonneg_left`, `mul_zero`, `mul_inv_cancel`,
//! `zero_lt_one`, `le_refl`, `le_total`, `lt_iff_le_not_le`) is a kernel-checked
//! `Declaration::Theorem` whose transitive admitted-axiom closure is empty on
//! the synced main (the formerly-`AxiomDependent` `Rat.lt_iff_le_not_le` is now
//! `Constructive` after `Int.lt_iff_le_not_le` was eliminated), so `Rat.inv_pos`
//! is genuinely `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.inv_pos`.
pub(crate) struct RatInvPosConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_inv: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_div: Expr,
    rat_mul_pos: Expr,
    rat_mul_zero: Expr,
    rat_mul_inv_cancel: Expr,
    rat_mul_le_mul_of_nonneg_left: Expr,
    rat_zero_lt_one: Expr,
    rat_le_refl: Expr,
    rat_le_total: Expr,
    rat_lt_iff_le_not_le: Expr,
    eq_c: Expr,
    eq_subst: Expr,
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    or_c: Expr,
    or_rec: Expr,
    not_c: Expr,
    false_c: Expr,
    false_elim: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
}

impl RatInvPosConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_inv: k("Rat.inv"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_div: k("Rat.div"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_mul_zero: k("Rat.mul_zero"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_mul_le_mul_of_nonneg_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_total: k("Rat.le_total"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            not_c: k("Not"),
            false_c: k("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    /// `Rat.div a b` (≡ `Rat.mul a (Rat.inv b)`, reducible).
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    /// `Rat.mul_pos a b ha hb : Rat.lt Rat.zero (Rat.mul a b)`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    /// `@Eq Rat a b`.
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [self.rat.clone(), a, b])
    }
    /// `Rat.mul_zero a : @Eq Rat (Rat.mul a Rat.zero) Rat.zero`.
    fn mul_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_zero.clone(), a)
    }
    /// `Rat.mul_inv_cancel a h_ne : @Eq Rat (Rat.mul a (Rat.inv a)) Rat.one`.
    fn mul_inv_cancel(&self, a: Expr, h_ne: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h_ne])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_a : Rat.le (a·b) (a·c)`.
    fn mul_le_mul_left(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.rat_mul_le_mul_of_nonneg_left.clone(),
            [a, b, cc, h_bc, h_a],
        )
    }
    /// `Rat.le_refl a : Rat.le a a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    /// `Rat.le_total a b : Or (Rat.le a b) (Rat.le b a)`.
    fn le_total(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_total.clone(), [a, b])
    }
    /// `Rat.lt_iff_le_not_le a b : Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))`.
    fn lt_iff(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
}

impl Environment {
    /// Register `Rat.inv_pos`. Idempotent. Pulls in the multiplicative-inverse
    /// surface (`Rat.mul_inv_cancel`, `Rat.mul_zero`), the order toolkit
    /// (`Rat.mul_le_mul_of_nonneg_left`), and the linear-order lemmas
    /// (`Rat.le_refl`, `Rat.le_total`, `Rat.zero_lt_one`, `Rat.lt_iff_le_not_le`).
    pub fn init_algebra_rat_inv_pos(&mut self) -> Result<(), EnvError> {
        // Rat.left_distrib/right_distrib/one_mul/mul_one/mul_inv_cancel/mul_zero,
        // plus Rat.inv as a Definition.
        self.init_rat_field_inst()?;
        // Rat.le_refl, Rat.le_total, Rat.zero_lt_one, Rat.lt_iff_le_not_le, Rat.mul_pos.
        self.init_rat_linear_order()?;
        // Rat.mul_le_mul_of_nonneg_left / _right.
        self.init_boolean_analysis_order_toolkit()?;
        self.init_or()?;
        self.init_and()?;
        self.init_true_false()?;
        self.init_eq()?;

        let c = RatInvPosConsts::new();
        self.register_rat_le_of_lt(&c)?;
        self.register_rat_inv_pos_recovered(&c)?;
        self.register_rat_div_pos(&c)?;
        Ok(())
    }

    /// `Rat.le_of_lt : ∀ a b : Rat, Rat.lt a b → Rat.le a b`.
    ///
    /// `λ a b h => And.left (Rat.le a b) (¬ Rat.le b a)
    ///                      (Iff.mp (lt_iff_le_not_le a b) h)`. Empty axiom
    /// closure (`Rat.lt_iff_le_not_le` is Constructive on synced main). This is
    /// the strict→weak bridge `NNReal.IsCauchy_mul` needs to feed strict Cauchy
    /// tails into the nonneg-monotone product bounds (`mul_le_mul_of_nonneg_*`).
    fn register_rat_le_of_lt(&mut self, c: &RatInvPosConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_ty = c.lt(a.clone(), bv.clone());
            let concl = c.le(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_ty = c.lt(a.clone(), bv.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());

            let le_ab = c.le(a.clone(), bv.clone());
            let not_le_ba = c.not_(c.le(bv.clone(), a.clone()));
            let and_ab = Expr::apps(c.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
            let iff_ab = c.lt_iff(a.clone(), bv.clone());
            let conj = Expr::apps(c.iff_mp.clone(), [h_ty.clone(), and_ab, iff_ab, h]);
            let body = Expr::apps(c.and_left.clone(), [le_ab, not_le_ba, conj]);

            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_rat_inv_pos_recovered(&mut self, c: &RatInvPosConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let one = c.rat_one.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(zero.clone(), a.clone());
            let (h_id, _h) = b.fresh_local(hpos.clone());
            let concl = c.lt(zero.clone(), c.inv(a.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, hpos, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(zero.clone(), a.clone());
            let (hp_id, hp) = b.fresh_local(hpos_ty.clone());
            let ai = c.inv(a.clone());

            // From `0 < a`: conj0a : And (0 ≤ a) (¬ a ≤ 0)  via Iff.mp lt_iff.
            let le_0a = c.le(zero.clone(), a.clone());
            let not_le_a0 = c.not_(c.le(a.clone(), zero.clone()));
            let and_0a = Expr::apps(c.and_c.clone(), [le_0a.clone(), not_le_a0.clone()]);
            let iff_0a = c.lt_iff(zero.clone(), a.clone());
            let conj_0a = Expr::apps(
                c.iff_mp.clone(),
                [hpos_ty.clone(), and_0a, iff_0a, hp.clone()],
            );
            // h0a : 0 ≤ a.
            let h0a = Expr::apps(
                c.and_left.clone(),
                [le_0a.clone(), not_le_a0.clone(), conj_0a.clone()],
            );
            // not_a_le_0 : ¬ a ≤ 0.
            let not_a_le_0 = Expr::apps(
                c.and_right.clone(),
                [le_0a.clone(), not_le_a0.clone(), conj_0a],
            );

            // h_ne : (a = 0) → False.
            //   λ heq => not_a_le_0 (Eq.subst (motive t := a ≤ t) a 0 heq (le_refl a)).
            let h_ne = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let eq_a0 = c.eq_ty(a.clone(), zero.clone());
                let (heq_id, heq) = bn.fresh_local(eq_a0.clone());
                // motive t := a ≤ t.
                let motive_a_le = {
                    let mut mb = EnvDeclBuilder::child_of(&bn);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(a.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // a ≤ 0  := subst (motive) a 0 heq (le_refl a).
                let a_le_0 = c.subst(
                    motive_a_le,
                    a.clone(),
                    zero.clone(),
                    heq,
                    c.le_refl(a.clone()),
                );
                let false_pf = Expr::app(not_a_le_0.clone(), a_le_0);
                let lam = bn.mk_lam(heq_id, BinderInfo::Default, eq_a0, false_pf);
                bn.finish_child(lam)
            };

            // ¬ 1 ≤ 0  := And.right (Iff.mp (lt_iff 0 1) zero_lt_one).
            let le_01 = c.le(zero.clone(), one.clone());
            let not_le_10 = c.not_(c.le(one.clone(), zero.clone()));
            let and_01 = Expr::apps(c.and_c.clone(), [le_01.clone(), not_le_10.clone()]);
            let iff_01 = c.lt_iff(zero.clone(), one.clone());
            let lt01_ty = c.lt(zero.clone(), one.clone());
            let conj_01 = Expr::apps(
                c.iff_mp.clone(),
                [lt01_ty, and_01, iff_01, c.rat_zero_lt_one.clone()],
            );
            let not_one_le_0 = Expr::apps(
                c.and_right.clone(),
                [le_01.clone(), not_le_10.clone(), conj_01],
            );

            // contra : (ai ≤ 0) → False.
            let contra = {
                let mut bc = EnvDeclBuilder::child_of(&b);
                let hle_ty = c.le(ai.clone(), zero.clone());
                let (hle_id, hle) = bc.fresh_local(hle_ty.clone());

                // step : (a·ai) ≤ (a·0)  := mul_le_mul_left a ai 0 hle h0a.
                let step = c.mul_le_mul_left(a.clone(), ai.clone(), zero.clone(), hle, h0a.clone());
                // a_ai_le_0 : (a·ai) ≤ 0  := subst (motive t := a·ai ≤ t) (a·0) 0 (mul_zero a) step.
                let a_ai = c.mul(a.clone(), ai.clone());
                let a_mul_0 = c.mul(a.clone(), zero.clone());
                let motive_aai_le = {
                    let mut mb = EnvDeclBuilder::child_of(&bc);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(a_ai.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let a_ai_le_0 = c.subst(
                    motive_aai_le,
                    a_mul_0,
                    zero.clone(),
                    c.mul_zero(a.clone()),
                    step,
                );
                // one_le_0 : 1 ≤ 0  := subst (motive t := t ≤ 0) (a·ai) 1 (mul_inv_cancel a h_ne) a_ai_le_0.
                let motive_le_0 = {
                    let mut mb = EnvDeclBuilder::child_of(&bc);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(t, zero.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let one_le_0 = c.subst(
                    motive_le_0,
                    a_ai.clone(),
                    one.clone(),
                    c.mul_inv_cancel(a.clone(), h_ne.clone()),
                    a_ai_le_0,
                );
                // not_one_le_0 one_le_0 : False.
                let false_pf = Expr::app(not_one_le_0.clone(), one_le_0);
                let lam = bc.mk_lam(hle_id, BinderInfo::Default, hle_ty, false_pf);
                bc.finish_child(lam)
            };

            // p1 : 0 ≤ ai  via Or.rec over (le_total 0 ai).
            let le_0ai = c.le(zero.clone(), ai.clone());
            let le_ai0 = c.le(ai.clone(), zero.clone());
            let or_total = c.le_total(zero.clone(), ai.clone());
            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let or_ty = Expr::apps(c.or_c.clone(), [le_0ai.clone(), le_ai0.clone()]);
                let (h_id, _) = mb.fresh_local(or_ty.clone());
                mb.finish_child(mb.mk_lam(h_id, BinderInfo::Default, or_ty, le_0ai.clone()))
            };
            let left_fn = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = lb.fresh_local(le_0ai.clone());
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, le_0ai.clone(), w))
            };
            let right_fn = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (hle_id, hle) = rb.fresh_local(le_ai0.clone());
                let false_pf = Expr::app(contra.clone(), hle);
                let body = Expr::apps(c.false_elim.clone(), [le_0ai.clone(), false_pf]);
                rb.finish_child(rb.mk_lam(hle_id, BinderInfo::Default, le_ai0.clone(), body))
            };
            let p1 = Expr::apps(
                c.or_rec.clone(),
                [
                    le_0ai.clone(),
                    le_ai0.clone(),
                    or_motive,
                    left_fn,
                    right_fn,
                    or_total,
                ],
            );

            // 0 < ai := Iff.mpr (lt_iff 0 ai) (And.intro (0≤ai)(¬ai≤0) p1 contra).
            let not_ai_le_0 = c.not_(le_ai0.clone());
            let and_ai = Expr::apps(c.and_c.clone(), [le_0ai.clone(), not_ai_le_0.clone()]);
            let and_pf = Expr::apps(
                c.and_intro.clone(),
                [le_0ai.clone(), not_ai_le_0, p1, contra],
            );
            let lt_0ai = c.lt(zero.clone(), ai.clone());
            let iff_ai = c.lt_iff(zero.clone(), ai.clone());
            let lt_proof = Expr::apps(c.iff_mpr.clone(), [lt_0ai, and_ai, iff_ai, and_pf]);

            let e = b.mk_lam(hp_id, BinderInfo::Default, hpos_ty, lt_proof);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.div_pos : ∀ a b : Rat,
    ///     Rat.lt Rat.zero a → Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.div a b)`.
    ///
    /// `Rat.div a b ≡ Rat.mul a (Rat.inv b)` (reducible), so the goal is defeq to
    /// `Rat.lt Rat.zero (Rat.mul a (Rat.inv b))`, discharged by
    /// `Rat.mul_pos a (Rat.inv b) ha (Rat.inv_pos b hb)`. Empty axiom closure
    /// (both delegates are constructive).
    fn register_rat_div_pos(&mut self, c: &RatInvPosConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.div_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let rat_inv_pos = Expr::const_(Name::from_string("Rat.inv_pos"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let ha_ty = c.lt(zero.clone(), a.clone());
            let hb_ty = c.lt(zero.clone(), bv.clone());
            let concl = c.lt(zero.clone(), c.div(a.clone(), bv.clone()));
            let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
            let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let ha_ty = c.lt(zero.clone(), a.clone());
            let hb_ty = c.lt(zero.clone(), bv.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());

            // inv_pos b hb : 0 < Rat.inv b.
            let inv_b_pos = Expr::apps(rat_inv_pos.clone(), [bv.clone(), hb]);
            // mul_pos a (inv b) ha (inv_pos b hb) : 0 < Rat.mul a (Rat.inv b)
            //   ≡ 0 < Rat.div a b  (defeq, Rat.div reducible).
            let body = c.mul_pos(a.clone(), c.inv(bv.clone()), ha, inv_b_pos);

            let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, body);
            let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_rat_inv_pos_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_pos()
            .expect("init_algebra_rat_inv_pos");
        env.init_algebra_rat_inv_pos().expect("idempotent");

        let nm = Name::from_string("Rat.inv_pos");
        let info = env.get_const(&nm).expect("Rat.inv_pos registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.inv_pos must kernel-check");

        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_rat_le_of_lt_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_pos()
            .expect("init_algebra_rat_inv_pos");

        let nm = Name::from_string("Rat.le_of_lt");
        let info = env.get_const(&nm).expect("Rat.le_of_lt registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.le_of_lt must kernel-check");

        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }

    #[test]
    fn test_rat_div_pos_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_pos()
            .expect("init_algebra_rat_inv_pos");

        let nm = Name::from_string("Rat.div_pos");
        let info = env.get_const(&nm).expect("Rat.div_pos registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.div_pos must kernel-check");

        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
