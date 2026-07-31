// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.half_pos` (strict positivity of `ε/2`).
//!
//! # Why this module exists
//!
//! `NNReal.CauSeq.Equiv.trans` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B) instantiates both
//! Cauchy hypotheses at `ε/2`, so it must supply a proof `Rat.lt 0 (ε/2)`. This
//! module proves that directly from `Rat.add_halves` — WITHOUT needing
//! inverse-positivity (`0 < Rat.inv Rat.two`), which would be a separate
//! quotient sign sub-build.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.half_pos : ∀ ε : Rat, Rat.lt Rat.zero ε →
//!       Rat.lt Rat.zero (Rat.div ε Rat.two)`
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.
//!
//! # Proof sketch
//!
//! Write `h := ε/2` (reducible to `ε · Rat.inv Rat.two`). The key lemma is
//! `contra : (h ≤ 0) → False`:
//!   `h ≤ 0  ⟹  h + h ≤ 0 + 0 = 0`   (`add_le_add` + `zero_add`)
//!         `⟹  ε ≤ 0`               (`add_halves : h + h = ε`)
//!         `⟹  False`               (contra `¬ ε ≤ 0` from `0 < ε`).
//! Then `0 < h` is `Iff.mpr (lt_iff_le_not_le 0 h) (And.intro p1 contra)` with
//! `p1 : 0 ≤ h` from `Rat.le_total 0 h` (the `h ≤ 0` branch discharged by
//! `contra` ⟶ `False.elim`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.half_pos`.
pub(crate) struct RatHalfPosConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_add_le_add: Expr,
    rat_zero_add: Expr,
    rat_add_halves: Expr,
    rat_le_total: Expr,
    rat_lt_iff_le_not_le: Expr,
    eq_subst: Expr,
    and_c: Expr,
    and_intro: Expr,
    and_right: Expr,
    or_c: Expr,
    or_rec: Expr,
    not_c: Expr,
    #[cfg(test)]
    false_c: Expr,
    false_elim: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
}

impl RatHalfPosConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_zero_add: k("Rat.zero_add"),
            rat_add_halves: k("Rat.add_halves"),
            rat_le_total: k("Rat.le_total"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_right: k("And.right"),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            not_c: k("Not"),
            #[cfg(test)]
            false_c: k("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
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
    /// `Rat.add_le_add a b c d h1 h2 : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.zero_add a : Eq Rat (0 + a) a`.
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }
    /// `Rat.add_halves ε : Eq Rat ((ε/2) + (ε/2)) ε`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
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
    /// Register `Rat.half_pos`. Idempotent. Pulls in `Rat.add_halves` (the
    /// halving sub-build) plus the order lemmas it needs.
    pub fn init_algebra_rat_half_pos(&mut self) -> Result<(), EnvError> {
        self.init_algebra_rat_halves()?; // Rat.two, Rat.two_ne_zero, Rat.add_halves
        self.init_rat_linear_order()?; // Rat.le_total, Rat.lt_iff_le_not_le
        self.init_or()?;
        self.init_and()?;
        self.init_true_false()?;

        let c = RatHalfPosConsts::new();
        self.register_rat_half_pos(&c)?;
        Ok(())
    }

    fn register_rat_half_pos(&mut self, c: &RatHalfPosConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.half_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(zero.clone(), eps.clone());
            let (h_id, _h) = b.fresh_local(hpos.clone());
            let half = c.div(eps.clone(), c.rat_two.clone());
            let concl = c.lt(zero.clone(), half);
            let e = b.mk_pi(h_id, BinderInfo::Default, hpos, concl);
            let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(zero.clone(), eps.clone());
            let (hp_id, hp) = b.fresh_local(hpos_ty.clone());
            let half = c.div(eps.clone(), c.rat_two.clone());

            // not_eps_le_0 : ¬ (ε ≤ 0) := And.right (Iff.mp (lt_iff_le_not_le 0 ε) hp).
            let le_0e = c.le(zero.clone(), eps.clone());
            let not_le_e0 = c.not_(c.le(eps.clone(), zero.clone()));
            let and_e = Expr::apps(c.and_c.clone(), [le_0e.clone(), not_le_e0.clone()]);
            let iff_e = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [zero.clone(), eps.clone()]);
            let conj_e = Expr::apps(
                c.iff_mp.clone(),
                [hpos_ty.clone(), and_e, iff_e, hp.clone()],
            );
            let not_eps_le_0 = Expr::apps(c.and_right.clone(), [le_0e, not_le_e0, conj_e]);

            // contra : (half ≤ 0) → False.
            let contra = {
                let mut bc = EnvDeclBuilder::child_of(&b);
                let hle_ty = c.le(half.clone(), zero.clone());
                let (hle_id, hle) = bc.fresh_local(hle_ty.clone());

                // step : (half + half) ≤ (0 + 0)  := add_le_add half 0 half 0 hle hle.
                let step = c.add_le_add(
                    half.clone(),
                    zero.clone(),
                    half.clone(),
                    zero.clone(),
                    hle.clone(),
                    hle,
                );
                // hh_le_0 : (half + half) ≤ 0  := subst (motive t := half+half ≤ t)
                //                                       (0+0) 0 (zero_add 0) step.
                let hh = c.add(half.clone(), half.clone());
                let motive_t_le = {
                    let mut mb = EnvDeclBuilder::child_of(&bc);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(hh.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let zz = c.add(zero.clone(), zero.clone());
                let hh_le_0 = c.subst(
                    motive_t_le,
                    zz,
                    zero.clone(),
                    c.zero_add(zero.clone()),
                    step,
                );

                // eps_le_0 : ε ≤ 0  := subst (motive t := t ≤ 0) (half+half) ε
                //                            (add_halves ε) hh_le_0.
                let motive_le_t = {
                    let mut mb = EnvDeclBuilder::child_of(&bc);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(t, zero.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let eps_le_0 = c.subst(
                    motive_le_t,
                    hh.clone(),
                    eps.clone(),
                    c.add_halves(eps.clone()),
                    hh_le_0,
                );
                // not_eps_le_0 eps_le_0 : False.
                let false_proof = Expr::app(not_eps_le_0.clone(), eps_le_0);
                let lam = bc.mk_lam(hle_id, BinderInfo::Default, hle_ty, false_proof);
                bc.finish_child(lam)
            };

            // p1 : 0 ≤ half  via Or.rec over (le_total 0 half).
            //   left  (w : 0 ≤ half) => w
            //   right (hle : half ≤ 0) => False.elim (0≤half) (contra hle)
            let le_0half = c.le(zero.clone(), half.clone());
            let le_half0 = c.le(half.clone(), zero.clone());
            let or_total = Expr::apps(c.rat_le_total.clone(), [zero.clone(), half.clone()]);

            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let or_ty = Expr::apps(c.or_c.clone(), [le_0half.clone(), le_half0.clone()]);
                let (h_id, _) = mb.fresh_local(or_ty.clone());
                mb.finish_child(mb.mk_lam(h_id, BinderInfo::Default, or_ty, le_0half.clone()))
            };
            let left_fn = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = lb.fresh_local(le_0half.clone());
                lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, le_0half.clone(), w))
            };
            let right_fn = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (hle_id, hle) = rb.fresh_local(le_half0.clone());
                let false_pf = Expr::app(contra.clone(), hle);
                let body = Expr::apps(c.false_elim.clone(), [le_0half.clone(), false_pf]);
                rb.finish_child(rb.mk_lam(hle_id, BinderInfo::Default, le_half0.clone(), body))
            };
            let p1 = Expr::apps(
                c.or_rec.clone(),
                [
                    le_0half.clone(),
                    le_half0.clone(),
                    or_motive,
                    left_fn,
                    right_fn,
                    or_total,
                ],
            );

            // 0 < half := Iff.mpr (lt_iff_le_not_le 0 half) (And.intro (0≤half)(¬half≤0) p1 contra).
            let not_half_le_0 = c.not_(le_half0.clone());
            let and_half = Expr::apps(c.and_c.clone(), [le_0half.clone(), not_half_le_0.clone()]);
            let and_pf = Expr::apps(
                c.and_intro.clone(),
                [le_0half.clone(), not_half_le_0, p1, contra],
            );
            let lt_0half = c.lt(zero.clone(), half.clone());
            let iff_half = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [zero.clone(), half.clone()]);
            let lt_proof = Expr::apps(c.iff_mpr.clone(), [lt_0half, and_half, iff_half, and_pf]);

            let e = b.mk_lam(hp_id, BinderInfo::Default, hpos_ty, lt_proof);
            let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
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
    fn test_rat_half_pos_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_half_pos()
            .expect("init_algebra_rat_half_pos");
        env.init_algebra_rat_half_pos().expect("idempotent");

        let nm = Name::from_string("Rat.half_pos");
        let info = env.get_const(&nm).expect("Rat.half_pos registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.half_pos must kernel-check");

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
