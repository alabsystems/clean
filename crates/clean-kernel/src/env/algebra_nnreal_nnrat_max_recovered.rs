// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B1 extension: `NNRat.max` + its lattice lemmas.
//!
//! # Why this module exists
//!
//! `NNReal.mul`'s `Quot.lift` respect proof needs the cross-term bound
//! `|fg − f'g'| ≤ |f|·|g−g'| + |g'|·|f−f'|`, which requires every Cauchy
//! sequence's `.val`s to be bounded by some `NNRat` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B2 remaining rung 2).
//! The bound `B` is built as a running `max` over a finite prefix — which needs
//! a nonneg-preserving `NNRat.max` with the standard lattice lemmas.
//!
//! This module adds, on top of the Stage-B1 base (`algebra_nnreal_nnrat.rs`):
//! - `NNRat.max : NNRat → NNRat → NNRat`
//!     `:= fun p q => NNRat.ofRat (Rat.max (val p) (val q)) h`
//!   where `h : 0 ≤ Rat.max (val p) (val q)` is `Rat.le_trans 0 (val p) (max …)
//!   (NNRat.property p) (Rat.le_max_left (val p) (val q))`. (Nonneg of the max
//!   follows from nonneg of either argument; we use the left one.)
//! - `NNRat.val_max : NNRat.val (NNRat.max p q) = Rat.max (val p) (val q)`
//!   (by `NNRat.val_ofRat` — the `Subtype.val ∘ Subtype.mk` projection).
//! - `NNRat.le_max_left  : NNRat.le p (NNRat.max p q)`
//! - `NNRat.le_max_right : NNRat.le q (NNRat.max p q)`
//! - `NNRat.max_le       : NNRat.le p r → NNRat.le q r → NNRat.le (NNRat.max p q) r`
//!
//! Each lattice lemma lifts the corresponding on-main `Rat` lattice lemma
//! (`Rat.le_max_left` / `Rat.le_max_right` / `Rat.max_le`) through the reducible
//! `NNRat.le := fun p q => Rat.le (val p)(val q)`, transporting the `.val (max …)`
//! occurrences along `NNRat.val_max` with `Eq.subst`. Every declaration is a
//! `Definition` or kernel-checked `Declaration::Theorem`, `ProofQuality::
//! Constructive`, empty admitted-axiom closure (foundational only). NO `sorry`
//! / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNRat.max` and its lattice
/// lemmas. The `.val`s live in `Rat`; the order is the reducible `NNRat.le`.
pub(crate) struct NNRatMaxConstsRecovered {
    rat: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    nnrat_property: Expr,
    nnrat_le: Expr,
    nnrat_val_ofrat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_max: Expr,
    rat_le_trans: Expr,
    rat_le_max_left: Expr,
    rat_le_max_right: Expr,
    rat_max_le: Expr,
    // Eq.{1} over Rat for the val_max soundness + the lattice transports.
    eq_rat: Expr,
    eq_subst_rat: Expr,
}

impl NNRatMaxConstsRecovered {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnrat_property: k("NNRat.property"),
            nnrat_le: k("NNRat.le"),
            nnrat_val_ofrat: k("NNRat.val_ofRat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_max: k("Rat.max"),
            rat_le_trans: k("Rat.le_trans"),
            rat_le_max_left: k("Rat.le_max_left"),
            rat_le_max_right: k("Rat.le_max_right"),
            rat_max_le: k("Rat.max_le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_subst_rat: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn rmax(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    /// `NNRat.le p q : Prop`.
    fn le(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le.clone(), [p, q])
    }
    /// `NNRat.max p q : NNRat`.
    fn nmax(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("NNRat.max"), vec![]), [p, q])
    }
    /// `NNRat.property q : 0 ≤ NNRat.val q`.
    fn property(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q)
    }
    /// `@Eq.{1} Rat a b`.
    fn eq_rat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst_rat.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.le_trans a b c (h1:a≤b)(h2:b≤c) : a≤c`.
    fn rat_le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.le_max_left a b : Rat.le a (Rat.max a b)`.
    fn rat_le_max_left(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_max_left.clone(), [a, b])
    }
    /// `Rat.le_max_right a b : Rat.le b (Rat.max a b)`.
    fn rat_le_max_right(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_max_right.clone(), [a, b])
    }
    /// `Rat.max_le a b c (h1:a≤c)(h2:b≤c) : Rat.le (Rat.max a b) c`.
    fn rat_max_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_max_le.clone(), [a, b, cc, h1, h2])
    }
    /// `NNRat.val_ofRat x h : NNRat.val (NNRat.ofRat x h) = x`.
    fn val_ofrat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnrat_val_ofrat.clone(), [x, h])
    }
    /// `NNRat.ofRat x h : NNRat`.
    fn of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnrat_of_rat.clone(), [x, h])
    }
}

impl Environment {
    /// Register `NNRat.max`, `NNRat.val_max`, and the three lattice lemmas
    /// (`le_max_left` / `le_max_right` / `max_le`). Idempotent. Pulls in the
    /// Stage-B1 base + the on-main `Rat.max` lattice surface.
    pub fn init_algebra_nnreal_nnrat_max_recovered(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat()?;
        // Rat.max + Rat.le_max_left/right + Rat.max_le + Rat.le_trans/le_total/…
        self.register_rat_minmax_proofs()?;
        let c = NNRatMaxConstsRecovered::new();
        self.register_nnrat_max_recovered(&c)?;
        self.register_nnrat_val_max_recovered(&c)?;
        self.register_nnrat_le_max_recovered(&c, true)?;
        self.register_nnrat_le_max_recovered(&c, false)?;
        self.register_nnrat_max_le_recovered(&c)?;
        Ok(())
    }

    /// `NNRat.max p q := NNRat.ofRat (Rat.max (val p)(val q)) hnn`.
    fn register_nnrat_max_recovered(
        &mut self,
        c: &NNRatMaxConstsRecovered,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNRat.max")).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.nnrat.clone(),
            Expr::pi(BinderInfo::Default, c.nnrat.clone(), c.nnrat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let vp = c.val(p.clone());
            let vq = c.val(q.clone());
            let m = c.rmax(vp.clone(), vq.clone());
            // hnn : 0 ≤ Rat.max (val p)(val q)
            //     = Rat.le_trans 0 (val p) (max) (property p) (le_max_left vp vq)
            let hp = c.property(p.clone());
            let hmax_left = c.rat_le_max_left(vp.clone(), vq.clone());
            let hnn = c.rat_le_trans(c.rat_zero.clone(), vp.clone(), m.clone(), hp, hmax_left);
            let body = c.of_rat(m, hnn);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNRat.max"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNRat.val_max : ∀ p q, NNRat.val (NNRat.max p q) = Rat.max (val p)(val q)`.
    ///
    /// `NNRat.max p q ≡ NNRat.ofRat (Rat.max …) hnn`, so `NNRat.val (NNRat.max p q)
    /// ≡ NNRat.val (NNRat.ofRat (Rat.max …) hnn)`, and `NNRat.val_ofRat` gives the
    /// equation to `Rat.max …`. We re-use the registered `NNRat.val_ofRat` so the
    /// proof is foundational (the `Subtype` projection reduces, but we route
    /// through the named lemma for robustness against reducibility settings).
    fn register_nnrat_val_max_recovered(
        &mut self,
        c: &NNRatMaxConstsRecovered,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNRat.val_max"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let lhs = c.val(c.nmax(p.clone(), q.clone()));
            let rhs = c.rmax(c.val(p.clone()), c.val(q.clone()));
            let concl = c.eq_rat_ty(lhs, rhs);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnrat.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let vp = c.val(p.clone());
            let vq = c.val(q.clone());
            let m = c.rmax(vp.clone(), vq.clone());
            // Reconstruct the nonneg witness so val_ofRat applies to the SAME term.
            let hp = c.property(p.clone());
            let hmax_left = c.rat_le_max_left(vp.clone(), vq.clone());
            let hnn = c.rat_le_trans(c.rat_zero.clone(), vp.clone(), m.clone(), hp, hmax_left);
            // NNRat.val_ofRat (Rat.max …) hnn
            //   : NNRat.val (NNRat.ofRat (Rat.max …) hnn) = Rat.max …
            // and NNRat.val (NNRat.max p q) ≡ that LHS (NNRat.max unfolds).
            let body = c.val_ofrat(m, hnn);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.val_max"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.le_max_left  : ∀ p q, NNRat.le p (NNRat.max p q)` (left=true) /
    /// `NNRat.le_max_right : ∀ p q, NNRat.le q (NNRat.max p q)` (left=false).
    ///
    /// `NNRat.le p (max p q) ≡ Rat.le (val p) (val (max p q))`. We need
    /// `Rat.le (val p) (Rat.max (val p)(val q))` (= `Rat.le_max_left`), so we
    /// transport the latter along `NNRat.val_max p q : val (max p q) = Rat.max …`
    /// backwards (motive on the RIGHT operand of `Rat.le`).
    fn register_nnrat_le_max_recovered(
        &mut self,
        c: &NNRatMaxConstsRecovered,
        left: bool,
    ) -> Result<(), EnvError> {
        let name = if left {
            Name::from_string("NNRat.le_max_left")
        } else {
            Name::from_string("NNRat.le_max_right")
        };
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let val_max = Expr::const_(Name::from_string("NNRat.val_max"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let lhs = if left { p.clone() } else { q.clone() };
            let concl = c.le(lhs, c.nmax(p.clone(), q.clone()));
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnrat.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let vp = c.val(p.clone());
            let vq = c.val(q.clone());
            let v_lhs = if left { vp.clone() } else { vq.clone() };
            let rmax = c.rmax(vp.clone(), vq.clone());
            let v_max = c.val(c.nmax(p.clone(), q.clone()));

            // base : Rat.le v_lhs (Rat.max vp vq)
            let base = if left {
                c.rat_le_max_left(vp.clone(), vq.clone())
            } else {
                c.rat_le_max_right(vp.clone(), vq.clone())
            };
            // eq : NNRat.val (max p q) = Rat.max vp vq   (NNRat.val_max p q)
            let eq = Expr::apps(val_max.clone(), [p.clone(), q.clone()]);
            // Transport base : (v_lhs ≤ Rat.max) to (v_lhs ≤ val(max)) via eq⁻¹.
            // Use Eq.subst with a=Rat.max, b=val(max) requires eq : Rat.max = val(max).
            // We have eq : val(max) = Rat.max, so subst with motive on the right
            // operand and (a:=val(max), b:=Rat.max) goes the WRONG way. Instead
            // substitute with eq directly: motive t := Rat.le v_lhs t, a:=val(max),
            // b:=Rat.max — that transports (v_lhs ≤ val(max)) → (v_lhs ≤ Rat.max).
            // We want the reverse, so use Eq.symm on eq first.
            let eq_symm = {
                let eq_symm_c = Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                );
                // @Eq.symm Rat (val(max)) (Rat.max) eq : Rat.max = val(max)
                Expr::apps(eq_symm_c, [c.rat.clone(), v_max.clone(), rmax.clone(), eq])
            };
            // motive t := Rat.le v_lhs t
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat.clone());
                let body = c.rle(v_lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // subst motive (a:=Rat.max) (b:=val(max)) (eq_symm) base : Rat.le v_lhs (val(max))
            let body = c.subst_rat(motive, rmax, v_max, eq_symm, base);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.max_le : ∀ p q r, NNRat.le p r → NNRat.le q r → NNRat.le (NNRat.max p q) r`.
    ///
    /// `NNRat.le (max p q) r ≡ Rat.le (val (max p q)) (val r)`. `Rat.max_le` gives
    /// `Rat.le (Rat.max vp vq) (val r)` from `vp ≤ vr` and `vq ≤ vr` (which are
    /// the unfolded hypotheses). Transport along `NNRat.val_max p q` (motive on
    /// the LEFT operand).
    fn register_nnrat_max_le_recovered(
        &mut self,
        c: &NNRatMaxConstsRecovered,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNRat.max_le")).is_some() {
            return Ok(());
        }
        let val_max = Expr::const_(Name::from_string("NNRat.val_max"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let (r_id, r) = b.fresh_local(c.nnrat.clone());
            let h1_ty = c.le(p.clone(), r.clone());
            let h2_ty = c.le(q.clone(), r.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, _h2) = b.fresh_local(h2_ty.clone());
            let concl = c.le(c.nmax(p.clone(), q.clone()), r.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let (r_id, r) = b.fresh_local(c.nnrat.clone());
            let h1_ty = c.le(p.clone(), r.clone());
            let h2_ty = c.le(q.clone(), r.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());

            let vp = c.val(p.clone());
            let vq = c.val(q.clone());
            let vr = c.val(r.clone());
            let rmax = c.rmax(vp.clone(), vq.clone());
            let v_max = c.val(c.nmax(p.clone(), q.clone()));

            // h1 : NNRat.le p r ≡ Rat.le vp vr ; h2 : Rat.le vq vr (defeq).
            // base : Rat.le (Rat.max vp vq) vr  via Rat.max_le.
            let base = c.rat_max_le(vp.clone(), vq.clone(), vr.clone(), h1, h2);
            // eq : NNRat.val (max p q) = Rat.max vp vq.
            let eq = Expr::apps(val_max.clone(), [p.clone(), q.clone()]);
            let eq_symm = {
                let eq_symm_c = Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                );
                Expr::apps(eq_symm_c, [c.rat.clone(), v_max.clone(), rmax.clone(), eq])
            };
            // motive t := Rat.le t vr
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat.clone());
                let body = c.rle(t, vr.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // subst motive (a:=Rat.max) (b:=val(max)) eq_symm base : Rat.le (val(max)) vr
            let body = c.subst_rat(motive, rmax, v_max, eq_symm, base);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNRat.max_le"),
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

    const DEFS: &[&str] = &["NNRat.max"];
    const THEOREMS: &[&str] = &[
        "NNRat.val_max",
        "NNRat.le_max_left",
        "NNRat.le_max_right",
        "NNRat.max_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_nnrat_max_recovered()
            .expect("init_algebra_nnreal_nnrat_max_recovered");
        env.init_algebra_nnreal_nnrat_max_recovered()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_nnrat_max_all_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_nnrat_max_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
