// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `NNRat` order/max layer for `IsCauchy_bounded`.
//!
//! # Why this module exists
//!
//! `NNReal.IsCauchy_bounded` (`algebra_nnreal_mul.rs`) needs a finite running
//! max over the nonneg-rational base, which in turn needs an axiom-free
//! `NNRat.max` and its lattice lemmas. `Rat.max` is available as a CONSTRUCTIVE
//! definition (`Bool.rec` on `Rat.ble`, `register_rat_minmax_proofs`) with the
//! lattice theorems `Rat.le_max_left` / `Rat.le_max_right` / `Rat.max_le`, all
//! empty-closure. We lift them to `NNRat` here.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNRat.le_refl  : ∀ p, NNRat.le p p`
//! - `NNRat.le_trans : ∀ p q r, NNRat.le p q → NNRat.le q r → NNRat.le p r`
//! - `NNRat.max : NNRat → NNRat → NNRat`
//!     `:= fun p q => NNRat.ofRat (Rat.max (val p)(val q)) hnn`
//!     (`hnn : 0 ≤ Rat.max (val p)(val q)` from `property p` + `Rat.le_max_left`)
//! - `NNRat.le_max_left  : ∀ p q, NNRat.le p (NNRat.max p q)`
//! - `NNRat.le_max_right : ∀ p q, NNRat.le q (NNRat.max p q)`
//!
//! Each `Declaration::Theorem` (except `NNRat.max`, a `Definition`),
//! `ProofQuality::Constructive`, empty admitted-axiom closure (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::ExprKind;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `NNRat` order/max layer.
pub(crate) struct NNRatMaxConsts {
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    prop: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_max: Expr,
    rat_le_refl: Expr,
    rat_le_trans: Expr,
    rat_le_max_left: Expr,
    rat_le_max_right: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    nnrat_val_of_rat: Expr,
    nnrat_property: Expr,
    nnrat_le: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl NNRatMaxConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            #[cfg(test)]
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_max: k("Rat.max"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_trans: k("Rat.le_trans"),
            rat_le_max_left: k("Rat.le_max_left"),
            rat_le_max_right: k("Rat.le_max_right"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnrat_val_of_rat: k("NNRat.val_ofRat"),
            nnrat_property: k("NNRat.property"),
            nnrat_le: k("NNRat.le"),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1]),
        }
    }

    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rmax(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [a, b])
    }
    fn nle(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le.clone(), [p, q])
    }
    fn property(&self, p: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), p)
    }
    /// `Rat.le_refl a : Rat.le a a`.
    fn rle_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    /// `Rat.le_trans a b c hab hbc : Rat.le a c`.
    fn rle_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.le_max_left a b : Rat.le a (Rat.max a b)`.
    fn rle_max_left(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_max_left.clone(), [a, b])
    }
    /// `Rat.le_max_right a b : Rat.le b (Rat.max a b)`.
    fn rle_max_right(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_max_right.clone(), [a, b])
    }
    /// `NNRat.val_ofRat x h : Eq Rat (NNRat.val (NNRat.ofRat x h)) x`.
    fn val_of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnrat_val_of_rat.clone(), [x, h])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }

    /// The nonneg witness `0 ≤ Rat.max (val p)(val q)`:
    ///   `Rat.le_trans 0 (val p) (Rat.max (val p)(val q)) (property p)
    ///      (Rat.le_max_left (val p)(val q))`.
    fn max_nonneg(&self, p: &Expr, q: &Expr) -> Expr {
        let vp = self.val(p.clone());
        let vq = self.val(q.clone());
        self.rle_trans(
            self.rat_zero.clone(),
            vp.clone(),
            self.rmax(vp.clone(), vq.clone()),
            self.property(p.clone()),
            self.rle_max_left(vp, vq),
        )
    }
    /// `NNRat.max p q : NNRat` (built as `ofRat (Rat.max …) (max_nonneg …)`).
    fn nnmax(&self, p: &Expr, q: &Expr) -> Expr {
        let vp = self.val(p.clone());
        let vq = self.val(q.clone());
        Expr::apps(
            self.nnrat_of_rat.clone(),
            [self.rmax(vp, vq), self.max_nonneg(p, q)],
        )
    }
}

impl Environment {
    /// Register the `NNRat` order/max layer. Idempotent.
    pub fn init_algebra_nnreal_nnrat_max(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat()?; // NNRat, NNRat.val, NNRat.le, val_ofRat, property
        self.register_rat_minmax_proofs()?; // Rat.max + Rat.le_max_left/right/max_le
        self.init_eq()?;

        let c = NNRatMaxConsts::new();
        self.register_nnrat_le_refl(&c)?;
        self.register_nnrat_le_trans(&c)?;
        self.register_nnrat_max(&c)?;
        self.register_nnrat_le_max(&c, /*left=*/ true)?;
        self.register_nnrat_le_max(&c, /*left=*/ false)?;
        Ok(())
    }

    /// `NNRat.le_refl : ∀ p, NNRat.le p p` := `Rat.le_refl (val p)`.
    fn register_nnrat_le_refl(&mut self, c: &NNRatMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let body = c.nle(p.clone(), p.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let body = c.rle_refl(c.val(p.clone()));
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.le_trans : ∀ p q r, le p q → le q r → le p r`.
    fn register_nnrat_le_trans(&mut self, c: &NNRatMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.le_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let (r_id, r) = b.fresh_local(c.nnrat.clone());
            let hpq = c.nle(p.clone(), q.clone());
            let (hpq_id, _h) = b.fresh_local(hpq.clone());
            let hqr = c.nle(q.clone(), r.clone());
            let (hqr_id, _h2) = b.fresh_local(hqr.clone());
            let concl = c.nle(p.clone(), r.clone());
            let e = b.mk_pi(hqr_id, BinderInfo::Default, hqr, concl);
            let e = b.mk_pi(hpq_id, BinderInfo::Default, hpq, e);
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
            let hpq = c.nle(p.clone(), q.clone());
            let (hpq_id, hpq_h) = b.fresh_local(hpq.clone());
            let hqr = c.nle(q.clone(), r.clone());
            let (hqr_id, hqr_h) = b.fresh_local(hqr.clone());
            // NNRat.le unfolds to Rat.le on .val, so Rat.le_trans applies directly.
            let body = c.rle_trans(
                c.val(p.clone()),
                c.val(q.clone()),
                c.val(r.clone()),
                hpq_h,
                hqr_h,
            );
            let e = b.mk_lam(hqr_id, BinderInfo::Default, hqr, body);
            let e = b.mk_lam(hpq_id, BinderInfo::Default, hpq, e);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), e);
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

    /// `NNRat.max : NNRat → NNRat → NNRat`.
    fn register_nnrat_max(&mut self, c: &NNRatMaxConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.max");
        if self.get_const(&name).is_some() {
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
            let body = c.nnmax(&p, &q);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNRat.le_max_left  : ∀ p q, NNRat.le p (NNRat.max p q)` (left = true)
    /// `NNRat.le_max_right : ∀ p q, NNRat.le q (NNRat.max p q)` (left = false).
    ///
    /// `NNRat.le p (NNRat.max p q)` unfolds to `Rat.le (val p) (val (ofRat
    /// (Rat.max (vp)(vq)) hnn))`. `NNRat.val_ofRat` rewrites the RHS to
    /// `Rat.max (vp)(vq)`; the goal becomes `Rat.le (val p) (Rat.max vp vq)`
    /// = `Rat.le_max_left`. We Eq.subst the goal RHS from `Rat.max vp vq`
    /// (where the proof lives) to `val (ofRat …)` (the unfolded `NNRat.max`).
    fn register_nnrat_le_max(&mut self, c: &NNRatMaxConsts, left: bool) -> Result<(), EnvError> {
        let name = Name::from_string(if left {
            "NNRat.le_max_left"
        } else {
            "NNRat.le_max_right"
        });
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let lhs = if left { p.clone() } else { q.clone() };
            let body = c.nle(lhs, c.nnmax(&p, &q));
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnrat.clone(), body);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let vp = c.val(p.clone());
            let vq = c.val(q.clone());
            let rmax = c.rmax(vp.clone(), vq.clone());
            let hnn = c.max_nonneg(&p, &q);
            // base : Rat.le (val lhs) (Rat.max vp vq).
            let (vlhs, base) = if left {
                (vp.clone(), c.rle_max_left(vp.clone(), vq.clone()))
            } else {
                (vq.clone(), c.rle_max_right(vp.clone(), vq.clone()))
            };
            // val (ofRat (Rat.max vp vq) hnn) — the unfolded NNRat.max RHS.
            let val_max = c.val(Expr::apps(
                c.nnrat_of_rat.clone(),
                [rmax.clone(), hnn.clone()],
            ));
            // val_ofRat : Eq Rat (val (ofRat (Rat.max vp vq) hnn)) (Rat.max vp vq).
            let h_eq = c.val_of_rat(rmax.clone(), hnn);
            // motive t := Rat.le (val lhs) t. subst from (Rat.max vp vq) to val_max
            // along Eq.symm h_eq.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.rle(vlhs.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.subst(
                motive,
                rmax.clone(),
                val_max.clone(),
                c.eq_symm(val_max, rmax, h_eq),
                base,
            );
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["NNRat.max"];
    const THEOREMS: &[&str] = &[
        "NNRat.le_refl",
        "NNRat.le_trans",
        "NNRat.le_max_left",
        "NNRat.le_max_right",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_nnrat_max()
            .expect("init_algebra_nnreal_nnrat_max");
        env.init_algebra_nnreal_nnrat_max().expect("idempotent");
        env
    }

    #[test]
    fn test_nnrat_max_present_and_kernel_check() {
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
