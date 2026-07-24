// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.add_lt_add_of_lt_of_le` (the mixed strict/weak
//! additive monotonicity rung `NNReal.IsCauchy_mul` needs).
//!
//! # Why this module exists
//!
//! The product-Cauchy bound combines a STRICT cross-term bound with a WEAK one
//! when summing the two `ε/2` budgets. The strict-strict twin `Rat.add_lt_add`
//! is on main, but the mixed `a<b → c≤d → a+c < b+d` is genuinely absent. This
//! module proves it directly (ZERO axioms added):
//!
//! - `Rat.add_lt_add_of_lt_of_le : ∀ a b c d : Rat,
//!       Rat.lt a b → Rat.le c d → Rat.lt (Rat.add a c) (Rat.add b d)`
//!
//! Proof: `Rat.add_lt_add_right a b c h1 : (a+c) < (b+c)`, then
//! `Rat.add_le_add_left c d h2 b : (b+c) ≤ (b+d)`, then
//! `Rat.lt_of_lt_of_le (a+c)(b+c)(b+d) … : (a+c) < (b+d)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.add_lt_add_of_lt_of_le` + `Rat.lt_add_of_pos_right`.
    /// Idempotent. Pulls in the strict / weak additive monotonicity spine and
    /// the mixed-transitivity lemmas.
    pub fn init_algebra_rat_add_lt_add_mixed(&mut self) -> Result<(), EnvError> {
        // Rat.add_lt_add_right, Rat.add_le_add_right, Rat.add_lt_add,
        // Rat.lt_of_lt_of_le, Rat.lt_of_le_of_lt, Rat.add_lt_add_left.
        self.init_boolean_analysis_kkl_strictadd2()?;
        // Rat.add_le_add_left, Rat.add_zero (via the quotient payoff inside
        // field-inst).
        self.init_rat_field_inst()?;
        self.init_eq()?;

        self.register_rat_add_lt_add_of_lt_of_le()?;
        self.register_rat_lt_add_of_pos_right()?;
        self.register_rat_le_add_of_nonneg_left()
    }

    /// `Rat.le_add_of_nonneg_left : ∀ a p, Rat.le Rat.zero p → Rat.le a (Rat.add p a)`.
    ///
    /// `Rat.le_add_of_nonneg_right a p h : a ≤ a+p`, then `Eq.subst` the RHS
    /// `a+p → p+a` via `Rat.add_comm a p` (motive `t := a ≤ t`).
    fn register_rat_le_add_of_nonneg_left(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_add_of_nonneg_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (p_id, p) = b.fresh_local(rat.clone());
            let h_ty = le(zero.clone(), p.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = le(a.clone(), add(p.clone(), a.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (p_id, p) = b.fresh_local(rat.clone());
            let h_ty = le(zero.clone(), p.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());

            // raw : a ≤ a+p  := le_add_of_nonneg_right a p h.
            let le_add_nn_right =
                Expr::const_(Name::from_string("Rat.le_add_of_nonneg_right"), vec![]);
            let raw = Expr::apps(le_add_nn_right, [a.clone(), p.clone(), h.clone()]);
            // motive t := a ≤ t.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(rat.clone());
                let body = le(a.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };
            // add_comm a p : (a+p) = (p+a).
            let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
            let h_eq = Expr::apps(add_comm, [a.clone(), p.clone()]);
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let ap = add(a.clone(), p.clone());
            let pa = add(p.clone(), a.clone());
            let body = Expr::apps(eq_subst, [rat.clone(), motive, ap, pa, h_eq, raw]);

            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(p_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_add_of_pos_right : ∀ a p, Rat.lt Rat.zero p → Rat.lt a (Rat.add a p)`.
    ///
    /// `Rat.add_lt_add_left Rat.zero p a hp : (a+0) < (a+p)`, then `Eq.subst` the
    /// LHS `(a+0) → a` via `Rat.add_zero a` (motive `t := t < a+p`).
    fn register_rat_lt_add_of_pos_right(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_add_of_pos_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let lt = |a: Expr, b: Expr| Expr::apps(rat_lt.clone(), [a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (p_id, p) = b.fresh_local(rat.clone());
            let hp_ty = lt(zero.clone(), p.clone());
            let (hp_id, _hp) = b.fresh_local(hp_ty.clone());
            let concl = lt(a.clone(), add(a.clone(), p.clone()));
            let e = b.mk_pi(hp_id, BinderInfo::Default, hp_ty, concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (p_id, p) = b.fresh_local(rat.clone());
            let hp_ty = lt(zero.clone(), p.clone());
            let (hp_id, hp) = b.fresh_local(hp_ty.clone());

            // raw : (a+0) < (a+p)  := add_lt_add_left 0 p a hp.
            let add_lt_add_left = Expr::const_(Name::from_string("Rat.add_lt_add_left"), vec![]);
            let raw = Expr::apps(
                add_lt_add_left,
                [zero.clone(), p.clone(), a.clone(), hp.clone()],
            );
            // motive t := t < (a+p).
            let ap = add(a.clone(), p.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(rat.clone());
                let body = lt(t, ap.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };
            // add_zero a : (a+0) = a.
            let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
            let h_eq = Expr::app(add_zero, a.clone()); // (a+0) = a
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let a0 = add(a.clone(), zero.clone());
            let body = Expr::apps(eq_subst, [rat.clone(), motive, a0, a.clone(), h_eq, raw]);

            let e = b.mk_lam(hp_id, BinderInfo::Default, hp_ty, body);
            let e = b.mk_lam(p_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_lt_add_of_lt_of_le :
    ///    ∀ a b c d, Rat.lt a b → Rat.le c d → Rat.lt (a+c) (b+d)`.
    fn register_rat_add_lt_add_of_lt_of_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_lt_add_of_lt_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let lt = |a: Expr, b: Expr| Expr::apps(rat_lt.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let (dv_id, dv) = b.fresh_local(rat.clone());
            let h1_ty = lt(a.clone(), bv.clone());
            let h2_ty = le(cv.clone(), dv.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, _h2) = b.fresh_local(h2_ty.clone());
            let concl = lt(add(a.clone(), cv.clone()), add(bv.clone(), dv.clone()));
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(dv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let (dv_id, dv) = b.fresh_local(rat.clone());
            let h1_ty = lt(a.clone(), bv.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = le(cv.clone(), dv.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());

            // step1 : (a+c) < (b+c)  := Rat.add_lt_add_right a b c h1.
            let add_lt_add_right = Expr::const_(Name::from_string("Rat.add_lt_add_right"), vec![]);
            let step1 = Expr::apps(
                add_lt_add_right,
                [a.clone(), bv.clone(), cv.clone(), h1.clone()],
            );
            // step2 : (b+c) ≤ (b+d)  := Rat.add_le_add_left c d h2 b.
            //   (`add_le_add_left a b h c : (c+a) ≤ (c+b)`, arg order a,b,h,c.)
            let add_le_add_left = Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]);
            let step2 = Expr::apps(
                add_le_add_left,
                [cv.clone(), dv.clone(), h2.clone(), bv.clone()],
            );
            // lt_of_lt_of_le (a+c)(b+c)(b+d) step1 step2 : (a+c) < (b+d).
            let lt_of_lt_of_le = Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]);
            let body = Expr::apps(
                lt_of_lt_of_le,
                [
                    add(a.clone(), cv.clone()),
                    add(bv.clone(), cv.clone()),
                    add(bv.clone(), dv.clone()),
                    step1,
                    step2,
                ],
            );

            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(dv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(cv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
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
    fn test_add_lt_add_of_lt_of_le_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_add_lt_add_mixed()
            .expect("init_algebra_rat_add_lt_add_mixed");
        env.init_algebra_rat_add_lt_add_mixed().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Rat.add_lt_add_of_lt_of_le",
            "Rat.lt_add_of_pos_right",
            "Rat.le_add_of_nonneg_left",
        ] {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));

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
