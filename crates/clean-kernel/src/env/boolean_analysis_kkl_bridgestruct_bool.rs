// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL STRUCTURAL bridge — the boolean conjunct-extraction helper (axiom-free).
//!
//! Split out of `boolean_analysis_kkl_bridgestruct_pointwise` to keep both files
//! under the 500-line module budget. Owns the single brick
//!
//! ```text
//! Bool.and_left_eq_true : ∀ (a b : Bool), Bool.and a b = Bool.true → a = Bool.true
//! ```
//!
//! used by the double-count bound (`boolean_analysis_kkl_bridgestruct_dc`) to turn
//! "the band bit fired" (`band = and (ble 1 |S|) (not (ble (k+1) |S|)) = true`)
//! into "the `|S| ≥ 1` conjunct fired" (`ble 1 |S| = true`), so the degree bound
//! `1 ≤ |S|` can be derived.
//!
//! ## Proof
//!
//! `Bool.rec` on `a` (Prop motive, universe 0):
//! - `a = true`: the goal is `true = true`, closed by `Eq.refl true`;
//! - `a = false`: `Bool.and false b ≡ Bool.false`, so the hypothesis is
//!   `false = true`, refuted by `Bool.noConfusion`.
//!
//! ## Soundness
//!
//! A CHECKED `Declaration::Theorem`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure. No `sorry`/`add_decl_unchecked`/`add_decl_structural`/
//! `native_decide`. No axiom is added or removed. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `Bool.and_left_eq_true : ∀ (a b : Bool), Bool.and a b = Bool.true → a = Bool.true`.
    ///
    /// `Bool.rec` on `a` (Prop motive, universe 0): `a = true` ⟹ `Eq.refl true`;
    /// `a = false` makes `Bool.and false b ≡ Bool.false`, so the hypothesis is
    /// `false = true`, refuted by `Bool.noConfusion`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_bool_and_left_eq_true(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Bool.and_left_eq_true");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;

        let u0 = Level::zero();
        let u1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let bool_ty = k("Bool");
        let bool_true = k("Bool.true");
        let bool_false = k("Bool.false");
        let bool_and = k("Bool.and");
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![u0.clone()]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![u0]);
        let eq_bool = move |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
                [bool_ty.clone(), l, r],
            )
        };
        let band = |a: Expr, b: Expr| Expr::apps(bool_and.clone(), [a, b]);
        let bool_c = k("Bool");

        // hyp_at a b : Bool.and a b = Bool.true ; goal_at a : a = Bool.true.
        let hyp_at = |a: Expr, b: Expr| eq_bool(band(a, b), bool_true.clone());
        let goal_at = |a: Expr| eq_bool(a, bool_true.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());
            let ante = hyp_at(a.clone(), bv.clone());
            let concl = goal_at(a.clone());
            let (h_id, _) = b.fresh_local(ante.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, ante, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let (bv_id, bv) = b.fresh_local(bool_c.clone());

            // motive : fun (a' : Bool) => (Bool.and a' b = true) → a' = true
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = d.fresh_local(bool_c.clone());
                let imp = Expr::pi(
                    BinderInfo::Default,
                    hyp_at(ap.clone(), bv.clone()),
                    goal_at(ap.clone()),
                );
                d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), imp))
            };

            // false minor : (Bool.and false b = true) → false = true.
            //   Bool.and false b ≡ false, so h : false = true; Bool.noConfusion.
            let false_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let ante = hyp_at(bool_false.clone(), bv.clone());
                let (h_id, h) = d.fresh_local(ante.clone());
                let body = Expr::apps(
                    no_conf.clone(),
                    [
                        goal_at(bool_false.clone()),
                        bool_false.clone(),
                        bool_true.clone(),
                        h,
                    ],
                );
                d.finish_child(d.mk_lam(h_id, BinderInfo::Default, ante, body))
            };

            // true minor : (Bool.and true b = true) → true = true.
            //   ignore the hypothesis; Eq.refl true.
            let true_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let ante = hyp_at(bool_true.clone(), bv.clone());
                let (h_id, _h) = d.fresh_local(ante.clone());
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [bool_c.clone(), bool_true.clone()],
                );
                d.finish_child(d.mk_lam(h_id, BinderInfo::Default, ante, body))
            };

            // @Bool.rec.{0} motive false_minor true_minor a : motive a
            let body = Expr::apps(bool_rec0, [motive, false_minor, true_minor, a.clone()]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_bool_and_left_eq_true_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_bool_and_left_eq_true()
            .expect("register_bool_and_left_eq_true");
        env.register_bool_and_left_eq_true().expect("idempotent");
        let nm = Name::from_string("Bool.and_left_eq_true");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Bool.and_left_eq_true must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "Bool.and_left_eq_true must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "Bool.and_left_eq_true closure must be empty (foundational-only)"
        );
    }
}
