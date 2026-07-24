// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the `Rat` cube ≤ square brick under `a ≤ 1`
//!
//! ```text
//! Rat.cube_le_sq_of_le_one_nonneg : ∀ a : Rat,
//!   Rat.le 0 a → Rat.le a Rat.one →
//!   Rat.le (Rat.mul a (Rat.mul a a)) (Rat.mul a a)
//! ```
//!
//! i.e. `0 ≤ a → a ≤ 1 → a³ ≤ a²` (cube right-nested `a·(a·a)`, square `a·a`).
//! The v3 Friedgut SIZE chain has `eps³` after cubing the guard but the budget
//! only carries an `eps²`; with `0 ≤ eps < 1` (so `eps ≤ 1`), `eps³ ≤ eps²`
//! discharges that gap. Banked as a reusable `Rat` order brick.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! - `inner : a·a ≤ a·1`  via `Rat.mul_le_mul_of_nonneg_left a a 1 (a≤1) (0≤a)`,
//! - `step  : a·(a·a) ≤ a·(a·1)`
//!           via `Rat.mul_le_mul_of_nonneg_left a (a·a) (a·1) inner (0≤a)`,
//! - `e     : a·(a·1) = a·a`  via `congrArg (λ x => a·x) (Rat.mul_one a)`,
//! - finish by `Eq.subst` of `step` along `e`:
//!   `@Eq.subst Rat (λ y => Rat.le (a·(a·a)) y) (a·(a·1)) (a·a) e step`.
//!
//! All order facts written through `@LE.le Rat instLERat`.
//!
//! # Axiom closure
//!
//! Every dependency (`Rat.mul_le_mul_of_nonneg_left`, `Rat.mul_one`, plus `Eq`
//! built-ins `Eq.subst`, `congrArg`) is a constructive `Declaration::Theorem` /
//! `Eq` built-in with an empty domain-axiom closure, so the proof quality is
//! `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.cube_le_sq_of_le_one_nonneg` as a kernel-checked
    /// constructive theorem: `∀ a, 0≤a → a≤1 → a³ ≤ a²`.
    pub(crate) fn register_rat_cube_le_sq_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cube_le_sq_of_le_one_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.init_rat_arith()?; // Rat.mul_one, Rat.one

        // ── Kernel constants ────────────────────────────────────────────────
        let l1 = Level::succ(Level::zero());
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
        let mul_le_left = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);
        let rat_mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let mul = |x: Expr, y: Expr| Expr::apps(rat_mul.clone(), [x, y]);
        let rle =
            |x: Expr, y: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), x, y]);

        // ── Type: ∀ a, 0≤a → a≤1 → a·(a·a) ≤ a·a ─────────────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, _) = b.fresh_local(ha_ty.clone());
            let h1_ty = rle(a.clone(), rat_one.clone());
            let (h1_id, _) = b.fresh_local(h1_ty.clone());
            let cube = mul(a.clone(), mul(a.clone(), a.clone()));
            let sq = mul(a.clone(), a.clone());
            let concl = rle(cube, sq);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        // ── Value ────────────────────────────────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let h1_ty = rle(a.clone(), rat_one.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());

            let aa = mul(a.clone(), a.clone()); // a·a
            let a1 = mul(a.clone(), rat_one.clone()); // a·1
            let cube = mul(a.clone(), aa.clone()); // a·(a·a)
            let a_mul_a1 = mul(a.clone(), a1.clone()); // a·(a·1)

            // inner : a·a ≤ a·1
            //   Rat.mul_le_mul_of_nonneg_left a a 1 (h1 : a≤1) (ha : 0≤a)
            let inner = Expr::apps(
                mul_le_left.clone(),
                [a.clone(), a.clone(), rat_one.clone(), h1, ha.clone()],
            );

            // step : a·(a·a) ≤ a·(a·1)
            //   Rat.mul_le_mul_of_nonneg_left a (a·a) (a·1) inner (ha : 0≤a)
            let step = Expr::apps(
                mul_le_left.clone(),
                [a.clone(), aa.clone(), a1.clone(), inner, ha],
            );

            // mo := Rat.mul_one a : a·1 = a
            let mo = Expr::app(rat_mul_one.clone(), a.clone());
            // λ x => a · x
            let mul_a = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = zb.fresh_local(rat.clone());
                let body = mul(a.clone(), x);
                zb.finish_child(zb.mk_lam(x_id, BinderInfo::Default, rat.clone(), body))
            };
            // e := congrArg (λx=>a·x) mo : a·(a·1) = a·a
            let e = Expr::apps(
                congr_arg.clone(),
                [rat.clone(), rat.clone(), a1.clone(), a.clone(), mul_a, mo],
            );

            // body := @Eq.subst Rat (λy => Rat.le (a·(a·a)) y) (a·(a·1)) (a·a) e step
            //   : Rat.le (a·(a·a)) (a·a)
            let motive = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = zb.fresh_local(rat.clone());
                let body = rle(cube.clone(), y);
                zb.finish_child(zb.mk_lam(y_id, BinderInfo::Default, rat.clone(), body))
            };
            let body = Expr::apps(
                eq_subst.clone(),
                [rat.clone(), motive, a_mul_a1.clone(), aa.clone(), e, step],
            );

            let lam_h1 = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, body);
            let lam_ha = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, lam_h1);
            let lam_a = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), lam_ha);
            b.finish(lam_a)
        };

        // SOUNDNESS: Real kernel-checked proof term. `a³ ≤ a²` (cube `a·(a·a)`,
        // square `a·a`) under `0≤a, a≤1` is `Rat.mul_le_mul_of_nonneg_left`
        // applied twice (`a·a ≤ a·1`, then `a·(a·a) ≤ a·(a·1)`), with the trailing
        // `a·1` rewritten to `a` by `Eq.subst` along
        // `congrArg (λx=>a·x) (Rat.mul_one a)`. No `sorry`, no self-reference,
        // no domain-axiom dependency — all consumed theorems are constructive.
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
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_rat_cube_le_sq_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_rat_cube_le_sq_proof().expect("register");
        env.register_rat_cube_le_sq_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Rat.cube_le_sq_of_le_one_nonneg");
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("lemma should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }
}
