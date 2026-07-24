// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the `Rat` cube-monotonicity brick
//!
//! ```text
//! Rat.pow3_le_pow3_of_le_nonneg : ∀ a b : Rat,
//!   Rat.le 0 a → Rat.le a b → Rat.le (Rat.mul a (Rat.mul a a)) (Rat.mul b (Rat.mul b b))
//! ```
//!
//! i.e. `0 ≤ a → a ≤ b → a³ ≤ b³` (with the cube written right-nested as
//! `a·(a·a)`, matching the v3 Friedgut SIZE statement's `K·(K·K)`). The SIZE
//! chain cubes the two-sided guard `K ≤ 2^(e+1)·eps` to `K³ ≤ (2^(e+1)·eps)³`;
//! this is exactly that monotone step. Banked as a reusable `Rat` order brick.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! - `hb    : 0 ≤ b`         via `Rat.le_trans 0 a b ha hab`,
//! - `haa   : 0 ≤ a·a`       via `Rat.mul_nonneg a a ha ha`,
//! - `inner : a·a ≤ b·b`     via `Rat.mul_le_mul a b a b ha ha hab hab`,
//! - `outer : a·(a·a) ≤ b·(b·b)`
//!            via `Rat.mul_le_mul a b (a·a) (b·b) ha haa hab inner`.
//!
//! All written through `@LE.le Rat instLERat`.
//!
//! # Axiom closure
//!
//! Every dependency (`Rat.mul_le_mul`, `Rat.mul_nonneg`, `Rat.le_trans`) is a
//! constructive `Declaration::Theorem` with an empty domain-axiom closure, so
//! the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.pow3_le_pow3_of_le_nonneg` as a kernel-checked constructive
    /// theorem: `∀ a b, 0≤a → a≤b → a³ ≤ b³` (cube `a·(a·a)`).
    pub(crate) fn register_rat_pow3_le_pow3_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.pow3_le_pow3_of_le_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_nonneg
        self.register_rat_mul_le_mul_proof()?; // Rat.mul_le_mul (this lane)
        self.register_rat_le_trans_proof()?; // Rat.le_trans

        // ── Kernel constants ────────────────────────────────────────────────
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
        let mul_le_mul = Expr::const_(Name::from_string("Rat.mul_le_mul"), vec![]);
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let mul = |x: Expr, y: Expr| Expr::apps(rat_mul.clone(), [x, y]);
        let rle =
            |x: Expr, y: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), x, y]);

        // ── Type: ∀ a b, 0≤a → a≤b → a·(a·a) ≤ b·(b·b) ───────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, _) = b.fresh_local(ha_ty.clone());
            let hab_ty = rle(a.clone(), bb.clone());
            let (hab_id, _) = b.fresh_local(hab_ty.clone());
            let cube_a = mul(a.clone(), mul(a.clone(), a.clone()));
            let cube_b = mul(bb.clone(), mul(bb.clone(), bb.clone()));
            let concl = rle(cube_a, cube_b);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        // ── Value ────────────────────────────────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hab_ty = rle(a.clone(), bb.clone());
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());

            let aa = mul(a.clone(), a.clone());
            let bbb = mul(bb.clone(), bb.clone());

            // hb : 0 ≤ b := Rat.le_trans 0 a b ha hab
            let hb = Expr::apps(
                le_trans.clone(),
                [
                    rat_zero.clone(),
                    a.clone(),
                    bb.clone(),
                    ha.clone(),
                    hab.clone(),
                ],
            );
            let _ = hb; // (not needed directly; Rat.mul_le_mul derives 0≤b internally)

            // haa : 0 ≤ a·a := Rat.mul_nonneg a a ha ha
            let haa = Expr::apps(
                mul_nonneg.clone(),
                [a.clone(), a.clone(), ha.clone(), ha.clone()],
            );

            // inner : a·a ≤ b·b := Rat.mul_le_mul a b a b ha ha hab hab
            let inner = Expr::apps(
                mul_le_mul.clone(),
                [
                    a.clone(),
                    bb.clone(),
                    a.clone(),
                    bb.clone(),
                    ha.clone(),
                    ha.clone(),
                    hab.clone(),
                    hab.clone(),
                ],
            );

            // outer : a·(a·a) ≤ b·(b·b)
            //   Rat.mul_le_mul a b (a·a) (b·b) ha haa hab inner
            let outer = Expr::apps(
                mul_le_mul.clone(),
                [
                    a.clone(),
                    bb.clone(),
                    aa.clone(),
                    bbb.clone(),
                    ha,
                    haa,
                    hab,
                    inner,
                ],
            );

            let lam_hab = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, outer);
            let lam_ha = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, lam_hab);
            let lam_bb = b.mk_lam(bb_id, BinderInfo::Default, rat.clone(), lam_ha);
            let lam_a = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), lam_bb);
            b.finish(lam_a)
        };

        // SOUNDNESS: Real kernel-checked proof term. `a³ ≤ b³` (cube `a·(a·a)`)
        // from `0≤a, a≤b` is two nested `Rat.mul_le_mul`: the inner square
        // `a·a ≤ b·b` and the outer `a·(a·a) ≤ b·(b·b)`, with `0≤a·a` supplied
        // by `Rat.mul_nonneg`. No `sorry`, no self-reference, no domain-axiom
        // dependency — all consumed theorems are constructive.
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
    fn test_rat_pow3_le_pow3_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow3_le_pow3_proof().expect("register");
        env.register_rat_pow3_le_pow3_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Rat.pow3_le_pow3_of_le_nonneg");
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
