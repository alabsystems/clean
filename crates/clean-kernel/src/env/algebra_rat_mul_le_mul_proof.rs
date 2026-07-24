// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the both-factor `Rat` product-monotonicity brick
//!
//! ```text
//! Rat.mul_le_mul : ∀ a b c d : Rat,
//!   Rat.le 0 a → Rat.le 0 c → Rat.le a b → Rat.le c d →
//!   Rat.le (Rat.mul a c) (Rat.mul b d)
//! ```
//!
//! The `Rat` mirror of the landed `Int.mul_le_mul`. The v3 Friedgut SIZE chain
//! repeatedly multiplies two nonneg-monotone factors (`4·9^(2d)·K³ ≤ …·…`), and
//! the on-main `Rat` surface only ships the ONE-sided
//! `Rat.mul_le_mul_of_nonneg_left/right`. This composes them into the standard
//! both-factor monotone lemma. Banked as a reusable `Rat` order brick.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! - `left  : a·c ≤ b·c`  via `Rat.mul_le_mul_of_nonneg_right c a b hab hc`
//!            (`mul_le_mul_of_nonneg_right x y z : y ≤ z → 0 ≤ x → y·x ≤ z·x`,
//!             here `x:=c, y:=a, z:=b`),
//! - `hb    : 0 ≤ b`      via `Rat.le_trans 0 a b ha hab`,
//! - `right : b·c ≤ b·d`  via `Rat.mul_le_mul_of_nonneg_left b c d hcd hb`
//!            (`mul_le_mul_of_nonneg_left x y z : y ≤ z → 0 ≤ x → x·y ≤ x·z`,
//!             here `x:=b, y:=c, z:=d`),
//! - finish `Rat.le_trans (a·c) (b·c) (b·d) left right`.
//!
//! The hypotheses/goal are written through `@LE.le Rat instLERat` (the surface
//! `Rat.le` of the Friedgut/KKL lane); the landed `Rat.le_trans` is stated over
//! the raw `Rat.le`, which is defeq, so it composes directly.
//!
//! # Axiom closure
//!
//! Every dependency (`Rat.mul_le_mul_of_nonneg_left/right`, `Rat.le_trans`) is a
//! constructive `Declaration::Theorem` with an empty domain-axiom closure, so
//! the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.mul_le_mul` as a kernel-checked constructive theorem:
    /// `∀ a b c d, 0≤a → 0≤c → a≤b → c≤d → a·c ≤ b·d`.
    pub(crate) fn register_rat_mul_le_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_le_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left/right
        self.register_rat_le_trans_proof()?; // Rat.le_trans

        // ── Kernel constants ────────────────────────────────────────────────
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
        let mul_le_left = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);
        let mul_le_right =
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let mul = |x: Expr, y: Expr| Expr::apps(rat_mul.clone(), [x, y]);
        let rle =
            |x: Expr, y: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), x, y]);

        // ── Type ─────────────────────────────────────────────────────────────
        // ∀ a b c d, 0≤a → 0≤c → a≤b → c≤d → a·c ≤ b·d
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let (cc_id, cc) = b.fresh_local(rat.clone());
            let (d_id, d) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, _) = b.fresh_local(ha_ty.clone());
            let hc_ty = rle(rat_zero.clone(), cc.clone());
            let (hc_id, _) = b.fresh_local(hc_ty.clone());
            let hab_ty = rle(a.clone(), bb.clone());
            let (hab_id, _) = b.fresh_local(hab_ty.clone());
            let hcd_ty = rle(cc.clone(), d.clone());
            let (hcd_id, _) = b.fresh_local(hcd_ty.clone());
            let concl = rle(mul(a.clone(), cc.clone()), mul(bb.clone(), d.clone()));
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd_ty, concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(hc_id, BinderInfo::Default, hc_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        // ── Value ────────────────────────────────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let (cc_id, cc) = b.fresh_local(rat.clone());
            let (d_id, d) = b.fresh_local(rat.clone());
            let ha_ty = rle(rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hc_ty = rle(rat_zero.clone(), cc.clone());
            let (hc_id, hc) = b.fresh_local(hc_ty.clone());
            let hab_ty = rle(a.clone(), bb.clone());
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            let hcd_ty = rle(cc.clone(), d.clone());
            let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());

            let ac = mul(a.clone(), cc.clone());
            let bc = mul(bb.clone(), cc.clone());
            let bd = mul(bb.clone(), d.clone());

            // left : a·c ≤ b·c
            //   Rat.mul_le_mul_of_nonneg_right c a b hab hc
            let left = Expr::apps(
                mul_le_right.clone(),
                [cc.clone(), a.clone(), bb.clone(), hab.clone(), hc],
            );

            // hb : 0 ≤ b := Rat.le_trans 0 a b ha hab
            let hb = Expr::apps(
                le_trans.clone(),
                [rat_zero.clone(), a.clone(), bb.clone(), ha, hab],
            );

            // right : b·c ≤ b·d
            //   Rat.mul_le_mul_of_nonneg_left b c d hcd hb
            let right = Expr::apps(
                mul_le_left.clone(),
                [bb.clone(), cc.clone(), d.clone(), hcd, hb],
            );

            // body : a·c ≤ b·d := Rat.le_trans (a·c) (b·c) (b·d) left right
            let body = Expr::apps(le_trans.clone(), [ac, bc, bd, left, right]);

            let lam_hcd = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, body);
            let lam_hab = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, lam_hcd);
            let lam_hc = b.mk_lam(hc_id, BinderInfo::Default, hc_ty, lam_hab);
            let lam_ha = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, lam_hc);
            let lam_d = b.mk_lam(d_id, BinderInfo::Default, rat.clone(), lam_ha);
            let lam_cc = b.mk_lam(cc_id, BinderInfo::Default, rat.clone(), lam_d);
            let lam_bb = b.mk_lam(bb_id, BinderInfo::Default, rat.clone(), lam_cc);
            let lam_a = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), lam_bb);
            b.finish(lam_a)
        };

        // SOUNDNESS: Real kernel-checked proof term. `a·c ≤ b·d` for nonneg
        // factors is the standard two-leg composition
        // `Rat.le_trans (a·c ≤ b·c) (b·c ≤ b·d)`, each leg a one-sided
        // `Rat.mul_le_mul_of_nonneg_right/left`, with `0 ≤ b` obtained by
        // `Rat.le_trans 0 a b`. No `sorry`, no self-reference, no domain-axiom
        // dependency — all three consumed theorems are constructive.
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
    fn test_rat_mul_le_mul_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_rat_mul_le_mul_proof().expect("register");
        env.register_rat_mul_le_mul_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Rat.mul_le_mul");
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
