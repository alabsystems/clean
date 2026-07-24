// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the reverse Nat-cast at the `Rat` level
//!
//! ```text
//! Rat.le_of_natCast_le_natCast : ∀ a b : Nat,
//!   (@LE.le Rat instLERat (natCast a) (natCast b)) → Nat.le a b
//! ```
//!
//! where `natCast n ≡ Rat.mk (Int.ofNat n) 1` (the KKL/Friedgut Nat→Rat cast,
//! matching `Nat.cast_le_of_ble` in `boolean_analysis_kkl_natbridge.rs`). This
//! is the converse of the forward `Nat.cast_le_of_ble` and the Rat-level
//! companion of `Int.le_of_ofNat_le_ofNat`; the v3 Friedgut SIZE branch needs
//! it to demote the cross-multiplied guard `K ≤ 2^(e+1)·eps` back to a `Nat`
//! comparison.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! `Rat.le` reduces to an `Int.le` cross-product (see `algebra_rat_order_proofs`)
//! and for the unit-denominator cast `natCast n = Rat.mk (ofNat n) 1` the
//! hypothesis
//! `hyp : @LE.le Rat instLERat (natCast a) (natCast b)`
//! is defeq to
//! `Int.le (Int.mul (ofNat a) (ofNat 1)) (Int.mul (ofNat b) (ofNat 1))`
//! (the exact defeq the forward `Nat.cast_le_of_ble` relies on). Rewriting the
//! two `Int.mul · (ofNat 1)` factors away with `Int.mul_one` (two `Eq.subst`
//! over `Int`) yields `Int.le (ofNat a) (ofNat b)`, and the landed constructive
//! `Int.le_of_ofNat_le_ofNat a b` closes the goal `Nat.le a b`.
//!
//! # Axiom closure
//!
//! Every dependency (`Int.mul_one`, `Int.le_of_ofNat_le_ofNat`, plus `Eq`
//! built-ins) is a constructive `Declaration::Theorem` / `Eq` built-in with an
//! empty domain-axiom closure, so the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.le_of_natCast_le_natCast` as a kernel-checked constructive
    /// theorem: `∀ a b : Nat, (natCast a ≤ natCast b) → Nat.le a b`.
    pub(crate) fn register_rat_le_of_natcast_le_natcast_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_natCast_le_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_le()?;
        self.init_rat()?; // Rat, Rat.mk, instLERat, Rat.le
        self.init_int_ord()?; // Int, Int.ofNat, Int.mul, Int.le
        self.register_int_mul_one_proof()?; // Int.mul_one
        self.register_int_le_of_ofnat_le_ofnat_proof()?; // Int.le_of_ofNat_le_ofNat

        // ── Kernel constants ────────────────────────────────────────────────
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![l0]);
        let int = Expr::const_(Name::from_string("Int"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
        let int_mul_one = Expr::const_(Name::from_string("Int.mul_one"), vec![]);
        let int_le_of_ofnat = Expr::const_(Name::from_string("Int.le_of_ofNat_le_ofNat"), vec![]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let of_nat = |n: Expr| Expr::app(int_of_nat.clone(), n);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone()); // Nat.succ Nat.zero
        let int_one = of_nat(nat_one.clone()); // Int.ofNat 1
        let imul = |x: Expr, y: Expr| Expr::apps(int_mul.clone(), [x, y]);
        let ile = |x: Expr, y: Expr| Expr::apps(int_le.clone(), [x, y]);
        let nle = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);
        // natCast n := Rat.mk (Int.ofNat n) 1
        let natcast = |n: Expr| Expr::apps(rat_mk.clone(), [of_nat(n), nat_one.clone()]);
        // @LE.le Rat instLERat a b
        let rat_le =
            |a: Expr, b: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), a, b]);

        // ── Type: ∀ a b : Nat, (natCast a ≤ natCast b) → Nat.le a b ──────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let ante = rat_le(natcast(a.clone()), natcast(bb.clone()));
            let (h_id, _h) = b.fresh_local(ante.clone());
            let concl = nle(a.clone(), bb.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, ante, concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // ── Value: fun (a b : Nat) (hyp : natCast a ≤ natCast b) => <proof> ──
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let ante = rat_le(natcast(a.clone()), natcast(bb.clone()));
            let (hyp_id, hyp) = b.fresh_local(ante.clone());

            let of_a = of_nat(a.clone());
            let of_b = of_nat(bb.clone());
            let mul_a1 = imul(of_a.clone(), int_one.clone()); // mul (ofNat a) 1
            let mul_b1 = imul(of_b.clone(), int_one.clone()); // mul (ofNat b) 1

            // e_a := Int.mul_one (ofNat a) : mul (ofNat a) 1 = ofNat a
            let e_a = Expr::app(int_mul_one.clone(), of_a.clone());
            // e_b := Int.mul_one (ofNat b) : mul (ofNat b) 1 = ofNat b
            let e_b = Expr::app(int_mul_one.clone(), of_b.clone());

            // subst left: motive_left x := Int.le x (mul (ofNat b) 1)
            //   @Eq.subst Int motive_left (mul (ofNat a) 1) (ofNat a) e_a hyp
            //   : Int.le (ofNat a) (mul (ofNat b) 1)
            // (hyp : LE.le Rat … is defeq to Int.le (mul (ofNat a) 1) (mul (ofNat b) 1)
            //  = motive_left (mul (ofNat a) 1).)
            let motive_left = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = d.fresh_local(int.clone());
                let body = ile(x, mul_b1.clone());
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, int.clone(), body))
            };
            let step1 = Expr::apps(
                eq_subst.clone(),
                [
                    int.clone(),
                    motive_left,
                    mul_a1.clone(),
                    of_a.clone(),
                    e_a,
                    hyp.clone(),
                ],
            );

            // subst right: motive_right y := Int.le (ofNat a) y
            //   @Eq.subst Int motive_right (mul (ofNat b) 1) (ofNat b) e_b step1
            //   : Int.le (ofNat a) (ofNat b)
            let motive_right = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = d.fresh_local(int.clone());
                let body = ile(of_a.clone(), y);
                d.finish_child(d.mk_lam(y_id, BinderInfo::Default, int.clone(), body))
            };
            let h_int = Expr::apps(
                eq_subst.clone(),
                [
                    int.clone(),
                    motive_right,
                    mul_b1.clone(),
                    of_b.clone(),
                    e_b,
                    step1,
                ],
            );

            // body := Int.le_of_ofNat_le_ofNat a b h_int : Nat.le a b
            let body = Expr::apps(int_le_of_ofnat.clone(), [a.clone(), bb.clone(), h_int]);

            let e = b.mk_lam(hyp_id, BinderInfo::Default, ante, body);
            let e = b.mk_lam(bb_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term. The hypothesis
        // `@LE.le Rat instLERat (natCast a) (natCast b)` is defeq to
        // `Int.le (mul (ofNat a) 1) (mul (ofNat b) 1)` (the `Rat.le` cross-product
        // at unit denominators — the same defeq `Nat.cast_le_of_ble` exploits).
        // Two `Eq.subst` along the constructive `Int.mul_one` strip the
        // `· (ofNat 1)` factors to `Int.le (ofNat a) (ofNat b)`, and the landed
        // constructive `Int.le_of_ofNat_le_ofNat` discharges `Nat.le a b`.
        // No `sorry`, no self-reference, no domain-axiom dependency.
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
    fn test_rat_le_of_natcast_le_natcast_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_rat_le_of_natcast_le_natcast_proof()
            .expect("register");
        env.register_rat_le_of_natcast_le_natcast_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Rat.le_of_natCast_le_natCast");
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
