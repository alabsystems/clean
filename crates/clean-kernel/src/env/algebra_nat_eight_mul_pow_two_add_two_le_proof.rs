// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE budget-exponent gluing lemma
//!
//! ```text
//! Nat.eight_mul_pow_two_add_two_le : ∀ e : Nat,
//!   Nat.le (Nat.mul 8 (Nat.pow 2 (Nat.add e 2))) (Nat.mul 48 (Nat.pow 2 e))
//! ```
//!
//! i.e. `8·2^(e+2) ≤ 48·2^e`. With `d := 2^(e+2)`, the junta-SIZE bound has an
//! `8·d = 8·2^(e+2)` budget exponent that must fit inside the `48·2^e` budget
//! (`Nat.pow 2 (48·2^e)`). Since `2^(e+2) = 2^e·2² = 4·2^e`, the LHS is
//! `8·4·2^e = 32·2^e ≤ 48·2^e`. Purely arithmetic — no Friedgut/boolean content
//! — banked as a reusable `Nat` lemma for the v3 SIZE derivation.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! Let `q := Nat.pow 2 e`. The constructive `Nat.pow_add 2 e 2` gives
//! `h1 : 2^(e+2) = q · 2²` (note `2² ≡ Nat.pow 2 2`, defeq to `4`).
//!
//! Build the equation `key : 8·2^(e+2) = (8·2²)·q` by chaining
//! - `congrArg (λ x => 8·x) h1`              : `8·2^(e+2) = 8·(q·2²)`,
//! - `congrArg (λ x => 8·x) (mul_comm q 2²)` : `8·(q·2²) = 8·(2²·q)`,
//! - `Eq.symm (mul_assoc 8 2² q)`            : `8·(2²·q) = (8·2²)·q`.
//!
//! `(8·2²)·q ≡ 32·q` by defeq (`Nat.mul 8 (Nat.pow 2 2) ≡ 32`, fully closed).
//! `step_le := Nat.mul_le_mul_right 32 48 q h_32_le_48 : Nat.le (32·q) (48·q)`,
//! where `h_32_le_48 : 32 ≤ 48` is a closed `Nat.le.step` chain off
//! `Nat.le.refl 32`. Finally transport the goal LHS with
//! `Eq.subst Nat (λ x => Nat.le x (48·q)) ((8·2²)·q) (8·2^(e+2)) (Eq.symm key)
//!   step_le : Nat.le (8·2^(e+2)) (48·q)`.
//!
//! # Axiom closure
//!
//! Every dependency (`Nat.pow_add`, `Nat.mul_comm`, `Nat.mul_assoc`,
//! `Nat.mul_le_mul_right`, plus `Eq` built-ins `Eq.refl/symm/trans/subst`,
//! `congrArg`) is a constructive `Declaration::Theorem` / `Eq` built-in with an
//! empty domain-axiom closure, so the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.eight_mul_pow_two_add_two_le` as a kernel-checked
    /// constructive theorem: `∀ e, 8·2^(e+2) ≤ 48·2^e`.
    pub(crate) fn register_nat_eight_mul_pow_two_add_two_le_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.eight_mul_pow_two_add_two_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step
        self.register_nat_pow_add_proof()?; // Nat.pow_add
        self.register_nat_mul_comm_proof()?; // Nat.mul_comm
        self.register_nat_mul_assoc_proof()?; // Nat.mul_assoc
        self.register_nat_arith_order_proofs()?; // Nat.mul_le_mul_right

        // ── Kernel constants ────────────────────────────────────────────────
        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let pow_add = Expr::const_(Name::from_string("Nat.pow_add"), vec![]);
        let mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
        let mul_assoc = Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]);
        let mul_le_mul_right = Expr::const_(Name::from_string("Nat.mul_le_mul_right"), vec![]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
        // congrArg.{1,1}
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let succ = |x: Expr| Expr::app(nat_succ.clone(), x);
        let lit = |n: u64| {
            let mut acc = nat_zero.clone();
            for _ in 0..n {
                acc = Expr::app(nat_succ.clone(), acc);
            }
            acc
        };
        let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
        let mul = |x: Expr, y: Expr| Expr::apps(nat_mul.clone(), [x, y]);
        let pow = |a: Expr, x: Expr| Expr::apps(nat_pow.clone(), [a, x]);
        let le = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);

        let two = lit(2);
        let eight = lit(8);
        let forty_eight = lit(48);

        // pow_two_2 := Nat.pow 2 2 (defeq 4)
        let pow_two_2 = pow(two.clone(), two.clone());

        // ── Type: ∀ e, Nat.le (8 · 2^(e+2)) (48 · 2^e) ───────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let lhs = mul(eight.clone(), pow(two.clone(), add(e.clone(), two.clone())));
            let rhs = mul(forty_eight.clone(), pow(two.clone(), e.clone()));
            let concl = le(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => <proof> ─────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let q = pow(two.clone(), e.clone()); // 2^e
            let pow_e2 = pow(two.clone(), add(e.clone(), two.clone())); // 2^(e+2)
            let q_mul_p2 = mul(q.clone(), pow_two_2.clone()); // q · 2²
            let p2_mul_q = mul(pow_two_2.clone(), q.clone()); // 2² · q
            let eight_p2_q = mul(mul(eight.clone(), pow_two_2.clone()), q.clone()); // (8·2²)·q

            // h1 := Nat.pow_add 2 e 2 : 2^(e+2) = q · 2²
            let h1 = Expr::apps(pow_add.clone(), [two.clone(), e.clone(), two.clone()]);

            // λ x => 8 · x  (for congrArg)
            let mul8 = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = mul(eight.clone(), z);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };

            // c1 := congrArg (λx=>8·x) (h1 : 2^(e+2)=q·2²) : 8·2^(e+2) = 8·(q·2²)
            let c1 = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    pow_e2.clone(),
                    q_mul_p2.clone(),
                    mul8.clone(),
                    h1,
                ],
            );

            // h_comm := Nat.mul_comm q 2² : q·2² = 2²·q
            let h_comm = Expr::apps(mul_comm.clone(), [q.clone(), pow_two_2.clone()]);
            // c2 := congrArg (λx=>8·x) h_comm : 8·(q·2²) = 8·(2²·q)
            let c2 = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    q_mul_p2.clone(),
                    p2_mul_q.clone(),
                    mul8,
                    h_comm,
                ],
            );

            // h_assoc := Nat.mul_assoc 8 2² q : (8·2²)·q = 8·(2²·q)
            let h_assoc = Expr::apps(
                mul_assoc.clone(),
                [eight.clone(), pow_two_2.clone(), q.clone()],
            );
            // c3 := Eq.symm h_assoc : 8·(2²·q) = (8·2²)·q
            let eight_mul_p2q = mul(eight.clone(), p2_mul_q.clone()); // 8·(2²·q)
            let c3 = Expr::apps(
                eq_symm.clone(),
                [
                    nat.clone(),
                    eight_p2_q.clone(),
                    eight_mul_p2q.clone(),
                    h_assoc,
                ],
            );

            // c12 := Eq.trans c1 c2 : 8·2^(e+2) = 8·(2²·q)
            let eight_mul_e2 = mul(eight.clone(), pow_e2.clone()); // 8·2^(e+2)
            let eight_mul_qp2 = mul(eight.clone(), q_mul_p2.clone()); // 8·(q·2²)
            let c12 = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    eight_mul_e2.clone(),
                    eight_mul_qp2.clone(),
                    eight_mul_p2q.clone(),
                    c1,
                    c2,
                ],
            );
            // key := Eq.trans c12 c3 : 8·2^(e+2) = (8·2²)·q
            let key = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    eight_mul_e2.clone(),
                    eight_mul_p2q.clone(),
                    eight_p2_q.clone(),
                    c12,
                    c3,
                ],
            );

            // h_32_le_48 : Nat.le 32 48 (closed Nat.le.step chain off le.refl 32)
            let thirty_two = lit(32);
            let h_32_le_48 = {
                let mut acc = Expr::app(nat_le_refl.clone(), thirty_two.clone()); // 32 ≤ 32
                let mut cur = thirty_two.clone();
                for _ in 0..16u64 {
                    acc = Expr::apps(nat_le_step.clone(), [thirty_two.clone(), cur.clone(), acc]);
                    cur = succ(cur);
                }
                acc
            };

            // step_le := Nat.mul_le_mul_right 32 48 q h_32_le_48 : 32·q ≤ 48·q
            // (32·q ≡ (8·2²)·q by defeq, so this is the motive at (8·2²)·q.)
            let step_le = Expr::apps(
                mul_le_mul_right.clone(),
                [
                    thirty_two.clone(),
                    forty_eight.clone(),
                    q.clone(),
                    h_32_le_48,
                ],
            );

            // motive z := Nat.le z (48·q)
            let rhs_48q = mul(forty_eight.clone(), q.clone());
            let motive = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = le(z, rhs_48q.clone());
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };

            // symm_key := Eq.symm key : (8·2²)·q = 8·2^(e+2)
            let symm_key = Expr::apps(
                eq_symm.clone(),
                [nat.clone(), eight_mul_e2.clone(), eight_p2_q.clone(), key],
            );

            // body := Eq.subst Nat motive ((8·2²)·q) (8·2^(e+2)) symm_key step_le
            //   : Nat.le (8·2^(e+2)) (48·q)
            let body = Expr::apps(
                eq_subst.clone(),
                [
                    nat.clone(),
                    motive,
                    eight_p2_q.clone(),
                    eight_mul_e2.clone(),
                    symm_key,
                    step_le,
                ],
            );

            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: Real kernel-checked proof term. `8·2^(e+2) ≤ 48·2^e` is
        // proved by rewriting `2^(e+2) = 2^e·2²` (constructive `Nat.pow_add`),
        // re-associating `8·(2^e·2²)` to `(8·2²)·2^e ≡ 32·2^e` (constructive
        // `Nat.mul_comm`, `Nat.mul_assoc`, plus kernel defeq `8·2² ≡ 32`), then
        // `Nat.mul_le_mul_right 32 48 (2^e)` with `32 ≤ 48` discharged by a
        // closed `Nat.le.step` chain. The result is transported to the goal LHS
        // by `Eq.subst`. No `sorry`, no self-reference, no domain-axiom
        // dependency — all consumed theorems are themselves constructive.
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
    fn test_eight_mul_pow_two_add_two_le_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_eight_mul_pow_two_add_two_le_proof()
            .expect("register");
        env.register_nat_eight_mul_pow_two_add_two_le_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.eight_mul_pow_two_add_two_le");
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

    /// Ground sanity at `e = 0`: `8·2^2 ≤ 48·2^0`, i.e. `32 ≤ 48`.
    #[test]
    fn test_eight_mul_pow_two_add_two_le_ground_zero() {
        let mut env = Environment::with_prelude();
        env.register_nat_eight_mul_pow_two_add_two_le_proof()
            .expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let lit = |n: u64| {
            let mut acc = nat_zero.clone();
            for _ in 0..n {
                acc = Expr::app(nat_succ.clone(), acc);
            }
            acc
        };
        let thm = Expr::const_(
            Name::from_string("Nat.eight_mul_pow_two_add_two_le"),
            vec![],
        );
        let app = Expr::app(thm, nat_zero.clone());
        let lhs = Expr::apps(
            nat_mul.clone(),
            [
                lit(8),
                Expr::apps(
                    nat_pow.clone(),
                    [
                        lit(2),
                        Expr::apps(nat_add.clone(), [nat_zero.clone(), lit(2)]),
                    ],
                ),
            ],
        );
        let rhs = Expr::apps(
            nat_mul.clone(),
            [
                lit(48),
                Expr::apps(nat_pow.clone(), [lit(2), nat_zero.clone()]),
            ],
        );
        let expected = Expr::apps(nat_le.clone(), [lhs, rhs]);
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("ground e=0 instance should type-check: {e:?}"));
    }
}
