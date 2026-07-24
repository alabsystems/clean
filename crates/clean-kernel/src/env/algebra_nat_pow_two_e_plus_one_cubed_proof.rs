// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE cube-exponent lemma
//!
//! ```text
//! Nat.pow_two_e_plus_one_cubed : ∀ e : Nat,
//!   Eq Nat (Nat.pow (Nat.pow 2 (Nat.add e 1)) 3)
//!          (Nat.pow 2 (Nat.add (Nat.mul 3 e) 3))
//! ```
//!
//! i.e. `(2^(e+1))³ = 2^(3e+3)`. The guard `K ≤ 2^(e+1)·eps` cubes to
//! `K³ ≤ (2^(e+1))³·eps³`, and `(2^(e+1))³ = 2^(3e+3)` is the closed-form
//! exponent the v3 SIZE derivation needs to fold the cubed power-of-two factor
//! into the `2^(3e+5)` tail. Purely arithmetic — banked as a reusable `Nat`
//! lemma.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! `(2^(e+1))³ = 2^((e+1)·3)` by `Eq.symm (Nat.pow_mul 2 (e+1) 3)`
//! (`a^(m·n) = (a^m)^n`). Then rewrite the exponent `(e+1)·3 = 3·e + 3`:
//! - `r  := Nat.right_distrib e 1 3 : (e+1)·3 = e·3 + 1·3`
//!          (RHS `1·3 ≡ 3` by defeq),
//! - `cm := Nat.mul_comm e 3 : e·3 = 3·e`,
//! - `c1 := congrArg (λ z => z + 1·3) cm : (e·3 + 1·3) = (3·e + 1·3)`,
//! - `eq_exp := Eq.trans r c1 : (e+1)·3 = 3·e + 1·3`   (`3·e + 1·3 ≡ 3·e + 3`).
//!
//! Lift through the exponent with
//! `e_cong := congrArg (λ x => 2^x) eq_exp : 2^((e+1)·3) = 2^(3·e + 1·3)`,
//! and chain `Eq.trans (Eq.symm (pow_mul …)) e_cong`. The result's RHS
//! `2^(3·e + 1·3)` is defeq to the stated `2^(3·e + 3)` (`Nat.mul 1 3 ≡ 3`).
//!
//! # Axiom closure
//!
//! Every dependency (`Nat.pow_mul`, `Nat.right_distrib`, `Nat.mul_comm`, plus
//! `Eq` built-ins `Eq.symm/trans`, `congrArg`) is a constructive
//! `Declaration::Theorem` / `Eq` built-in with an empty domain-axiom closure,
//! so the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.pow_two_e_plus_one_cubed` as a kernel-checked constructive
    /// theorem: `∀ e, (2^(e+1))³ = 2^(3e+3)`.
    pub(crate) fn register_nat_pow_two_e_plus_one_cubed_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_two_e_plus_one_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.register_nat_pow_mul_proof()?; // Nat.pow_mul
        self.register_nat_right_distrib_proof()?; // Nat.right_distrib
        self.register_nat_mul_comm_proof()?; // Nat.mul_comm

        // ── Kernel constants ────────────────────────────────────────────────
        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let pow_mul = Expr::const_(Name::from_string("Nat.pow_mul"), vec![]);
        let right_distrib = Expr::const_(Name::from_string("Nat.right_distrib"), vec![]);
        let mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

        // ── Helpers ─────────────────────────────────────────────────────────
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
        let eq_nat = |x: Expr, y: Expr| Expr::apps(eq_const.clone(), [nat.clone(), x, y]);

        let one = lit(1);
        let two = lit(2);
        let three = lit(3);

        // ── Type: ∀ e, (2^(e+1))³ = 2^(3e+3) ─────────────────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let lhs = pow(pow(two.clone(), add(e.clone(), one.clone())), three.clone());
            let rhs = pow(
                two.clone(),
                add(mul(three.clone(), e.clone()), three.clone()),
            );
            let concl = eq_nat(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => <proof> ─────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());

            let e_plus_1 = add(e.clone(), one.clone()); // e+1
            let pow_e1 = pow(two.clone(), e_plus_1.clone()); // 2^(e+1)
            let pow_e1_cubed = pow(pow_e1.clone(), three.clone()); // (2^(e+1))³
            let exp_mul = mul(e_plus_1.clone(), three.clone()); // (e+1)·3
            let pow_exp_mul = pow(two.clone(), exp_mul.clone()); // 2^((e+1)·3)

            // e·3, 1·3, 3·e
            let e_mul_3 = mul(e.clone(), three.clone());
            let one_mul_3 = mul(one.clone(), three.clone());
            let three_mul_e = mul(three.clone(), e.clone());
            let e3_plus_13 = add(e_mul_3.clone(), one_mul_3.clone()); // e·3 + 1·3
            let three_e_plus_13 = add(three_mul_e.clone(), one_mul_3.clone()); // 3·e + 1·3

            // r := Nat.right_distrib e 1 3 : (e+1)·3 = e·3 + 1·3
            let r = Expr::apps(
                right_distrib.clone(),
                [e.clone(), one.clone(), three.clone()],
            );

            // cm := Nat.mul_comm e 3 : e·3 = 3·e
            let cm = Expr::apps(mul_comm.clone(), [e.clone(), three.clone()]);

            // λ z => Nat.add z (1·3)
            let add_right_13 = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = add(z, one_mul_3.clone());
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };
            // c1 := congrArg (λz=>z+1·3) cm : (e·3 + 1·3) = (3·e + 1·3)
            let c1 = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    e_mul_3.clone(),
                    three_mul_e.clone(),
                    add_right_13,
                    cm,
                ],
            );
            // eq_exp := Eq.trans r c1 : (e+1)·3 = 3·e + 1·3
            let eq_exp = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    exp_mul.clone(),
                    e3_plus_13.clone(),
                    three_e_plus_13.clone(),
                    r,
                    c1,
                ],
            );

            // λ x => Nat.pow 2 x
            let pow2 = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = zb.fresh_local(nat.clone());
                let body = pow(two.clone(), x);
                zb.finish_child(zb.mk_lam(x_id, BinderInfo::Default, nat.clone(), body))
            };
            // e_cong := congrArg (λx=>2^x) eq_exp : 2^((e+1)·3) = 2^(3·e + 1·3)
            let pow_three_e_13 = pow(two.clone(), three_e_plus_13.clone()); // 2^(3·e + 1·3)
            let e_cong = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    exp_mul.clone(),
                    three_e_plus_13.clone(),
                    pow2,
                    eq_exp,
                ],
            );

            // pm := Nat.pow_mul 2 (e+1) 3 : 2^((e+1)·3) = (2^(e+1))³
            let pm = Expr::apps(
                pow_mul.clone(),
                [two.clone(), e_plus_1.clone(), three.clone()],
            );
            // e_pow := Eq.symm pm : (2^(e+1))³ = 2^((e+1)·3)
            let e_pow = Expr::apps(
                eq_symm.clone(),
                [nat.clone(), pow_exp_mul.clone(), pow_e1_cubed.clone(), pm],
            );

            // body := Eq.trans e_pow e_cong : (2^(e+1))³ = 2^(3·e + 1·3)
            //   (RHS defeq to stated 2^(3·e+3))
            let body = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    pow_e1_cubed.clone(),
                    pow_exp_mul.clone(),
                    pow_three_e_13.clone(),
                    e_pow,
                    e_cong,
                ],
            );

            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: Real kernel-checked proof term. `(2^(e+1))³ = 2^(3e+3)` is
        // proved by `Eq.symm (Nat.pow_mul 2 (e+1) 3)` to expose the exponent
        // `(e+1)·3`, then rewriting `(e+1)·3 = 3·e + 3` via constructive
        // `Nat.right_distrib` and `Nat.mul_comm` (with closed `1·3 ≡ 3`),
        // lifted through `congrArg (λx => 2^x)`. No `sorry`, no self-reference,
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
    fn test_pow_two_e_plus_one_cubed_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_pow_two_e_plus_one_cubed_proof()
            .expect("register");
        env.register_nat_pow_two_e_plus_one_cubed_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.pow_two_e_plus_one_cubed");
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

    /// Ground sanity at `e = 0`: `(2^1)³ = 2^3`, i.e. `8 = 8`.
    #[test]
    fn test_pow_two_e_plus_one_cubed_ground_zero() {
        let mut env = Environment::with_prelude();
        env.register_nat_pow_two_e_plus_one_cubed_proof()
            .expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let lit = |n: u64| {
            let mut acc = nat_zero.clone();
            for _ in 0..n {
                acc = Expr::app(nat_succ.clone(), acc);
            }
            acc
        };
        let thm = Expr::const_(Name::from_string("Nat.pow_two_e_plus_one_cubed"), vec![]);
        let app = Expr::app(thm, nat_zero.clone());
        let lhs = Expr::apps(
            nat_pow.clone(),
            [
                Expr::apps(
                    nat_pow.clone(),
                    [
                        lit(2),
                        Expr::apps(nat_add.clone(), [nat_zero.clone(), lit(1)]),
                    ],
                ),
                lit(3),
            ],
        );
        let rhs = Expr::apps(
            nat_pow.clone(),
            [
                lit(2),
                Expr::apps(
                    nat_add.clone(),
                    [
                        Expr::apps(nat_mul.clone(), [lit(3), nat_zero.clone()]),
                        lit(3),
                    ],
                ),
            ],
        );
        let expected = Expr::apps(eq_const.clone(), [nat.clone(), lhs, rhs]);
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("ground e=0 instance should type-check: {e:?}"));
    }
}
