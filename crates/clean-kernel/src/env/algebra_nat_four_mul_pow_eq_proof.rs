// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE four-fold absorb lemma
//!
//! ```text
//! Nat.four_mul_pow_eq : ∀ e : Nat,
//!   Eq Nat (Nat.mul 4 (Nat.pow 2 (Nat.add (Nat.mul 3 e) 3)))
//!          (Nat.pow 2 (Nat.add (Nat.mul 3 e) 5))
//! ```
//!
//! i.e. `4·2^(3e+3) = 2^(3e+5)`. After cubing the guard, the SIZE head carries
//! a literal `4 = 2²` factor; absorbing it into the `2^(3e+3)` tail yields the
//! `2^(3e+5)` exponent that `Nat.three_e_add_five_le_sixteen_pow_two` then
//! bounds by `2^(16·2^e)`. Purely arithmetic — banked as a reusable `Nat`
//! lemma.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! `4·2^(3e+3) = 2²·2^(3e+3) = 2^(2 + (3e+3))` by `Eq.symm (Nat.pow_add 2 2
//! (3e+3))` (LHS `2² ≡ 4` by defeq). Then rewrite the exponent
//! `2 + (3e+3) = 3e + 5`:
//! - `ac := Nat.add_comm 2 (3e+3) : 2 + (3e+3) = (3e+3) + 2`,
//! - `aa := Nat.add_assoc (3e) 3 2 : ((3e)+3)+2 = (3e)+(3+2)`   (`3+2 ≡ 5`),
//! - `eq_exp := Eq.trans ac aa : 2 + (3e+3) = (3e) + (3+2)`.
//!
//! Lift through the exponent with `congrArg (λ x => 2^x) eq_exp`, chained onto
//! `Eq.symm (pow_add …)`. The result's RHS `2^((3e)+(3+2))` is defeq to the
//! stated `2^((3e)+5)` (`Nat.add 3 2 ≡ 5`), and its LHS `2²·2^(3e+3)` is defeq
//! to the stated `4·2^(3e+3)` (`Nat.pow 2 2 ≡ 4`).
//!
//! # Axiom closure
//!
//! Every dependency (`Nat.pow_add`, `Nat.add_comm`, `Nat.add_assoc`, plus `Eq`
//! built-ins `Eq.symm/trans`, `congrArg`) is a constructive
//! `Declaration::Theorem` / `Eq` built-in with an empty domain-axiom closure,
//! so the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.four_mul_pow_eq` as a kernel-checked constructive theorem:
    /// `∀ e, 4·2^(3e+3) = 2^(3e+5)`.
    pub(crate) fn register_nat_four_mul_pow_eq_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.four_mul_pow_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.register_nat_pow_add_proof()?; // Nat.pow_add
        self.register_nat_add_comm_proof()?; // Nat.add_comm
        self.register_nat_add_assoc_proof()?; // Nat.add_assoc

        // ── Kernel constants ────────────────────────────────────────────────
        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let pow_add = Expr::const_(Name::from_string("Nat.pow_add"), vec![]);
        let add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);
        let add_assoc = Expr::const_(Name::from_string("Nat.add_assoc"), vec![]);
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

        let two = lit(2);
        let three = lit(3);
        let four = lit(4);
        let five = lit(5);

        // ── Type: ∀ e, 4·2^(3e+3) = 2^(3e+5) ─────────────────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let exp3e3 = add(mul(three.clone(), e.clone()), three.clone()); // 3e+3
            let exp3e5 = add(mul(three.clone(), e.clone()), five.clone()); // 3e+5
            let lhs = mul(four.clone(), pow(two.clone(), exp3e3));
            let rhs = pow(two.clone(), exp3e5);
            let concl = eq_nat(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => <proof> ─────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());

            let three_e = mul(three.clone(), e.clone()); // 3e
            let exp3e3 = add(three_e.clone(), three.clone()); // 3e+3
            let pow_3e3 = pow(two.clone(), exp3e3.clone()); // 2^(3e+3)
            let two_sq = pow(two.clone(), two.clone()); // 2²
            let two_sq_mul = mul(two_sq.clone(), pow_3e3.clone()); // 2²·2^(3e+3)
            let exp_sum = add(two.clone(), exp3e3.clone()); // 2 + (3e+3)
            let pow_exp_sum = pow(two.clone(), exp_sum.clone()); // 2^(2+(3e+3))

            // exponent equation pieces
            let exp3e3_plus2 = add(exp3e3.clone(), two.clone()); // (3e+3) + 2
            let three_plus2 = add(three.clone(), two.clone()); // 3+2 (≡5)
            let exp_3e_3p2 = add(three_e.clone(), three_plus2.clone()); // 3e + (3+2)
            let pow_3e_3p2 = pow(two.clone(), exp_3e_3p2.clone()); // 2^(3e+(3+2))

            // ac := Nat.add_comm 2 (3e+3) : 2 + (3e+3) = (3e+3) + 2
            let ac = Expr::apps(add_comm.clone(), [two.clone(), exp3e3.clone()]);
            // aa := Nat.add_assoc (3e) 3 2 : ((3e)+3)+2 = (3e)+(3+2)
            let aa = Expr::apps(
                add_assoc.clone(),
                [three_e.clone(), three.clone(), two.clone()],
            );
            // eq_exp := Eq.trans ac aa : 2 + (3e+3) = (3e)+(3+2)
            let eq_exp = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    exp_sum.clone(),
                    exp3e3_plus2.clone(),
                    exp_3e_3p2.clone(),
                    ac,
                    aa,
                ],
            );

            // λ x => Nat.pow 2 x
            let pow2 = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = zb.fresh_local(nat.clone());
                let body = pow(two.clone(), x);
                zb.finish_child(zb.mk_lam(x_id, BinderInfo::Default, nat.clone(), body))
            };
            // e_cong := congrArg (λx=>2^x) eq_exp : 2^(2+(3e+3)) = 2^(3e+(3+2))
            let e_cong = Expr::apps(
                congr_arg.clone(),
                [
                    nat.clone(),
                    nat.clone(),
                    exp_sum.clone(),
                    exp_3e_3p2.clone(),
                    pow2,
                    eq_exp,
                ],
            );

            // pa := Nat.pow_add 2 2 (3e+3) : 2^(2+(3e+3)) = 2²·2^(3e+3)
            let pa = Expr::apps(pow_add.clone(), [two.clone(), two.clone(), exp3e3.clone()]);
            // e_pow := Eq.symm pa : 2²·2^(3e+3) = 2^(2+(3e+3))
            let e_pow = Expr::apps(
                eq_symm.clone(),
                [nat.clone(), pow_exp_sum.clone(), two_sq_mul.clone(), pa],
            );

            // body := Eq.trans e_pow e_cong : 2²·2^(3e+3) = 2^(3e+(3+2))
            //   LHS defeq 4·2^(3e+3); RHS defeq 2^(3e+5).
            let body = Expr::apps(
                eq_trans.clone(),
                [
                    nat.clone(),
                    two_sq_mul.clone(),
                    pow_exp_sum.clone(),
                    pow_3e_3p2.clone(),
                    e_pow,
                    e_cong,
                ],
            );

            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: Real kernel-checked proof term. `4·2^(3e+3) = 2^(3e+5)` is
        // proved by `Eq.symm (Nat.pow_add 2 2 (3e+3))` (with `2² ≡ 4`) to expose
        // the exponent `2 + (3e+3)`, then rewriting it to `3e + 5` via
        // constructive `Nat.add_comm`/`Nat.add_assoc` (with closed `3+2 ≡ 5`),
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
    fn test_four_mul_pow_eq_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_four_mul_pow_eq_proof().expect("register");
        env.register_nat_four_mul_pow_eq_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.four_mul_pow_eq");
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

    /// Ground sanity at `e = 0`: `4·2^3 = 2^5`, i.e. `32 = 32`.
    #[test]
    fn test_four_mul_pow_eq_ground_zero() {
        let mut env = Environment::with_prelude();
        env.register_nat_four_mul_pow_eq_proof().expect("register");
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
        let thm = Expr::const_(Name::from_string("Nat.four_mul_pow_eq"), vec![]);
        let app = Expr::app(thm, nat_zero.clone());
        let exp3e3 = Expr::apps(
            nat_add.clone(),
            [
                Expr::apps(nat_mul.clone(), [lit(3), nat_zero.clone()]),
                lit(3),
            ],
        );
        let exp3e5 = Expr::apps(
            nat_add.clone(),
            [
                Expr::apps(nat_mul.clone(), [lit(3), nat_zero.clone()]),
                lit(5),
            ],
        );
        let lhs = Expr::apps(
            nat_mul.clone(),
            [lit(4), Expr::apps(nat_pow.clone(), [lit(2), exp3e3])],
        );
        let rhs = Expr::apps(nat_pow.clone(), [lit(2), exp3e5]);
        let expected = Expr::apps(eq_const.clone(), [nat.clone(), lhs, rhs]);
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("ground e=0 instance should type-check: {e:?}"));
    }
}
