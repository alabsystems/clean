// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE-exponent bound
//!
//! ```text
//! Nat.three_e_add_five_le_sixteen_pow_two : ∀ e : Nat,
//!   Nat.le (Nat.add (Nat.mul 3 e) 5) (Nat.mul 16 (Nat.pow 2 e))
//! ```
//!
//! i.e. `3·e + 5 ≤ 16·2^e`. This is the closed-form Nat inequality the v3
//! Friedgut SIZE branch needs to collapse the size-exponent `3e+5` into the
//! `48·2^e` junta budget (via `4·9^(2d) ≤ 2^(32·2^e)` and the `2^(3e+5)`
//! tail). It is purely arithmetic — no Friedgut/boolean-analysis content —
//! and lives here as a bankable, reusable `Nat` lemma.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! Let `p := Nat.pow 2 e`. Two landed monotone facts drive the bound:
//!
//! - `Nat.le_two_pow_self e : e ≤ p`        (`e ≤ 2^e`)
//! - `Nat.one_le_two_pow e : 1 ≤ p`         (`1 ≤ 2^e`)
//!
//! Step A   `3·e ≤ 3·p`     `Nat.mul_le_mul_left e p 3 (le_two_pow_self e)`
//! Step B   `5   ≤ 5·p`     `Nat.mul_le_mul_left 1 p 5 (one_le_two_pow e)`,
//!                          whose stated LHS `Nat.mul 5 1 ≡ 5` (ι-reduction:
//!                          `mul 5 1 = add (mul 5 0) 5 = add 0 5 = 5`).
//! Step AB  `3·e + 5 ≤ 3·p + 5·p`
//!                          `Nat.add_le_add (3·e) (3·p) 5 (5·p) hA hB`.
//! Step D   rewrite `3·p + 5·p` back to `8·p` via
//!                          `Nat.right_distrib 3 5 p : (3+5)·p = 3·p + 5·p`,
//!                          and `Nat.add 3 5 ≡ 8` (closed ι-reduction), so its
//!                          LHS is `Nat.mul 8 p`. `Eq.subst` along the symm
//!                          transports `hAB` to `3·e + 5 ≤ 8·p`.
//! Step E   `8·p ≤ 16·p`    `Nat.mul_le_mul_right 8 16 p h_8_le_16`, where
//!                          `h_8_le_16 : 8 ≤ 16` is a closed `Nat.le.step`
//!                          chain off `Nat.le.refl 8`.
//! Finish   `Nat.le_trans (3·e+5) (8·p) (16·p) hAB8 hE`.
//!
//! All literals are succ-chains (`Nat.succ^n Nat.zero`), matching the
//! `2 ≡ succ (succ 0)` carrier inside `Nat.le_two_pow_self`'s `Nat.pow 2 e`.
//!
//! # Axiom closure
//!
//! Every dependency (`Nat.le_two_pow_self`, `Nat.one_le_two_pow`,
//! `Nat.mul_le_mul_left`, `Nat.mul_le_mul_right`, `Nat.add_le_add`,
//! `Nat.right_distrib`, `Nat.le_trans`, plus `Eq.subst`) is a constructive
//! `Declaration::Theorem` / `Eq` built-in with an empty domain-axiom closure,
//! so `env.axiom_deps("Nat.three_e_add_five_le_sixteen_pow_two")` is empty and
//! `env.proof_quality(..) == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.three_e_add_five_le_sixteen_pow_two` as a kernel-checked
    /// constructive theorem: `∀ e, 3·e + 5 ≤ 16·2^e`.
    pub(crate) fn register_nat_three_e_add_five_bound_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.three_e_add_five_le_sixteen_pow_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step
        self.register_nat_arith_order_proofs()?; // mul_le_mul_left/right, add_le_add, le_trans
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow
        self.register_nat_le_two_pow_self()?; // Nat.le_two_pow_self
        self.register_nat_right_distrib_proof()?; // Nat.right_distrib

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
        let mul_le_mul_left = Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]);
        let mul_le_mul_right = Expr::const_(Name::from_string("Nat.mul_le_mul_right"), vec![]);
        let add_le_add = Expr::const_(Name::from_string("Nat.add_le_add"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let one_le_two_pow = Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]);
        let le_two_pow_self = Expr::const_(Name::from_string("Nat.le_two_pow_self"), vec![]);
        let right_distrib = Expr::const_(Name::from_string("Nat.right_distrib"), vec![]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);

        // ── Helpers ─────────────────────────────────────────────────────────
        let succ = |x: Expr| Expr::app(nat_succ.clone(), x);
        // Build the literal `n` as the succ-chain `Nat.succ^n Nat.zero`.
        let lit = |n: u64| {
            let mut acc = nat_zero.clone();
            for _ in 0..n {
                acc = Expr::app(nat_succ.clone(), acc);
            }
            acc
        };
        let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
        let mul = |x: Expr, y: Expr| Expr::apps(nat_mul.clone(), [x, y]);
        let pow2 = |x: Expr| Expr::apps(nat_pow.clone(), [lit(2), x]);
        let le = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);

        let three = lit(3);
        let five = lit(5);
        let eight = lit(8);
        let sixteen = lit(16);
        let one = lit(1);

        // ── Type: ∀ e, Nat.le (Nat.add (Nat.mul 3 e) 5) (Nat.mul 16 (Nat.pow 2 e))
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let lhs = add(mul(three.clone(), e.clone()), five.clone());
            let rhs = mul(sixteen.clone(), pow2(e.clone()));
            let concl = le(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => <proof> ─────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let p = pow2(e.clone());

            let mul_3e = mul(three.clone(), e.clone());
            let mul_3p = mul(three.clone(), p.clone());
            let mul_5p = mul(five.clone(), p.clone());
            let mul_8p = mul(eight.clone(), p.clone());
            let mul_16p = mul(sixteen.clone(), p.clone());

            // hA : Nat.le (3·e) (3·p)
            //   Nat.mul_le_mul_left e p 3 (Nat.le_two_pow_self e)
            let h_le_two_pow = Expr::app(le_two_pow_self.clone(), e.clone());
            let h_a = Expr::apps(
                mul_le_mul_left.clone(),
                [e.clone(), p.clone(), three.clone(), h_le_two_pow],
            );

            // hB : Nat.le 5 (5·p)
            //   Nat.mul_le_mul_left 1 p 5 (Nat.one_le_two_pow e)
            //   stated LHS `Nat.mul 5 1 ≡ 5` (defeq); supplied where `5` is
            //   expected by `add_le_add`, accepted via defeq.
            let h_one_le_two_pow = Expr::app(one_le_two_pow.clone(), e.clone());
            let h_b = Expr::apps(
                mul_le_mul_left.clone(),
                [one.clone(), p.clone(), five.clone(), h_one_le_two_pow],
            );

            // hAB : Nat.le (3·e + 5) (3·p + 5·p)
            //   Nat.add_le_add (3·e) (3·p) 5 (5·p) hA hB
            let h_ab = Expr::apps(
                add_le_add.clone(),
                [
                    mul_3e.clone(),
                    mul_3p.clone(),
                    five.clone(),
                    mul_5p.clone(),
                    h_a,
                    h_b,
                ],
            );

            // h_distrib : Nat.mul (Nat.add 3 5) p = Nat.add (Nat.mul 3 p) (Nat.mul 5 p)
            //   Nat.right_distrib 3 5 p   (LHS `Nat.mul (3+5) p ≡ Nat.mul 8 p`)
            let three_add_five = add(three.clone(), five.clone());
            let mul_8p_lit = mul(three_add_five.clone(), p.clone()); // ≡ 8·p syntactically (3+5)·p
            let h_distrib = Expr::apps(
                right_distrib.clone(),
                [three.clone(), five.clone(), p.clone()],
            );
            let add_3p_5p = add(mul_3p.clone(), mul_5p.clone());
            // h_distrib_symm : (3·p + 5·p) = (3+5)·p
            let h_distrib_symm = Expr::apps(
                eq_symm.clone(),
                [
                    nat.clone(),
                    mul_8p_lit.clone(),
                    add_3p_5p.clone(),
                    h_distrib,
                ],
            );

            // hAB8 : Nat.le (3·e + 5) ((3+5)·p)  via Eq.subst
            //   motive z := Nat.le (3·e + 5) z
            //   @Eq.subst Nat motive (3·p+5·p) ((3+5)·p) h_distrib_symm hAB
            let lhs_sum = add(mul_3e.clone(), five.clone());
            let subst_motive = {
                let mut zb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = zb.fresh_local(nat.clone());
                let body = le(lhs_sum.clone(), z);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
            };
            let h_ab8 = Expr::apps(
                eq_subst.clone(),
                [
                    nat.clone(),
                    subst_motive,
                    add_3p_5p.clone(),
                    mul_8p_lit.clone(),
                    h_distrib_symm,
                    h_ab,
                ],
            );

            // h_8_le_16 : Nat.le 8 16  (closed `Nat.le.step` chain off le.refl 8)
            //   le.refl 8 : 8 ≤ 8; eight `le.step` increments to 8 ≤ 16.
            let h_8_le_16 = {
                let mut acc = Expr::app(nat_le_refl.clone(), eight.clone()); // 8 ≤ 8
                let mut cur = eight.clone();
                for _ in 0..8u64 {
                    // Nat.le.step 8 cur acc : 8 ≤ succ cur
                    acc = Expr::apps(nat_le_step.clone(), [eight.clone(), cur.clone(), acc]);
                    cur = succ(cur);
                }
                acc
            };

            // hE : Nat.le (8·p) (16·p)
            //   Nat.mul_le_mul_right 8 16 p h_8_le_16
            let h_e = Expr::apps(
                mul_le_mul_right.clone(),
                [eight.clone(), sixteen.clone(), p.clone(), h_8_le_16],
            );

            // body : Nat.le (3·e + 5) (16·p)
            //   Nat.le_trans (3·e+5) (8·p) (16·p) hAB8 hE
            //   (hAB8 : ... ≤ (3+5)·p ≡ 8·p by defeq; hE : 8·p ≤ 16·p)
            let body = Expr::apps(
                le_trans.clone(),
                [lhs_sum, mul_8p.clone(), mul_16p, h_ab8, h_e],
            );

            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
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
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_three_e_add_five_bound_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_three_e_add_five_bound_proof()
            .expect("register");
        env.register_nat_three_e_add_five_bound_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.three_e_add_five_le_sixteen_pow_two");
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

    /// Ground sanity at `e = 0`: `3·0 + 5 ≤ 16·2^0`, i.e. `5 ≤ 16`.
    #[test]
    fn test_three_e_add_five_bound_ground_zero() {
        let mut env = Environment::with_prelude();
        env.register_nat_three_e_add_five_bound_proof()
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
            Name::from_string("Nat.three_e_add_five_le_sixteen_pow_two"),
            vec![],
        );
        let app = Expr::app(thm, nat_zero.clone());
        // expected: Nat.le (Nat.add (Nat.mul 3 0) 5) (Nat.mul 16 (Nat.pow 2 0))
        let lhs = Expr::apps(
            nat_add.clone(),
            [
                Expr::apps(nat_mul.clone(), [lit(3), nat_zero.clone()]),
                lit(5),
            ],
        );
        let rhs = Expr::apps(
            nat_mul.clone(),
            [
                lit(16),
                Expr::apps(nat_pow.clone(), [lit(2), nat_zero.clone()]),
            ],
        );
        let expected = Expr::apps(nat_le.clone(), [lhs, rhs]);
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("ground e=0 instance should type-check: {e:?}"));
    }
}
