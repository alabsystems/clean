// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE budget-exponent composition lemma
//!
//! ```text
//! Nat.pow_nine_eightfold_le_budget : ∀ e : Nat,
//!   Nat.le (Nat.pow 9 (Nat.mul 2 (Nat.pow 2 (Nat.add e 2))))
//!          (Nat.pow 2 (Nat.mul 48 (Nat.pow 2 e)))
//! ```
//!
//! i.e. `9^(2·d) ≤ 2^(48·2^e)` with `d := 2^(e+2)`. This is the dominant term of
//! the genuine-Friedgut junta-SIZE bound `K/dr² = 4·9^(2d)·K³/eps²` (O'Donnell
//! §9.6) for the v3 budget `2^(48·2^e)` (`friedgut_budget_v3`): with the threshold
//! degree cutoff `d := 2^(e+2)`, the `9^(2d)` factor must fit inside the budget
//! exponent. Purely arithmetic — no Friedgut/boolean content — banked as a
//! reusable `Nat` lemma the v3 SIZE assembly chains.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! Compose two landed constructive bricks at `d := Nat.pow 2 (Nat.add e 2)`:
//!
//! 1. `Nat.pow_nine_le_pow_two_eightfold d`
//!    : `Nat.le (9^(2·d)) (2^(8·d))`.
//! 2. `Nat.eight_mul_pow_two_add_two_le e`
//!    : `Nat.le (8·2^(e+2)) (48·2^e)`. Since `d := 2^(e+2)`, its LHS `8·2^(e+2)`
//!    is SYNTACTICALLY `8·d` (`Nat.mul 8 (Nat.pow 2 (Nat.add e 2))`), the exact
//!    exponent in (1)'s RHS `2^(8·d)`.
//! 3. `Nat.pow_le_pow_right 2 (8·d) (48·2^e) h12 h2`
//!    : `Nat.le (2^(8·d)) (2^(48·2^e))`, where `h12 : Nat.le 1 2` is the closed
//!    `Nat.le.step (Nat.le.refl 1)` and `h2` is brick (2).
//! 4. `Nat.le_trans (9^(2·d)) (2^(8·d)) (2^(48·2^e)) h1 h3`
//!    : `Nat.le (9^(2·d)) (2^(48·2^e))` — the goal.
//!
//! # Axiom closure
//!
//! Every dependency (`Nat.pow_nine_le_pow_two_eightfold`,
//! `Nat.eight_mul_pow_two_add_two_le`, `Nat.pow_le_pow_right`, `Nat.le_trans`,
//! `Nat.le.refl`, `Nat.le.step`) is a constructive `Declaration::Theorem` /
//! inductive constructor with an empty domain-axiom closure, so
//! `env.axiom_deps("Nat.pow_nine_eightfold_le_budget")` is empty and the proof
//! quality is `Constructive`.

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Register `Nat.pow_nine_eightfold_le_budget` as a kernel-checked
    /// constructive theorem: `∀ e, 9^(2·2^(e+2)) ≤ 2^(48·2^e)`.
    ///
    /// The dominant `9^(2d)` term of the Friedgut junta-SIZE bound, composed from
    /// the landed `Nat.pow_nine_le_pow_two_eightfold` (`9^(2d) ≤ 2^(8d)`) and
    /// `Nat.eight_mul_pow_two_add_two_le` (`8·2^(e+2) ≤ 48·2^e`) via
    /// `Nat.pow_le_pow_right` and `Nat.le_trans`. Constructive, empty
    /// admitted-axiom closure. Idempotent. No axiom added or removed.
    #[cfg(test)]
    pub(crate) fn register_nat_pow_nine_eightfold_le_budget_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_nine_eightfold_le_budget");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right
        self.register_nat_pow_nine_le_pow_two_eightfold_proof()?;
        self.register_nat_eight_mul_pow_two_add_two_le_proof()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // ── Kernel constants ────────────────────────────────────────────────
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
        let pow_nine = Expr::const_(
            Name::from_string("Nat.pow_nine_le_pow_two_eightfold"),
            vec![],
        );
        let eight_mul = Expr::const_(
            Name::from_string("Nat.eight_mul_pow_two_add_two_le"),
            vec![],
        );

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
        let le = |x: Expr, y: Expr| Expr::apps(nat_le.clone(), [x, y]);

        let two = lit(2);
        let eight = lit(8);
        let nine = lit(9);
        let forty_eight = lit(48);
        let one = lit(1);

        // ── Type: ∀ e, Nat.le (9^(2·2^(e+2))) (2^(48·2^e)) ──────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let d = pow(two.clone(), add(e.clone(), two.clone())); // 2^(e+2)
            let lhs = pow(nine.clone(), mul(two.clone(), d.clone())); // 9^(2·d)
            let rhs = pow(
                two.clone(),
                mul(forty_eight.clone(), pow(two.clone(), e.clone())),
            ); // 2^(48·2^e)
            let concl = le(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => <proof> ─────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());

            let d = pow(two.clone(), add(e.clone(), two.clone())); // d := 2^(e+2)
            let pow_e = pow(two.clone(), e.clone()); // 2^e
            let two_d = mul(two.clone(), d.clone()); // 2·d
            let eight_d = mul(eight.clone(), d.clone()); // 8·d ≡ 8·2^(e+2)
            let forty_eight_pow_e = mul(forty_eight.clone(), pow_e.clone()); // 48·2^e

            let pow9_2d = pow(nine.clone(), two_d.clone()); // 9^(2·d)
            let pow2_8d = pow(two.clone(), eight_d.clone()); // 2^(8·d)
            let pow2_budget = pow(two.clone(), forty_eight_pow_e.clone()); // 2^(48·2^e)

            // h1 := Nat.pow_nine_le_pow_two_eightfold d : 9^(2·d) ≤ 2^(8·d)
            let h1 = Expr::app(pow_nine.clone(), d.clone());

            // h2 := Nat.eight_mul_pow_two_add_two_le e : 8·2^(e+2) ≤ 48·2^e
            //   (LHS `8·2^(e+2)` is SYNTACTICALLY `8·d`.)
            let h2 = Expr::app(eight_mul.clone(), e.clone());

            // h12 := Nat.le.step 1 1 (Nat.le.refl 1) : Nat.le 1 2.
            let h12 = Expr::apps(
                nat_le_step.clone(),
                [
                    one.clone(),
                    one.clone(),
                    Expr::app(nat_le_refl.clone(), one.clone()),
                ],
            );

            // h3 := Nat.pow_le_pow_right 2 (8·d) (48·2^e) h12 h2 : 2^(8·d) ≤ 2^(48·2^e)
            let h3 = Expr::apps(
                pow_le_pow_right.clone(),
                [
                    two.clone(),
                    eight_d.clone(),
                    forty_eight_pow_e.clone(),
                    h12,
                    h2,
                ],
            );

            // body := Nat.le_trans (9^(2·d)) (2^(8·d)) (2^(48·2^e)) h1 h3
            let body = Expr::apps(
                le_trans.clone(),
                [
                    pow9_2d.clone(),
                    pow2_8d.clone(),
                    pow2_budget.clone(),
                    h1,
                    h3,
                ],
            );

            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: Real kernel-checked proof term. `9^(2d) ≤ 2^(48·2^e)` with
        // `d := 2^(e+2)` is proved by transitivity of the landed constructive
        // bricks `Nat.pow_nine_le_pow_two_eightfold d` (`9^(2d) ≤ 2^(8d)`) and
        // `Nat.eight_mul_pow_two_add_two_le e` (`8·2^(e+2) ≤ 48·2^e`, whose LHS is
        // syntactically `8·d`) lifted to exponents by `Nat.pow_le_pow_right` with
        // base `2` and `1 ≤ 2` (a closed `Nat.le.step` of `Nat.le.refl`). No
        // `sorry`, no self-reference, no domain-axiom dependency — all consumed
        // theorems are themselves constructive.
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
    fn test_pow_nine_eightfold_le_budget_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_pow_nine_eightfold_le_budget_proof()
            .expect("register");
        env.register_nat_pow_nine_eightfold_le_budget_proof()
            .expect("idempotent");

        let name = Name::from_string("Nat.pow_nine_eightfold_le_budget");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a Declaration::Theorem"
        );

        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("lemma should kernel-check: {e:?}"));

        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&name)
                .expect("deps")
                .iter()
                .map(|dp| dp.to_string())
                .collect::<Vec<_>>()
        );
    }
}
