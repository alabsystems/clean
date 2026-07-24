// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the Friedgut SIZE budget-split lemma
//!
//! ```text
//! Nat.forty_eight_pow_eq_split : ∀ e : Nat,
//!   Eq Nat (Nat.mul 48 (Nat.pow 2 e))
//!          (Nat.add (Nat.mul 32 (Nat.pow 2 e)) (Nat.mul 16 (Nat.pow 2 e)))
//! ```
//!
//! i.e. `48·2^e = 32·2^e + 16·2^e`. This is the additive split of the
//! `48·2^e` junta budget exponent into its `32·2^e` (the `4·9^(2d)` head) and
//! `16·2^e` (the `2^(3e+5)` tail) halves; via `Nat.pow_add` it powers
//! `2^(48·2^e) = 2^(32·2^e) · 2^(16·2^e)`, the glue point of the v3 SIZE
//! derivation. Purely arithmetic — banked as a reusable `Nat` lemma.
//!
//! # Proof strategy (hand-built `Expr`, no tactics)
//!
//! `Nat.right_distrib 32 16 (2^e) : (32+16)·2^e = 32·2^e + 16·2^e`. Its LHS
//! `Nat.mul (Nat.add 32 16) (Nat.pow 2 e)` is defeq to `Nat.mul 48 (Nat.pow 2 e)`
//! (the kernel reduces `Nat.add 32 16 ≡ 48`, a closed ι-reduction), so the
//! `right_distrib` term inhabits the stated goal type directly.
//!
//! # Axiom closure
//!
//! The sole dependency `Nat.right_distrib` is a constructive
//! `Declaration::Theorem` with an empty domain-axiom closure, so the proof
//! quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.forty_eight_pow_eq_split` as a kernel-checked constructive
    /// theorem: `∀ e, 48·2^e = 32·2^e + 16·2^e`.
    pub(crate) fn register_nat_forty_eight_pow_eq_split_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.forty_eight_pow_eq_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.register_nat_right_distrib_proof()?; // Nat.right_distrib

        // ── Kernel constants ────────────────────────────────────────────────
        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let right_distrib = Expr::const_(Name::from_string("Nat.right_distrib"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![l1]);

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
        let sixteen = lit(16);
        let thirty_two = lit(32);
        let forty_eight = lit(48);

        // ── Type: ∀ e, 48·2^e = 32·2^e + 16·2^e ──────────────────────────────
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let p = pow(two.clone(), e.clone());
            let lhs = mul(forty_eight.clone(), p.clone());
            let rhs = add(mul(thirty_two.clone(), p.clone()), mul(sixteen.clone(), p));
            let concl = eq_nat(lhs, rhs);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, nat.clone(), concl))
        };

        // ── Value: fun (e : Nat) => Nat.right_distrib 32 16 (2^e) ────────────
        // LHS `(32+16)·2^e ≡ 48·2^e` by defeq (Nat.add 32 16 ≡ 48).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(nat.clone());
            let p = pow(two.clone(), e.clone());
            let body = Expr::apps(
                right_distrib.clone(),
                [thirty_two.clone(), sixteen.clone(), p],
            );
            b.finish(b.mk_lam(e_id, BinderInfo::Default, nat.clone(), body))
        };

        // SOUNDNESS: Real kernel-checked proof term. `48·2^e = 32·2^e + 16·2^e`
        // is exactly `Nat.right_distrib 32 16 (2^e) : (32+16)·2^e = 32·2^e +
        // 16·2^e` whose stated LHS `Nat.mul (Nat.add 32 16) (2^e)` is defeq to
        // `Nat.mul 48 (2^e)` (closed `Nat.add 32 16 ≡ 48`). No `sorry`, no
        // self-reference, no domain-axiom dependency — `Nat.right_distrib` is
        // itself constructive.
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
    fn test_forty_eight_pow_eq_split_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_forty_eight_pow_eq_split_proof()
            .expect("register");
        env.register_nat_forty_eight_pow_eq_split_proof()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.forty_eight_pow_eq_split");
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

    /// Ground sanity at `e = 0`: `48·1 = 32·1 + 16·1`, i.e. `48 = 48`.
    #[test]
    fn test_forty_eight_pow_eq_split_ground_zero() {
        let mut env = Environment::with_prelude();
        env.register_nat_forty_eight_pow_eq_split_proof()
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
        let thm = Expr::const_(Name::from_string("Nat.forty_eight_pow_eq_split"), vec![]);
        let app = Expr::app(thm, nat_zero.clone());
        let p = Expr::apps(nat_pow.clone(), [lit(2), nat_zero.clone()]);
        let lhs = Expr::apps(nat_mul.clone(), [lit(48), p.clone()]);
        let rhs = Expr::apps(
            nat_add.clone(),
            [
                Expr::apps(nat_mul.clone(), [lit(32), p.clone()]),
                Expr::apps(nat_mul.clone(), [lit(16), p]),
            ],
        );
        let expected = Expr::apps(eq_const.clone(), [nat.clone(), lhs, rhs]);
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("ground e=0 instance should type-check: {e:?}"));
    }
}
