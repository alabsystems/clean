// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.pow_two_succ` — rung 3 of the Parseval ladder.
//!
//! ```text
//! Nat.pow_two_succ : ∀ n : Nat,
//!   @Eq Nat (Nat.pow 2 (Nat.succ n)) (Nat.add (Nat.pow 2 n) (Nat.pow 2 n))
//! ```
//!
//! `Nat.pow` is the reducible `Nat.rec` carrier `pow m (succ k) ≡ mul (pow m k) m`
//! and `Nat.mul k n` recurses on `n` as `Nat.rec 0 (λ _ ih => add ih k) n`, so
//! with `2 ≡ succ (succ 0)`:
//!
//! ```text
//! Nat.pow 2 (succ n) ≡ Nat.mul (Nat.pow 2 n) 2
//!                    ≡ Nat.add (Nat.add Nat.zero (Nat.pow 2 n)) (Nat.pow 2 n)
//! ```
//!
//! (`Nat.add Nat.zero (Nat.pow 2 n)` does NOT ι-collapse to `Nat.pow 2 n` —
//! `Nat.add` recurses on its second argument — so the only non-defeq step is
//! `Nat.zero_add`.) Hence
//!
//! ```text
//! @congrArg Nat Nat (Nat.add 0 (2^n)) (2^n) (fun w => Nat.add w (2^n))
//!           (Nat.zero_add (2^n))
//!   : Nat.add (Nat.add 0 (2^n)) (2^n) = Nat.add (2^n) (2^n)
//! ```
//!
//! whose LHS is definitionally `Nat.pow 2 (succ n)`. Axiom-free: the closure is
//! `{Eq, congrArg, Nat, Nat.pow, Nat.add, Nat.zero_add, Nat.succ, Nat.zero}` —
//! `Nat.zero_add` is itself a constructive theorem.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.pow_two_succ` as a kernel-checked constructive theorem.
    pub(crate) fn register_nat_pow_two_succ_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_two_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.register_nat_zero_add_proof()?; // Nat.zero_add

        let l1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

        let two = Expr::app(
            nat_succ.clone(),
            Expr::app(nat_succ.clone(), nat_zero.clone()),
        );
        let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
        let pow2 = |e: Expr| Expr::apps(nat_pow.clone(), [two.clone(), e]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [nat.clone(), l, r]);

        // Type: ∀ n, Eq Nat (Nat.pow 2 (succ n)) (Nat.add (Nat.pow 2 n) (Nat.pow 2 n))
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let lhs = pow2(Expr::app(nat_succ.clone(), n.clone()));
            let p = pow2(n.clone());
            let rhs = add(p.clone(), p);
            let concl = eq_nat(lhs, rhs);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(r)
        };

        // Value: fun n =>
        //   @congrArg Nat Nat (Nat.add 0 (2^n)) (2^n) (fun w => Nat.add w (2^n))
        //           (Nat.zero_add (2^n))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let p = pow2(n.clone());
            let zero_add_p = add(nat_zero.clone(), p.clone());
            // f := fun (w : Nat) => Nat.add w (2^n)
            let f = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = d.fresh_local(nat.clone());
                let body = add(w, p.clone());
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, nat.clone(), body))
            };
            // h := Nat.zero_add (2^n) : Nat.add 0 (2^n) = 2^n
            let h = Expr::app(nat_zero_add.clone(), p.clone());
            // @congrArg Nat Nat (add 0 p) p f h
            let body = Expr::apps(
                congr_arg.clone(),
                [nat.clone(), nat.clone(), zero_add_p, p.clone(), f, h],
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body);
            b.finish(r)
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
    fn test_nat_pow_two_succ_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_nat_pow_two_succ_proof().expect("register");
        env.register_nat_pow_two_succ_proof().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Nat.pow_two_succ");
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("Nat.pow_two_succ should type-check: {e:?}"));
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

    /// Ground sanity: `Nat.pow_two_succ 1 : 2^2 = 2^1 + 2^1`, i.e. `4 = 2 + 2`.
    #[test]
    fn test_nat_pow_two_succ_ground() {
        let mut env = Environment::with_prelude();
        env.register_nat_pow_two_succ_proof().expect("register");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(succ.clone(), zero.clone());
        let pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let two = Expr::app(succ.clone(), one.clone());
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let thm = Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]);
        // pow_two_succ 1 : Nat.pow 2 (succ 1) = Nat.add (Nat.pow 2 1) (Nat.pow 2 1)
        let app = Expr::app(thm, one.clone());
        let pow21 = Expr::apps(pow.clone(), [two.clone(), one.clone()]);
        let expected = Expr::apps(
            eq1,
            [
                nat,
                Expr::apps(
                    pow.clone(),
                    [two.clone(), Expr::app(succ.clone(), one.clone())],
                ),
                Expr::apps(add, [pow21.clone(), pow21]),
            ],
        );
        tc.check_type(&app, &expected)
            .unwrap_or_else(|e| panic!("pow_two_succ 1 should have type 2^2 = 2^1+2^1: {e:?}"));
    }
}
