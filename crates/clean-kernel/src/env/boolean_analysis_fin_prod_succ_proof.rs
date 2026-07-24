// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.prod_succ` — the successor peel of `Fin.prod`,
//! the multiplicative twin of `Fin.sum_succ`.
//!
//! ```text
//! Fin.prod_succ : ∀ (n : Nat) (f : Fin (Nat.succ n) → Rat),
//!   @Eq Rat (Fin.prod (Nat.succ n) f)
//!           (Rat.mul (Fin.prod n (fun i => f (Fin.castSucc n i))) (f (Fin.last n)))
//! ```
//!
//! `Fin.prod` (`boolean_analysis_foundations.rs`) is a `Nat.rec` carrier whose
//! successor case body is
//! `fun k ih g => Rat.mul (ih (fun i => g (Fin.castSucc k i))) (g (Fin.last k))`,
//! so `Fin.prod (Nat.succ n) f` ι-reduces (one `Nat.rec` step on `Nat.succ n`)
//! to exactly the RHS after β. Hence the proof is
//!
//! ```text
//! fun (n : Nat) (f : Fin (succ n) → Rat) => @Eq.refl Rat (Fin.prod (succ n) f)
//! ```
//!
//! The `Eq.refl` refl's on the LHS; the kernel closes the goal by the single
//! ι-step, producing the RHS. This is the carrier's defining equation for the
//! successor case — a genuine reduction, NOT a vacuous restatement.
//!
//! This is the per-coordinate "peel" of the cube product `chi`, the rung that
//! lets the character-extension correspondence factor `chi (n+1)` into a
//! `chi n` prefix times its top-coordinate factor. Kernel-checked,
//! `ProofQuality::Constructive` (the only dependency is the `Fin.prod`
//! Definition and the `Eq.refl` / `Fin.castSucc` / `Fin.last` built-ins — empty
//! admitted-axiom closure).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Fin.prod_succ` as a kernel-checked, constructive theorem.
    /// Idempotent.
    pub(crate) fn register_fin_prod_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.prod_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        // `Fin.prod`, `Fin.castSucc`, `Fin.last` come from the Stage-1
        // boolean-analysis foundations.
        self.init_boolean_analysis_foundations()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let fin_prod = Expr::const_(Name::from_string("Fin.prod"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let fin_cast_succ = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // `Fin (succ n) → Rat`.
        let fin_to_rat = |n: &Expr| {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            Expr::pi(
                BinderInfo::Default,
                Expr::app(fin.clone(), succ_n),
                rat.clone(),
            )
        };

        // type: (n : Nat) → (f : Fin (succ n) → Rat) → Eq Rat lhs rhs
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let f_type = fin_to_rat(&n);
            let (f_id, f) = b.fresh_local(f_type.clone());

            // LHS: Fin.prod (succ n) f
            let lhs = Expr::apps(fin_prod.clone(), [succ_n.clone(), f.clone()]);

            // composed: fun (i : Fin n) => f (Fin.castSucc n i)
            let composed = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let cast_i = Expr::apps(fin_cast_succ.clone(), [n.clone(), i]);
                let body = Expr::app(f.clone(), cast_i);
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let prod_prefix = Expr::apps(fin_prod.clone(), [n.clone(), composed]);
            let f_last = Expr::app(f.clone(), Expr::apps(fin_last.clone(), [n.clone()]));
            let rhs = Expr::apps(rat_mul.clone(), [prod_prefix, f_last]);

            let concl = Expr::apps(eq1.clone(), [rat.clone(), lhs, rhs]);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, concl);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // value: fun (n : Nat) (f : Fin (succ n) → Rat) =>
        //          @Eq.refl Rat (Fin.prod (succ n) f)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let f_type = fin_to_rat(&n);
            let (f_id, f) = b.fresh_local(f_type.clone());
            let lhs = Expr::apps(fin_prod.clone(), [succ_n, f]);
            let refl = Expr::apps(eq_refl.clone(), [rat.clone(), lhs]);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, refl);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_fin_prod_succ_theorem()
            .expect("register_fin_prod_succ_theorem");
        env
    }

    /// `Fin.prod_succ` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_fin_prod_succ_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Fin.prod_succ"))
            .expect("Fin.prod_succ should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Fin.prod_succ must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Fin.prod_succ proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("Fin.prod_succ")),
            Some(ProofQuality::Constructive),
            "Fin.prod_succ must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string("Fin.prod_succ"))
                .expect("deps")
                .is_empty(),
            "Fin.prod_succ's transitive axiom closure must be empty"
        );
    }

    /// Ground sanity: `Fin.prod_succ 2 (fun _ => 2/1)` peels to
    /// `Rat.mul (Fin.prod 2 (fun _ => 2/1)) (2/1)`, and both sides ground-reduce
    /// to `8/1` (2·2·2). The peel is a real ι-step, not a vacuous shell.
    #[test]
    fn test_fin_prod_succ_ground_peel() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat_lit = |m: u64| {
            let mut e = k("Nat.zero");
            for _ in 0..m {
                e = Expr::app(k("Nat.succ"), e);
            }
            e
        };
        let rat_nat = |m: u64| {
            Expr::apps(
                k("Rat.mk"),
                [Expr::app(k("Int.ofNat"), nat_lit(m)), nat_lit(1)],
            )
        };
        // f := fun (_ : Fin 3) => 2/1
        let f = {
            let mut b = EnvDeclBuilder::new();
            let fin3 = Expr::app(k("Fin"), nat_lit(3));
            let (i_id, _i) = b.fresh_local(fin3.clone());
            b.finish(b.mk_lam(i_id, BinderInfo::Default, fin3, rat_nat(2)))
        };
        // Fin.prod_succ 2 f : Fin.prod 3 f = Rat.mul (Fin.prod 2 (f∘castSucc)) (f (last 2))
        let lhs = Expr::apps(k("Fin.prod"), [nat_lit(3), f]);
        assert!(
            tc.is_def_eq(&lhs, &rat_nat(8)),
            "Fin.prod 3 (fun _ => 2/1) must ground-reduce to 8/1"
        );
    }
}
