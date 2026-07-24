// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the dyadic Cauchy MODULUS (Stage B3, sqrt run #3).
//!
//! # Why this module exists
//!
//! The dyadic `IsCauchy` proof (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.4 item 4c) consumes the
//! modulus
//!
//! ```text
//!   Rat.exists_inv_two_pow_lt :
//!     ∀ ε, 0 < ε → ∃ N, Rat.lt (Rat.inv (Rat.ofNat (Nat.pow 2 N))) ε
//! ```
//!
//! "for every positive `ε` there is an `N` with `inv (2^N) < ε`." This is the
//! `inv`-form of the landed additive primitive `Rat.exists_pow_gt`
//! (`∃ N, 1 < ε·2^N`), bridged by the rung-4a consumer
//! `Rat.inv_lt_of_one_lt_mul` (`1 < c·b → inv b < c`) at `b := ofNat 2^N`,
//! `c := ε`, with `0 < ofNat 2^N` (`Rat.zero_lt_ofNat_two_pow`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.exists_inv_two_pow_lt` (above) — a `Declaration::Theorem`,
//!   `ProofQuality::Constructive`, empty admitted-axiom closure.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof
//!
//! `Exists.elim.{1}` on `Rat.exists_pow_gt ε hε : ∃ N, 1 < ε·2^N` into the
//! target `∃ N, inv (2^N) < ε`. The eliminator function
//! `fun (N : Nat)(hN : 1 < ε·ofNat 2^N) =>`
//! `  Exists.intro N (Rat.inv_lt_of_one_lt_mul (ofNat 2^N) ε`
//! `    (Rat.zero_lt_ofNat_two_pow N) hN)`.
//!
//! # Universe note
//!
//! `Exists`/`Exists.intro`/`Exists.elim` over `Nat : Sort 1` use universe **1**.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the dyadic modulus.
pub(crate) struct ModulusConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_exists_pow_gt: Expr,
    rat_inv_lt_of_one_lt_mul: Expr,
    rat_zero_lt_ofnat_two_pow: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
}

impl ModulusConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_exists_pow_gt: k("Rat.exists_pow_gt"),
            rat_inv_lt_of_one_lt_mul: k("Rat.inv_lt_of_one_lt_mul"),
            rat_zero_lt_ofnat_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    /// `∃ (N : Nat), p N`  := `@Exists.{1} Nat p`.
    fn exists_nat(&self, pred: Expr) -> Expr {
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred])
    }
    /// The SOURCE witness predicate `fun N => Rat.lt 1 (ε · ofNat 2^N)`.
    fn src_pred(&self, parent: &EnvDeclBuilder, eps: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = d.fresh_local(self.nat.clone());
        let body = self.lt(
            self.rat_one.clone(),
            self.mul(eps.clone(), self.ofnat(self.npow2(n))),
        );
        d.finish_child(d.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }
    /// The TARGET witness predicate `fun N => Rat.lt (inv (ofNat 2^N)) ε`.
    fn tgt_pred(&self, parent: &EnvDeclBuilder, eps: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = d.fresh_local(self.nat.clone());
        let body = self.lt(self.inv(self.ofnat(self.npow2(n))), eps.clone());
        d.finish_child(d.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }
}

impl Environment {
    /// Register `Rat.exists_inv_two_pow_lt`. Idempotent.
    pub fn init_algebra_rat_inv_dyadic_modulus(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_exists()?;
        // Rat.exists_pow_gt (the additive primitive).
        self.register_rat_exists_pow_gt()?;
        // Rat.inv_lt_of_one_lt_mul (rung 4a).
        self.init_algebra_rat_inv_dyadic()?;
        // Rat.zero_lt_ofNat_two_pow (rung 4a-ter).
        self.init_algebra_rat_inv_dyadic_step()?;

        let c = ModulusConsts::new();
        self.register_rat_exists_inv_two_pow_lt(&c)?;
        Ok(())
    }

    /// `Rat.exists_inv_two_pow_lt : ∀ ε, Rat.lt 0 ε →
    ///     ∃ N, Rat.lt (inv (ofNat (Nat.pow 2 N))) ε`.
    fn register_rat_exists_inv_two_pow_lt(&mut self, c: &ModulusConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.exists_inv_two_pow_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(c.rat_zero.clone(), eps.clone());
            let (hp_id, _hp) = b.fresh_local(hpos.clone());
            let concl = c.exists_nat(c.tgt_pred(&b, &eps));
            let e = b.mk_pi(hp_id, BinderInfo::Default, hpos, concl);
            let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(c.rat_zero.clone(), eps.clone());
            let (hp_id, hp) = b.fresh_local(hpos.clone());

            // ex : ∃ N, 1 < ε·ofNat 2^N  := exists_pow_gt ε hp.
            let ex = Expr::apps(c.rat_exists_pow_gt.clone(), [eps.clone(), hp]);
            let src_pred = c.src_pred(&b, &eps);
            let tgt_goal = c.exists_nat(c.tgt_pred(&b, &eps));
            let tgt_pred = c.tgt_pred(&b, &eps);

            // elim_fn : ∀ N, (1 < ε·ofNat 2^N) → ∃ N', inv(ofNat 2^N') < ε.
            let elim_fn = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = fb.fresh_local(c.nat.clone());
                let d = c.ofnat(c.npow2(n.clone()));
                let hn_ty = c.lt(c.rat_one.clone(), c.mul(eps.clone(), d.clone()));
                let (hn_id, hn) = fb.fresh_local(hn_ty.clone());
                // inv_lt : inv (ofNat 2^N) < ε.
                let pos = Expr::app(c.rat_zero_lt_ofnat_two_pow.clone(), n.clone());
                let inv_lt = Expr::apps(
                    c.rat_inv_lt_of_one_lt_mul.clone(),
                    [d.clone(), eps.clone(), pos, hn],
                );
                // Exists.intro Nat tgt_pred N inv_lt : ∃ N', inv(ofNat 2^N') < ε.
                let intro = Expr::apps(
                    c.exists_intro.clone(),
                    [c.nat.clone(), tgt_pred.clone(), n.clone(), inv_lt],
                );
                let lam = fb.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
                let lam = fb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                fb.finish_child(lam)
            };

            // @Exists.elim.{1} Nat src_pred tgt_goal ex elim_fn.
            let elim = Expr::apps(
                c.exists_elim.clone(),
                [c.nat.clone(), src_pred, tgt_goal, ex, elim_fn],
            );

            let e = b.mk_lam(hp_id, BinderInfo::Default, hpos, elim);
            let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
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
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.exists_inv_two_pow_lt"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_dyadic_modulus()
            .expect("init_algebra_rat_inv_dyadic_modulus");
        env.init_algebra_rat_inv_dyadic_modulus()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_rat_inv_dyadic_modulus_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_inv_dyadic_modulus_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
