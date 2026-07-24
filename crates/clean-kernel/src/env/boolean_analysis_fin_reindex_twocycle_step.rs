// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The 2-CYCLE inductive step of `Fin.sum_reindex_involution`, closed modulo the
//! size-`(k0+1)` induction hypothesis.
//!
//! At `m = k0+2` with the involution `σ` SWAPPING the top with an interior point
//! (`σ (last (k0+1)) = castSucc (k0+1) p`, `p : Fin (k0+1)`), reduce
//! `Σ_{k0+2}(F∘σ) = Σ_{k0+2} F` to the IH at `σ''` on `Fin (k0+1)`.
//!
//! ```text
//! Fin.sum_reindex_twocycle_step :
//!   (k0 : Nat) (σ : Fin (k0+2) → Fin (k0+2))
//!   → (∀ x, σ (σ x) = x)                                   -- σ involution
//!   → (p : Fin (k0+1))
//!   → (σ (Fin.last (k0+1)) = Fin.castSucc (k0+1) p)        -- σ swaps top with p
//!   → (∀ (τ : Fin (k0+1) → Fin (k0+1)), (∀ j, τ (τ j) = j)
//!        → ∀ G, Fin.sum (k0+1) (fun j => G (τ j)) = Fin.sum (k0+1) G)  -- IH
//!   → ∀ F, Fin.sum (k0+2) (fun jx => F (σ jx)) = Fin.sum (k0+2) F
//! ```
//!
//! Proof (Route B, constructive, empty admitted-axiom closure).  Write `k =
//! k0+1`, `σ'' := Fin.sigmaComplement k σ hinv p hcase`, `a := F (last k)`,
//! `b := F (castSucc p)`, `W := Σ_{k0} (complement)`.
//!
//! - `Fin.sum_succ` peels `last` on both sides:
//!     LHS = `Σ_k (Sσ) + F (σ (last))`, RHS = `Σ_k (Cf) + a`,
//!     where `Sσ j = F (σ (castSucc j))`, `Cf j = F (castSucc j)`.
//!   `F (σ (last)) = b` by `congrArg F hcase`.
//! - `Fin.sum_remove k0 p` pulls `p` out of `Σ_k(Sσ)` and `Σ_k(Sσ'')`:
//!     `Σ_k(Sσ) = Sσ p + W`,  `Sσ p = F (σ (castSucc p)) = a`  [partner];
//!     `Σ_k(Sσ'') = Sσ'' p + W`,  `Sσ'' p = F (castSucc (σ'' p)) = b`  [fix_p];
//!   the two `W`s match by `Fin.sum_congr` + `coh_ne` (off-`p`, via
//!   `skipNth_ne_p`).
//! - IH at `σ''`: `Σ_k(Sσ'') = Σ_k(Cf)`.
//! - Rat rearrange `(a + W) + b = (b + W) + a` (`Rat.add_swap_outer`).

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct TwoCycleConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_succ: Expr,
    fin_sum_congr: Expr,
    fin_sum_remove: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    skip_nth: Expr,
    skip_ne_p: Expr,
    sigma_complement: Expr,
    sc_partner: Expr,
    sc_fix_p: Expr,
    sc_coh_ne: Expr,
    sc_involutive: Expr,
    rat_add: Expr,
    rat_add_swap_outer: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl TwoCycleConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_succ: k("Fin.sum_succ"),
            fin_sum_congr: k("Fin.sum_congr"),
            fin_sum_remove: k("Fin.sum_remove"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            skip_nth: k("Fin.skipNth"),
            skip_ne_p: k("Fin.skipNth_ne_p"),
            sigma_complement: k("Fin.sigmaComplement"),
            sc_partner: k("Fin.sigmaComplement_partner"),
            sc_fix_p: k("Fin.sigmaComplement_fix_p"),
            sc_coh_ne: k("Fin.sigmaComplement_coh_ne"),
            sc_involutive: k("Fin.sigmaComplement_involutive"),
            rat_add: k("Rat.add"),
            rat_add_swap_outer: k("Rat.add_swap_outer"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f.clone()])
    }
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [x, y])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn eq_fin(&self, n: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.fin_of(n), l, r])
    }
    fn cast_succ(&self, k: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j.clone()])
    }
    fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }
    fn skip(&self, k0: &Expr, p: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.skip_nth.clone(), [k0.clone(), p.clone(), i.clone()])
    }
}

include!("boolean_analysis_fin_reindex_twocycle_build.rs");

impl Environment {
    /// Register `Rat.add_swap_outer : ∀ a w b, (a+w)+b = (b+w)+a`.
    /// Constructive (add_comm/add_assoc chain), empty axiom closure. Idempotent.
    pub(crate) fn register_rat_add_swap_outer(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_swap_outer");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat_field_inst()?; // Rat.add_assoc
        self.register_rat_add_comm_proof()?; // Rat.add_comm

        let c = TwoCycleConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: add_swap_outer_type(&c),
            value: add_swap_outer_value(&c),
        })
    }

    /// Register `Fin.sum_reindex_twocycle_step` (see module docs). Constructive,
    /// empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_fin_sum_reindex_twocycle_step(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_reindex_twocycle_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.register_rat_add_swap_outer()?;
        self.register_fin_sum_remove()?; // Fin.sum_remove
        self.register_fin_sigma_complement()?; // σ'' bundle
        self.register_fin_skip_ne_p()?; // Fin.skipNth_ne_p
        {
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?; // Fin.sum_congr
        }

        let c = TwoCycleConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: twocycle_step_type(&c),
            value: twocycle_step_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_rat_add_swap_outer_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_rat_add_swap_outer().expect("register");
        env.register_rat_add_swap_outer().expect("idempotent");
        let name = Name::from_string("Rat.add_swap_outer");
        let info = env.get_const(&name).expect("registered");
        let value = info.value.clone().expect("value");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("add_swap_outer must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_fin_sum_reindex_twocycle_step_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_reindex_twocycle_step()
            .expect("register");
        env.register_fin_sum_reindex_twocycle_step()
            .expect("idempotent");

        let name = Name::from_string("Fin.sum_reindex_twocycle_step");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("twocycle_step must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
