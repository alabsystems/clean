// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin.sum_reindex_involution` — the keystone: a `Fin.sum` is invariant under
//! reindexing by an involution.  This is the precise primitive the kkl-retirement
//! `subsetSum_flip_invariant` consumes.
//!
//! ```text
//! Fin.sum_reindex_involution :
//!   ∀ (m : Nat) (σ : Fin m → Fin m),
//!     (∀ jx, σ (σ jx) = jx) → ∀ (F : Fin m → Rat),
//!       Fin.sum m (fun jx => F (σ jx)) = Fin.sum m F
//! ```
//!
//! Proof by `Nat.rec` on `m` (decrease by 1 suffices — both branches reduce to
//! the IH at size `k`), with motive `M m := ∀ σ, (∀x, σ(σ x)=x) → ∀ F,
//! Σ_m(F∘σ)=Σ_m F`:
//!
//! - **base `m = 0`**: `Σ_0` ι-reduces to `Rat.zero` on both sides — `Eq.refl`.
//! - **step `m = k+1`**: introduce `σ, hinv, F`; `Fin.lastCases` on `σ (last k)`
//!   (with an equality-carrying motive) splits:
//!   - `σ (last k) = last k`  → `Fin.sum_reindex_fixed_step k σ hinv hfix ih F`.
//!   - `σ (last k) = castSucc p` (`p : Fin k`) → the 2-cycle branch.  Here the
//!     `Fin.sum_remove` removals inside `twocycle_step` need the size `k` to be a
//!     successor, so `Nat.rec` (`casesOn`) on `k` exposes it: `k = 0` is vacuous
//!     (`p : Fin 0` is empty — `Nat.not_succ_le_zero` on `Fin.isLt p`), `k =
//!     k0+1` dispatches to `Fin.sum_reindex_twocycle_step k0 σ hinv p hcase ih F`.
//!
//! Constructive, empty admitted-axiom closure.  Once registered, it activates
//! `BoolAnalysis.subsetSum_flip_invariant`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct KeystoneConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_last_cases: Expr, // Fin.lastCases.{0}
    fixed_step: Expr,
    twocycle_step: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nat_rec1: Expr, // Nat.rec.{1} — motive M : Nat → Prop wrapped (returns Prop, but recursion on Nat is Sort 1 elimination → level of motive is 0; use Nat.rec.{0})
    nat_rec0: Expr, // Nat.rec.{0}
    nat_not_succ_le_zero: Expr,
    false_elim0: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl KeystoneConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            fin_last_cases: Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]),
            fixed_step: k("Fin.sum_reindex_fixed_step"),
            twocycle_step: k("Fin.sum_reindex_twocycle_step"),
            #[cfg(test)]
            nat_rec1: Expr::const_(Name::from_string("Nat.rec"), vec![l1.clone()]),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            nat_not_succ_le_zero: k("Nat.not_succ_le_zero"),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
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
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }

    /// `M m := ∀ (σ : Fin m → Fin m), (∀ x, σ (σ x) = x) → ∀ F, Σ_m (F∘σ) = Σ_m F`.
    fn motive_body(&self, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_m = self.fin_of(m);
        let sigma_ty = Expr::pi(BinderInfo::Default, fin_m.clone(), fin_m.clone());
        let (sigma_id, sigma) = d.fresh_local(sigma_ty.clone());
        let hinv = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = e.fresh_local(fin_m.clone());
            let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
            let body = self.eq_fin(m, ssx, x.clone());
            e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin_m.clone(), body))
        };
        let (hinv_id, _hinv) = d.fresh_local(hinv.clone());
        let f_ty = self.fin_to_rat(m);
        let (f_id, f) = d.fresh_local(f_ty.clone());
        let reindexed = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (jx_id, jx) = e.fresh_local(fin_m.clone());
            let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
            e.finish_child(e.mk_lam(jx_id, BinderInfo::Default, fin_m.clone(), body))
        };
        let concl = self.eq_rat(self.sum(m, &reindexed), self.sum(m, &f));
        let r = d.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
        let r = d.mk_pi(hinv_id, BinderInfo::Default, hinv, r);
        d.finish_child(d.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, r))
    }
}

include!("boolean_analysis_fin_reindex_keystone_build.rs");

impl Environment {
    /// Register `Fin.sum_reindex_involution` (see module docs). Constructive,
    /// empty admitted-axiom closure. Idempotent.  After this, call
    /// `register_subset_sum_flip_invariant` to activate the kkl-retirement leg.
    pub(crate) fn register_fin_sum_reindex_involution(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_reindex_involution");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ, Fin.sum_zero
        self.register_fin_last_cases()?; // Fin.lastCases
        self.register_fin_sum_reindex_fixed_step()?; // fixed branch
        self.register_fin_sum_reindex_twocycle_step()?; // 2-cycle branch
        self.register_nat_not_succ_le_zero_theorem()?; // empty Fin 0

        let c = KeystoneConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: keystone_type(&c),
            value: keystone_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_reindex_involution_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_reindex_involution().expect("register");
        env.register_fin_sum_reindex_involution()
            .expect("idempotent");

        let name = Name::from_string("Fin.sum_reindex_involution");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("keystone must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
