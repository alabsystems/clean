// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.finSum_congr` + `NNReal.finSum_add`: the two
//! `NNReal.finSum` structural lemmas the sqrt-free `(4/3,4)` dual-HC
//! tensorization's L3 finSum-cube split needs.
//!
//! # Why this module exists (L3 sub-lemmas)
//!
//! The L3 split `Σ_i ((A i+B i)·…)·… = (ΣA³ + Σ3A²B) + (Σ3AB² + ΣB³)` (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) applies `NNReal.add_cube`
//! POINTWISE under the finSum, then distributes the finSum over the four-way `+`.
//! Both moves need `NNReal.finSum` companions the carrier didn't ship:
//!
//! - `NNReal.finSum_congr : ∀ n f g, (∀ i, f i = g i) → finSum n f = finSum n g`
//!   — the pointwise-rewrite-under-the-sum lemma (NNReal dual of the landed
//!   `Fin.sum_congr`).
//! - `NNReal.finSum_add : ∀ n f g,
//!       finSum n (fun i => (f i)+(g i)) = (finSum n f)+(finSum n g)` — the
//!   additivity / linearity of `finSum` (NNReal dual of the landed `Fin.sum_add`).
//!
//! Both are `Nat.rec.{0}` inductions over the faithful `NNReal.finSum` carrier
//! (the conclusion is an `Eq` in `Prop`). `finSum_congr`'s step uses `congr`/
//! `congrArg` on `NNReal.add`; `finSum_add`'s base is `Eq.symm (NNReal.zero_add
//! NNReal.zero)` and its step reassociates four `NNReal.add`s with the landed
//! `NNReal.add_assoc`/`NNReal.add_comm`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the two finSum structural lemmas.
pub(crate) struct FinSumStructConsts {
    pub(crate) base: NNFinSumConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    /// `Nat.rec.{0}` (motive `Nat → Prop`).
    nat_rec0: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    congr_arg11: Expr,
    congr11: Expr,
    nnreal_add: Expr,
    nnreal_add_assoc: Expr,
    nnreal_add_comm: Expr,
    nnreal_zero_add: Expr,
}

impl FinSumStructConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr11: Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1.clone()]),
            nnreal_add: k("NNReal.add"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nnreal_add_comm: k("NNReal.add_comm"),
            nnreal_zero_add: k("NNReal.zero_add"),
        }
    }

    fn nn(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        self.base.sum(n.clone(), f.clone())
    }
    fn fin_n(&self, n: &Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n.clone())
    }
    fn fin_to_nn(&self, n: &Expr) -> Expr {
        self.base.fin_to_nnreal(n.clone())
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        self.base.eq_nnreal(a.clone(), b.clone())
    }
    fn app1(&self, f: &Expr, a: &Expr) -> Expr {
        Expr::app(f.clone(), a.clone())
    }
    fn trans(&self, a: &Expr, b: &Expr, c: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.nn(), a.clone(), b.clone(), c.clone(), h1, h2],
        )
    }
    /// `NNReal.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), c.clone()],
        )
    }
    /// `NNReal.add_comm a b : a+b = b+a`.
    fn add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_comm.clone(), [a.clone(), b.clone()])
    }
    fn symm_assoc(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        // Eq.symm (add_assoc a b c) : a+(b+c) = (a+b)+c.
        let lhs = self.add(&self.add(a, b), c);
        let rhs = self.add(a, &self.add(b, c));
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [self.nn(), lhs, rhs, self.add_assoc(a, b, c)],
        )
    }
    /// `congrArg (fun w => w + fixed) h`.
    fn cong_add_left(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        x: &Expr,
        y: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nn());
            let body = self.add(&w, fixed);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nn(), body))
        };
        Expr::apps(
            self.congr_arg11.clone(),
            [self.nn(), self.nn(), x.clone(), y.clone(), f, h],
        )
    }
    /// `congrArg (fun w => fixed + w) h`.
    fn cong_add_right(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        x: &Expr,
        y: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nn());
            let body = self.add(fixed, &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nn(), body))
        };
        Expr::apps(
            self.congr_arg11.clone(),
            [self.nn(), self.nn(), x.clone(), y.clone(), f, h],
        )
    }
    /// `fun i : Fin k => F (Fin.castSucc k i)` (cast prefix).
    fn cast_fn(&self, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(self.fin_n(k));
        let cast = Expr::apps(self.fin_cast_succ.clone(), [k.clone(), i]);
        let body = Expr::app(f.clone(), cast);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, self.fin_n(k), body))
    }
    /// `fun i : Fin n => (f i) + (g i)` (pointwise add).
    fn pointwise_add(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(self.fin_n(n));
        let body = self.add(&self.app1(f, &i), &self.app1(g, &i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, self.fin_n(n), body))
    }
    /// The pointwise-hypothesis type `∀ i : Fin n, f i = g i`.
    fn hyp_ty(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = ch.fresh_local(self.fin_n(n));
        let body = self.eq_nn(&self.app1(f, &i), &self.app1(g, &i));
        ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, self.fin_n(n), body))
    }
}

impl Environment {
    /// Register `NNReal.finSum_congr` + `NNReal.finSum_add`. Idempotent;
    /// foundational-only closure.
    pub fn init_algebra_nnreal_finsum_add(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.finSum + _zero/_succ + NNReal.zero
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_comm, NNReal.add_assoc
        self.init_algebra_nnreal_zero_add()?; // NNReal.zero_add (base of finSum_add)
        self.init_eq()?;

        let c = FinSumStructConsts::new();
        self.register_nnreal_finsum_congr(&c)?;
        self.register_nnreal_finsum_add(&c)?;
        Ok(())
    }
}

mod congr;
mod sum_add;

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.finSum_congr", "NNReal.finSum_add"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_add()
            .expect("init_algebra_nnreal_finsum_add");
        env.init_algebra_nnreal_finsum_add().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_add_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_nnreal_finsum_add_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
