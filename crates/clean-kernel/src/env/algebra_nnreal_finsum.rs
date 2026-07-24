// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component B, target 1: the `NNReal`-valued `Fin.sum`
//! (`NNReal.zero`, `NNReal.finSum`) + its defining equations.
//!
//! # Why this module exists
//!
//! The sharp KKL max-influence charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` sums the
//! half-power values `Inf_i^{3/2}`, which are IRRATIONAL `NNReal` (e.g.
//! `(1/2)^{3/2}`). The on-main `Fin.sum` (`nn_verify_fin_sum.rs`) is MONOMORPHIC
//! over `Rat` (`Fin.sum : (n : Nat) → (Fin n → Rat) → Rat`), so it cannot type
//! the charge sum. This module builds the `NNReal`-valued companion.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.zero : NNReal := NNReal.ofRat Rat.zero (Rat.le_refl Rat.zero)` — the
//!   additive identity of the carrier (mirrors `NNRat.zero`). Reducible
//!   `Definition`.
//! - `NNReal.finSum : (n : Nat) → (Fin n → NNReal) → NNReal` — the faithful
//!   `Nat.rec.{1}` carrier mirroring the on-main `Fin.sum`:
//!   ```text
//!   NNReal.finSum := fun (n : Nat) (f : Fin n → NNReal) =>
//!     @Nat.rec.{1}
//!       (fun k => (Fin k → NNReal) → NNReal)              -- Π-motive
//!       (fun _ => NNReal.zero)                             -- zero case
//!       (fun k ih f' => NNReal.add (ih (fun i => f' (Fin.castSucc k i)))
//!                                   (f' (Fin.last k)))     -- succ case
//!       n f
//!   ```
//!   Reducible `Definition`.
//! - `NNReal.finSum_zero : ∀ f, NNReal.finSum 0 f = NNReal.zero` — base ι.
//! - `NNReal.finSum_succ : ∀ n f, NNReal.finSum (n+1) f =
//!       NNReal.add (NNReal.finSum n (fun i => f (Fin.castSucc n i)))
//!                   (f (Fin.last n))` — step ι (the carrier's defining equation).
//!
//! The two equations close by `@Eq.refl.{1} NNReal …` on a real `Nat.rec`
//! ι-step (mirroring `Fin.sum_zero`/`Fin.sum_succ`), so they are genuine
//! reductions, not placeholder collapses.
//!
//! `Declaration::Definition` (carrier) / `Declaration::Theorem` (equations),
//! `ProofQuality::Constructive`, empty admitted-axiom closure (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `NNReal` `Fin.sum`.
pub(crate) struct NNFinSumConsts {
    pub(crate) nat: Expr,
    pub(crate) nat_zero: Expr,
    pub(crate) nat_succ: Expr,
    pub(crate) fin: Expr,
    pub(crate) fin_cast_succ: Expr,
    pub(crate) fin_last: Expr,
    pub(crate) nnreal: Expr,
    pub(crate) nnreal_zero: Expr,
    pub(crate) nnreal_add: Expr,
    pub(crate) nnreal_finsum: Expr,
    /// `Nat.rec.{1}` (motive returns `(Fin k → NNReal) → NNReal : Sort 1`).
    pub(crate) nat_rec: Expr,
    /// `Eq.{1}` over `NNReal : Type 0 = Sort 1`.
    pub(crate) eq_nnreal: Expr,
    pub(crate) eq_refl_nnreal: Expr,
}

impl NNFinSumConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            nnreal: k("NNReal"),
            nnreal_zero: k("NNReal.zero"),
            nnreal_add: k("NNReal.add"),
            nnreal_finsum: k("NNReal.finSum"),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![lvl1.clone()]),
            eq_nnreal: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl_nnreal: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1]),
        }
    }

    /// `Fin n → NNReal` (the type of a summand function).
    pub(crate) fn fin_to_nnreal(&self, n: Expr) -> Expr {
        let fin_n = Expr::app(self.fin.clone(), n);
        Expr::pi(BinderInfo::Default, fin_n, self.nnreal.clone())
    }

    /// `NNReal.add a b : NNReal`.
    pub(crate) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a, b])
    }

    /// `NNReal.finSum n f : NNReal`.
    pub(crate) fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [n, f])
    }

    /// `@Eq.{1} NNReal lhs rhs`.
    pub(crate) fn eq_nnreal(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_nnreal.clone(), [self.nnreal.clone(), lhs, rhs])
    }

    /// The cast-prefix function `fun i : Fin k => f (Fin.castSucc k i)`.
    pub(crate) fn cast_prefix(&self, parent: &EnvDeclBuilder, k: Expr, f: Expr) -> Expr {
        let fin_k = Expr::app(self.fin.clone(), k.clone());
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(fin_k.clone());
        let cast_i = Expr::app(Expr::app(self.fin_cast_succ.clone(), k), i);
        let body = Expr::app(f, cast_i);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
        b.finish_child(lam)
    }
}

impl Environment {
    /// Register `NNReal.zero`, `NNReal.finSum`, and its two defining equations.
    /// Idempotent. Pulls in the carrier (`NNReal`, `NNReal.add`, `NNReal.ofRat`),
    /// `Fin.castSucc`/`Fin.last`, and `Eq`.
    pub fn init_algebra_nnreal_finsum(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // NNReal, NNReal.add, carrier (+ NNRat)
        self.init_fin_sum()?; // Fin, Fin.castSucc, Fin.last (the Rat Fin.sum infra)
        self.init_eq()?;

        let c = NNFinSumConsts::new();
        self.register_nnreal_zero(&c)?;
        self.register_nnreal_finsum(&c)?;
        self.register_nnreal_finsum_zero(&c)?;
        self.register_nnreal_finsum_succ(&c)?;
        Ok(())
    }

    /// `NNReal.zero : NNReal := NNReal.ofRat Rat.zero (Rat.le_refl Rat.zero)`.
    fn register_nnreal_zero(&mut self, c: &NNFinSumConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNReal.zero")).is_some() {
            return Ok(());
        }
        let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        // 0 ≤ 0 via Rat.le_refl Rat.zero (the on-main constructive theorem).
        let h00 = Expr::app(rat_le_refl, rat_zero.clone());
        let value = Expr::apps(of_rat, [rat_zero, h00]);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.zero"),
            level_params: vec![],
            type_: c.nnreal.clone(),
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.finSum : (n : Nat) → (Fin n → NNReal) → NNReal` — faithful
    /// `Nat.rec.{1}` carrier (mirrors `Fin.sum`).
    fn register_nnreal_finsum(&mut self, c: &NNFinSumConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.finSum"))
            .is_some()
        {
            return Ok(());
        }

        // Type: (n : Nat) → (Fin n → NNReal) → NNReal.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_nnreal(n);
            let (f_id, _f) = b.fresh_local(f_type.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, c.nnreal.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun n f => Nat.rec.{1} motive zero_case succ_case n f.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let f_type = c.fin_to_nnreal(n.clone());
            let (f_id, f_outer) = b.fresh_local(f_type.clone());

            // Motive: fun (k : Nat) => (Fin k → NNReal) → NNReal.
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let fk_to_nnreal = c.fin_to_nnreal(k);
                let body = Expr::pi(BinderInfo::Default, fk_to_nnreal, c.nnreal.clone());
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
                ch.finish_child(r)
            };

            // Zero case: fun (_f : Fin 0 → NNReal) => NNReal.zero.
            let zero_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let f0_type = c.fin_to_nnreal(c.nat_zero.clone());
                let (f0_id, _f0) = ch.fresh_local(f0_type.clone());
                let r = ch.mk_lam(f0_id, BinderInfo::Default, f0_type, c.nnreal_zero.clone());
                ch.finish_child(r)
            };

            // Succ case: fun (k : Nat) (ih : (Fin k → NNReal) → NNReal)
            //                (f' : Fin (k+1) → NNReal) =>
            //              NNReal.add (ih (fun i => f' (Fin.castSucc k i)))
            //                          (f' (Fin.last k)).
            let succ_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = ch.fresh_local(c.nat.clone());
                let ih_type = Expr::pi(
                    BinderInfo::Default,
                    c.fin_to_nnreal(k.clone()),
                    c.nnreal.clone(),
                );
                let (ih_id, ih) = ch.fresh_local(ih_type.clone());
                let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
                let f_type_succ = c.fin_to_nnreal(succ_k);
                let (fp_id, fp) = ch.fresh_local(f_type_succ.clone());

                let composed = c.cast_prefix(&ch, k.clone(), fp.clone());
                let ih_app = Expr::app(ih, composed);
                let last_k = Expr::app(c.fin_last.clone(), k.clone());
                let f_last = Expr::app(fp, last_k);
                let sum = c.add(ih_app, f_last);

                let r = ch.mk_lam(fp_id, BinderInfo::Default, f_type_succ, sum);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
                let r = ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            let rec_app = Expr::apps(
                c.nat_rec.clone(),
                [motive, zero_case, succ_case, n.clone(), f_outer],
            );
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, rec_app);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.finSum"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.finSum_zero : ∀ (f : Fin 0 → NNReal), NNReal.finSum 0 f = NNReal.zero`.
    /// Closes by `@Eq.refl.{1} NNReal NNReal.zero` (base ι on Nat.rec).
    fn register_nnreal_finsum_zero(&mut self, c: &NNFinSumConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.finSum_zero"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let f_type = c.fin_to_nnreal(c.nat_zero.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let lhs = c.sum(c.nat_zero.clone(), f);
            let body = c.eq_nnreal(lhs, c.nnreal_zero.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let f_type = c.fin_to_nnreal(c.nat_zero.clone());
            let (f_id, _f) = b.fresh_local(f_type.clone());
            let body = Expr::apps(
                c.eq_refl_nnreal.clone(),
                [c.nnreal.clone(), c.nnreal_zero.clone()],
            );
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, body);
            b.finish(r)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNReal.finSum_zero"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.finSum_succ : ∀ (n : Nat) (f : Fin (n+1) → NNReal),
    ///     NNReal.finSum (n+1) f =
    ///       NNReal.add (NNReal.finSum n (fun i => f (Fin.castSucc n i)))
    ///                   (f (Fin.last n))`.
    /// Closes by `@Eq.refl.{1} NNReal (NNReal.finSum (n+1) f)` (step ι on Nat.rec).
    fn register_nnreal_finsum_succ(&mut self, c: &NNFinSumConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.finSum_succ"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(c.nat_succ.clone(), n.clone());
            let f_type = c.fin_to_nnreal(succ_n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());

            let lhs = c.sum(succ_n, f.clone());
            let composed = c.cast_prefix(&b, n.clone(), f.clone());
            let sum_prefix = c.sum(n.clone(), composed);
            let f_last = Expr::app(f, Expr::app(c.fin_last.clone(), n.clone()));
            let rhs = c.add(sum_prefix, f_last);

            let body = c.eq_nnreal(lhs, rhs);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_n = Expr::app(c.nat_succ.clone(), n.clone());
            let f_type = c.fin_to_nnreal(succ_n.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());
            let lhs = c.sum(succ_n, f);
            let refl = Expr::apps(c.eq_refl_nnreal.clone(), [c.nnreal.clone(), lhs]);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_type, refl);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNReal.finSum_succ"),
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

    const DEFS: &[&str] = &["NNReal.zero", "NNReal.finSum"];
    const THEOREMS: &[&str] = &["NNReal.finSum_zero", "NNReal.finSum_succ"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum()
            .expect("init_algebra_nnreal_finsum");
        env.init_algebra_nnreal_finsum().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_all_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
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
    fn test_nnreal_finsum_defs_are_definitions() {
        let env = env();
        for name in DEFS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be Definition"
            );
        }
    }

    #[test]
    fn test_nnreal_finsum_theorems_constructive_empty_closure() {
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
