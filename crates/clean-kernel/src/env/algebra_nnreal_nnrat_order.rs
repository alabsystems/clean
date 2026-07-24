// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B1 order lemmas: `NNRat.le_refl` / `NNRat.le_trans`.
//!
//! # Why this module exists
//!
//! The finite-prefix max bound (`algebra_nnreal_nnrat_prefixmax.rs`) — the core
//! of the `NNReal.CauSeq` boundedness theorem the `NNReal.mul` respect proof
//! needs (plan `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B2) —
//! chains `NNRat.le` through `NNRat.le_max_left` + transitivity. So we need the
//! reflexive/transitive structure of the reducible
//! `NNRat.le := fun p q => Rat.le (val p)(val q)`.
//!
//! Both lift directly from the on-main `Rat.le_refl` / `Rat.le_trans` (which are
//! genuine constructive quotient theorems, empty closure). Since `NNRat.le p q`
//! reduces to `Rat.le (val p)(val q)`, `NNRat.le_refl p` is `Rat.le_refl (val p)`
//! and `NNRat.le_trans p q r h1 h2` is `Rat.le_trans (val p)(val q)(val r) h1 h2`
//! (the hypotheses defeq-unfold to the `Rat.le` shape). Empty closure.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNRat.le_refl` and `NNRat.le_trans`. Idempotent. Pulls in the
    /// Stage-B1 base + the on-main `Rat.le_refl` / `Rat.le_trans`.
    pub fn init_algebra_nnreal_nnrat_order(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat()?;
        // Rat.le_refl / Rat.le_trans (genuine quotient theorems, empty closure).
        self.register_rat_le_trans_proof()?;
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.register_nnrat_le_refl_recovered()?;
        self.register_nnrat_le_trans_recovered()?;
        Ok(())
    }

    /// `NNRat.le_refl : ∀ p, NNRat.le p p`.
    fn register_nnrat_le_refl_recovered(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let nnrat_le = Expr::const_(Name::from_string("NNRat.le"), vec![]);
        let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        let val = |q: Expr| Expr::app(nnrat_val.clone(), q);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nnrat.clone());
            let concl = Expr::apps(nnrat_le.clone(), [p.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, nnrat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nnrat.clone());
            // Rat.le_refl (val p) : Rat.le (val p)(val p) ≡ NNRat.le p p.
            let body = Expr::app(rat_le_refl.clone(), val(p.clone()));
            let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.le_trans : ∀ p q r, NNRat.le p q → NNRat.le q r → NNRat.le p r`.
    fn register_nnrat_le_trans_recovered(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.le_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let nnrat_le = Expr::const_(Name::from_string("NNRat.le"), vec![]);
        let rat_le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let val = |q: Expr| Expr::app(nnrat_val.clone(), q);
        let le = |p: Expr, q: Expr| Expr::apps(nnrat_le.clone(), [p, q]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nnrat.clone());
            let (q_id, q) = b.fresh_local(nnrat.clone());
            let (r_id, r) = b.fresh_local(nnrat.clone());
            let h1_ty = le(p.clone(), q.clone());
            let h2_ty = le(q.clone(), r.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, _h2) = b.fresh_local(h2_ty.clone());
            let concl = le(p.clone(), r.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, nnrat.clone(), e);
            let e = b.mk_pi(q_id, BinderInfo::Default, nnrat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, nnrat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nnrat.clone());
            let (q_id, q) = b.fresh_local(nnrat.clone());
            let (r_id, r) = b.fresh_local(nnrat.clone());
            let h1_ty = le(p.clone(), q.clone());
            let h2_ty = le(q.clone(), r.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());
            // Rat.le_trans (val p)(val q)(val r) h1 h2 : Rat.le (val p)(val r).
            let body = Expr::apps(
                rat_le_trans.clone(),
                [val(p.clone()), val(q.clone()), val(r.clone()), h1, h2],
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(r_id, BinderInfo::Default, nnrat.clone(), e);
            let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
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

    const THEOREMS: &[&str] = &["NNRat.le_refl", "NNRat.le_trans"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_nnrat_order()
            .expect("init_algebra_nnreal_nnrat_order");
        env.init_algebra_nnreal_nnrat_order().expect("idempotent");
        env
    }

    #[test]
    fn test_nnrat_order_kernel_check() {
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
    fn test_nnrat_order_constructive_empty_closure() {
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
