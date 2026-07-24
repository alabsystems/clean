// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C, target 1: the HALF-POWER value `x^{3/2}`
//! (`NNReal.pow32`).
//!
//! # Why this module exists
//!
//! The sharp KKL max-influence retirement needs the `n`-FREE per-coordinate
//! charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]`. With `NNReal.sqrtRat` landed
//! axiom-free (`algebra_nnreal_sqrt_def.rs` / `_identity.rs`), the value
//! `x^{3/2} = x·√x` is now NAMEABLE in the `NNReal` carrier (it is irrational
//! in general — e.g. `(1/2)^{3/2}` — so the `Rat`-only overlay cannot name it).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.pow32 : (x : Rat) → Rat.le Rat.zero x → NNReal`
//!     `:= fun x h0 => NNReal.mul (NNReal.ofRat x h0) (NNReal.sqrtRat x)`.
//!   Reducible `Definition`. This is the half-power `x^{3/2}` of a nonneg
//!   rational `x`: the product of the embedded value `x` and its square root.
//!   `NNReal.mul`, `NNReal.ofRat`, `NNReal.sqrtRat` are all the landed
//!   axiom-free carrier operations.
//!
//! # Bridge to the rational shadow (the SQUARE)
//!
//! `(pow32 x)·(pow32 x) = ofRat (x·x)·x` — both sides nonneg — reduces (via
//! the keystone `NNReal.sqrtRat_mul_self : √x·√x = ofRat x` plus `NNReal.mul`
//! commutativity/associativity and `ofRat` multiplicativity) to the rational
//! cube `ofRat ((x·x)·x)`. That is the SQUARE of the half-power bound
//! `x^{3/2} ≤ ε^{1/2}·x`, whose rational shadow `(x·x)·x ≤ ε·(x·x)` is the
//! landed `BoolAnalysis.cube_le_eps_sq_mul`. The reverse-square inversion over
//! the genuine `NNReal` carrier is the next rung (see the Stage-C status note).
//!
//! # Domain note
//!
//! The dyadic-floor `sqrtRat` is faithful on `x ∈ [0,1)` (the KKL range;
//! influences `Inf_i ∈ [0,1]`). `pow32` is total as a guarded `Rat → NNReal`
//! map, but the key SQUARE identity carries the `x < 1` hypothesis from the
//! `NNReal.sqrtRat_mul_self` keystone.
//!
//! See `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` (Stage C).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNReal.pow32`. Idempotent; axiom-free.
    ///
    /// `NNReal.pow32 x h0 := NNReal.mul (NNReal.ofRat x h0) (NNReal.sqrtRat x)`.
    pub fn init_algebra_nnreal_pow32(&mut self) -> Result<(), EnvError> {
        // carrier + sqrtRat (pulls NNReal, NNReal.ofRat, sqrtRat).
        self.init_algebra_nnreal_sqrt_def()?; // NNReal.sqrtRat (+ carrier)
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul

        let name = Name::from_string("NNReal.pow32");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let nnreal = Expr::const_(Name::from_string("NNReal"), vec![]);
        let nnreal_mul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let nnreal_of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
        let nnreal_sqrt = Expr::const_(Name::from_string("NNReal.sqrtRat"), vec![]);

        // Type: (x : Rat) → Rat.le 0 x → NNReal.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            let h0_ty = Expr::apps(rat_le.clone(), [rat_zero.clone(), x.clone()]);
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, nnreal.clone());
            b.finish(b.mk_pi(x_id, BinderInfo::Default, rat.clone(), e))
        };

        // Value: fun x h0 => NNReal.mul (NNReal.ofRat x h0) (NNReal.sqrtRat x).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            let h0_ty = Expr::apps(rat_le.clone(), [rat_zero.clone(), x.clone()]);
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let xnn = Expr::apps(nnreal_of_rat.clone(), [x.clone(), h0.clone()]);
            let sx = Expr::app(nnreal_sqrt.clone(), x.clone());
            let body = Expr::apps(nnreal_mul.clone(), [xnn, sx]);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, body);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, rat.clone(), e))
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_pow32()
            .expect("init_algebra_nnreal_pow32");
        env.init_algebra_nnreal_pow32().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_pow32_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.pow32");
        let info = env.get_const(&nm).expect("NNReal.pow32 registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.pow32 must kernel-check");
    }
}
