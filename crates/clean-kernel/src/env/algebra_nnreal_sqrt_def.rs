// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `NNReal.sqrt` DEFINITION (Stage B3, sqrt run #4,
//! rung 8 part 1).
//!
//! # Why this module exists
//!
//! With rung 6 closed (`NNReal.dyadicApprox_isCauchy`), the scaled dyadic
//! approximation is a genuine `NNReal` Cauchy sequence, so it lifts through
//! `NNReal.CauSeq.mk` + `NNReal.mk` into an actual `NNReal`. That element is the
//! square root of the rational input `x ∈ [0,1)` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 8).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sqrtRat : Rat → NNReal`
//!     `:= fun x => NNReal.mk (NNReal.CauSeq.mk (Rat.dyadicApproxNN x)
//!                                              (NNReal.dyadicApprox_isCauchy x))`.
//!   Reducible `Definition`.
//! - `NNReal.le` of `NNReal.ofRat 0 _` to `sqrtRat x` is NOT proved here (it is
//!   the nonneg statement, immediate from the carrier; deferred to the order
//!   rung).
//!
//! Every declaration is a checked `Definition` through `self.add_decl`.
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Domain note
//!
//! The dyadic floor hardcodes `k_0 = 0`, so the construction is faithful on
//! `x ∈ [0,1)` (the KKL range; influences `Inf_i ∈ [0,1]`). `sqrtRat` is total
//! as a `Rat → NNReal` map, but the key identity `sqrtRat x · sqrtRat x = ofRat x`
//! holds on `0 ≤ x < 1` (the squeeze hypotheses, rung 7).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNReal.sqrtRat`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_def(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // NNReal, NNReal.mk, NNReal.CauSeq.mk
        self.init_algebra_nnreal_sqrt_iscauchy()?; // dyadicApproxNN, dyadicApprox_isCauchy

        let name = Name::from_string("NNReal.sqrtRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nnreal = Expr::const_(Name::from_string("NNReal"), vec![]);
        let nnreal_mk = Expr::const_(Name::from_string("NNReal.mk"), vec![]);
        let causeq_mk = Expr::const_(Name::from_string("NNReal.CauSeq.mk"), vec![]);
        let approxnn = Expr::const_(Name::from_string("Rat.dyadicApproxNN"), vec![]);
        let iscauchy = Expr::const_(Name::from_string("NNReal.dyadicApprox_isCauchy"), vec![]);

        let ty = Expr::pi(BinderInfo::Default, rat.clone(), nnreal.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            // CauSeq.mk (dyadicApproxNN x) (dyadicApprox_isCauchy x).
            let seq = Expr::app(approxnn, x.clone());
            let hcau = Expr::app(iscauchy, x.clone());
            let causeq = Expr::apps(causeq_mk, [seq, hcau]);
            let body = Expr::app(nnreal_mk, causeq);
            let e = b.mk_lam(x_id, BinderInfo::Default, rat.clone(), body);
            b.finish(e)
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
        env.init_algebra_nnreal_sqrt_def()
            .expect("init_algebra_nnreal_sqrt_def");
        env.init_algebra_nnreal_sqrt_def().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_sqrtrat_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.sqrtRat");
        let info = env.get_const(&nm).expect("NNReal.sqrtRat registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.sqrtRat must kernel-check");
    }
}
