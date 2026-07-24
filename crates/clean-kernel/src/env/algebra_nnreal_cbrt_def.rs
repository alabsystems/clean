// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the `NNReal.cbrt` DEFINITION (Rung 2 capstone).
//!
//! # Why this module exists
//!
//! With the cube telescoping `IsCauchy` closed
//! (`NNReal.cbrtDyadicApprox_isCauchy`, `algebra_nnreal_cbrt_iscauchy.rs`), the
//! scaled cube dyadic approximation is a genuine `NNReal` Cauchy sequence, so it
//! lifts through `NNReal.CauSeq.mk` + `NNReal.mk` into an actual `NNReal`. That
//! element is the cube root of the rational input `x ∈ [0,1)`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.cbrt : Rat → NNReal`
//!     `:= fun x => NNReal.mk (NNReal.CauSeq.mk (Rat.cbrtDyadicApproxNN x)
//!                                              (NNReal.cbrtDyadicApprox_isCauchy x))`.
//!   Reducible `Definition`.
//!
//! Every declaration is a checked `Definition` through `self.add_decl`.
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Domain note
//!
//! The cube dyadic floor hardcodes `k_0 = 0`, so the construction is faithful on
//! `x ∈ [0,1)` (the KKL range; influences `Inf_i ∈ [0,1]`). `NNReal.cbrt` is
//! total as a `Rat → NNReal` map, but the cube identity `cbrt x · cbrt x · cbrt x
//! = ofRat x` holds on `0 ≤ x < 1`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNReal.cbrt`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_def(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // NNReal, NNReal.mk, NNReal.CauSeq.mk
        self.init_algebra_nnreal_cbrt_iscauchy()?; // cbrtDyadicApproxNN, cbrtDyadicApprox_isCauchy

        let name = Name::from_string("NNReal.cbrt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nnreal = Expr::const_(Name::from_string("NNReal"), vec![]);
        let nnreal_mk = Expr::const_(Name::from_string("NNReal.mk"), vec![]);
        let causeq_mk = Expr::const_(Name::from_string("NNReal.CauSeq.mk"), vec![]);
        let approxnn = Expr::const_(Name::from_string("Rat.cbrtDyadicApproxNN"), vec![]);
        let iscauchy = Expr::const_(
            Name::from_string("NNReal.cbrtDyadicApprox_isCauchy"),
            vec![],
        );

        let ty = Expr::pi(BinderInfo::Default, rat.clone(), nnreal.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
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
        env.init_algebra_nnreal_cbrt_def()
            .expect("init_algebra_nnreal_cbrt_def");
        env.init_algebra_nnreal_cbrt_def().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_cbrt_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.cbrt");
        let info = env.get_const(&nm).expect("NNReal.cbrt registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.cbrt must kernel-check");
    }
}
