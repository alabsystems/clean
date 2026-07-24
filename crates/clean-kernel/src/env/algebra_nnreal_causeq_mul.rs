// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.CauSeq.mul` (the carrier-level pointwise
//! product of Cauchy sequences).
//!
//! # What this registers (axiom-free, kernel-checked)
//!
//! - `NNReal.CauSeq.mul : NNReal.CauSeq → NNReal.CauSeq → NNReal.CauSeq`
//!     `:= fun f g => CauSeq.mk (fun n => NNRat.mul (seq f n) (seq g n))
//!                              (IsCauchy_mul (seq f)(seq g)(property f)(property g))`
//!
//! The SUBTYPE carrier requires every `CauSeq.mk` to carry an `IsCauchy` proof
//! of its underlying sequence; `NNReal.IsCauchy_mul` (this lane) supplies it for
//! the pointwise product. This is the multiplicative twin of `NNReal.CauSeq.add`
//! and the carrier-level prerequisite for `NNReal.mul`'s `Quot.lift`.
//!
//! `Declaration::Definition`, foundational-only admitted-axiom closure (it rides
//! on the `Constructive` `IsCauchy_mul`). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNReal.CauSeq.mul`. Idempotent.
    pub fn init_algebra_nnreal_causeq_mul(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // CauSeq, mk, seq, property; NNRat.mul
        self.init_algebra_nnreal_iscauchy_mul()?; // NNReal.IsCauchy_mul

        let name = Name::from_string("NNReal.CauSeq.mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let causeq = Expr::const_(Name::from_string("NNReal.CauSeq"), vec![]);
        let causeq_mk = Expr::const_(Name::from_string("NNReal.CauSeq.mk"), vec![]);
        let causeq_seq = Expr::const_(Name::from_string("NNReal.CauSeq.seq"), vec![]);
        let causeq_property = Expr::const_(Name::from_string("NNReal.CauSeq.property"), vec![]);
        let nnrat_mul = Expr::const_(Name::from_string("NNRat.mul"), vec![]);
        let is_cauchy_mul = Expr::const_(Name::from_string("NNReal.IsCauchy_mul"), vec![]);

        let seq_of = |f: &Expr| Expr::app(causeq_seq.clone(), f.clone());
        let seq_at = |f: &Expr, n: &Expr| Expr::app(seq_of(f), n.clone());
        let property = |f: &Expr| Expr::app(causeq_property.clone(), f.clone());

        let ty = Expr::pi(
            BinderInfo::Default,
            causeq.clone(),
            Expr::pi(BinderInfo::Default, causeq.clone(), causeq.clone()),
        );

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(causeq.clone());
            let (g_id, g) = b.fresh_local(causeq.clone());
            // pointwise product sequence : fun n => NNRat.mul (seq f n)(seq g n).
            let prod_seq = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = bn.fresh_local(nat.clone());
                let body = Expr::apps(nnrat_mul.clone(), [seq_at(&f, &n), seq_at(&g, &n)]);
                bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, nat.clone(), body))
            };
            // hcau := IsCauchy_mul (seq f)(seq g)(property f)(property g).
            let hcau = Expr::apps(
                is_cauchy_mul.clone(),
                [seq_of(&f), seq_of(&g), property(&f), property(&g)],
            );
            let body = Expr::apps(causeq_mk.clone(), [prod_seq, hcau]);
            let e = b.mk_lam(g_id, BinderInfo::Default, causeq.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, causeq.clone(), e);
            b.finish(e)
        };
        let _ = nnrat;
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

    #[test]
    fn test_causeq_mul_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_causeq_mul()
            .expect("init_algebra_nnreal_causeq_mul");
        env.init_algebra_nnreal_causeq_mul().expect("idempotent");

        let nm = Name::from_string("NNReal.CauSeq.mul");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.CauSeq.mul must kernel-check");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
