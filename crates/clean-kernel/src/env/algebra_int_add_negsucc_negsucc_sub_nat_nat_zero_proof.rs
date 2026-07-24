// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_negSucc_negSucc_subNatNat_zero :
//!    ∀ n k : Nat,
//!      Eq Int
//!        (Int.add (Int.negSucc n) (Int.negSucc k))
//!        (Int.subNatNat Nat.zero (Nat.add (Nat.succ n) (Nat.succ k)))`.
//!
//! This is the zero-left/successor branch needed by the remaining
//! negative transport theorem over intermediate `Int.subNatNat` results.
//! The proof composes the checked `Int.subNatNat_zero_succ`
//! normalization with checked Nat index rewrites.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddNegSuccNegSuccSubNatNatZeroConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_add_succ: Expr,
    nat_succ_add: Expr,
    int_sub_nat_nat_zero_succ: Expr,
}

impl IntAddNegSuccNegSuccSubNatNatZeroConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_succ: Expr::const_(Name::from_string("Nat.add_succ"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nat_add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), lhs), rhs)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn sub_zero(&self, n: Expr) -> Expr {
        self.sub_nat_nat(self.nat_zero.clone(), n)
    }

    fn lhs(&self, n: Expr, k: Expr) -> Expr {
        self.add_int(self.neg_succ(n), self.neg_succ(k))
    }

    fn rhs(&self, n: Expr, k: Expr) -> Expr {
        self.sub_zero(self.nat_add(self.succ(n), self.succ(k)))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_negsucc_negsucc_sub_nat_nat_zero_type(
    c: &IntAddNegSuccNegSuccSubNatNatZeroConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(n.clone(), k.clone()), c.rhs(n, k));
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_sub_zero_fn(c: &IntAddNegSuccNegSuccSubNatNatZeroConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.sub_zero(x);
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_negsucc_negsucc_sub_nat_nat_zero_value(
    c: &IntAddNegSuccNegSuccSubNatNatZeroConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    let add_n_k = c.nat_add(n.clone(), k.clone());
    let reduced_index = c.succ(add_n_k.clone());
    let succ_reduced_index = c.succ(reduced_index.clone());
    let target_index = c.nat_add(c.succ(n.clone()), c.succ(k.clone()));
    let add_succ_mid = c.succ(c.nat_add(c.succ(n.clone()), k.clone()));

    let h_zero_forward = Expr::app(c.int_sub_nat_nat_zero_succ.clone(), reduced_index.clone());
    let h_zero = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            c.sub_zero(succ_reduced_index.clone()),
            c.neg_succ(reduced_index.clone()),
            h_zero_forward,
        ],
    );

    let h_add_succ = Expr::app(
        Expr::app(c.nat_add_succ.clone(), c.succ(n.clone())),
        k.clone(),
    );
    let h_succ_add = Expr::app(Expr::app(c.nat_succ_add.clone(), n.clone()), k.clone());
    let h_congr_succ = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            c.nat_add(c.succ(n.clone()), k.clone()),
            reduced_index.clone(),
            c.nat_succ.clone(),
            h_succ_add,
        ],
    );
    let h_index_forward = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            target_index.clone(),
            add_succ_mid,
            succ_reduced_index.clone(),
            h_add_succ,
            h_congr_succ,
        ],
    );
    let h_index = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            target_index.clone(),
            succ_reduced_index.clone(),
            h_index_forward,
        ],
    );
    let sub_zero_fn = build_sub_zero_fn(c, &b);
    let h_target = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            succ_reduced_index.clone(),
            target_index.clone(),
            sub_zero_fn,
            h_index,
        ],
    );

    let proof = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            c.neg_succ(reduced_index),
            c.sub_zero(succ_reduced_index),
            c.sub_zero(target_index),
            h_zero,
            h_target,
        ],
    );

    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_negSucc_negSucc_subNatNat_zero` as a kernel-checked theorem.
    pub(crate) fn register_int_add_negsucc_negsucc_sub_nat_nat_zero_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_negSucc_negSucc_subNatNat_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_succ_proof()?;
        self.register_nat_succ_add_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;

        let c = IntAddNegSuccNegSuccSubNatNatZeroConsts::new();
        let type_ = build_int_add_negsucc_negsucc_sub_nat_nat_zero_type(&c);
        let value = build_int_add_negsucc_negsucc_sub_nat_nat_zero_value(&c);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_add_negsucc_negsucc_sub_nat_nat_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_negsucc_negsucc_sub_nat_nat_zero_proof()
            .expect("first registration");
        env.register_int_add_negsucc_negsucc_sub_nat_nat_zero_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_negSucc_negSucc_subNatNat_zero"))
            .expect("Int.add_negSucc_negSucc_subNatNat_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_negsucc_negsucc_sub_nat_nat_zero_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_negSucc_negSucc_subNatNat_zero"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_negSucc_negSucc_subNatNat_zero must be Constructive, got {:?}",
            quality
        );
    }
}
