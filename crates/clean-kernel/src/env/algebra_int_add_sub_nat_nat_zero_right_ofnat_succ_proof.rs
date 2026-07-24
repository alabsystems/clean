// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_subNatNat_zero_right_ofNat_succ :
//!    ∀ m k : Nat,
//!      Eq Int
//!        (Int.add (Int.subNatNat m Nat.zero) (Int.ofNat (Nat.succ k)))
//!        (Int.subNatNat (Nat.add m (Nat.succ k)) Nat.zero)`.
//!
//! This is the arbitrary-`m` zero-right base case for the remaining
//! positive transport theorem over intermediate `Int.subNatNat` results.
//! Both sides reduce to `Int.ofNat (Nat.add m (Nat.succ k))`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddSubNatNatZeroRightOfNatSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntAddSubNatNatZeroRightOfNatSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nat_add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), lhs), rhs)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn lhs(&self, m: Expr, k: Expr) -> Expr {
        Expr::app(
            Expr::app(
                self.int_add.clone(),
                self.sub_nat_nat(m, self.nat_zero.clone()),
            ),
            self.of_nat(self.succ(k)),
        )
    }

    fn rhs(&self, m: Expr, k: Expr) -> Expr {
        self.sub_nat_nat(self.nat_add(m, self.succ(k)), self.nat_zero.clone())
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_sub_nat_nat_zero_right_ofnat_succ_type(
    c: &IntAddSubNatNatZeroRightOfNatSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(m.clone(), k.clone()), c.rhs(m, k));
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_int_add_sub_nat_nat_zero_right_ofnat_succ_value(
    c: &IntAddSubNatNatZeroRightOfNatSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let reduced = c.of_nat(c.nat_add(m, c.succ(k)));
    let proof = Expr::apps(c.eq_refl.clone(), [c.int_type.clone(), reduced]);
    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_subNatNat_zero_right_ofNat_succ` as a kernel-checked theorem.
    pub(crate) fn register_int_add_sub_nat_nat_zero_right_ofnat_succ_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_subNatNat_zero_right_ofNat_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let c = IntAddSubNatNatZeroRightOfNatSuccConsts::new();
        let type_ = build_int_add_sub_nat_nat_zero_right_ofnat_succ_type(&c);
        let value = build_int_add_sub_nat_nat_zero_right_ofnat_succ_value(&c);

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
    fn test_int_add_sub_nat_nat_zero_right_ofnat_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_sub_nat_nat_zero_right_ofnat_succ_proof()
            .expect("first registration");
        env.register_int_add_sub_nat_nat_zero_right_ofnat_succ_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string(
                "Int.add_subNatNat_zero_right_ofNat_succ",
            ))
            .expect("Int.add_subNatNat_zero_right_ofNat_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_sub_nat_nat_zero_right_ofnat_succ_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string(
                "Int.add_subNatNat_zero_right_ofNat_succ",
            ))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_subNatNat_zero_right_ofNat_succ must be Constructive, got {:?}",
            quality
        );
    }
}
