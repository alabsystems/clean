// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_negSucc_subNatNat :
//!    ∀ k m n : Nat,
//!      Eq Int
//!        (Int.add (Int.negSucc k) (Int.subNatNat m n))
//!        (Int.subNatNat m (Nat.add n (Nat.succ k)))`.
//!
//! This left-operand negative transport composes checked `Int.add_comm`
//! with the checked right-operand negative transport
//! `Int.add_subNatNat_negSucc`. It is a direct reusable piece for the
//! `Int.add_assoc` cases where `b + c` normalizes to `Int.subNatNat`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddNegSuccSubNatNatConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    int_add_comm: Expr,
    right_transport: Expr,
}

impl IntAddNegSuccSubNatNatConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
            int_add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            right_transport: Expr::const_(Name::from_string("Int.add_subNatNat_negSucc"), vec![]),
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

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.neg_succ(k), self.sub_nat_nat(m, n))
    }

    fn mid(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.add_int(self.sub_nat_nat(m, n), self.neg_succ(k))
    }

    fn rhs(&self, k: Expr, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(m, self.nat_add(n, self.succ(k)))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_negsucc_sub_nat_nat_type(c: &IntAddNegSuccSubNatNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(k.clone(), m.clone(), n.clone()), c.rhs(k, m, n));
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_int_add_negsucc_sub_nat_nat_value(c: &IntAddNegSuccSubNatNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let lhs = c.lhs(k.clone(), m.clone(), n.clone());
    let mid = c.mid(k.clone(), m.clone(), n.clone());
    let rhs = c.rhs(k.clone(), m.clone(), n.clone());
    let h_comm = Expr::app(
        Expr::app(c.int_add_comm.clone(), c.neg_succ(k.clone())),
        c.sub_nat_nat(m.clone(), n.clone()),
    );
    let h_transport = Expr::app(
        Expr::app(Expr::app(c.right_transport.clone(), m.clone()), n.clone()),
        k.clone(),
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.int_type.clone(), lhs, mid, rhs, h_comm, h_transport],
    );

    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_negSucc_subNatNat` as a kernel-checked theorem.
    pub(crate) fn register_int_add_negsucc_sub_nat_nat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_negSucc_subNatNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_add_comm_proof()?;
        self.register_int_add_sub_nat_nat_negsucc_proof()?;

        let c = IntAddNegSuccSubNatNatConsts::new();
        let type_ = build_int_add_negsucc_sub_nat_nat_type(&c);
        let value = build_int_add_negsucc_sub_nat_nat_value(&c);

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
    fn test_int_add_negsucc_sub_nat_nat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_negsucc_sub_nat_nat_proof()
            .expect("first registration");
        env.register_int_add_negsucc_sub_nat_nat_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_negSucc_subNatNat"))
            .expect("Int.add_negSucc_subNatNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_negsucc_sub_nat_nat_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_negSucc_subNatNat"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_negSucc_subNatNat must be Constructive, got {:?}",
            quality
        );
    }
}
