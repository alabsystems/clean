// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_ofNat_succ_ofNat_negSucc :
//!    ∀ m n k : Nat,
//!      Eq Int
//!        (Int.add
//!          (Int.add (Int.ofNat (Nat.succ m)) (Int.ofNat n))
//!          (Int.negSucc k))
//!        (Int.add
//!          (Int.ofNat (Nat.succ m))
//!          (Int.add (Int.ofNat n) (Int.negSucc k)))`.
//!
//! This closes one positive outer / mixed inner-negative branch of the
//! remaining `Int.add_assoc` case split. The proof rewrites both sides to
//! `Int.subNatNat` normal forms, uses checked `Nat.add_comm` for the Nat
//! index order, and composes with checked left positive transport over
//! intermediate `Int.subNatNat` results.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocOfNatSuccOfNatNegSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_add_comm: Expr,
    left_transport: Expr,
}

impl IntAddAssocOfNatSuccOfNatNegSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            left_transport: Expr::const_(Name::from_string("Int.add_ofNat_succ_subNatNat"), vec![]),
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

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(
            self.add_int(self.of_nat(self.succ(m)), self.of_nat(n)),
            self.neg_succ(k),
        )
    }

    fn rhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(
            self.of_nat(self.succ(m)),
            self.add_int(self.of_nat(n), self.neg_succ(k)),
        )
    }

    fn lhs_normal(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.sub_nat_nat(self.nat_add(self.succ(m), n), self.succ(k))
    }

    fn rhs_normal(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.sub_nat_nat(self.nat_add(n, self.succ(m)), self.succ(k))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_ofnat_succ_ofnat_negsucc_type(
    c: &IntAddAssocOfNatSuccOfNatNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(m.clone(), n.clone(), k.clone()), c.rhs(m, n, k));
    let ty_raw = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_lhs_index_fn(
    c: &IntAddAssocOfNatSuccOfNatNegSuccConsts,
    parent: &EnvDeclBuilder,
    k: Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.sub_nat_nat(x, c.succ(k));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

fn build_int_add_assoc_ofnat_succ_ofnat_negsucc_value(
    c: &IntAddAssocOfNatSuccOfNatNegSuccConsts,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    let lhs_normal = c.lhs_normal(m.clone(), n.clone(), k.clone());
    let rhs_normal = c.rhs_normal(m.clone(), n.clone(), k.clone());
    let rhs = c.rhs(m.clone(), n.clone(), k.clone());

    let h_add_comm = Expr::app(
        Expr::app(c.nat_add_comm.clone(), c.succ(m.clone())),
        n.clone(),
    );
    let sub_nat_nat_fn = build_lhs_index_fn(c, &b, k.clone());
    let h_index = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            c.nat_add(c.succ(m.clone()), n.clone()),
            c.nat_add(n.clone(), c.succ(m.clone())),
            sub_nat_nat_fn,
            h_add_comm,
        ],
    );

    let h_rhs_forward = Expr::app(
        Expr::app(Expr::app(c.left_transport.clone(), m.clone()), n.clone()),
        c.succ(k.clone()),
    );
    let h_rhs = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            rhs.clone(),
            rhs_normal.clone(),
            h_rhs_forward,
        ],
    );
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [
            c.int_type.clone(),
            lhs_normal,
            rhs_normal,
            rhs,
            h_index,
            h_rhs,
        ],
    );

    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_ofNat_succ_ofNat_negSucc` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_ofnat_succ_ofnat_negsucc_proof(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Int.add_assoc_ofNat_succ_ofNat_negSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_comm_proof()?;
        self.register_int_add_ofnat_succ_sub_nat_nat_proof()?;

        let c = IntAddAssocOfNatSuccOfNatNegSuccConsts::new();
        let type_ = build_int_add_assoc_ofnat_succ_ofnat_negsucc_type(&c);
        let value = build_int_add_assoc_ofnat_succ_ofnat_negsucc_value(&c);

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
    fn test_int_add_assoc_ofnat_succ_ofnat_negsucc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_ofnat_succ_ofnat_negsucc_proof()
            .expect("first registration");
        env.register_int_add_assoc_ofnat_succ_ofnat_negsucc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_ofNat_succ_ofNat_negSucc"))
            .expect("Int.add_assoc_ofNat_succ_ofNat_negSucc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_ofnat_succ_ofnat_negsucc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_ofNat_succ_ofNat_negSucc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_ofNat_succ_ofNat_negSucc must be Constructive, got {:?}",
            quality
        );
    }
}
