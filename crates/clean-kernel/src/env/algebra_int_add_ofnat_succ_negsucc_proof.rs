// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_ofNat_succ_negSucc :
//!    ∀ m n : Nat,
//!      Eq Int
//!        (Int.add (Int.ofNat (Nat.succ m)) (Int.negSucc n))
//!        (Int.subNatNat m n)`.
//!
//! This composes the checked mixed-sign `Int.add` branch with
//! successor/successor cancellation for `Int.subNatNat`. It is a direct
//! normalization step needed by mixed-sign `Int.add_assoc` cases.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddOfNatSuccNegSuccConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_add_ofnat_negsucc: Expr,
    int_sub_nat_nat_succ_succ: Expr,
    eq_const: Expr,
    eq_trans: Expr,
}

impl IntAddOfNatSuccNegSuccConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_add_ofnat_negsucc: Expr::const_(Name::from_string("Int.add_ofNat_negSucc"), vec![]),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn lhs(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(
            Expr::app(
                self.int_add.clone(),
                Expr::app(self.int_of_nat.clone(), self.succ(m)),
            ),
            Expr::app(self.int_neg_succ.clone(), n),
        )
    }

    fn mid(&self, m: Expr, n: Expr) -> Expr {
        self.sub_nat_nat(self.succ(m), self.succ(n))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_ofnat_succ_negsucc_type(c: &IntAddOfNatSuccNegSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_int(c.lhs(m.clone(), n.clone()), c.sub_nat_nat(m, n));
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn build_int_add_ofnat_succ_negsucc_value(c: &IntAddOfNatSuccNegSuccConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let lhs = c.lhs(m.clone(), n.clone());
    let mid = c.mid(m.clone(), n.clone());
    let rhs = c.sub_nat_nat(m.clone(), n.clone());

    let h_branch = Expr::app(
        Expr::app(c.int_add_ofnat_negsucc.clone(), c.succ(m.clone())),
        n.clone(),
    );
    let h_cancel = Expr::app(Expr::app(c.int_sub_nat_nat_succ_succ.clone(), m), n);
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.int_type.clone(), lhs, mid, rhs, h_branch, h_cancel],
    );

    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_ofNat_succ_negSucc` as a kernel-checked theorem.
    ///
    /// The proof is `Eq.trans (Int.add_ofNat_negSucc (succ m) n)
    /// (Int.subNatNat_succ_succ m n)`.
    pub(crate) fn register_int_add_ofnat_succ_negsucc_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_ofNat_succ_negSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_add_ofnat_negsucc_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntAddOfNatSuccNegSuccConsts::new();
        let type_ = build_int_add_ofnat_succ_negsucc_type(&c);
        let value = build_int_add_ofnat_succ_negsucc_value(&c);

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
    fn test_int_add_ofnat_succ_negsucc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_ofnat_succ_negsucc_proof()
            .expect("first registration");
        env.register_int_add_ofnat_succ_negsucc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_ofNat_succ_negSucc"))
            .expect("Int.add_ofNat_succ_negSucc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_ofnat_succ_negsucc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_ofNat_succ_negSucc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_ofNat_succ_negSucc must be Constructive, got {:?}",
            quality
        );
    }
}
