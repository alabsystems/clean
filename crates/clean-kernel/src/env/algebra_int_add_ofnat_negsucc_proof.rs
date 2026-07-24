// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_ofNat_negSucc :
//!    ∀ m n : Nat,
//!      Eq Int (Int.add (Int.ofNat m) (Int.negSucc n))
//!             (Int.subNatNat m (Nat.succ n))`.
//!
//! This is the checked mixed-sign branch equation for `Int.add`. It does
//! not solve `Int.add_assoc`, but it exposes the normalization step later
//! mixed-sign reassociation proofs need.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.add_ofNat_negSucc` as a kernel-checked theorem.
    ///
    /// The proof body is
    /// `λ m n : Nat => @Eq.refl.{1} Int (Int.subNatNat m (Nat.succ n))`.
    /// The kernel accepts this against the stated type because
    /// `Int.add (Int.ofNat m) (Int.negSucc n)` reduces to
    /// `Int.subNatNat m (Nat.succ n)` by delta on reducible `Int.add`
    /// and iota on its nested `Int.rec` cases.
    pub(crate) fn register_int_add_ofnat_negsucc_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_ofNat_negSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_sub_nat_nat = Expr::const_(Name::from_string("Int.subNatNat"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type:
        //   ∀ m n : Nat,
        //     @Eq.{1} Int
        //       (Int.add (Int.ofNat m) (Int.negSucc n))
        //       (Int.subNatNat m (Nat.succ n))
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(nat_type.clone());
        let (n_id, n) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(
            Expr::app(int_add.clone(), Expr::app(int_of_nat.clone(), m.clone())),
            Expr::app(int_neg_succ.clone(), n.clone()),
        );
        let rhs = Expr::app(
            Expr::app(int_sub_nat_nat.clone(), m.clone()),
            Expr::app(nat_succ.clone(), n),
        );
        let concl = Expr::apps(eq_const, [int_type.clone(), lhs, rhs]);
        let ty_inner = b.mk_pi(n_id, BinderInfo::Default, nat_type.clone(), concl);
        let ty_raw = b.mk_pi(m_id, BinderInfo::Default, nat_type.clone(), ty_inner);
        let type_ = b.finish(ty_raw);

        // Value:
        //   λ m n : Nat => @Eq.refl.{1} Int (Int.subNatNat m (Nat.succ n))
        let mut vb = EnvDeclBuilder::new();
        let (vm_id, vm) = vb.fresh_local(nat_type.clone());
        let (vn_id, vn) = vb.fresh_local(nat_type.clone());
        let v_rhs = Expr::app(Expr::app(int_sub_nat_nat, vm), Expr::app(nat_succ, vn));
        let refl_app = Expr::apps(eq_refl, [int_type, v_rhs]);
        let val_inner = vb.mk_lam(vn_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let val_raw = vb.mk_lam(vm_id, BinderInfo::Default, nat_type, val_inner);
        let value = vb.finish(val_raw);

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
    fn test_int_add_ofnat_negsucc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_ofnat_negsucc_proof()
            .expect("first registration");
        env.register_int_add_ofnat_negsucc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_ofNat_negSucc"))
            .expect("Int.add_ofNat_negSucc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_ofnat_negsucc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_ofNat_negSucc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_ofNat_negSucc must be Constructive, got {:?}",
            quality
        );
    }
}
