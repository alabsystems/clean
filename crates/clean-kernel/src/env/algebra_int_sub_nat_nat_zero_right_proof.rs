// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_zero_right : ∀ m : Nat, Eq Int (Int.subNatNat m Nat.zero) (Int.ofNat m)`.
//!
//! `Int.subNatNat` is a reducible definition by recursion on its second
//! `Nat` argument. At `Nat.zero`, it reduces directly to `Int.ofNat m`.
//! This gives the first checked normalization fact needed by mixed-sign
//! `Int.add` arithmetic without depending on `Int.add_assoc`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.subNatNat_zero_right` as a kernel-checked theorem.
    ///
    /// The proof body is `λ m : Nat => @Eq.refl.{1} Int (Int.ofNat m)`.
    /// The kernel accepts this against the stated type because
    /// `Int.subNatNat m Nat.zero` reduces to `Int.ofNat m` by delta on
    /// the reducible `Int.subNatNat` definition and the zero iota case
    /// of its underlying `Nat.rec`.
    pub(crate) fn register_int_sub_nat_nat_zero_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_zero_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_sub_nat_nat = Expr::const_(Name::from_string("Int.subNatNat"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type:
        //   ∀ m : Nat, @Eq.{1} Int (Int.subNatNat m Nat.zero) (Int.ofNat m)
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(int_sub_nat_nat.clone(), m.clone()), nat_zero);
        let rhs = Expr::app(int_of_nat.clone(), m);
        let concl = Expr::apps(eq_const, [int_type.clone(), lhs, rhs]);
        let ty_raw = b.mk_pi(m_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ m : Nat => @Eq.refl.{1} Int (Int.ofNat m)
        let mut vb = EnvDeclBuilder::new();
        let (vm_id, vm) = vb.fresh_local(nat_type.clone());
        let v_rhs = Expr::app(int_of_nat, vm);
        let refl_app = Expr::apps(eq_refl, [int_type, v_rhs]);
        let val_raw = vb.mk_lam(vm_id, BinderInfo::Default, nat_type, refl_app);
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
    fn test_int_sub_nat_nat_zero_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_zero_right_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_zero_right_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.subNatNat_zero_right"))
            .expect("Int.subNatNat_zero_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_nat_nat_zero_right_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.subNatNat_zero_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.subNatNat_zero_right must be Constructive, got {:?}",
            quality
        );
    }
}
