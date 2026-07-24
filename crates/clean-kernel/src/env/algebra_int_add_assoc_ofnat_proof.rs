// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_assoc_ofNat :
//!    ∀ m n k : Nat,
//!      Eq Int
//!        (Int.add (Int.add (Int.ofNat m) (Int.ofNat n)) (Int.ofNat k))
//!        (Int.add (Int.ofNat m) (Int.add (Int.ofNat n) (Int.ofNat k)))`.
//!
//! This closes the all-positive branch of the remaining `Int.add_assoc`
//! case split by lifting checked `Nat.add_assoc` through `Int.ofNat`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocOfNatConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    eq_const: Expr,
    congr_arg: Expr,
    nat_add_assoc: Expr,
}

impl IntAddAssocOfNatConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_assoc: Expr::const_(Name::from_string("Nat.add_assoc"), vec![]),
        }
    }

    fn nat_add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), lhs), rhs)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn lhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(self.add_int(self.of_nat(m), self.of_nat(n)), self.of_nat(k))
    }

    fn rhs(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.add_int(self.of_nat(m), self.add_int(self.of_nat(n), self.of_nat(k)))
    }

    fn lhs_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.nat_add(self.nat_add(m, n), k)
    }

    fn rhs_index(&self, m: Expr, n: Expr, k: Expr) -> Expr {
        self.nat_add(m, self.nat_add(n, k))
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_ofnat_type(c: &IntAddAssocOfNatConsts) -> Expr {
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

fn build_int_add_assoc_ofnat_value(c: &IntAddAssocOfNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    let lhs_index = c.lhs_index(m.clone(), n.clone(), k.clone());
    let rhs_index = c.rhs_index(m.clone(), n.clone(), k.clone());
    let h_nat = Expr::app(
        Expr::app(Expr::app(c.nat_add_assoc.clone(), m.clone()), n.clone()),
        k.clone(),
    );
    let proof = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            lhs_index,
            rhs_index,
            c.int_of_nat.clone(),
            h_nat,
        ],
    );

    let val_raw = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val_raw = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc_ofNat` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_ofnat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_assoc_ofNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_assoc_proof()?;

        let c = IntAddAssocOfNatConsts::new();
        let type_ = build_int_add_assoc_ofnat_type(&c);
        let value = build_int_add_assoc_ofnat_value(&c);

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
    fn test_int_add_assoc_ofnat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_ofnat_proof()
            .expect("first registration");
        env.register_int_add_assoc_ofnat_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc_ofNat"))
            .expect("Int.add_assoc_ofNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_ofnat_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc_ofNat"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc_ofNat must be Constructive, got {:?}",
            quality
        );
    }
}
