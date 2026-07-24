// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.ofNat_zero_le : ∀ n : Nat,
//!    Int.le (Int.ofNat Nat.zero) (Int.ofNat n)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)         -- reducible Definition
//! Int.sub a b := Int.add a (Int.neg b)           -- reducible Definition
//! Int.neg (Int.ofNat 0) ≡ Int.ofNat 0            -- by Int.neg / Int.negOfNat
//! Int.add (Int.ofNat n) (Int.ofNat 0) ≡ Int.ofNat (Nat.add n 0) ≡ Int.ofNat n
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! So the goal `Int.le (Int.ofNat 0) (Int.ofNat n)` delta/iota-reduces to
//! `Int.NonNeg (Int.sub (Int.ofNat n) (Int.ofNat 0))` ≡
//! `Int.NonNeg (Int.ofNat n)`.
//!
//! # Proof sketch
//!
//! The canonical constructor `@Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)`
//! inhabits the goal directly: the subtraction `(Int.ofNat n) - (Int.ofNat 0)`
//! computes to `Int.ofNat n` by kernel reduction (`Nat.add n Nat.zero ≡ n`),
//! so no transport is required.
//!
//! ```text
//! λ (n : Nat) => @Int.NonNeg.mk n
//!   : Int.NonNeg (Int.ofNat n)   ≡   Int.le (Int.ofNat 0) (Int.ofNat n)
//! ```
//!
//! # Axiom closure
//!
//! Depends only on the inductive constructor `Int.NonNeg.mk` and the reducible
//! `Int.le` / `Int.sub` definitions. None is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.ofNat_zero_le")` is empty and
//! `env.proof_quality("Int.ofNat_zero_le") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntOfNatZeroLeConsts {
    nat_type: Expr,
    int_le: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nonneg_mk: Expr,
}

impl IntOfNatZeroLeConsts {
    fn new() -> Self {
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }
}

/// Build `∀ n : Nat, Int.le (Int.ofNat Nat.zero) (Int.ofNat n)`.
fn build_type(c: &IntOfNatZeroLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let int_zero = c.of_nat(c.nat_zero.clone());
    let concl = c.le(int_zero, c.of_nat(n));
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(r)
}

/// Body: `λ (n : Nat) => @Int.NonNeg.mk n`.
fn build_value(c: &IntOfNatZeroLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    // @Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)
    let witness = Expr::app(c.nonneg_mk.clone(), n);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), witness);
    b.finish(val)
}

impl Environment {
    /// Register `Int.ofNat_zero_le` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.sub`, `Int.ofNat`.
    /// ENSURES: On success, `Int.ofNat_zero_le` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.ofNat_zero_le` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without modification.
    pub(crate) fn register_int_ofnat_zero_le_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.ofNat_zero_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;

        let c = IntOfNatZeroLeConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. The canonical constructor
        // `@Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)` inhabits the goal
        // `Int.le (Int.ofNat 0) (Int.ofNat n)` ≡
        // `Int.NonNeg (Int.sub (Int.ofNat n) (Int.ofNat 0))`, since the
        // subtraction kernel-reduces to `Int.ofNat n`
        // (`Int.neg (Int.ofNat 0) ≡ Int.ofNat 0` and `Nat.add n 0 ≡ n`). No
        // `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    use crate::env::ConstantKind;

    #[test]
    fn test_int_ofnat_zero_le_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_ofnat_zero_le_proof()
            .expect("first registration");
        env.register_int_ofnat_zero_le_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.ofNat_zero_le"))
            .expect("Int.ofNat_zero_le should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_ofnat_zero_le_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_ofnat_zero_le_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.ofNat_zero_le"))
            .expect("Int.ofNat_zero_le is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.ofNat_zero_le must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_ofnat_zero_le_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_ofnat_zero_le_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.ofNat_zero_le"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.ofNat_zero_le must be Constructive, got {:?}",
            quality
        );
    }
}
