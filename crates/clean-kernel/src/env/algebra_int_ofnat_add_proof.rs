// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.ofNat_add : ∀ m n : Nat, Eq Int (Int.ofNat (Nat.add m n)) (Int.add (Int.ofNat m) (Int.ofNat n))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs::init_int_nat_conv_lemmas` with a
//! `Declaration::Theorem` whose proof term is pure
//! `@Eq.refl.{1} Int (Int.ofNat (Nat.add m n))`.
//!
//! # Proof sketch
//!
//! `Int.add` is a reducible Definition (see `data_types_arithmetic.rs`)
//! implemented as a 4-case split via two nested `Int.rec`:
//!
//! ```text
//! Int.add (ofNat m)  (ofNat n)   = ofNat (Nat.add m n)
//! Int.add (ofNat m)  (negSucc n) = Int.subNatNat m (Nat.succ n)
//! Int.add (negSucc m) (ofNat n)  = Int.subNatNat n (Nat.succ m)
//! Int.add (negSucc m) (negSucc n) = Int.negSucc (Nat.succ (Nat.add m n))
//! ```
//!
//! Specializing both arguments to `Int.ofNat _`, the outer `Int.rec`
//! reduces by the `Int.ofNat` case (iota), then the inner `Int.rec`
//! also reduces by the `Int.ofNat` case (iota), yielding
//! `Int.ofNat (Nat.add m n)` directly.
//!
//! Therefore `Int.add (Int.ofNat m) (Int.ofNat n)` is **definitionally
//! equal** to `Int.ofNat (Nat.add m n)`, and a pure
//! `@Eq.refl.{1} Int (Int.ofNat (Nat.add m n))` proof term type-checks
//! against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.add m n))
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ m n : Nat, @Eq.{1} Int (Int.ofNat (Nat.add m n))
//!                          (Int.add (Int.ofNat m) (Int.ofNat n))
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Int`, `Int.ofNat`,
//! `Int.add`, `Nat`, `Nat.add`: none of these are
//! `Declaration::Axiom`. `Int.add` / `Nat.add` are reducible
//! Definitions, `Int.ofNat` is a constructor. Therefore
//! `env.axiom_deps("Int.ofNat_add")` is empty and
//! `env.proof_quality("Int.ofNat_add") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Int batch). Sibling proofs:
//! `algebra_int_ofnat_mul_proof.rs` (same proof shape, multiplicative),
//! `algebra_nat_add_zero_proof.rs` (same refl pattern, Nat side).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.ofNat_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is
    /// `λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.add m n))`.
    /// The kernel accepts this against the stated type because
    /// `Int.add (Int.ofNat m) (Int.ofNat n)` reduces to
    /// `Int.ofNat (Nat.add m n)` by iota on `Int.rec` (ofNat case on
    /// both arguments) + delta on the reducible `Int.add` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`,
    ///           `Int.ofNat`, `Int.add` (reducible Definition).
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.add`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.ofNat_add` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.ofNat_add` is already registered
    ///          with any declaration kind, this call returns `Ok(())`
    ///          without modification.
    pub(crate) fn register_int_ofnat_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.ofNat_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type:
        //   ∀ m n : Nat, @Eq.{1} Int
        //                  (Int.ofNat (Nat.add m n))
        //                  (Int.add (Int.ofNat m) (Int.ofNat n))
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(nat_type.clone());
        let (n_id, n) = b.fresh_local(nat_type.clone());
        let nat_add_mn = Expr::app(Expr::app(nat_add.clone(), m.clone()), n.clone());
        let lhs = Expr::app(int_of_nat.clone(), nat_add_mn);
        let rhs = Expr::app(
            Expr::app(int_add.clone(), Expr::app(int_of_nat.clone(), m.clone())),
            Expr::app(int_of_nat.clone(), n.clone()),
        );
        let concl = Expr::apps(eq_const, [int_type.clone(), lhs, rhs]);
        let ty_inner = b.mk_pi(n_id, BinderInfo::Default, nat_type.clone(), concl);
        let ty_raw = b.mk_pi(m_id, BinderInfo::Default, nat_type.clone(), ty_inner);
        let type_ = b.finish(ty_raw);

        // Value: λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.add m n))
        let mut vb = EnvDeclBuilder::new();
        let (vm_id, vm) = vb.fresh_local(nat_type.clone());
        let (vn_id, vn) = vb.fresh_local(nat_type.clone());
        let v_nat_add_mn = Expr::app(Expr::app(nat_add.clone(), vm.clone()), vn.clone());
        let v_lhs = Expr::app(int_of_nat.clone(), v_nat_add_mn);
        let refl_app = Expr::apps(eq_refl, [int_type.clone(), v_lhs]);
        let val_inner = vb.mk_lam(vn_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let val_raw = vb.mk_lam(vm_id, BinderInfo::Default, nat_type.clone(), val_inner);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Int
        // batch). Pure `@Eq.refl.{1} Int (Int.ofNat (Nat.add m n))`
        // relies on the kernel's definitional equality reducing
        // `Int.add (Int.ofNat m) (Int.ofNat n)` to
        // `Int.ofNat (Nat.add m n)` via iota on `Int.rec` (ofNat case
        // on both arguments) + delta on the reducible `Int.add`
        // definition. No `sorry`, no self-reference. Replaces the
        // prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_nat_conv_lemmas`.
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

    /// Kernel accepts the `Eq.refl` proof term. Verifies the theorem is
    /// registered as a Theorem (not Axiom) and idempotent re-invocation
    /// is a no-op.
    #[test]
    fn test_int_ofnat_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_ofnat_add_proof()
            .expect("first registration");
        env.register_int_ofnat_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.ofNat_add"))
            .expect("Int.ofNat_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a nested `λ`
    /// term whose innermost body is an `Eq.refl` application. Guards
    /// against the axiom-wrapping masquerade (#3559) where a Theorem's
    /// value is just `@<same_name>` lifted to a term.
    #[test]
    fn test_int_ofnat_add_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_ofnat_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.ofNat_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Top-level must be a lambda (over the outer `m : Nat` binder).
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.ofNat_add proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
        // Second-level must also be a lambda (over the `n : Nat` binder).
        if let ExprKind::Lam(_, _, inner) = value.kind() {
            assert!(
                matches!(inner.kind(), ExprKind::Lam(..)),
                "Int.ofNat_add proof must be a λ-λ-abstraction, got outer λ \
                 with body {:?}",
                inner.kind()
            );
        }
    }

    /// The theorem is free of domain-specific axioms — its transitive
    /// axiom closure is empty. This is the condition for
    /// `ProofQuality::Constructive` and for inclusion in the
    /// clean-Native mathverse shard.
    #[test]
    fn test_int_ofnat_add_axiom_closure_is_empty() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.init_int_nat_conv_lemmas()
            .expect("int/nat conversion lemmas init should succeed");
        let quality = env
            .proof_quality(&Name::from_string("Int.ofNat_add"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.ofNat_add must be Constructive (zero domain axioms), got {:?}",
            quality
        );
    }
}
