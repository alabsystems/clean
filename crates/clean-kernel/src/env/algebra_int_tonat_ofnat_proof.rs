// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.toNat_ofNat : ∀ n : Nat, Eq Nat (Int.toNat (Int.ofNat n)) n`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs::init_int_nat_conv_lemmas` with a
//! `Declaration::Theorem` whose proof term is pure
//! `@Eq.refl.{1} Nat n`.
//!
//! # Proof sketch
//!
//! `Int.toNat` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Int.toNat i := Int.rec (λ _ : Int => Nat)
//!                        (λ n : Nat => n)           -- ofNat case
//!                        (λ _ : Nat => Nat.zero)    -- negSucc case
//!                        i
//! ```
//!
//! Specializing to `i = Int.ofNat n`, the outer `Int.rec` reduces by
//! the `Int.ofNat` case (iota), yielding `(λ n' : Nat => n') n` which
//! beta-reduces to `n` directly. Therefore `Int.toNat (Int.ofNat n)` is
//! **definitionally equal** to `n`, and a pure `@Eq.refl.{1} Nat n`
//! proof term type-checks against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ n : Nat => @Eq.refl.{1} Nat n
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ n : Nat, @Eq.{1} Nat (Int.toNat (Int.ofNat n)) n
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Int.toNat`,
//! `Int.ofNat`: none of these are `Declaration::Axiom`. `Eq.refl` is a
//! kernel-level constructor, `Nat` and `Int` are inductive types,
//! `Int.toNat` is a reducible `Declaration::Definition`, `Int.ofNat` is
//! a constructor.
//!
//! Therefore `env.axiom_deps("Int.toNat_ofNat")` is empty and
//! `env.proof_quality("Int.toNat_ofNat") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Int batch). Sibling proofs:
//! `algebra_int_ofnat_mul_proof.rs`, `algebra_nat_add_zero_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.toNat_ofNat` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ n : Nat => @Eq.refl.{1} Nat n`. The kernel
    /// accepts this against the stated type because
    /// `Int.toNat (Int.ofNat n)` reduces to `n` by iota on `Int.rec`
    /// (ofNat case) + delta on the reducible `Int.toNat` definition +
    /// beta on the resulting `(λ n' => n') n` application.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`,
    ///           `Int.ofNat`, `Int.toNat` (reducible Definition).
    /// REQUIRES: `self.init_nat()` has registered `Nat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.toNat_ofNat` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.toNat_ofNat` is already registered
    ///          with any declaration kind, this call returns `Ok(())`
    ///          without modification.
    pub(crate) fn register_int_tonat_ofnat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.toNat_ofNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_to_nat = Expr::const_(Name::from_string("Int.toNat"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type: ∀ n : Nat, @Eq.{1} Nat (Int.toNat (Int.ofNat n)) n
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(int_to_nat, Expr::app(int_of_nat, n.clone()));
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, n.clone()]);
        let ty_raw = b.mk_pi(n_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ n : Nat => @Eq.refl.{1} Nat n
        let mut vb = EnvDeclBuilder::new();
        let (vn_id, vn) = vb.fresh_local(nat_type.clone());
        let refl_app = Expr::apps(eq_refl, [nat_type.clone(), vn]);
        let val_raw = vb.mk_lam(vn_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Int
        // batch). Pure `@Eq.refl.{1} Nat n` relies on the kernel's
        // definitional equality reducing `Int.toNat (Int.ofNat n)` to
        // `n` via iota on `Int.rec` (ofNat case) + delta on the
        // reducible `Int.toNat` definition + beta on the resulting
        // `(λ n' => n') n` application. No `sorry`, no self-reference.
        // Replaces the prior `Declaration::Axiom` in
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
    fn test_int_tonat_ofnat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_tonat_ofnat_proof()
            .expect("first registration");
        env.register_int_tonat_ofnat_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.toNat_ofNat"))
            .expect("Int.toNat_ofNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term
    /// whose body is an `Eq.refl` application. Guards against the
    /// axiom-wrapping masquerade (#3559) where a Theorem's value is
    /// just `@<same_name>` lifted to a term.
    #[test]
    fn test_int_tonat_ofnat_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_tonat_ofnat_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.toNat_ofNat"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.toNat_ofNat proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The theorem is free of domain-specific axioms — its transitive
    /// axiom closure is empty. This is the condition for
    /// `ProofQuality::Constructive` and for inclusion in the
    /// clean-Native mathverse shard.
    #[test]
    fn test_int_tonat_ofnat_axiom_closure_is_empty() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.init_int_nat_conv_lemmas()
            .expect("int/nat conversion lemmas init should succeed");
        let quality = env
            .proof_quality(&Name::from_string("Int.toNat_ofNat"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.toNat_ofNat must be Constructive (zero domain axioms), got {:?}",
            quality
        );
    }
}
