// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.ofNat_mul : ∀ m n : Nat, Eq (Int.ofNat (Nat.mul m n)) (Int.mul (Int.ofNat m) (Int.ofNat n))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is pure `@Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))`.
//!
//! # Proof sketch
//!
//! `Int.mul` is a reducible Definition (see `data_types_arithmetic.rs`):
//!
//! ```text
//! Int.mul a b := Int.rec mul_motive mul_of_nat_case mul_neg_succ_case a b
//! ```
//!
//! where the `mul_of_nat_case` step yields, after instantiating the
//! first argument to `Int.ofNat m`,
//!
//! ```text
//! λ n : Int => Int.rec inner_motive
//!                (λ n' : Nat => Int.ofNat (Nat.mul m n'))
//!                (λ n' : Nat => Int.negOfNat (Nat.mul m (Nat.succ n')))
//!                n
//! ```
//!
//! Specializing further to the second argument `Int.ofNat n`, the inner
//! `Int.rec` reduces by the `Int.ofNat` case (iota), yielding
//! `Int.ofNat (Nat.mul m n)` directly.
//!
//! Therefore `Int.mul (Int.ofNat m) (Int.ofNat n)` is **definitionally
//! equal** to `Int.ofNat (Nat.mul m n)`, and a pure
//! `@Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))` proof term type-checks
//! against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ m n : Nat, @Eq.{1} Int (Int.ofNat (Nat.mul m n))
//!                          (Int.mul (Int.ofNat m) (Int.ofNat n))
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Int`, `Int.ofNat`,
//! `Int.mul`, `Nat`, `Nat.mul`: none of these are
//! `Declaration::Axiom`.  `Int.mul` / `Nat.mul` are reducible
//! Definitions, `Int.ofNat` is a constructor.  Therefore
//! `env.axiom_deps("Int.ofNat_mul")` is empty and
//! `env.proof_quality("Int.ofNat_mul") == ProofQuality::Constructive`.
//!
//! # Impact on Rat
//!
//! `Int.ofNat_mul` appears in the axiom closure of several Rat tranche
//! theorems (e.g., `Rat.add_assoc`, `Rat.add_comm`, `Rat.mul_assoc` and
//! their Tier-B neighbors).  Demoting it from axiom to theorem removes
//! one entry from each of those `axiom_deps` sets without requiring any
//! Rat-layer work.
//!
//! Tracks issue #3551 (Rat Tier-D triage).
//!
//! Sibling proofs: `algebra_nat_add_zero_proof.rs` (#3604, pure
//! `Eq.refl`), `algebra_nat_add_succ_proof.rs` (#3551, pure `Eq.refl`),
//! `algebra_nat_mul_zero_proof.rs` (#3551, pure `Eq.refl`),
//! `order_nat_le_trans_proof.rs` (#3552, `Nat.le` induction).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Int.ofNat_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is
    /// `λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))`.  The
    /// kernel accepts this against the stated type because
    /// `Int.mul (Int.ofNat m) (Int.ofNat n)` reduces to
    /// `Int.ofNat (Nat.mul m n)` by iota on `Int.rec` (ofNat × ofNat
    /// case) + delta on the reducible `Int.mul` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`,
    ///           `Int.ofNat`, `Int.mul` (reducible Definition).
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.ofNat_mul` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.ofNat_mul` is already registered
    ///          with any declaration kind, this call returns `Ok(())`
    ///          without modification.
    pub(crate) fn register_int_ofnat_mul_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.ofNat_mul");
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
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type:
        //   ∀ m n : Nat, @Eq.{1} Int
        //                  (Int.ofNat (Nat.mul m n))
        //                  (Int.mul (Int.ofNat m) (Int.ofNat n))
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(nat_type.clone());
        let (n_id, n) = b.fresh_local(nat_type.clone());
        let nat_mul_mn = Expr::app(Expr::app(nat_mul.clone(), m.clone()), n.clone());
        let lhs = Expr::app(int_of_nat.clone(), nat_mul_mn);
        let rhs = Expr::app(
            Expr::app(int_mul.clone(), Expr::app(int_of_nat.clone(), m.clone())),
            Expr::app(int_of_nat.clone(), n.clone()),
        );
        let concl = Expr::apps(eq_const, [int_type.clone(), lhs, rhs]);
        let ty_inner = b.mk_pi(n_id, BinderInfo::Default, nat_type.clone(), concl);
        let ty_raw = b.mk_pi(m_id, BinderInfo::Default, nat_type.clone(), ty_inner);
        let type_ = b.finish(ty_raw);

        // Value: λ m n : Nat => @Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))
        let mut vb = EnvDeclBuilder::new();
        let (vm_id, vm) = vb.fresh_local(nat_type.clone());
        let (vn_id, vn) = vb.fresh_local(nat_type.clone());
        let v_nat_mul_mn = Expr::app(Expr::app(nat_mul.clone(), vm.clone()), vn.clone());
        let v_lhs = Expr::app(int_of_nat.clone(), v_nat_mul_mn);
        let refl_app = Expr::apps(eq_refl, [int_type.clone(), v_lhs]);
        let val_inner = vb.mk_lam(vn_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let val_raw = vb.mk_lam(vm_id, BinderInfo::Default, nat_type.clone(), val_inner);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier-D path).
        // Pure `@Eq.refl.{1} Int (Int.ofNat (Nat.mul m n))` relies on
        // the kernel's definitional equality reducing
        // `Int.mul (Int.ofNat m) (Int.ofNat n)` to
        // `Int.ofNat (Nat.mul m n)` via iota on `Int.rec` (ofNat case
        // on both arguments) + delta on the reducible `Int.mul`
        // definition.  No `sorry`, no self-reference.  Replaces the
        // prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_arith_lemmas`.
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

    /// Kernel accepts the `Eq.refl` proof term.  Verifies the theorem
    /// is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_int_ofnat_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_ofnat_mul_proof()
            .expect("first registration");
        env.register_int_ofnat_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.ofNat_mul"))
            .expect("Int.ofNat_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        // Proof value must be present (Theorem, not Axiom).
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a nested `λ`
    /// term whose innermost body is an `Eq.refl` application.  This
    /// guards against the axiom-wrapping masquerade (#3559) where a
    /// Theorem's value is just `@<same_name>` lifted to a term.
    #[test]
    fn test_int_ofnat_mul_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_ofnat_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.ofNat_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Top-level must be a lambda (over the outer `m : Nat` binder).
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.ofNat_mul proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
        // Second-level must also be a lambda (over the `n : Nat` binder).
        if let ExprKind::Lam(_, _, inner) = value.kind() {
            assert!(
                matches!(inner.kind(), ExprKind::Lam(..)),
                "Int.ofNat_mul proof must be a λ-λ-abstraction, got outer λ \
                 with body {:?}",
                inner.kind()
            );
        }
    }

    /// The theorem is free of domain-specific axioms — its transitive
    /// axiom closure is empty.  This is the condition for
    /// `ProofQuality::Constructive` and for inclusion in the
    /// clean-Native mathverse shard.
    #[test]
    fn test_int_ofnat_mul_axiom_closure_is_empty() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.init_int_nat_conv_lemmas()
            .expect("int/nat conversion lemmas init should succeed");
        let quality = env
            .proof_quality(&Name::from_string("Int.ofNat_mul"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.ofNat_mul must be Constructive (zero domain axioms), got {:?}",
            quality
        );
    }
}
