// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.mul_zero : ∀ a : Nat, Eq (Nat.mul a Nat.zero) Nat.zero`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is pure `@Eq.refl.{1} Nat Nat.zero`.
//!
//! # Proof sketch
//!
//! `Nat.mul` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n
//! ```
//!
//! i.e. recursion on the *second* argument with `Nat.zero` as the base
//! value.  Specializing to `n = Nat.zero`, the `Nat.rec` major reduces
//! by the `Nat.zero` case (iota), yielding `Nat.zero` directly.
//!
//! Therefore `Nat.mul a Nat.zero` is **definitionally equal** to
//! `Nat.zero`, and a pure `@Eq.refl.{1} Nat Nat.zero` proof term
//! type-checks against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a : Nat => @Eq.refl.{1} Nat Nat.zero
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ a : Nat, @Eq.{1} Nat (Nat.mul a Nat.zero) Nat.zero
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.zero`: none of
//! these are `Declaration::Axiom`.  Therefore
//! `env.axiom_deps("Nat.mul_zero")` is empty and
//! `env.proof_quality("Nat.mul_zero") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Rat Tier-D triage — demoting the symmetric
//! `Nat.mul_zero` / `Nat.mul_one` / etc. pure-refl Nat axioms feeds
//! the Int / Rat induction ladder).
//!
//! Sibling proofs: `algebra_nat_add_succ_proof.rs` (#3551, pure
//! `Eq.refl` — same pattern), `algebra_nat_add_zero_proof.rs` (#3604,
//! pure `Eq.refl`), `order_nat_le_trans_proof.rs` (#3552, `Nat.le`
//! induction), `algebra_rat_tranche_b_proofs` (#3581, pure `Eq.refl` on
//! Rat).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.mul_zero` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a : Nat => @Eq.refl.{1} Nat Nat.zero`.  The
    /// kernel accepts this against the stated type because
    /// `Nat.mul a Nat.zero` reduces to `Nat.zero` by iota on `Nat.rec`
    /// (zero case) + delta on the reducible `Nat.mul` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.mul` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.mul_zero` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.mul_zero` is already registered
    ///          with any declaration kind, this call returns `Ok(())`
    ///          without modification.
    pub(crate) fn register_nat_mul_zero_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type: ∀ a : Nat, @Eq.{1} Nat (Nat.mul a Nat.zero) Nat.zero
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(nat_mul.clone(), a.clone()), nat_zero.clone());
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, nat_zero.clone()]);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ a : Nat => @Eq.refl.{1} Nat Nat.zero
        let mut vb = EnvDeclBuilder::new();
        let (va_id, _va) = vb.fresh_local(nat_type.clone());
        let refl_app = Expr::apps(eq_refl, [nat_type.clone(), nat_zero.clone()]);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier-D path).
        // Pure `@Eq.refl.{1} Nat Nat.zero` relies on the kernel's
        // definitional equality reducing `Nat.mul a Nat.zero` to
        // `Nat.zero` via iota on `Nat.rec` (zero case) + delta on the
        // reducible `Nat.mul` definition.  No `sorry`, no
        // self-reference.  Replaces the prior `Declaration::Axiom` in
        // `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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
    fn test_nat_mul_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_mul_zero_proof()
            .expect("first registration");
        env.register_nat_mul_zero_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_zero"))
            .expect("Nat.mul_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        // Proof value must be present (Theorem, not Axiom).
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term
    /// whose body is an `Eq.refl` application on `Nat.zero`.  This
    /// guards against the axiom-wrapping masquerade (#3559) where a
    /// Theorem's value is just `@<same_name>` lifted to a term.
    #[test]
    fn test_nat_mul_zero_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_zero_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_zero"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Top-level must be a lambda (over the `a : Nat` binder).
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.mul_zero proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The theorem is free of domain-specific axioms — its transitive
    /// axiom closure is empty.  This is the condition for
    /// `ProofQuality::Constructive` and for inclusion in the
    /// clean-Native mathverse shard.
    #[test]
    fn test_nat_mul_zero_axiom_closure_is_empty() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.init_nat_arith_lemmas()
            .expect("nat arith lemmas init should succeed");
        let quality = env
            .proof_quality(&Name::from_string("Nat.mul_zero"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.mul_zero must be Constructive (zero domain axioms), got {:?}",
            quality
        );
    }
}
