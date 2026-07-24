// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.add_zero : ∀ a : Nat, Eq (Nat.add a Nat.zero) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof term
//! is pure `@Eq.refl.{1} Nat a`.
//!
//! # Proof sketch
//!
//! `Nat.add` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n
//! ```
//!
//! Specializing to `n = Nat.zero`, the `Nat.rec` major reduces by the
//! `Nat.zero` case (iota), yielding `m` directly. Therefore
//! `Nat.add a Nat.zero` is **definitionally equal** to `a`, and a pure
//! `@Eq.refl.{1} Nat a` proof term type-checks against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a : Nat => @Eq.refl.{1} Nat a
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ a : Nat, @Eq.{1} Nat (Nat.add a Nat.zero) a
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.add`, `Nat.zero`:
//! none of these are `Declaration::Axiom`. `Eq.refl` is a kernel-level
//! `Declaration::Theorem`, `Nat` is an inductive type, `Nat.add` is a
//! reducible `Declaration::Definition`, `Nat.zero` is a constructor.
//!
//! Therefore `env.axiom_deps("Nat.add_zero")` is empty and
//! `env.proof_quality("Nat.add_zero") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604. Sibling proofs: `order_nat_le_trans_proof.rs` (#3552,
//! `Nat.le` induction) and `algebra_rat_tranche_b_proofs` (#3581, pure
//! `Eq.refl` on Rat).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.add_zero` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a : Nat => @Eq.refl.{1} Nat a`. The kernel
    /// accepts this against the stated type because `Nat.add a Nat.zero`
    /// reduces to `a` by iota on `Nat.rec` + delta on `Nat.add`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.add` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.add_zero` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.add_zero` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_add_zero_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type: ∀ a : Nat, @Eq.{1} Nat (Nat.add a Nat.zero) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(nat_add, a.clone()), nat_zero);
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, a.clone()]);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ a : Nat => @Eq.refl.{1} Nat a
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let refl_app = Expr::apps(eq_refl, [nat_type.clone(), va]);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Pure
        // `@Eq.refl.{1} Nat a` relies on the kernel's definitional equality
        // reducing `Nat.add a Nat.zero` to `a` via iota on `Nat.rec` (zero
        // case) + delta on the reducible `Nat.add` definition. No `sorry`,
        // no self-reference. Replaces the prior `Declaration::Axiom` in
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

    /// Kernel accepts the `Eq.refl` proof term. Verifies the theorem is
    /// registered as a Theorem (not Axiom) and idempotent re-invocation is
    /// a no-op.
    #[test]
    fn test_nat_add_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_zero_proof()
            .expect("first registration");
        env.register_nat_add_zero_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_zero"))
            .expect("Nat.add_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        // Proof value must be present (Theorem, not Axiom).
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body is an `Eq.refl` application. This guards against the axiom-
    /// wrapping masquerade (#3559) where a Theorem's value is just
    /// `@<same_name>` lifted to a term.
    #[test]
    fn test_nat_add_zero_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_zero_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_zero"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Top-level must be a lambda (over the `a : Nat` binder).
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.add_zero proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }
}
