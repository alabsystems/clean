// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.succ_eq_add_one : ∀ n : Nat, Eq Nat (Nat.succ n) (Nat.add n (Nat.succ Nat.zero))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs::init_int_nat_conv_lemmas` with a
//! `Declaration::Theorem` whose proof term is pure
//! `@Eq.refl.{1} Nat (Nat.succ n)`.
//!
//! # Proof sketch
//!
//! `Nat.add` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n
//! ```
//!
//! Specializing to `Nat.add n (Nat.succ Nat.zero)`:
//! * outer `Nat.rec` on the argument `Nat.succ Nat.zero` reduces by
//!   the `Nat.succ` case (iota), yielding
//!   `(λ _ ih => Nat.succ ih) Nat.zero (Nat.rec n succ_br Nat.zero)`
//!   which beta-reduces to `Nat.succ (Nat.rec n succ_br Nat.zero)`.
//! * The inner `Nat.rec n succ_br Nat.zero` reduces by the `Nat.zero`
//!   case (iota) to `n`.
//!
//! Therefore `Nat.add n (Nat.succ Nat.zero)` is **definitionally equal**
//! to `Nat.succ n`, and a pure `@Eq.refl.{1} Nat (Nat.succ n)` proof
//! term type-checks against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ n : Nat => @Eq.refl.{1} Nat (Nat.succ n)
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ n : Nat, @Eq.{1} Nat (Nat.succ n) (Nat.add n (Nat.succ Nat.zero))
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.succ`,
//! `Nat.zero`, `Nat.add`: none of these are `Declaration::Axiom`.
//! `Nat.add` is a reducible `Declaration::Definition`; `Nat.succ` and
//! `Nat.zero` are constructors; `Eq.refl` is a constructor. Therefore
//! `env.axiom_deps("Nat.succ_eq_add_one")` is empty and
//! `env.proof_quality("Nat.succ_eq_add_one") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Int batch). Sibling proofs:
//! `algebra_nat_add_zero_proof.rs`, `algebra_nat_add_succ_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.succ_eq_add_one` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// The proof body is `λ n : Nat => @Eq.refl.{1} Nat (Nat.succ n)`.
    /// The kernel accepts this against the stated type because
    /// `Nat.add n (Nat.succ Nat.zero)` reduces to `Nat.succ n` by iota
    /// on `Nat.rec` (succ case with zero inside — two iota reductions)
    /// + delta on the reducible `Nat.add` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.succ_eq_add_one` is a
    ///          `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.succ_eq_add_one` is already
    ///          registered with any declaration kind, this call returns
    ///          `Ok(())` without modification.
    pub(crate) fn register_nat_succ_eq_add_one_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_eq_add_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());

        // Type: ∀ n : Nat, @Eq.{1} Nat (Nat.succ n)
        //                              (Nat.add n (Nat.succ Nat.zero))
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(nat_succ.clone(), n.clone());
        let rhs = Expr::app(Expr::app(nat_add.clone(), n.clone()), nat_one.clone());
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, rhs]);
        let ty_raw = b.mk_pi(n_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ n : Nat => @Eq.refl.{1} Nat (Nat.succ n)
        let mut vb = EnvDeclBuilder::new();
        let (vn_id, vn) = vb.fresh_local(nat_type.clone());
        let v_lhs = Expr::app(nat_succ.clone(), vn);
        let refl_app = Expr::apps(eq_refl, [nat_type.clone(), v_lhs]);
        let val_raw = vb.mk_lam(vn_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Int
        // batch). Pure `@Eq.refl.{1} Nat (Nat.succ n)` relies on the
        // kernel's definitional equality reducing
        // `Nat.add n (Nat.succ Nat.zero)` to `Nat.succ n` via iota on
        // `Nat.rec` (succ case + zero case) + delta on the reducible
        // `Nat.add` definition + beta. No `sorry`, no self-reference.
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
    fn test_nat_succ_eq_add_one_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_succ_eq_add_one_proof()
            .expect("first registration");
        env.register_nat_succ_eq_add_one_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.succ_eq_add_one"))
            .expect("Nat.succ_eq_add_one should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term
    /// whose body is an `Eq.refl` application. Guards against the
    /// axiom-wrapping masquerade (#3559) where a Theorem's value is
    /// just `@<same_name>` lifted to a term.
    #[test]
    fn test_nat_succ_eq_add_one_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_succ_eq_add_one_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_eq_add_one"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.succ_eq_add_one proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The theorem is free of domain-specific axioms — its transitive
    /// axiom closure is empty. This is the condition for
    /// `ProofQuality::Constructive` and for inclusion in the
    /// clean-Native mathverse shard.
    #[test]
    fn test_nat_succ_eq_add_one_axiom_closure_is_empty() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.init_int_nat_conv_lemmas()
            .expect("int/nat conversion lemmas init should succeed");
        let quality = env
            .proof_quality(&Name::from_string("Nat.succ_eq_add_one"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Nat.succ_eq_add_one must be Constructive (zero domain axioms), got {:?}",
            quality
        );
    }
}
