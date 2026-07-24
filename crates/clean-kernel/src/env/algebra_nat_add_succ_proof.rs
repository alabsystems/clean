// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.add_succ : ∀ a b : Nat, Eq (Nat.add a (Nat.succ b)) (Nat.succ (Nat.add a b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof term
//! is pure `@Eq.refl.{1} Nat (Nat.succ (Nat.add a b))`.
//!
//! # Proof sketch
//!
//! `Nat.add` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.add m n := Nat.rec m (λ _ ih => Nat.succ ih) n
//! ```
//!
//! `Nat.add` recurses on its SECOND argument. Specializing to
//! `n = Nat.succ b`, the `Nat.rec` major reduces by the `Nat.succ` case
//! (iota), yielding
//!
//! ```text
//! (λ _ ih => Nat.succ ih) b (Nat.rec a (λ _ ih => Nat.succ ih) b)
//!   β→ Nat.succ (Nat.rec a (λ _ ih => Nat.succ ih) b)
//!   δ← Nat.succ (Nat.add a b)
//! ```
//!
//! Therefore `Nat.add a (Nat.succ b)` is **definitionally equal** to
//! `Nat.succ (Nat.add a b)`, and a pure
//! `@Eq.refl.{1} Nat (Nat.succ (Nat.add a b))` proof term type-checks
//! against the stated type.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ (a b : Nat) => @Eq.refl.{1} Nat (Nat.succ (Nat.add a b))
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ a b : Nat, @Eq.{1} Nat (Nat.add a (Nat.succ b)) (Nat.succ (Nat.add a b))
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.add`, `Nat.succ`:
//! none of these are `Declaration::Axiom`. `Eq.refl` is a kernel-level
//! `Declaration::Theorem`, `Nat` is an inductive type, `Nat.add` is a
//! reducible `Declaration::Definition`, `Nat.succ` is a constructor.
//!
//! Therefore `env.axiom_deps("Nat.add_succ")` is empty and
//! `env.proof_quality("Nat.add_succ") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604. Sibling proofs:
//! - `algebra_nat_add_zero_proof.rs` (Nat.add_zero via iota zero-case).
//! - `algebra_nat_zero_add_proof.rs` (Nat.zero_add via Nat.rec induction).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.add_succ` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is
    /// `λ (a b : Nat) => @Eq.refl.{1} Nat (Nat.succ (Nat.add a b))`. The
    /// kernel accepts this against the stated type because
    /// `Nat.add a (Nat.succ b)` reduces to `Nat.succ (Nat.add a b)` by iota
    /// on `Nat.rec` (succ case) + delta on the reducible `Nat.add` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`,
    ///           `Nat.add` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.add_succ` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.add_succ` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_add_succ_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type: ∀ a b : Nat, @Eq.{1} Nat (Nat.add a (Nat.succ b)) (Nat.succ (Nat.add a b))
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let (b_id, bv) = b.fresh_local(nat_type.clone());
        let succ_b = Expr::app(nat_succ.clone(), bv.clone());
        let lhs = Expr::app(Expr::app(nat_add.clone(), a.clone()), succ_b);
        let ab = Expr::app(Expr::app(nat_add.clone(), a.clone()), bv.clone());
        let rhs = Expr::app(nat_succ.clone(), ab);
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, rhs]);
        let ty_raw = b.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), concl);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), ty_raw);
        let type_ = b.finish(ty_raw);

        // Value: λ (a b : Nat) => @Eq.refl.{1} Nat (Nat.succ (Nat.add a b))
        //
        // We provide the RHS (which is the normal form) as the Eq.refl
        // argument; the kernel's def_eq check unfolds the LHS to this form
        // via delta+iota+beta on Nat.add.
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let (vb_id, vbv) = vb.fresh_local(nat_type.clone());
        let v_ab = Expr::app(Expr::app(nat_add.clone(), va.clone()), vbv.clone());
        let v_succ_ab = Expr::app(nat_succ.clone(), v_ab);
        let refl_app = Expr::apps(eq_refl, [nat_type.clone(), v_succ_ab]);
        let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, nat_type.clone(), refl_app);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), val_raw);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Pure
        // `@Eq.refl.{1} Nat (Nat.succ (Nat.add a b))` relies on the kernel's
        // definitional equality reducing `Nat.add a (Nat.succ b)` to
        // `Nat.succ (Nat.add a b)` via iota on `Nat.rec` (succ case) + delta
        // on the reducible `Nat.add` definition + beta. No `sorry`, no
        // self-reference. Replaces the prior `Declaration::Axiom` in
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
    fn test_nat_add_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_add_succ_proof()
            .expect("first registration");
        env.register_nat_add_succ_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.add_succ"))
            .expect("Nat.add_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body is an `Eq.refl` application. Guards against axiom-wrapping
    /// masquerade (#3559).
    #[test]
    fn test_nat_add_succ_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_add_succ_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.add_succ"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.add_succ proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }
}
