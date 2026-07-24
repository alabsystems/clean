// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.mul_one : ∀ a : Nat, Eq (Nat.mul a (Nat.succ Nat.zero)) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is `λ a : Nat => Nat.zero_add a`.
//!
//! # Proof sketch
//!
//! `Nat.mul` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n
//! ```
//!
//! (recurses on the SECOND argument.) Specializing to `n = Nat.succ Nat.zero`,
//! the kernel reduces `Nat.mul a (Nat.succ Nat.zero)` as follows:
//!
//! ```text
//! Nat.mul a (Nat.succ Nat.zero)
//!   δ→ Nat.rec Nat.zero (λ _ ih => Nat.add ih a) (Nat.succ Nat.zero)
//!   ι→ (λ _ ih => Nat.add ih a) Nat.zero (Nat.rec Nat.zero (λ _ ih => Nat.add ih a) Nat.zero)
//!   β→ Nat.add (Nat.rec Nat.zero (λ _ ih => Nat.add ih a) Nat.zero) a
//!   ι→ Nat.add Nat.zero a
//! ```
//!
//! Therefore `Nat.mul a (Nat.succ Nat.zero)` is **definitionally equal** to
//! `Nat.add Nat.zero a`, and the proof term `Nat.zero_add a`, which has type
//! `Eq Nat (Nat.add Nat.zero a) a`, type-checks against the stated type
//! `Eq Nat (Nat.mul a (Nat.succ Nat.zero)) a`.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a : Nat => Nat.zero_add a
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ a : Nat, @Eq.{1} Nat (Nat.mul a (Nat.succ Nat.zero)) a
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.mul`,
//! `Nat.zero_add`. `Nat.zero_add` is a `Declaration::Theorem` (constructive
//! #3604), all others are constructors / reducible Definitions / inductives.
//! Therefore `env.axiom_deps("Nat.mul_one")` is empty and
//! `env.proof_quality("Nat.mul_one") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Batch 5 Nat axiom demotion). Sibling proofs:
//! - `algebra_nat_mul_zero_proof.rs` (#3551, pure `Eq.refl` on Nat.mul_zero).
//! - `algebra_nat_zero_add_proof.rs` (#3604, dependency — Nat.rec induction).
//! - `algebra_nat_mul_succ_proof.rs` (#3551, companion — uses Nat.add_comm).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.mul_one` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a : Nat => Nat.zero_add a`. The kernel accepts
    /// this against the stated type because `Nat.mul a (Nat.succ Nat.zero)`
    /// reduces to `Nat.add Nat.zero a` by iota+beta on `Nat.rec` (succ case
    /// unfolding to `Nat.add (Nat.rec Nat.zero minor Nat.zero) a`) + iota
    /// (zero case reducing the inner `Nat.rec` to `Nat.zero`) + delta on
    /// the reducible `Nat.mul` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`.
    /// REQUIRES: `Nat.zero_add` is registered as a `Declaration::Theorem`
    ///           (constructive proof — see `register_nat_zero_add_proof`).
    /// ENSURES: On success, `Nat.mul_one` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.mul_one` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_mul_one_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_add_proof()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ, nat_zero);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1]);
        let nat_zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);

        // Type: ∀ a : Nat, @Eq.{1} Nat (Nat.mul a (Nat.succ Nat.zero)) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(nat_mul, a.clone()), nat_one);
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, a.clone()]);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ a : Nat => Nat.zero_add a
        //
        // `Nat.zero_add a : Eq (Nat.add Nat.zero a) a`. The kernel's defn-eq
        // check accepts this against `Eq (Nat.mul a (Nat.succ Nat.zero)) a`
        // because both `Nat.mul a (Nat.succ Nat.zero)` and `Nat.add Nat.zero a`
        // share the same normal form (chain of iota/beta/delta reductions).
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let zero_add_a = Expr::app(nat_zero_add, va);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), zero_add_a);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Batch 5).
        // `Nat.zero_add a` has type `Eq (Nat.add Nat.zero a) a`; kernel
        // def-eq reduces `Nat.mul a (Nat.succ Nat.zero)` to `Nat.add Nat.zero a`
        // via iota (succ-case on Nat.rec) + beta + iota (zero-case on inner
        // Nat.rec) + delta on reducible Nat.mul. No `sorry`, no
        // self-reference, no domain-axiom dependency (Nat.zero_add itself is
        // constructive #3604). Replaces the prior `Declaration::Axiom` in
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

    /// Kernel accepts the `Nat.zero_add`-application proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_nat_mul_one_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_mul_one_proof()
            .expect("first registration");
        env.register_nat_mul_one_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_one"))
            .expect("Nat.mul_one should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body is a `Nat.zero_add` application. Guards against axiom-wrapping
    /// masquerade (#3559).
    #[test]
    fn test_nat_mul_one_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_one_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_one"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.mul_one proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The theorem has empty axiom closure. `Nat.zero_add` is constructive
    /// (#3604), so its transitive axiom deps are empty, and `Nat.mul_one`
    /// inherits that property.
    #[test]
    fn test_nat_mul_one_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_mul_one_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.mul_one"))
            .expect("Nat.mul_one is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.mul_one must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
