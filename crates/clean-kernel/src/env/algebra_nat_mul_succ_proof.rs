// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.mul_succ : ∀ a b : Nat, Eq (Nat.mul a (Nat.succ b)) (Nat.add a (Nat.mul a b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is `λ a b : Nat => Nat.add_comm (Nat.mul a b) a`.
//!
//! # Proof sketch
//!
//! `Nat.mul` is a reducible Definition (see `data_types_nat.rs`):
//!
//! ```text
//! Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n
//! ```
//!
//! (recurses on the SECOND argument.) Specializing to `n = Nat.succ b`, the
//! kernel reduces `Nat.mul a (Nat.succ b)` as follows:
//!
//! ```text
//! Nat.mul a (Nat.succ b)
//!   δ→ Nat.rec Nat.zero (λ _ ih => Nat.add ih a) (Nat.succ b)
//!   ι→ (λ _ ih => Nat.add ih a) b (Nat.rec Nat.zero (λ _ ih => Nat.add ih a) b)
//!   β→ Nat.add (Nat.rec Nat.zero (λ _ ih => Nat.add ih a) b) a
//!   δ← Nat.add (Nat.mul a b) a
//! ```
//!
//! Therefore `Nat.mul a (Nat.succ b)` is **definitionally equal** to
//! `Nat.add (Nat.mul a b) a`. The stated RHS is `Nat.add a (Nat.mul a b)`,
//! so we need to witness `Eq (Nat.add (Nat.mul a b) a) (Nat.add a (Nat.mul a b))`,
//! which is exactly `Nat.add_comm (Nat.mul a b) a`.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a b : Nat => Nat.add_comm (Nat.mul a b) a
//! ```
//!
//! against the type
//!
//! ```text
//! ∀ a b : Nat, @Eq.{1} Nat (Nat.mul a (Nat.succ b)) (Nat.add a (Nat.mul a b))
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Nat`, `Nat.succ`, `Nat.mul`, `Nat.add`,
//! `Nat.add_comm`. `Nat.add_comm` is a `Declaration::Theorem` (constructive
//! #3604); all others are constructors / reducible Definitions / inductives.
//! Therefore `env.axiom_deps("Nat.mul_succ")` is empty and
//! `env.proof_quality("Nat.mul_succ") == ProofQuality::Constructive`.
//!
//! Tracks issue #3551 (Tier A Batch 5 Nat axiom demotion). Sibling proofs:
//! - `algebra_nat_add_comm_proof.rs` (#3604, dependency — Nat.rec induction).
//! - `algebra_nat_mul_zero_proof.rs` (#3551, pure `Eq.refl`).
//! - `algebra_nat_mul_one_proof.rs` (#3551, companion — uses Nat.zero_add).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.mul_succ` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a b : Nat => Nat.add_comm (Nat.mul a b) a`. The
    /// kernel accepts this against the stated type because
    /// `Nat.mul a (Nat.succ b)` reduces to `Nat.add (Nat.mul a b) a` via
    /// iota+beta on `Nat.rec` (succ case) + delta on the reducible `Nat.mul`
    /// definition, making the LHS of the stated Eq definitionally equal to
    /// the LHS of `Nat.add_comm (Nat.mul a b) a`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`,
    ///           `Nat.mul`, `Nat.add` (reducible Definitions).
    /// REQUIRES: `self.init_eq()` has registered `Eq`.
    /// REQUIRES: `Nat.add_comm` is registered as a `Declaration::Theorem`
    ///           (constructive proof — see `register_nat_add_comm_proof`).
    /// ENSURES: On success, `Nat.mul_succ` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.mul_succ` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_mul_succ_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_comm_proof()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1]);
        let nat_add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);

        // Type: ∀ a b : Nat, @Eq.{1} Nat (Nat.mul a (Nat.succ b)) (Nat.add a (Nat.mul a b))
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let (b_id, bv) = b.fresh_local(nat_type.clone());
        let succ_b = Expr::app(nat_succ.clone(), bv.clone());
        let lhs = Expr::app(Expr::app(nat_mul.clone(), a.clone()), succ_b);
        let ab = Expr::app(Expr::app(nat_mul.clone(), a.clone()), bv.clone());
        let rhs = Expr::app(Expr::app(nat_add.clone(), a.clone()), ab);
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, rhs]);
        let ty_raw = b.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), concl);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), ty_raw);
        let type_ = b.finish(ty_raw);

        // Value: λ a b : Nat => Nat.add_comm (Nat.mul a b) a
        //
        // `Nat.add_comm (Nat.mul a b) a : Eq (Nat.add (Nat.mul a b) a)
        //                                    (Nat.add a (Nat.mul a b))`.
        // Kernel def-eq reduces `Nat.mul a (Nat.succ b)` to
        // `Nat.add (Nat.mul a b) a`, matching the stated Eq LHS.
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let (vb_id, vbv) = vb.fresh_local(nat_type.clone());
        let v_ab = Expr::app(Expr::app(nat_mul.clone(), va.clone()), vbv.clone());
        let comm_app = Expr::apps(nat_add_comm, [v_ab, va.clone()]);
        let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, nat_type.clone(), comm_app);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), val_raw);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3551 Tier A Batch 5).
        // `Nat.add_comm (Nat.mul a b) a` witnesses the commuted equality;
        // kernel def-eq reduces `Nat.mul a (Nat.succ b)` to
        // `Nat.add (Nat.mul a b) a` via iota (succ-case on Nat.rec) + beta +
        // delta on reducible Nat.mul, so the LHS of the witness matches the
        // LHS of the stated Eq. No `sorry`, no self-reference, no
        // domain-axiom dependency (Nat.add_comm itself is constructive
        // #3604). Replaces the prior `Declaration::Axiom` in
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

    #[test]
    fn test_nat_mul_succ_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_mul_succ_proof()
            .expect("first registration");
        env.register_nat_mul_succ_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_succ"))
            .expect("Nat.mul_succ should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_mul_succ_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_succ_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_succ"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.mul_succ proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_nat_mul_succ_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_mul_succ_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.mul_succ"))
            .expect("Nat.mul_succ is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.mul_succ must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
