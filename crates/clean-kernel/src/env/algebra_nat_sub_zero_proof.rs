// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.sub_zero : ∀ a : Nat, Eq Nat (Nat.sub a Nat.zero) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_arith.rs::init_nat_sub_ord` with a `Declaration::Theorem` whose
//! proof term is pure `@Eq.refl.{1} Nat a`.
//!
//! # Proof sketch
//!
//! `Nat.sub` is a reducible Definition (see `data_types_nat.rs`) that
//! recurses on its SECOND argument:
//!
//! ```text
//! Nat.sub m n := Nat.rec m (λ _ ih => Nat.pred ih) n
//! Nat.sub m Nat.zero      = m
//! Nat.sub m (Nat.succ n)  = Nat.pred (Nat.sub m n)
//! ```
//!
//! Specializing to `n = Nat.zero`, the `Nat.rec` reduces by the zero
//! iota-case directly to the major premise `m = a`. Therefore
//! `Nat.sub a Nat.zero` is **definitionally equal** to `a`, and a pure
//! `@Eq.refl.{1} Nat a` proof term type-checks against the stated type:
//!
//! ```text
//! λ a : Nat => @Eq.refl.{1} Nat a
//!   : ∀ a : Nat, @Eq.{1} Nat (Nat.sub a Nat.zero) a
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Nat`, `Nat.sub`,
//! `Nat.zero`: none of these are `Declaration::Axiom`. `Eq.refl` is a
//! kernel-level constructor, `Nat` is an inductive type, `Nat.zero` is a
//! constructor, and `Nat.sub` is a reducible `Declaration::Definition`.
//! Therefore `env.axiom_deps("Nat.sub_zero")` is empty and
//! `env.proof_quality("Nat.sub_zero") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604 (kernel-soundness Tier 6). Sibling proofs:
//! - `algebra_int_tonat_ofnat_proof.rs` (#3551, pure `Eq.refl` — same shape).
//! - `algebra_nat_pow_zero_proof.rs` (#3604, pure `Eq.refl` — same shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.sub_zero` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a : Nat => @Eq.refl.{1} Nat a`. The kernel
    /// accepts this against the stated type because `Nat.sub a Nat.zero`
    /// reduces to `a` by iota on `Nat.rec` (zero case) + delta on the
    /// reducible `Nat.sub` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.sub` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Nat.sub_zero` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.sub_zero` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_sub_zero_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        // Type: ∀ a : Nat, @Eq.{1} Nat (Nat.sub a Nat.zero) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(nat_sub, a.clone()), nat_zero);
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
        // reducing `Nat.sub a Nat.zero` to `a` via iota on `Nat.rec` (zero
        // case) + delta on the reducible `Nat.sub` definition. No `sorry`,
        // no self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `order_arith.rs::init_nat_sub_ord`.
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
    /// registered as a Theorem (not Axiom) and idempotent re-invocation is a
    /// no-op.
    #[test]
    fn test_nat_sub_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_sub_zero_proof()
            .expect("first registration");
        env.register_nat_sub_zero_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.sub_zero"))
            .expect("Nat.sub_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body is an `Eq.refl` application. Guards against the axiom-wrapping
    /// masquerade where a Theorem's value is just `@<same_name>` lifted to a
    /// term.
    #[test]
    fn test_nat_sub_zero_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_sub_zero_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.sub_zero"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.sub_zero proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_sub_zero_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_sub_zero_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.sub_zero"))
            .expect("Nat.sub_zero is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.sub_zero must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
