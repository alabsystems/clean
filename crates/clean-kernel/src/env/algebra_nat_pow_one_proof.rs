// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.pow_one : ∀ a : Nat, Eq Nat (Nat.pow a (Nat.succ Nat.zero)) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_arith.rs::init_nat_pow_ord` with a `Declaration::Theorem` whose
//! proof term is `λ a : Nat => Nat.one_mul a`.
//!
//! # Proof sketch
//!
//! `Nat.pow` is a reducible Definition (see `data_types_nat.rs`) that
//! recurses on its SECOND argument:
//!
//! ```text
//! Nat.pow m n := Nat.rec (Nat.succ Nat.zero) (λ _ ih => Nat.mul ih m) n
//! Nat.pow m Nat.zero      = Nat.succ Nat.zero
//! Nat.pow m (Nat.succ n)  = Nat.mul (Nat.pow m n) m
//! ```
//!
//! Specializing the LHS to `Nat.pow a (Nat.succ Nat.zero)`:
//!
//! ```text
//! Nat.pow a (Nat.succ Nat.zero)
//!   ι→ Nat.mul (Nat.pow a Nat.zero) a            (succ iota-case)
//!   ι→ Nat.mul (Nat.succ Nat.zero) a             (zero iota-case)
//! ```
//!
//! So `Nat.pow a (Nat.succ Nat.zero)` is **definitionally equal** to
//! `Nat.mul (Nat.succ Nat.zero) a`. The constructive theorem
//! `Nat.one_mul : ∀ a, Eq Nat (Nat.mul (Nat.succ Nat.zero) a) a`
//! therefore has, at `a`, the type `Eq Nat (Nat.mul (Nat.succ Nat.zero) a) a`,
//! which is defeq to the goal `Eq Nat (Nat.pow a (Nat.succ Nat.zero)) a`.
//! Hence the proof body is simply `λ a : Nat => Nat.one_mul a`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Nat` and the constructive `Declaration::Theorem`
//! `Nat.one_mul` (#3551). `Nat.one_mul` is itself proved by `Nat.rec`
//! induction with empty domain-axiom closure, so
//! `env.axiom_deps("Nat.pow_one")` is empty and
//! `env.proof_quality("Nat.pow_one") == ProofQuality::Constructive`.
//!
//! Tracks issue #3604 (kernel-soundness Tier 6). Sibling proofs:
//! - `algebra_nat_pow_zero_proof.rs` (#3604, pure `Eq.refl`).
//! - `algebra_nat_one_pow_proof.rs` (#3604, induction via `Nat.mul_one`).
//! - `algebra_int_sub_self_proof.rs` (#3604, one-liner `λ a => <thm> a`).

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Register `Nat.pow_one` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body is `λ a : Nat => Nat.one_mul a`. The kernel accepts
    /// this against the stated type because `Nat.pow a (Nat.succ Nat.zero)`
    /// reduces to `Nat.mul (Nat.succ Nat.zero) a` by iota on `Nat.rec`
    /// (succ then zero cases) + delta on the reducible `Nat.pow` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.pow` (reducible Definition).
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// REQUIRES: `Nat.one_mul` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_one_mul_proof`).
    /// ENSURES: On success, `Nat.pow_one` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.pow_one` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    #[cfg(test)]
    pub(crate) fn register_nat_pow_one_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pow_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency: Nat.mul (succ zero) a = a.
        self.register_nat_one_mul_proof()?;

        let type1 = Level::succ(Level::zero());
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_one_mul = Expr::const_(Name::from_string("Nat.one_mul"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1]);

        let one = Expr::app(nat_succ, nat_zero);

        // Type: ∀ a : Nat, @Eq.{1} Nat (Nat.pow a (Nat.succ Nat.zero)) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_type.clone());
        let lhs = Expr::app(Expr::app(nat_pow, a.clone()), one.clone());
        let concl = Expr::apps(eq_const, [nat_type.clone(), lhs, a.clone()]);
        let ty_raw = b.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), concl);
        let type_ = b.finish(ty_raw);

        // Value: λ a : Nat => Nat.one_mul a
        let mut vb = EnvDeclBuilder::new();
        let (va_id, va) = vb.fresh_local(nat_type.clone());
        let body = Expr::app(nat_one_mul, va);
        let val_raw = vb.mk_lam(va_id, BinderInfo::Default, nat_type.clone(), body);
        let value = vb.finish(val_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Body
        // `λ a => Nat.one_mul a`; the kernel reduces
        // `Nat.pow a (Nat.succ Nat.zero)` to `Nat.mul (Nat.succ Nat.zero) a`
        // via iota on `Nat.rec` (succ then zero cases) + delta on the
        // reducible `Nat.pow` definition, so the constructive
        // `Nat.one_mul a : Eq (Nat.mul (Nat.succ Nat.zero) a) a` is defeq to
        // the goal. No `sorry`, no self-reference, no domain-axiom
        // dependency (`Nat.one_mul` is itself constructive #3551). Replaces
        // the prior `Declaration::Axiom` in
        // `order_arith.rs::init_nat_pow_ord`.
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

    /// Kernel accepts the `Nat.one_mul`-based proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_nat_pow_one_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_pow_one_proof()
            .expect("first registration");
        env.register_nat_pow_one_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.pow_one"))
            .expect("Nat.pow_one should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` term whose
    /// body applies the constructive `Nat.one_mul`.
    #[test]
    fn test_nat_pow_one_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_pow_one_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.pow_one"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let body = match value.kind() {
            ExprKind::Lam(_, _, inner) => (**inner).clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.one_mul",
                "Nat.pow_one proof must apply Nat.one_mul, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.one_mul, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_nat_pow_one_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_pow_one_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.pow_one"))
            .expect("Nat.pow_one is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.pow_one must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
