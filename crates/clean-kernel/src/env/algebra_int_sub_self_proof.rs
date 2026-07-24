// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.sub_self : ∀ a : Int, Eq Int (Int.sub a a) Int.zero`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem`. This is the
//! subtraction self-cancellation identity `a - a = 0`.
//!
//! # Proof sketch
//!
//! `Int.sub` is a reducible Definition (see `data_types_arithmetic.rs`):
//!
//! ```text
//! Int.sub m n := Int.add m (Int.neg n)
//! ```
//!
//! so `Int.sub a a` reduces to `Int.add a (Int.neg a)` purely by delta on
//! the reducible `Int.sub` definition (then beta). The constructive
//! `Int.add_neg_self` theorem already proves
//!
//! ```text
//! Int.add_neg_self a : Eq Int (Int.add a (Int.neg a)) Int.zero,
//! ```
//!
//! whose type is therefore definitionally equal to the goal
//! `Eq Int (Int.sub a a) Int.zero`. The proof is simply
//!
//! ```text
//! λ a : Int => Int.add_neg_self a
//! ```
//!
//! checked against `∀ a : Int, @Eq.{1} Int (Int.sub a a) Int.zero`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.sub` (in the stated type) and
//! the constructive `Int.add_neg_self` (a `Declaration::Theorem`, #3604).
//! Neither is `Declaration::Axiom` (`Int.sub` is a reducible Definition),
//! so `env.axiom_deps("Int.sub_self")` is empty and
//! `env.proof_quality("Int.sub_self") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_add_neg_self_proof.rs` (dependency).
//! - `algebra_int_sub_eq_add_neg_proof.rs` (same `Int.sub` delta reduction).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubSelfConsts {
    int_type: Expr,
    int_sub: Expr,
    int_zero: Expr,
    int_add_neg_self: Expr,
    eq_const: Expr,
}

impl IntSubSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1]),
        }
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), a), b)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

/// Build `∀ a : Int, Eq Int (Int.sub a a) Int.zero`.
fn build_type(c: &IntSubSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.sub(a.clone(), a), c.int_zero.clone());
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body: `λ (a : Int) => Int.add_neg_self a`.
fn build_value(c: &IntSubSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let body = Expr::app(c.int_add_neg_self.clone(), a);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), body);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.sub_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.sub`,
    ///           `Int.add`, `Int.neg`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`.
    /// ENSURES: On success, `Int.sub_self` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.sub_self` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_sub_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.sub_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        // Constructive dependency: a + (-a) = 0.
        self.register_int_add_neg_self_proof()?;

        let c = IntSubSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). The body
        // `λ a => Int.add_neg_self a` type-checks because `Int.sub a a`
        // reduces to `Int.add a (Int.neg a)` by delta on the reducible
        // `Int.sub` definition (literally `λ m n => Int.add m (Int.neg n)`)
        // + beta, making the goal definitionally equal to the type of the
        // constructive `Int.add_neg_self a`. No `sorry`, no self-reference,
        // no domain-axiom dependency. Replaces the prior `Declaration::Axiom`
        // in `data_types_int_lemmas.rs`.
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

    /// Kernel accepts the `λ a => Int.add_neg_self a` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_int_sub_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_self_proof()
            .expect("first registration");
        env.register_int_sub_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.sub_self"))
            .expect("Int.sub_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ` abstraction.
    /// Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_int_sub_self_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_self_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.sub_self"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.sub_self proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Axiom closure is empty (constructive proof). The proof reduces
    /// transitively through `Int.add_neg_self` and `Int.subNatNat_self`,
    /// none of which are `Declaration::Axiom`.
    #[test]
    fn test_int_sub_self_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_self_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.sub_self"))
            .expect("Int.sub_self is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.sub_self must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
