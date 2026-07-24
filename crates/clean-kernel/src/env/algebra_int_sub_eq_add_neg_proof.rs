// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.sub_eq_add_neg : ∀ a b : Int, Eq Int (Int.sub a b) (Int.add a (Int.neg b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is a pure `@Eq.refl.{1} Int (Int.sub a b)`.
//!
//! # Proof sketch
//!
//! `Int.sub` is a reducible Definition (see `data_types_arithmetic.rs`):
//!
//! ```text
//! Int.sub m n := Int.add m (Int.neg n)
//! ```
//!
//! So `Int.sub a b` reduces to `Int.add a (Int.neg b)` purely by delta on
//! the reducible `Int.sub` definition (then beta). The two sides of the
//! conclusion are therefore definitionally equal, and the goal is closed
//! by the reflexivity proof
//!
//! ```text
//! λ a b : Int => @Eq.refl.{1} Int (Int.sub a b)
//! ```
//!
//! checked against
//! `∀ a b : Int, @Eq.{1} Int (Int.sub a b) (Int.add a (Int.neg b))`.
//! The kernel accepts this because `Eq.refl` forces the two arguments of
//! `Eq` to be definitionally equal, which holds here by delta/beta.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.sub`, `Eq`, `Eq.refl` — none
//! of which are `Declaration::Axiom` (`Int.sub` is a reducible Definition;
//! `Eq` / `Eq.refl` are inductive machinery). Therefore
//! `env.axiom_deps("Int.sub_eq_add_neg")` is empty and
//! `env.proof_quality("Int.sub_eq_add_neg") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_mul_zero_proof.rs` (Int.mul_zero via pure `Eq.refl`).
//! - `algebra_int_tonat_ofnat_proof.rs` (Int.toNat_ofNat via pure `Eq.refl`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubEqAddNegConsts {
    int_type: Expr,
    int_sub: Expr,
    int_add: Expr,
    int_neg: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntSubEqAddNegConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), a), b)
    }

    fn add_neg(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(self.int_add.clone(), a),
            Expr::app(self.int_neg.clone(), b),
        )
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

/// Build `∀ a b : Int, Eq Int (Int.sub a b) (Int.add a (Int.neg b))`.
fn build_type(c: &IntSubEqAddNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.sub(a.clone(), bv.clone()), c.add_neg(a, bv));
    let ty_raw = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Body: `λ a b : Int => @Eq.refl.{1} Int (Int.sub a b)`.
fn build_value(c: &IntSubEqAddNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let refl = Expr::apps(
        c.eq_refl.clone(),
        [c.int_type.clone(), c.sub(a.clone(), bv.clone())],
    );
    let val_raw = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), refl);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.sub_eq_add_neg` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.sub`,
    ///           `Int.add`, `Int.neg`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.sub_eq_add_neg` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.sub_eq_add_neg` is already registered
    ///          with any declaration kind, this call returns `Ok(())`
    ///          without modification.
    pub(crate) fn register_int_sub_eq_add_neg_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.sub_eq_add_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;

        let c = IntSubEqAddNegConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Pure
        // `@Eq.refl.{1} Int (Int.sub a b)`; the conclusion's two sides are
        // definitionally equal because `Int.sub a b` reduces to
        // `Int.add a (Int.neg b)` by delta on the reducible `Int.sub`
        // definition (which is literally `λ m n => Int.add m (Int.neg n)`)
        // + beta. No `sorry`, no self-reference, no domain-axiom
        // dependency. Replaces the prior `Declaration::Axiom` in
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

    /// Kernel accepts the pure `Eq.refl` proof term. Verifies the theorem
    /// is registered as a Theorem (not Axiom) and idempotent re-invocation
    /// is a no-op.
    #[test]
    fn test_int_sub_eq_add_neg_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_eq_add_neg_proof()
            .expect("first registration");
        env.register_int_sub_eq_add_neg_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.sub_eq_add_neg"))
            .expect("Int.sub_eq_add_neg should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction. Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_int_sub_eq_add_neg_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_eq_add_neg_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.sub_eq_add_neg"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.sub_eq_add_neg proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Proof root (after peeling the two outer λ binders) must be an
    /// `@Eq.refl.{1}` application. Guards against a trivial masquerade.
    #[test]
    fn test_int_sub_eq_add_neg_proof_uses_eq_refl() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_eq_add_neg_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.sub_eq_add_neg"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel two outer λ binders (a, b).
        let mut body = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Eq.refl",
                "Int.sub_eq_add_neg proof root must be Eq.refl, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Eq.refl, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_sub_eq_add_neg_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_eq_add_neg_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.sub_eq_add_neg"))
            .expect("Int.sub_eq_add_neg is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.sub_eq_add_neg must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
