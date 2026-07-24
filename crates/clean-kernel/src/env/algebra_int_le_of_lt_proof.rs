// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Int.le_of_lt : ∀ a b : Int, Int.lt a b → Int.le a b`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b   -- reducible Definition
//! ```
//!
//! So the hypothesis `h : Int.lt a b` delta-reduces to `Int.le (a + 1) b`.
//!
//! # Proof sketch
//!
//! `a ≤ a + 1` (`Int.le_self_add_one a`) chains with `a + 1 ≤ b` (the
//! delta-reduct of `h`) through the already-constructive `Int.le_trans`:
//!
//! ```text
//! Int.le_trans a (Int.add a one) b (Int.le_self_add_one a) h : Int.le a b
//! ```
//!
//! The kernel accepts `h : Int.lt a b` in the `Int.le (a + 1) b` slot because
//! `Int.lt a b` is definitionally `Int.le (Int.add a (Int.ofNat 1)) b`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.le_trans` and `Int.le_self_add_one`
//! theorems. Neither is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_of_lt")` is empty and
//! `env.proof_quality("Int.le_of_lt") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeOfLtConsts {
    int_type: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    le_trans: Expr,
    le_self_add_one: Expr,
}

impl IntLeOfLtConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            le_self_add_one: Expr::const_(Name::from_string("Int.le_self_add_one"), vec![]),
        }
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`.
    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
}

/// Build `∀ a b : Int, Int.lt a b → Int.le a b`.
fn build_type(c: &IntLeOfLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let (h_id, _h) = b.fresh_local(lt_ab.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, lt_ab, le_ab);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) (h : Int.lt a b) =>
///   Int.le_trans a (Int.add a one) b (Int.le_self_add_one a) h
/// ```
fn build_value(c: &IntLeOfLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(lt_ab.clone());

    let a_plus_one = c.add(a.clone(), c.one());
    // Int.le_self_add_one a : Int.le a (a + 1)
    let bridge = Expr::app(c.le_self_add_one.clone(), a.clone());
    // Int.le_trans a (a + 1) b bridge h : Int.le a b
    let proof = Expr::apps(
        c.le_trans.clone(),
        [a.clone(), a_plus_one, bv.clone(), bridge, h.clone()],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, lt_ab, proof);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.le_of_lt` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.lt`,
    ///           `Int.add`, `Int.ofNat`.
    /// ENSURES: On success, `Int.le_of_lt` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_of_lt` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_of_lt_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        // Constructive dependencies.
        self.register_int_le_trans_proof()?;
        self.register_int_le_self_add_one_proof()?;

        let c = IntLeOfLtConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Chains the constructive
        // bridge `Int.le_self_add_one a : Int.le a (a + 1)` with the incoming
        // hypothesis `h : Int.lt a b` (definitionally `Int.le (a + 1) b`) through
        // the constructive `Int.le_trans`, yielding `Int.le a b`. No `sorry`, no
        // self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_le_of_lt_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_of_lt_proof()
            .expect("first registration");
        env.register_int_le_of_lt_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_of_lt"))
            .expect("Int.le_of_lt should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_of_lt_proof_body_uses_le_trans() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_le_of_lt_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.le_of_lt"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the three outer λ binders (a, b, h), then the head must be
        // Int.le_trans.
        let mut body: Expr = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.le_trans",
                "Int.le_of_lt proof root must be Int.le_trans"
            ),
            k => panic!("expected Const(Int.le_trans), got {:?}", k),
        }
    }

    #[test]
    fn test_int_le_of_lt_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_of_lt_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_of_lt"))
            .expect("Int.le_of_lt is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_of_lt must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_le_of_lt_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_le_of_lt_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_of_lt"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_of_lt must be Constructive, got {:?}",
            quality
        );
    }
}
