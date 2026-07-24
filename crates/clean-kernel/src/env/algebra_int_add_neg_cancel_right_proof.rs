// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_neg_cancel_right : ∀ a b : Int, Eq Int (Int.add (Int.add a b) (Int.neg b)) a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem`. This is the
//! right-cancellation identity `(a + b) + (-b) = a`, derived entirely from
//! already-constructive Int lemmas (no new recursion).
//!
//! # Proof sketch
//!
//! Let `nb := Int.neg b` and `Z := Int.zero`. The chain is
//!
//! ```text
//! s1 := Int.add_assoc a b nb
//!     : Eq Int (Int.add (Int.add a b) nb) (Int.add a (Int.add b nb))
//! s2 := Int.add_neg_self b
//!     : Eq Int (Int.add b nb) Int.zero
//! s3 := congrArg Int Int (Int.add b nb) Int.zero (λ x => Int.add a x) s2
//!     : Eq Int (Int.add a (Int.add b nb)) (Int.add a Int.zero)
//! s4 := Int.add_zero a
//!     : Eq Int (Int.add a Int.zero) a
//! ```
//!
//! and the proof term is
//!
//! ```text
//! λ (a b : Int) =>
//!   Eq.trans s1 (Eq.trans s3 s4)
//! ```
//!
//! Each `Eq.trans` is fully applied with its three explicit value arguments
//! (the implicit `α := Int` plus the three endpoints), exactly as in the
//! sibling `Eq.trans`-chain proofs (`algebra_nat_left_distrib_proof.rs`,
//! `algebra_nat_right_distrib_proof.rs`).
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.add`, `Int.neg`, `Eq`,
//! `Eq.trans`, `congrArg`, and the three constructive Int lemmas
//! `Int.add_assoc`, `Int.add_neg_self`, `Int.add_zero` (all
//! `Declaration::Theorem`s with empty domain-axiom closure, #3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.add_neg_cancel_right")` is
//! empty and
//! `env.proof_quality("Int.add_neg_cancel_right") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_add_assoc_proof.rs` (dependency).
//! - `algebra_int_add_neg_self_proof.rs` (dependency).
//! - `algebra_int_add_zero_proof.rs` (dependency).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddNegCancelRightConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_zero: Expr,
    int_add_assoc: Expr,
    int_add_neg_self: Expr,
    int_add_zero: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntAddNegCancelRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            int_add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) →
            //   Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `Eq.trans Int x y z h1 h2 : Eq Int x z`.
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }
}

/// Build `∀ a b : Int, Eq Int (Int.add (Int.add a b) (Int.neg b)) a`.
fn build_type(c: &IntAddNegCancelRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.add(c.add(a.clone(), bv.clone()), c.neg(bv));
    let concl = c.eq_int(lhs, a);
    let ty_raw = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Body: `λ (a b : Int) => Eq.trans s1 (Eq.trans s3 s4)`.
fn build_value(c: &IntAddNegCancelRightConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (b_id, bv) = vb.fresh_local(c.int_type.clone());

    let nb = c.neg(bv.clone()); // Int.neg b
    let ab = c.add(a.clone(), bv.clone()); // Int.add a b
    let lhs = c.add(ab.clone(), nb.clone()); // (a + b) + (-b)
    let b_plus_nb = c.add(bv.clone(), nb.clone()); // b + (-b)
    let a_plus_grp = c.add(a.clone(), b_plus_nb.clone()); // a + (b + (-b))
    let a_plus_zero = c.add(a.clone(), c.int_zero.clone()); // a + 0

    // s1 := Int.add_assoc a b nb
    //     : Eq Int ((a + b) + nb) (a + (b + nb))
    let s1 = Expr::apps(c.int_add_assoc.clone(), [a.clone(), bv.clone(), nb.clone()]);

    // s2 := Int.add_neg_self b : Eq Int (b + nb) Int.zero
    let s2 = Expr::app(c.int_add_neg_self.clone(), bv.clone());

    // func := λ (x : Int) => Int.add a x
    let func = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = fb.fresh_local(c.int_type.clone());
        let body = c.add(a.clone(), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };

    // s3 := congrArg Int Int (b + nb) Int.zero func s2
    //     : Eq Int (a + (b + nb)) (a + Int.zero)
    let s3 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            b_plus_nb.clone(),
            c.int_zero.clone(),
            func,
            s2,
        ],
    );

    // s4 := Int.add_zero a : Eq Int (a + Int.zero) a
    let s4 = Expr::app(c.int_add_zero.clone(), a.clone());

    // inner := Eq.trans Int (a + (b + nb)) (a + Int.zero) a s3 s4
    //        : Eq Int (a + (b + nb)) a
    let inner = c.trans(a_plus_grp.clone(), a_plus_zero.clone(), a.clone(), s3, s4);

    // result := Eq.trans Int ((a + b) + nb) (a + (b + nb)) a s1 inner
    //         : Eq Int ((a + b) + nb) a
    let result = c.trans(lhs, a_plus_grp, a.clone(), s1, inner);

    let lam_b = vb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), result);
    let val_raw = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), lam_b);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_neg_cancel_right` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.add`,
    ///           `Int.neg`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// ENSURES: On success, `Int.add_neg_cancel_right` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_neg_cancel_right` is already
    ///          registered with any declaration kind, this call returns
    ///          `Ok(())` without modification.
    pub(crate) fn register_int_add_neg_cancel_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_neg_cancel_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        // Constructive dependencies (all #3604 Theorems with empty closure).
        self.register_int_add_assoc_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_add_zero_proof()?;

        let c = IntAddNegCancelRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). No recursion of
        // its own — a two-step `Eq.trans` chain over `Int.add_assoc`,
        // `Int.add_neg_self` (transported through `Int.add a ·` by
        // `congrArg`), and `Int.add_zero`, all of which are constructive
        // `Declaration::Theorem`s with empty domain-axiom closure. No
        // `sorry`, no self-reference, no domain-axiom dependency. Replaces
        // the prior `Declaration::Axiom` in
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

    /// Kernel accepts the `Eq.trans` / `congrArg` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_int_add_neg_cancel_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_neg_cancel_right_proof()
            .expect("first registration");
        env.register_int_add_neg_cancel_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_neg_cancel_right"))
            .expect("Int.add_neg_cancel_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction whose root, after peeling the two outer binders, is an
    /// `Eq.trans` application. Guards against the axiom-wrapping masquerade.
    #[test]
    fn test_int_add_neg_cancel_right_proof_uses_eq_trans() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_add_neg_cancel_right_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_neg_cancel_right"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel λ a => λ b => body.
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
                "Eq.trans",
                "Int.add_neg_cancel_right proof root must be Eq.trans, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Eq.trans, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof). Also guards against a
    /// feeder lemma silently reintroducing a domain axiom.
    #[test]
    fn test_int_add_neg_cancel_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_neg_cancel_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_neg_cancel_right"))
            .expect("Int.add_neg_cancel_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_neg_cancel_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
