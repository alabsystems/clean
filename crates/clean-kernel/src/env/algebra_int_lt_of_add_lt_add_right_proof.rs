// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_of_add_lt_add_right : ∀ a b c : Int,
//!    Int.lt (Int.add a b) (Int.add c b) → Int.lt a c`.
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
//! # Proof sketch
//!
//! Commute both addends so the shared summand `b` moves to the left, then
//! reuse the constructive left-cancellation lemma. Two `Eq.subst` rewrites at
//! the `Prop` level turn `h : Int.lt (a+b) (c+b)` into `Int.lt (b+a) (b+c)`:
//!
//! ```text
//! s1 := @Eq.subst.{1} Int (fun x => Int.lt x (c+b))
//!         (a+b) (b+a) (Int.add_comm a b) h
//!     : Int.lt (b+a) (c+b)
//! s2 := @Eq.subst.{1} Int (fun y => Int.lt (b+a) y)
//!         (c+b) (b+c) (Int.add_comm c b) s1
//!     : Int.lt (b+a) (b+c)
//! ```
//!
//! Then `Int.lt_of_add_lt_add_left b a c s2 : Int.lt a c`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_comm` and
//! `Int.lt_of_add_lt_add_left` theorems plus the foundational `Eq.subst`.
//! Neither is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.lt_of_add_lt_add_right")` is empty and
//! `env.proof_quality("Int.lt_of_add_lt_add_right") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtOfAddLtAddRightConsts {
    int_type: Expr,
    int_lt: Expr,
    int_add: Expr,
    add_comm: Expr,
    lt_of_add_lt_add_left: Expr,
    eq_subst: Expr,
}

impl IntLtOfAddLtAddRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            lt_of_add_lt_add_left: Expr::const_(
                Name::from_string("Int.lt_of_add_lt_add_left"),
                vec![],
            ),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }
}

/// Build `∀ a b c : Int, Int.lt (a+b) (c+b) → Int.lt a c`.
fn build_type(c: &IntLtOfAddLtAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.lt(c.add(a.clone(), bv.clone()), c.add(cc.clone(), bv.clone()));
    let conclusion = c.lt(a.clone(), cc.clone());
    let (h_id, _h) = b.fresh_local(premise.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h : Int.lt (a+b) (c+b)) =>
///   Int.lt_of_add_lt_add_left b a c
///     (@Eq.subst.{1} Int (fun y => Int.lt (b+a) y)
///        (c+b) (b+c) (Int.add_comm c b)
///        (@Eq.subst.{1} Int (fun x => Int.lt x (c+b))
///           (a+b) (b+a) (Int.add_comm a b) h))
/// ```
fn build_value(c: &IntLtOfAddLtAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.lt(c.add(a.clone(), bv.clone()), c.add(cc.clone(), bv.clone()));
    let (h_id, h) = b.fresh_local(premise.clone());

    let a_plus_b = c.add(a.clone(), bv.clone()); // a + b
    let b_plus_a = c.add(bv.clone(), a.clone()); // b + a
    let c_plus_b = c.add(cc.clone(), bv.clone()); // c + b
    let b_plus_c = c.add(bv.clone(), cc.clone()); // b + c

    // motive1: fun x : Int => Int.lt x (c+b)
    let motive1 = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.lt(x, c_plus_b.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // Int.add_comm a b : Eq Int (a+b) (b+a)
    let comm_ab = Expr::apps(c.add_comm.clone(), [a.clone(), bv.clone()]);
    // s1 := @Eq.subst.{1} Int motive1 (a+b) (b+a) comm_ab h : Int.lt (b+a) (c+b)
    let s1 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive1,
            a_plus_b,
            b_plus_a.clone(),
            comm_ab,
            h.clone(),
        ],
    );

    // motive2: fun y : Int => Int.lt (b+a) y
    let motive2 = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = mb.fresh_local(c.int_type.clone());
        let body = c.lt(b_plus_a.clone(), y);
        let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // Int.add_comm c b : Eq Int (c+b) (b+c)
    let comm_cb = Expr::apps(c.add_comm.clone(), [cc.clone(), bv.clone()]);
    // s2 := @Eq.subst.{1} Int motive2 (c+b) (b+c) comm_cb s1 : Int.lt (b+a) (b+c)
    let s2 = Expr::apps(
        c.eq_subst.clone(),
        [c.int_type.clone(), motive2, c_plus_b, b_plus_c, comm_cb, s1],
    );

    // Int.lt_of_add_lt_add_left b a c s2 : Int.lt a c
    let proof = Expr::apps(
        c.lt_of_add_lt_add_left.clone(),
        [bv.clone(), a.clone(), cc.clone(), s2],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, premise, proof);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.lt_of_add_lt_add_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.add`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// ENSURES: On success, `Int.lt_of_add_lt_add_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_of_add_lt_add_right` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_of_add_lt_add_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_of_add_lt_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_comm_proof()?;
        self.register_int_lt_of_add_lt_add_left_proof()?;

        let c = IntLtOfAddLtAddRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Commutes both addends of the
        // strict premise `h : Int.lt (a+b) (c+b)` to `Int.lt (b+a) (b+c)` via two
        // `@Eq.subst.{1}` rewrites over `Int.add_comm a b` / `Int.add_comm c b`
        // (Prop-valued motives placing the variable in each `Int.lt` argument),
        // then cancels the now-shared left addend `b` with the constructive
        // `Int.lt_of_add_lt_add_left b a c`, yielding `Int.lt a c`. No `sorry`, no
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
    fn test_int_lt_of_add_lt_add_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_right_proof()
            .expect("first registration");
        env.register_int_lt_of_add_lt_add_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_of_add_lt_add_right"))
            .expect("Int.lt_of_add_lt_add_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_lt_of_add_lt_add_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_of_add_lt_add_right"))
            .expect("Int.lt_of_add_lt_add_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_of_add_lt_add_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_lt_of_add_lt_add_right_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_right_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.lt_of_add_lt_add_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.lt_of_add_lt_add_right must be Constructive, got {:?}",
            quality
        );
    }
}
