// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.le_of_add_le_add_left : ∀ a b c : Int,
//!    Int.le (Int.add a b) (Int.add a c) → Int.le b c`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! ```
//!
//! So `h : Int.le (a+b) (a+c)` delta-reduces to
//! `Int.NonNeg (Int.sub (a+c) (a+b))` and the goal `Int.le b c` to
//! `Int.NonNeg (Int.sub c b)`.
//!
//! # Proof sketch
//!
//! `Int.add_sub_add_left b c a : Eq Int (Int.sub (a+c) (a+b)) (Int.sub c b)`
//! (instantiating the left-cancellation identity `(a+c) - (a+b) = c - b`).
//! Transport `h` forward along it with motive `fun x => Int.NonNeg x`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg x)
//!   (Int.sub (a+c) (a+b)) (Int.sub c b)
//!   (Int.add_sub_add_left b c a)
//!   h
//!   : Int.NonNeg (Int.sub c b)   ≡   Int.le b c
//! ```
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_sub_add_left` theorem and the
//! foundational `Eq.subst`. Neither domain dependency is a `Declaration::Axiom`,
//! so `env.axiom_deps("Int.le_of_add_le_add_left")` is empty and
//! `env.proof_quality("Int.le_of_add_le_add_left") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeOfAddLeAddLeftConsts {
    int_type: Expr,
    int_le: Expr,
    int_add: Expr,
    int_sub: Expr,
    nonneg: Expr,
    add_sub_add_left: Expr,
    eq_subst: Expr,
}

impl IntLeOfAddLeAddLeftConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            add_sub_add_left: Expr::const_(Name::from_string("Int.add_sub_add_left"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }
}

/// Build `∀ a b c : Int, Int.le (a+b) (a+c) → Int.le b c`.
fn build_type(c: &IntLeOfAddLeAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.le(c.add(a.clone(), bv.clone()), c.add(a.clone(), cc.clone()));
    let conclusion = c.le(bv.clone(), cc.clone());
    let (h_id, _h) = b.fresh_local(premise.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h : Int.le (a+b) (a+c)) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg x)
///     (Int.sub (a+c) (a+b)) (Int.sub c b)
///     (Int.add_sub_add_left b c a)
///     h
/// ```
fn build_value(c: &IntLeOfAddLeAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.le(c.add(a.clone(), bv.clone()), c.add(a.clone(), cc.clone()));
    let (h_id, h) = b.fresh_local(premise.clone());

    // motive: fun x : Int => Int.NonNeg x
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    let sub_acab = c.sub(c.add(a.clone(), cc.clone()), c.add(a.clone(), bv.clone())); // (a+c)-(a+b)
    let sub_cb = c.sub(cc.clone(), bv.clone()); // c - b

    // Int.add_sub_add_left b c a : Eq Int ((a+c)-(a+b)) (c-b)
    let id_eq = Expr::apps(
        c.add_sub_add_left.clone(),
        [bv.clone(), cc.clone(), a.clone()],
    );

    // @Eq.subst.{1} Int motive ((a+c)-(a+b)) (c-b) id_eq h : NonNeg (c-b)
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            sub_acab,
            sub_cb,
            id_eq,
            h.clone(),
        ],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, premise, proof);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.le_of_add_le_add_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.add`, `Int.sub`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// ENSURES: On success, `Int.le_of_add_le_add_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_of_add_le_add_left` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_of_add_le_add_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_of_add_le_add_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependency: (a+c) - (a+b) = c - b.
        self.register_int_add_sub_add_left_proof()?;

        let c = IntLeOfAddLeAddLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Transports the incoming
        // `h : Int.le (a+b) (a+c)` (≡ `NonNeg ((a+c)-(a+b))`) forward along
        // `Int.add_sub_add_left b c a : Eq ((a+c)-(a+b)) (c-b)` via `@Eq.subst.{1}`
        // with motive `fun x => Int.NonNeg x`, yielding `Int.NonNeg (Int.sub c b)`
        // ≡ `Int.le b c`. No `sorry`, no self-reference, no domain-axiom
        // dependency. Replaces the prior `Declaration::Axiom` in
        // `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_le_of_add_le_add_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_of_add_le_add_left_proof()
            .expect("first registration");
        env.register_int_le_of_add_le_add_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_of_add_le_add_left"))
            .expect("Int.le_of_add_le_add_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_of_add_le_add_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_of_add_le_add_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_of_add_le_add_left"))
            .expect("Int.le_of_add_le_add_left is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_of_add_le_add_left must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_le_of_add_le_add_left_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_le_of_add_le_add_left_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_of_add_le_add_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_of_add_le_add_left must be Constructive, got {:?}",
            quality
        );
    }
}
