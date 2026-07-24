// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.le_trans : ∀ a b c : Int, Int.le a b → Int.le b c → Int.le a c`.
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
//! So the hypotheses unfold (delta) to `h1 : NonNeg (Int.sub b a)` and
//! `h2 : NonNeg (Int.sub c b)`, and the goal to `NonNeg (Int.sub c a)`.
//!
//! # Proof sketch
//!
//! 1. `Int.NonNeg.add (Int.sub c b) (Int.sub b a) h2 h1`
//!    `: NonNeg (Int.add (Int.sub c b) (Int.sub b a))`
//!    (additive closure of `Int.NonNeg`, see `algebra_int_nonneg_add_proof.rs`).
//! 2. `Int.sub_add_sub_cancel a b c`
//!    `: Eq Int (Int.add (Int.sub c b) (Int.sub b a)) (Int.sub c a)`
//!    (the arithmetic identity `(c-b)+(b-a) = c-a`, see
//!    `algebra_int_sub_add_sub_cancel_proof.rs`).
//! 3. Transport (1) along (2) with `@Eq.subst.{1}` and motive
//!    `fun x : Int => Int.NonNeg x`, giving `NonNeg (Int.sub c a)` ≡ `Int.le a c`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.NonNeg.add`, `Int.sub_add_sub_cancel`
//! theorems and the foundational `Eq.subst`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_trans")` is empty and
//! `env.proof_quality("Int.le_trans") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeTransConsts {
    int_type: Expr,
    int_le: Expr,
    int_sub: Expr,
    int_add: Expr,
    nonneg: Expr,
    nonneg_add: Expr,
    sub_add_sub_cancel: Expr,
    eq_subst: Expr,
}

impl IntLeTransConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_add: Expr::const_(Name::from_string("Int.NonNeg.add"), vec![]),
            sub_add_sub_cancel: Expr::const_(Name::from_string("Int.sub_add_sub_cancel"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), a), b)
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), a), b)
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), a), b)
    }
}

/// Build `∀ a b c : Int, Int.le a b → Int.le b c → Int.le a c`.
fn build_type(c: &IntLeTransConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let le_bc = c.le(bv.clone(), cc.clone());
    let le_ac = c.le(a.clone(), cc.clone());
    let (h2_id, _h2) = b.fresh_local(le_bc.clone());
    let (h1_id, _h1) = b.fresh_local(le_ab.clone());
    let r = b.mk_pi(h2_id, BinderInfo::Default, le_bc, le_ac);
    let r = b.mk_pi(h1_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h1 : le a b) (h2 : le b c) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg x)
///     (Int.add (Int.sub c b) (Int.sub b a)) (Int.sub c a)
///     (Int.sub_add_sub_cancel a b c)
///     (Int.NonNeg.add (Int.sub c b) (Int.sub b a) h2 h1)
/// ```
fn build_value(c: &IntLeTransConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let le_bc = c.le(bv.clone(), cc.clone());
    // h1 : le a b  ≡  NonNeg (sub b a); h2 : le b c  ≡  NonNeg (sub c b).
    let (h1_id, h1) = b.fresh_local(le_ab.clone());
    let (h2_id, h2) = b.fresh_local(le_bc.clone());

    // motive: fun x : Int => Int.NonNeg x
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    let sub_cb = c.sub(cc.clone(), bv.clone()); // c - b
    let sub_ba = c.sub(bv.clone(), a.clone()); // b - a
    let sub_ca = c.sub(cc.clone(), a.clone()); // c - a
    let added = c.add(sub_cb.clone(), sub_ba.clone()); // (c-b) + (b-a)

    // Int.NonNeg.add (c-b) (b-a) h2 h1 : NonNeg ((c-b)+(b-a)).
    // (h2 : NonNeg (sub c b), h1 : NonNeg (sub b a) — both definitionally the
    // arguments expected by Int.NonNeg.add.)
    let witness = Expr::apps(
        c.nonneg_add.clone(),
        [sub_cb, sub_ba, h2.clone(), h1.clone()],
    );

    // Int.sub_add_sub_cancel a b c : Eq ((c-b)+(b-a)) (c-a).
    let cancel = Expr::apps(
        c.sub_add_sub_cancel.clone(),
        [a.clone(), bv.clone(), cc.clone()],
    );

    // @Eq.subst.{1} Int motive added sub_ca cancel witness : NonNeg (c-a).
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [c.int_type.clone(), motive, added, sub_ca, cancel, witness],
    );

    let val = b.mk_lam(h2_id, BinderInfo::Default, le_bc, proof);
    let val = b.mk_lam(h1_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.le_trans` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.sub`, `Int.add`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// ENSURES: On success, `Int.le_trans` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_trans` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_trans_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_nonneg_add_proof()?;
        self.register_int_sub_add_sub_cancel_proof()?;

        let c = IntLeTransConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Combines the two `NonNeg`
        // witnesses via the constructive `Int.NonNeg.add`, then transports along
        // `Int.sub_add_sub_cancel a b c : (c-b)+(b-a) = c-a` with `@Eq.subst.{1}`
        // (motive `fun x => Int.NonNeg x`) to obtain `NonNeg (Int.sub c a)` ≡
        // `Int.le a c`. The hypotheses `Int.le a b` / `Int.le b c` delta-reduce
        // to `NonNeg (Int.sub b a)` / `NonNeg (Int.sub c b)`, matching the
        // `Int.NonNeg.add` argument slots up to definitional equality. No
        // `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_le_trans_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_trans_proof()
            .expect("first registration");
        env.register_int_le_trans_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_trans"))
            .expect("Int.le_trans should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_trans_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_le_trans_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.le_trans"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the five outer λ binders, then the head must be Eq.subst.
        let mut body: Expr = value.clone();
        for _ in 0..5 {
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
                "Eq.subst",
                "Int.le_trans proof root must be Eq.subst"
            ),
            k => panic!("expected Const(Eq.subst), got {:?}", k),
        }
    }

    #[test]
    fn test_int_le_trans_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_trans_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_trans"))
            .expect("Int.le_trans is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_trans must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_le_trans_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_le_trans_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_trans"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_trans must be Constructive, got {:?}",
            quality
        );
    }
}
