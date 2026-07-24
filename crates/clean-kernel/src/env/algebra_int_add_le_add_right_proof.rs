// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_le_add_right : ∀ a b : Int, Int.le a b → ∀ c : Int,
//!    Int.le (Int.add a c) (Int.add b c)`.
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
//! So `h : Int.le a b` delta-reduces to `Int.NonNeg (Int.sub b a)` and the goal
//! `Int.le (a + c) (b + c)` to `Int.NonNeg (Int.sub (b + c) (a + c))`.
//!
//! # Proof sketch
//!
//! `Int.add_sub_add_right a b c : Eq Int (Int.sub (b+c) (a+c)) (Int.sub b a)`
//! (`(b+c) - (a+c) = b - a`). Transport `h : NonNeg (Int.sub b a)` along its
//! `Eq.symm` with motive `fun x => Int.NonNeg x`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg x)
//!   (Int.sub b a) (Int.sub (b+c) (a+c))
//!   (@Eq.symm.{1} Int (Int.sub (b+c) (a+c)) (Int.sub b a) (Int.add_sub_add_right a b c))
//!   h
//!   : Int.NonNeg (Int.sub (b+c) (a+c))   ≡   Int.le (a + c) (b + c)
//! ```
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_sub_add_right` theorem and the
//! foundational `Eq.subst` / `Eq.symm`. Neither domain dependency is a
//! `Declaration::Axiom`, so `env.axiom_deps("Int.add_le_add_right")` is empty and
//! `env.proof_quality("Int.add_le_add_right") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddLeAddRightConsts {
    int_type: Expr,
    int_le: Expr,
    int_add: Expr,
    int_sub: Expr,
    nonneg: Expr,
    add_sub_add_right: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl IntAddLeAddRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            add_sub_add_right: Expr::const_(Name::from_string("Int.add_sub_add_right"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
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

/// Build `∀ a b : Int, Int.le a b → ∀ c : Int, Int.le (a+c) (b+c)`.
fn build_type(c: &IntAddLeAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let (h_id, _h) = b.fresh_local(le_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let concl = c.le(c.add(a.clone(), cc.clone()), c.add(bv.clone(), cc.clone()));
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(h_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) (h : Int.le a b) (c : Int) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg x)
///     (Int.sub b a) (Int.sub (b+c) (a+c))
///     (@Eq.symm.{1} Int (Int.sub (b+c) (a+c)) (Int.sub b a) (Int.add_sub_add_right a b c))
///     h
/// ```
fn build_value(c: &IntAddLeAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(le_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    // motive: fun x : Int => Int.NonNeg x
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    let sub_ba = c.sub(bv.clone(), a.clone()); // b - a
    let sub_bcac = c.sub(c.add(bv.clone(), cc.clone()), c.add(a.clone(), cc.clone())); // (b+c)-(a+c)

    // Int.add_sub_add_right a b c : Eq Int ((b+c)-(a+c)) (b-a)
    let id_eq = Expr::apps(
        c.add_sub_add_right.clone(),
        [a.clone(), bv.clone(), cc.clone()],
    );
    // @Eq.symm.{1} Int ((b+c)-(a+c)) (b-a) id_eq : Eq Int (b-a) ((b+c)-(a+c))
    let symm = Expr::apps(
        c.eq_symm.clone(),
        [c.int_type.clone(), sub_bcac.clone(), sub_ba.clone(), id_eq],
    );

    // @Eq.subst.{1} Int motive (b-a) ((b+c)-(a+c)) symm h : NonNeg ((b+c)-(a+c))
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            sub_ba,
            sub_bcac,
            symm,
            h.clone(),
        ],
    );

    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(h_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.add_le_add_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.add`, `Int.sub`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`.
    /// ENSURES: On success, `Int.add_le_add_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_le_add_right` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_add_le_add_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_le_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependency: (b+c) - (a+c) = b - a.
        self.register_int_add_sub_add_right_proof()?;

        let c = IntAddLeAddRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Transports the incoming
        // `h : Int.le a b` (≡ `NonNeg (Int.sub b a)`) along
        // `Eq.symm (Int.add_sub_add_right a b c) : Eq (b-a) ((b+c)-(a+c))` via
        // `@Eq.subst.{1}` with motive `fun x => Int.NonNeg x`, yielding
        // `Int.NonNeg (Int.sub (b+c) (a+c))` ≡ `Int.le (a+c) (b+c)`. No `sorry`,
        // no self-reference, no domain-axiom dependency. Replaces the prior
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
    fn test_int_add_le_add_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_le_add_right_proof()
            .expect("first registration");
        env.register_int_add_le_add_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_le_add_right"))
            .expect("Int.add_le_add_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_le_add_right_proof_body_uses_eq_subst() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_add_le_add_right_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_le_add_right"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the four outer λ binders (a, b, h, c), then the head must be
        // Eq.subst.
        let mut body: Expr = value.clone();
        for _ in 0..4 {
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
                "Int.add_le_add_right proof root must be Eq.subst"
            ),
            k => panic!("expected Const(Eq.subst), got {:?}", k),
        }
    }

    #[test]
    fn test_int_add_le_add_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_le_add_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_le_add_right"))
            .expect("Int.add_le_add_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_le_add_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_add_le_add_right_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_add_le_add_right_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.add_le_add_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_le_add_right must be Constructive, got {:?}",
            quality
        );
    }
}
