// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.right_distrib : ∀ a b c : Int,
//!     Eq Int (Int.mul (Int.add a b) c) (Int.add (Int.mul a c) (Int.mul b c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` derived from the
//! now-constructive `Int.left_distrib` and `Int.mul_comm` — no fresh
//! induction.
//!
//! # Proof sketch
//!
//! ```text
//! e1 := Int.mul_comm (add a b) c
//!     : Eq (mul (add a b) c) (mul c (add a b))
//! e2 := Int.left_distrib c a b
//!     : Eq (mul c (add a b)) (add (mul c a) (mul c b))
//! e3a := congrArg (λ x => add x (mul c b)) (Int.mul_comm c a)
//!     : Eq (add (mul c a) (mul c b)) (add (mul a c) (mul c b))
//! e3b := congrArg (λ y => add (mul a c) y) (Int.mul_comm c b)
//!     : Eq (add (mul a c) (mul c b)) (add (mul a c) (mul b c))
//! ```
//!
//! Chaining `Eq.trans e1 (Eq.trans e2 (Eq.trans e3a e3b))` yields
//! `Eq (mul (add a b) c) (add (mul a c) (mul b c))`.
//!
//! # Axiom closure
//!
//! Mentions only `Eq`, `Eq.trans`, `congrArg`, `Int`, `Int.add`, `Int.mul`
//! and the constructive `Declaration::Theorem`s `Int.left_distrib` and
//! `Int.mul_comm` (#3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.right_distrib")` is empty and the proof quality is
//! `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling: `algebra_int_left_distrib_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntRightDistribConsts {
    int_type: Expr,
    int_add: Expr,
    int_mul: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    int_mul_comm: Expr,
    int_left_distrib: Expr,
}

impl IntRightDistribConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            int_mul_comm: Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
            int_left_distrib: Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `congrArg Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    fn congr_arg_int(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    /// `Int.mul_comm x y : Eq (mul x y) (mul y x)`.
    fn mul_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul_comm.clone(), [x, y])
    }

    /// `Int.left_distrib x y z : Eq (mul x (add y z)) (add (mul x y)(mul x z))`.
    fn left_distrib(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::apps(self.int_left_distrib.clone(), [x, y, z])
    }
}

/// `∀ a b c : Int, Eq (mul (add a b) c) (add (mul a c) (mul b c))`.
fn build_type(c: &IntRightDistribConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());
    let lhs = c.mul(c.add(a.clone(), bv.clone()), cv.clone());
    let rhs = c.add(c.mul(a.clone(), cv.clone()), c.mul(bv.clone(), cv.clone()));
    let concl = c.eq_int(lhs, rhs);
    let ty = b.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty);
    b.finish(ty)
}

/// Body: `λ (a b c : Int) => Eq.trans e1 (Eq.trans e2 (Eq.trans e3a e3b))`.
fn build_value(c: &IntRightDistribConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = vb.fresh_local(c.int_type.clone());

    let ab = c.add(a.clone(), bv.clone());
    let mul_ab_c = c.mul(ab.clone(), cv.clone());
    let mul_c_ab = c.mul(cv.clone(), ab.clone());
    let mul_c_a = c.mul(cv.clone(), a.clone());
    let mul_c_b = c.mul(cv.clone(), bv.clone());
    let mul_a_c = c.mul(a.clone(), cv.clone());
    let mul_b_c = c.mul(bv.clone(), cv.clone());

    // e1 : mul (add a b) c = mul c (add a b)
    let e1 = c.mul_comm(ab.clone(), cv.clone());
    // e2 : mul c (add a b) = add (mul c a)(mul c b)
    let e2 = c.left_distrib(cv.clone(), a.clone(), bv.clone());

    // e3a : add (mul c a)(mul c b) = add (mul a c)(mul c b)
    let f_a = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = fb.fresh_local(c.int_type.clone());
        let body = c.add(x, mul_c_b.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let e3a = c.congr_arg_int(
        mul_c_a.clone(),
        mul_a_c.clone(),
        f_a,
        c.mul_comm(cv.clone(), a.clone()),
    );
    // e3b : add (mul a c)(mul c b) = add (mul a c)(mul b c)
    let f_b = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (y_id, y) = fb.fresh_local(c.int_type.clone());
        let body = c.add(mul_a_c.clone(), y);
        let lam = fb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let e3b = c.congr_arg_int(
        mul_c_b.clone(),
        mul_b_c.clone(),
        f_b,
        c.mul_comm(cv.clone(), bv.clone()),
    );

    let add_ca_cb = c.add(mul_c_a, mul_c_b.clone());
    let add_ac_cb = c.add(mul_a_c.clone(), mul_c_b);
    let add_ac_bc = c.add(mul_a_c, mul_b_c);

    // e3 := Eq.trans e3a e3b : add (mul c a)(mul c b) = add (mul a c)(mul b c)
    let e3 = c.trans_int(add_ca_cb.clone(), add_ac_cb, add_ac_bc.clone(), e3a, e3b);
    // t2 := Eq.trans e2 e3 : mul c (add a b) = add (mul a c)(mul b c)
    let t2 = c.trans_int(mul_c_ab.clone(), add_ca_cb, add_ac_bc.clone(), e2, e3);
    // proof := Eq.trans e1 t2 : mul (add a b) c = add (mul a c)(mul b c)
    let proof = c.trans_int(mul_ab_c, mul_c_ab, add_ac_bc, e1, t2);

    let val = vb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = vb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Int.right_distrib` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.add`,
    ///           `Int.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// REQUIRES: `Int.left_distrib` and `Int.mul_comm` are registered as
    ///           constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.right_distrib` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_right_distrib_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.right_distrib");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_left_distrib_proof()?;
        self.register_int_mul_comm_proof()?;

        let c = IntRightDistribConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). No fresh
        // induction: a four-step `Eq.trans` chain composing constructive
        // `Int.mul_comm` (to flip `(a+b)*c` into `c*(a+b)`), constructive
        // `Int.left_distrib c a b`, and two `congrArg`-lifted `Int.mul_comm`
        // rewrites (`c*a → a*c`, `c*b → b*c`). No `sorry`, no self-reference,
        // no domain-axiom dependency (`Int.left_distrib` and `Int.mul_comm`
        // are constructive #3604). Replaces the prior `Declaration::Axiom` in
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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_right_distrib_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_right_distrib_proof()
            .expect("first registration");
        env.register_int_right_distrib_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.right_distrib"))
            .expect("Int.right_distrib should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_right_distrib_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_right_distrib_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.right_distrib"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.right_distrib proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_int_right_distrib_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_right_distrib_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.right_distrib"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.right_distrib must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_right_distrib_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_right_distrib_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.right_distrib"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.right_distrib must be Constructive, got {:?}",
            quality
        );
    }
}
