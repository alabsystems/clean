// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.right_distrib : ∀ a b c : Nat,
//!     Eq (Nat.mul (Nat.add a b) c) (Nat.add (Nat.mul a c) (Nat.mul b c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term reduces right-distributivity to LEFT-distributivity via
//! commutativity, threading four `Eq.trans` rewrites (no induction needed
//! here — the induction lives in the constructive `Nat.left_distrib` /
//! `Nat.mul_comm` dependencies).
//!
//! # Proof sketch
//!
//! ```text
//! Nat.mul (a + b) c
//!   = Nat.mul c (a + b)                              -- Nat.mul_comm (a+b) c        (s1)
//!   = Nat.add (Nat.mul c a) (Nat.mul c b)            -- Nat.left_distrib c a b       (s2)
//!   = Nat.add (Nat.mul a c) (Nat.mul c b)            -- congr (Nat.mul_comm c a)     (s3a)
//!   = Nat.add (Nat.mul a c) (Nat.mul b c)            -- congr (Nat.mul_comm c b)     (s3b)
//! ```
//!
//! Concretely, the proof term is
//!
//! ```text
//! λ (a b c : Nat) => Eq.trans (Eq.trans (Eq.trans s1 s2) s3a) s3b
//! ```
//!
//! where
//! - `s1 := Nat.mul_comm (Nat.add a b) c
//!        : Eq (Nat.mul (Nat.add a b) c) (Nat.mul c (Nat.add a b))`,
//! - `s2 := Nat.left_distrib c a b
//!        : Eq (Nat.mul c (Nat.add a b)) (Nat.add (Nat.mul c a) (Nat.mul c b))`,
//! - `s3a := congrArg (λ x => Nat.add x (Nat.mul c b)) (Nat.mul_comm c a)
//!        : Eq (Nat.add (Nat.mul c a) (Nat.mul c b))
//!             (Nat.add (Nat.mul a c) (Nat.mul c b))`,
//! - `s3b := congrArg (λ x => Nat.add (Nat.mul a c) x) (Nat.mul_comm c b)
//!        : Eq (Nat.add (Nat.mul a c) (Nat.mul c b))
//!             (Nat.add (Nat.mul a c) (Nat.mul b c))`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.trans`, `congrArg`, `Nat`, `Nat.add`,
//! `Nat.mul`, `Nat.mul_comm` (constructive `Declaration::Theorem`, #3604),
//! and `Nat.left_distrib` (constructive `Declaration::Theorem`, #3604).
//! None are `Declaration::Axiom`, so `env.axiom_deps("Nat.right_distrib")`
//! is empty and
//! `env.proof_quality("Nat.right_distrib") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_nat_left_distrib_proof.rs` (dependency — Nat.left_distrib).
//! - `algebra_nat_mul_comm_proof.rs` (#3604, dependency — Nat.mul_comm).
//! - `algebra_nat_mul_succ_proof.rs` (#3604, same Eq.trans-chain shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatRightDistribConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_mul_comm: Expr,
    nat_left_distrib: Expr,
}

impl NatRightDistribConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_mul_comm: Expr::const_(Name::from_string("Nat.mul_comm"), vec![]),
            nat_left_distrib: Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }

    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.nat_type.clone(), x, y, z, h1, h2],
        )
    }
}

/// Build
/// `∀ a b c : Nat, Eq Nat (Nat.mul (Nat.add a b) c) (Nat.add (Nat.mul a c) (Nat.mul b c))`.
fn build_type(c: &NatRightDistribConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let (cv_id, cv) = b.fresh_local(c.nat_type.clone());
    let lhs = c.mul(c.add(a.clone(), bv.clone()), cv.clone());
    let rhs = c.add(c.mul(a.clone(), cv.clone()), c.mul(bv.clone(), cv));
    let concl = c.eq_nat(lhs, rhs);
    let ty_raw = b.mk_pi(cv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Body: `λ (a b c : Nat) => Eq.trans (Eq.trans (Eq.trans s1 s2) s3a) s3b`.
fn build_value(c: &NatRightDistribConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = vb.fresh_local(c.nat_type.clone());
    let (cv_id, cv) = vb.fresh_local(c.nat_type.clone());

    // Named subexpressions.
    let a_plus_b = c.add(a.clone(), bv.clone());
    let mul_ab_c = c.mul(a_plus_b.clone(), cv.clone()); // (a+b)*c
    let mul_c_ab = c.mul(cv.clone(), a_plus_b.clone()); // c*(a+b)
    let mul_c_a = c.mul(cv.clone(), a.clone());
    let mul_c_b = c.mul(cv.clone(), bv.clone());
    let mul_a_c = c.mul(a.clone(), cv.clone());
    let mul_b_c = c.mul(bv.clone(), cv.clone());
    let add_ca_cb = c.add(mul_c_a.clone(), mul_c_b.clone());
    let add_ac_cb = c.add(mul_a_c.clone(), mul_c_b.clone());
    let add_ac_bc = c.add(mul_a_c.clone(), mul_b_c.clone());

    // s1 := Nat.mul_comm (a+b) c : Eq ((a+b)*c) (c*(a+b))
    let s1 = Expr::apps(c.nat_mul_comm.clone(), [a_plus_b.clone(), cv.clone()]);

    // s2 := Nat.left_distrib c a b : Eq (c*(a+b)) ((c*a) + (c*b))
    let s2 = Expr::apps(
        c.nat_left_distrib.clone(),
        [cv.clone(), a.clone(), bv.clone()],
    );

    // s3a := congrArg (λ x => Nat.add x (c*b)) (Nat.mul_comm c a)
    //      : Eq ((c*a) + (c*b)) ((a*c) + (c*b))
    let func_s3a = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = fb.fresh_local(c.nat_type.clone());
        let body = c.add(x, mul_c_b.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
        fb.finish_child(lam)
    };
    let comm_c_a = Expr::apps(c.nat_mul_comm.clone(), [cv.clone(), a.clone()]);
    let s3a = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            mul_c_a.clone(),
            mul_a_c.clone(),
            func_s3a,
            comm_c_a,
        ],
    );

    // s3b := congrArg (λ x => Nat.add (a*c) x) (Nat.mul_comm c b)
    //      : Eq ((a*c) + (c*b)) ((a*c) + (b*c))
    let func_s3b = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = fb.fresh_local(c.nat_type.clone());
        let body = c.add(mul_a_c.clone(), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
        fb.finish_child(lam)
    };
    let comm_c_b = Expr::apps(c.nat_mul_comm.clone(), [cv.clone(), bv.clone()]);
    let s3b = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            mul_c_b.clone(),
            mul_b_c.clone(),
            func_s3b,
            comm_c_b,
        ],
    );

    // t1 := Eq.trans (a+b)*c  c*(a+b)  ((c*a)+(c*b))  s1 s2
    let t1 = c.trans(mul_ab_c.clone(), mul_c_ab, add_ca_cb.clone(), s1, s2);
    // t2 := Eq.trans (a+b)*c  ((c*a)+(c*b))  ((a*c)+(c*b))  t1 s3a
    let t2 = c.trans(mul_ab_c.clone(), add_ca_cb, add_ac_cb.clone(), t1, s3a);
    // t3 := Eq.trans (a+b)*c  ((a*c)+(c*b))  ((a*c)+(b*c))  t2 s3b
    let t3 = c.trans(mul_ab_c, add_ac_cb, add_ac_bc, t2, s3b);

    let val_raw = vb.mk_lam(cv_id, BinderInfo::Default, c.nat_type.clone(), t3);
    let val_raw = vb.mk_lam(b_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.right_distrib` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.add`, `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// REQUIRES: `Nat.mul_comm` and `Nat.left_distrib` are registered as
    ///           `Declaration::Theorem` (constructive — see
    ///           `register_nat_mul_comm_proof` / `register_nat_left_distrib_proof`).
    /// ENSURES: On success, `Nat.right_distrib` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.right_distrib` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_right_distrib_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.right_distrib");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_mul_comm_proof()?;
        self.register_nat_left_distrib_proof()?;

        let c = NatRightDistribConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Reduces
        // right-distributivity to constructive `Nat.left_distrib` via
        // `Nat.mul_comm`, threading four `Eq.trans` rewrites:
        //   s1  := Nat.mul_comm (a+b) c
        //   s2  := Nat.left_distrib c a b
        //   s3a := congrArg (λ x => Nat.add x (c*b)) (Nat.mul_comm c a)
        //   s3b := congrArg (λ x => Nat.add (a*c) x) (Nat.mul_comm c b)
        // No `sorry`, no self-reference, no domain-axiom dependency
        // (`Nat.mul_comm` / `Nat.left_distrib` are both constructive #3604).
        // Replaces the prior `Declaration::Axiom` in
        // `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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
    fn test_nat_right_distrib_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_right_distrib_proof()
            .expect("first registration");
        env.register_nat_right_distrib_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.right_distrib"))
            .expect("Nat.right_distrib should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction. Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_nat_right_distrib_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_right_distrib_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.right_distrib"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.right_distrib proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// After peeling three outer λ binders, the proof root is `@Eq.trans.{1}`
    /// (the right-distributivity rewrite chain). Guards against a trivial
    /// axiom-reference masquerade.
    #[test]
    fn test_nat_right_distrib_proof_uses_eq_trans() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_right_distrib_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.right_distrib"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let b1 = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ a, got {:?}", k),
        };
        let b2 = match b1.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ b, got {:?}", k),
        };
        let b3 = match b2.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ c, got {:?}", k),
        };
        let mut head = b3.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Eq.trans",
                "Nat.right_distrib proof root must be Eq.trans, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Eq.trans, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof). `Nat.mul_comm` and
    /// `Nat.left_distrib` are constructive (#3604), so `Nat.right_distrib`
    /// inherits empty deps.
    #[test]
    fn test_nat_right_distrib_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_right_distrib_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.right_distrib"))
            .expect("Nat.right_distrib is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.right_distrib must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
