// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_right_cancel : ∀ a b c : Int, Eq (Int.add a b) (Int.add c b) → Eq a c`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem`. Unlike the Nat
//! cancellation law, this is a purely algebraic (non-inductive) derivation: it
//! adds `-b` to both sides of the hypothesis and collapses with the
//! right-cancellation identity `Int.add_neg_cancel_right`.
//!
//! # Proof sketch
//!
//! Let `nb := Int.neg b`. The right-cancellation identity gives
//! `Int.add_neg_cancel_right x b : Eq (Int.add (Int.add x b) nb) x` for any `x`.
//! From the hypothesis `h : Eq (Int.add a b) (Int.add c b)`:
//!
//! ```text
//! s0 := Int.add_neg_cancel_right a b
//!     : Eq (Int.add (Int.add a b) nb) a
//! s1 := Eq.symm s0
//!     : Eq a (Int.add (Int.add a b) nb)
//! s2 := congrArg (λ x => Int.add x nb) h
//!     : Eq (Int.add (Int.add a b) nb) (Int.add (Int.add c b) nb)
//! s3 := Int.add_neg_cancel_right c b
//!     : Eq (Int.add (Int.add c b) nb) c
//! ```
//!
//! and the proof term is
//!
//! ```text
//! λ (a b c : Int) (h : Eq (Int.add a b) (Int.add c b)) =>
//!   Eq.trans s1 (Eq.trans s2 s3)   : Eq a c
//! ```
//!
//! # Axiom closure
//!
//! The proof mentions only `Int`, `Int.add`, `Int.neg`, `Eq`, `Eq.symm`,
//! `Eq.trans`, `congrArg`, and `Int.add_neg_cancel_right` (a constructive
//! `Declaration::Theorem`, #3604, whose own closure is empty). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.add_right_cancel")` is empty
//! and `env.proof_quality("Int.add_right_cancel") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (cancellation-law demotion). Dependency:
//! `algebra_int_add_neg_cancel_right_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddRightCancelConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_add_neg_cancel_right: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntAddRightCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_add_neg_cancel_right: Expr::const_(
                Name::from_string("Int.add_neg_cancel_right"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
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

    /// `Eq.symm Int x y h : Eq Int y x`.
    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), x, y, h])
    }

    /// `Eq.trans Int x y z h1 h2 : Eq Int x z`.
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `Int.add_neg_cancel_right x b : Eq Int ((x + b) + (-b)) x`.
    fn cancel_right(&self, x: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_add_neg_cancel_right.clone(), [x, b])
    }
}

/// Build `∀ a b c : Int, Eq (Int.add a b) (Int.add c b) → Eq a c`.
fn build_type(c: &IntAddRightCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());
    let hyp = c.eq_int(c.add(a.clone(), bv.clone()), c.add(cv.clone(), bv.clone()));
    let concl = c.eq_int(a.clone(), cv.clone());
    let body = {
        let (h_id, _h) = b.fresh_local(hyp.clone());
        b.mk_pi(h_id, BinderInfo::Default, hyp, concl)
    };
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let e = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), e);
    b.finish(e)
}

/// Body:
/// `λ (a b c : Int) (h : Eq (a+b) (c+b)) => Eq.trans s1 (Eq.trans s2 s3)`.
fn build_value(c: &IntAddRightCancelConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (b_id, bv) = vb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = vb.fresh_local(c.int_type.clone());
    let hyp = c.eq_int(c.add(a.clone(), bv.clone()), c.add(cv.clone(), bv.clone()));
    let (h_id, h) = vb.fresh_local(hyp.clone());

    let nb = c.neg(bv.clone());
    let ab = c.add(a.clone(), bv.clone()); // a + b
    let cb = c.add(cv.clone(), bv.clone()); // c + b
    let ab_nb = c.add(ab.clone(), nb.clone()); // (a + b) + (-b)
    let cb_nb = c.add(cb.clone(), nb.clone()); // (c + b) + (-b)

    // s0 := Int.add_neg_cancel_right a b : Eq ((a+b)+nb) a
    let s0 = c.cancel_right(a.clone(), bv.clone());
    // s1 := Eq.symm s0 : Eq a ((a+b)+nb)
    let s1 = c.symm(ab_nb.clone(), a.clone(), s0);

    // func := λ (x : Int) => Int.add x nb
    let func = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = fb.fresh_local(c.int_type.clone());
        let body = c.add(x, nb.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };

    // s2 := congrArg Int Int (a+b) (c+b) func h
    //     : Eq ((a+b)+nb) ((c+b)+nb)
    let s2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            ab.clone(),
            cb.clone(),
            func,
            h.clone(),
        ],
    );

    // s3 := Int.add_neg_cancel_right c b : Eq ((c+b)+nb) c
    let s3 = c.cancel_right(cv.clone(), bv.clone());

    // inner := Eq.trans ((a+b)+nb) ((c+b)+nb) c s2 s3 : Eq ((a+b)+nb) c
    let inner = c.trans(ab_nb.clone(), cb_nb, cv.clone(), s2, s3);

    // result := Eq.trans a ((a+b)+nb) c s1 inner : Eq a c
    let result = c.trans(a.clone(), ab_nb, cv.clone(), s1, inner);

    let lam_h = vb.mk_lam(h_id, BinderInfo::Default, hyp, result);
    let lam_c = vb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), lam_h);
    let lam_b = vb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), lam_c);
    let lam_a = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), lam_b);
    vb.finish(lam_a)
}

impl Environment {
    /// Register `Int.add_right_cancel` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`, `Eq.trans`,
    ///           `congrArg`.
    /// REQUIRES: `Int`, `Int.add`, `Int.neg` are registered.
    /// REQUIRES: `Int.add_neg_cancel_right` is a constructive
    ///           `Declaration::Theorem` (see `register_int_add_neg_cancel_right_proof`).
    /// ENSURES: On success, `Int.add_right_cancel` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_right_cancel` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_add_right_cancel_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_right_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.register_int_add_neg_cancel_right_proof()?;

        let c = IntAddRightCancelConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Purely algebraic
        // (non-inductive) derivation: add `-b` to both sides of the hypothesis
        // and collapse with the right-cancellation identity
        // `Int.add_neg_cancel_right`. The proof chains
        //   s1 := Eq.symm (Int.add_neg_cancel_right a b)
        //   s2 := congrArg (λ x => Int.add x (Int.neg b)) h
        //   s3 := Int.add_neg_cancel_right c b
        // via two `Eq.trans` steps. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Int.add_neg_cancel_right` is itself
        // constructive #3604). Replaces the prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs`.
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
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the algebraic `Eq.trans` chain; registered as a Theorem
    /// (not Axiom), idempotently.
    #[test]
    fn test_int_add_right_cancel_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_right_cancel_proof()
            .expect("first registration");
        env.register_int_add_right_cancel_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_right_cancel"))
            .expect("Int.add_right_cancel should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Int.add_right_cancel"),
                vec![],
            ))
            .expect("Int.add_right_cancel should type-check");
    }

    /// After peeling four λ binders (a, b, c, h), the proof root is `Eq.trans`
    /// — guards against an axiom-reference / `Eq.refl` masquerade.
    #[test]
    fn test_int_add_right_cancel_proof_uses_eq_trans() {
        let mut env = Environment::new();
        env.register_int_add_right_cancel_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.add_right_cancel"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..4 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Eq.trans",
                "Int.add_right_cancel proof root must be Eq.trans"
            ),
            k => panic!("expected Const(Eq.trans, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive). `Int.add_neg_cancel_right` is
    /// constructive, so the cancellation law inherits empty domain-axiom deps.
    #[test]
    fn test_int_add_right_cancel_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_right_cancel_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_right_cancel"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_right_cancel must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Int.add_right_cancel"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
