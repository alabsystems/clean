// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotion of `Int.mul_left_cancel_ofNat_succ` — the last
//! `Declaration::Axiom` in `data_types_int_lemmas.rs`.
//!
//! ```text
//! Int.mul_left_cancel_ofNat_succ :
//!   ∀ (n : Nat) (a b : Int),
//!     Eq (Int.mul (Int.ofNat (Nat.succ n)) a) (Int.mul (Int.ofNat (Nat.succ n)) b)
//!       → Eq a b
//! ```
//!
//! # Proof route (reduction to `Nat` cancellation)
//!
//! Write `s := Int.ofNat (Nat.succ n)` — a *positive* scalar. The proof is a
//! nested `@Int.rec.{0}` (outer on `a`, inner on `b`) with four constructor
//! leaves. The kernel reduces `Int.mul s ·` on each constructor:
//!
//! - `Int.mul s (Int.ofNat m)  ≡ Int.ofNat (Nat.mul (Nat.succ n) m)`,
//! - `Int.mul s (Int.negSucc q) ≡ Int.negOfNat (Nat.mul (Nat.succ n) (Nat.succ q))`
//!   `≡ Int.negSucc (Nat.add (Nat.mul (Nat.succ n) q) n)`
//!   (since `Nat.mul x (succ q) ≡ Nat.add (Nat.mul x q) x` and
//!    `Nat.add y (succ n) ≡ Nat.succ (Nat.add y n)`, so the magnitude is a
//!    `Nat.succ`, hence `negOfNat` lands on the `negSucc` branch).
//!
//! So a positive scalar *preserves the constructor* of its operand. The four
//! leaves are therefore:
//!
//! - `(ofNat m, ofNat p)`: hypothesis `ofNat ((n+1)*m) = ofNat ((n+1)*p)`.
//!   `Int.noConfusion` extracts the field equality `(n+1)*m = (n+1)*p`,
//!   `Nat.mul_left_cancel_succ` cancels the positive factor to `m = p`, and
//!   `congrArg Int.ofNat` lifts back to `ofNat m = ofNat p`.
//! - `(negSucc m, negSucc p)`: hypothesis `ofNat ((n+1)*(m+1)) = ofNat ((n+1)*(p+1))`.
//!   Same `noConfusion` + `Nat.mul_left_cancel_succ` gives `m+1 = p+1`, and
//!   `congrArg Int.negSucc` lifts to `negSucc m = negSucc p`.
//! - `(ofNat m, negSucc p)` and `(negSucc m, ofNat p)`: the two sides have
//!   *different* constructors, so `Int.noConfusionType P · ·` reduces directly
//!   to `P` (the goal) — `Int.noConfusion` discharges the impossible-equality
//!   leaf with no continuation.
//!
//! # Axiom closure
//!
//! The proof mentions only `Int`, `Int.ofNat`, `Int.negSucc`, `Int.mul`,
//! `Int.rec`, `Int.noConfusion` (a generated reducible definition, not an
//! `Axiom`), `Nat`, `Nat.succ`, `Nat.mul`, `Eq`, `congrArg`, and the
//! constructive `Nat.mul_left_cancel_succ`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.mul_left_cancel_ofNat_succ")` is empty and
//! `env.proof_quality(..) == ProofQuality::Constructive`.
//!
//! Tracks #3604 (cancellation-law demotion). No `Int.le` / `Int.NonNeg`
//! ordering machinery is touched — the cancellation is purely a magnitude
//! `Nat` argument behind the sign-preserving positive scalar.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the cancellation proof.
struct IntMulCancelConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    int_rec: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    eq_const: Expr,
    congr_arg: Expr,
    /// `Int.noConfusion.{0}` — Prop-valued continuation/result `P`.
    int_no_confusion: Expr,
    /// `Nat.mul_left_cancel_succ` (constructive #3604 Theorem).
    nat_mul_cancel: Expr,
    /// `Nat.succ_inj` (constructive #3604 Theorem).
    nat_succ_inj: Expr,
    /// `Nat.pred` — used to name the genuine `Int.negSucc` field (def-eq to
    /// `Nat.pred (Nat.mul (succ n) (succ m))`) that `Int.noConfusion` extracts.
    nat_pred: Expr,
}

impl IntMulCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            // `Int.rec.{0}` — Prop motive (the conclusion is in Prop).
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            // `congrArg.{1,1}` — Nat and Int both live in `Sort 1`.
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            int_no_confusion: Expr::const_(
                Name::from_string("Int.noConfusion"),
                vec![Level::zero()],
            ),
            nat_mul_cancel: Expr::const_(Name::from_string("Nat.mul_left_cancel_succ"), vec![]),
            nat_succ_inj: Expr::const_(Name::from_string("Nat.succ_inj"), vec![]),
            nat_pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
        }
    }

    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }

    fn of_nat(&self, x: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), x)
    }

    fn neg_succ(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), x)
    }

    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [x, y])
    }

    fn imul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }

    fn pred(&self, x: Expr) -> Expr {
        Expr::app(self.nat_pred.clone(), x)
    }

    /// `@congrArg.{1,1} Nat Int x y f h : Eq Int (f x) (f y)`.
    fn congr_arg_nat_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat_type.clone(), self.int_type.clone(), x, y, f, h],
        )
    }

    /// `@congrArg.{1,1} Nat Nat x y f h : Eq Nat (f x) (f y)`.
    fn congr_arg_nat_nat(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat_type.clone(), self.nat_type.clone(), x, y, f, h],
        )
    }

    /// `Nat.mul_left_cancel_succ n x y h : Eq Nat x y`
    /// (from `Eq Nat (Nat.mul (succ n) x) (Nat.mul (succ n) y)`).
    fn nat_cancel(&self, n: Expr, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_mul_cancel.clone(), [n, x, y, h])
    }

    /// `Nat.succ_inj x y h : Eq Nat x y` (from `Eq Nat (succ x) (succ y)`).
    fn nat_succ_inj(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_succ_inj.clone(), [x, y, h])
    }
}

/// `∀ (n : Nat) (a b : Int), Eq (mul s a) (mul s b) → Eq a b` where
/// `s = Int.ofNat (Nat.succ n)`.
fn build_type(c: &IntMulCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let scale = c.of_nat(c.succ(n.clone()));
    let h_type = c.eq_int(c.imul(scale.clone(), a.clone()), c.imul(scale, bv.clone()));
    let (h_id, _h) = b.fresh_local(h_type.clone());
    let concl = c.eq_int(a.clone(), bv.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Int.mul_left_cancel_ofNat_succ` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.mul`, `Int.rec`, `Int.noConfusion`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`, `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `congrArg`.
    /// REQUIRES: `Nat.mul_left_cancel_succ` is registered as a constructive
    ///           `Declaration::Theorem` (see `register_nat_mul_left_cancel_succ_proof`).
    /// ENSURES: On success, `Int.mul_left_cancel_ofNat_succ` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if it is already a `Theorem`, returns `Ok(())`.
    pub(crate) fn register_int_mul_left_cancel_ofnat_succ_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_left_cancel_ofNat_succ");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_mul_left_cancel_succ_proof()?;
        self.register_nat_succ_inj_proof()?;
        // `Int.noConfusion` may be missing in minimal environments that have
        // not run a full prelude; regenerate it from the inductive declaration.
        if self
            .get_const(&Name::from_string("Int.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let c = IntMulCancelConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` (outer on `a`, inner on `b`). The positive scalar
        // `Int.ofNat (Nat.succ n)` preserves the operand constructor under
        // `Int.mul`, so the two same-sign leaves reduce to a `Nat` magnitude
        // equality discharged by the constructive `Nat.mul_left_cancel_succ`
        // (after `Int.noConfusion` constructor-injectivity) and re-lifted by
        // `congrArg`; the two mixed-sign leaves are impossible equalities that
        // `Int.noConfusion` discharges directly (cross-constructor
        // `noConfusionType` reduces to the goal `P`). No `sorry`, no
        // self-reference, no domain-axiom dependency — `Int.noConfusion` is a
        // generated reducible definition and `Nat.mul_left_cancel_succ` is a
        // constructive Theorem. Replaces the prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_arith_lemmas`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// `λ (n : Nat) (a b : Int) (H : Eq (mul s a) (mul s b)) =>`
/// `  (@Int.rec.{0} outer_motive outer_ofNat outer_negSucc a) b H`.
fn build_value(c: &IntMulCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let scale = c.of_nat(c.succ(n.clone()));
    let h_type = c.eq_int(c.imul(scale.clone(), a.clone()), c.imul(scale, bv.clone()));
    let (h_id, h) = b.fresh_local(h_type.clone());

    let outer_motive = build_outer_motive(c, &b, &n);
    let outer_ofnat = build_outer_ofnat_case(c, &b, &n);
    let outer_negsucc = build_outer_negsucc_case(c, &b, &n);

    // (@Int.rec.{0} motive ofNatCase negSuccCase a) b H
    let rec_app = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, a.clone()],
    );
    let applied = Expr::apps(rec_app, [bv.clone(), h.clone()]);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_type, applied);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

/// Outer `@Int.rec` motive:
/// `fun (x : Int) => ∀ (y : Int), Eq (mul s x) (mul s y) → Eq x y`.
fn build_outer_motive(c: &IntMulCancelConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let scale = c.of_nat(c.succ(n.clone()));
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let inner = {
        let mut yb = EnvDeclBuilder::child_of(&mb);
        let (y_id, y) = yb.fresh_local(c.int_type.clone());
        let h_type = c.eq_int(
            c.imul(scale.clone(), x.clone()),
            c.imul(scale.clone(), y.clone()),
        );
        let (h_id, _h) = yb.fresh_local(h_type.clone());
        let concl = c.eq_int(x.clone(), y.clone());
        let pi_h = yb.mk_pi(h_id, BinderInfo::Default, h_type, concl);
        let pi_y = yb.mk_pi(y_id, BinderInfo::Default, c.int_type.clone(), pi_h);
        yb.finish_child(pi_y)
    };
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), inner);
    mb.finish_child(lam)
}

/// Inner motive for a fixed outer operand `outer = ofNat m` / `negSucc m`:
/// `fun (y : Int) => Eq (mul s outer) (mul s y) → Eq outer y`.
fn build_inner_motive(
    c: &IntMulCancelConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    outer: &Expr,
) -> Expr {
    let scale = c.of_nat(c.succ(n.clone()));
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = mb.fresh_local(c.int_type.clone());
    let h_type = c.eq_int(
        c.imul(scale.clone(), outer.clone()),
        c.imul(scale, y.clone()),
    );
    let (h_id, _h) = mb.fresh_local(h_type.clone());
    let concl = c.eq_int(outer.clone(), y.clone());
    let pi_h = mb.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), pi_h);
    mb.finish_child(lam)
}

/// Outer `ofNat` case: `fun (m : Nat) =>` the inner `Int.rec` on `y`.
fn build_outer_ofnat_case(c: &IntMulCancelConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let scale = c.of_nat(c.succ(n.clone()));
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = mb.fresh_local(c.nat_type.clone());
    let outer = c.of_nat(m.clone());

    let inner_motive = build_inner_motive(c, &mb, n, &outer);

    // Inner ofNat leaf (diagonal): same-sign `ofNat`/`ofNat`.
    let inner_ofnat = {
        let mut pb = EnvDeclBuilder::child_of(&mb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let inner_op = c.of_nat(p.clone());
        // H : Eq Int (mul s (ofNat m)) (mul s (ofNat p)).
        let h_type = c.eq_int(
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
        );
        let (h_id, h) = pb.fresh_local(h_type.clone());
        // Goal: Eq Int (ofNat m) (ofNat p).
        let goal = c.eq_int(outer.clone(), inner_op.clone());
        // Magnitudes (mul s (ofNat ·) ≡ ofNat ((n+1)*·)); cancel factors m/p.
        let mag_m = c.nmul(c.succ(n.clone()), m.clone());
        let mag_p = c.nmul(c.succ(n.clone()), p.clone());
        let body = same_sign_leaf(
            c,
            &pb,
            n,
            &outer,
            &inner_op,
            &h,
            &mag_m,
            &mag_p,
            &m,
            &p,
            LiftCtor::OfNat,
        );
        let _ = &goal; // goal pinned by the kernel against the leaf's expected type.
        let lam = pb.mk_lam(h_id, BinderInfo::Default, h_type, body);
        pb.finish_child(lam_with_p(&pb, p_id, lam))
    };

    // Inner negSucc leaf (mixed sign): `ofNat`/`negSucc` — impossible.
    let inner_negsucc = {
        let mut qb = EnvDeclBuilder::child_of(&mb);
        let (q_id, q) = qb.fresh_local(c.nat_type.clone());
        let inner_op = c.neg_succ(q.clone());
        let h_type = c.eq_int(
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
        );
        let (h_id, h) = qb.fresh_local(h_type.clone());
        let goal = c.eq_int(outer.clone(), inner_op.clone());
        let body = mixed_sign_leaf(
            c,
            goal,
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
            h,
        );
        let lam = qb.mk_lam(h_id, BinderInfo::Default, h_type, body);
        qb.finish_child(lam_with_p(&qb, q_id, lam))
    };

    let inner_rec = Expr::apps(
        c.int_rec.clone(),
        [inner_motive, inner_ofnat, inner_negsucc],
    );
    let lam = mb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), inner_rec);
    mb.finish_child(lam)
}

/// Outer `negSucc` case: `fun (m : Nat) =>` the inner `Int.rec` on `y`.
fn build_outer_negsucc_case(c: &IntMulCancelConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let scale = c.of_nat(c.succ(n.clone()));
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = mb.fresh_local(c.nat_type.clone());
    let outer = c.neg_succ(m.clone());

    let inner_motive = build_inner_motive(c, &mb, n, &outer);

    // Inner ofNat leaf (mixed sign): `negSucc`/`ofNat` — impossible.
    let inner_ofnat = {
        let mut pb = EnvDeclBuilder::child_of(&mb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let inner_op = c.of_nat(p.clone());
        let h_type = c.eq_int(
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
        );
        let (h_id, h) = pb.fresh_local(h_type.clone());
        let goal = c.eq_int(outer.clone(), inner_op.clone());
        let body = mixed_sign_leaf(
            c,
            goal,
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
            h,
        );
        let lam = pb.mk_lam(h_id, BinderInfo::Default, h_type, body);
        pb.finish_child(lam_with_p(&pb, p_id, lam))
    };

    // Inner negSucc leaf (diagonal): same-sign `negSucc`/`negSucc`.
    let inner_negsucc = {
        let mut qb = EnvDeclBuilder::child_of(&mb);
        let (q_id, q) = qb.fresh_local(c.nat_type.clone());
        let inner_op = c.neg_succ(q.clone());
        let h_type = c.eq_int(
            c.imul(scale.clone(), outer.clone()),
            c.imul(scale.clone(), inner_op.clone()),
        );
        let (h_id, h) = qb.fresh_local(h_type.clone());
        let goal = c.eq_int(outer.clone(), inner_op.clone());
        // Magnitudes (mul s (negSucc ·) ≡ ofNat ((n+1)*(·+1))); cancel factors
        // succ m / succ q, then `Nat.succ_inj` strips to lift factors m / q.
        let succ_m = c.succ(m.clone());
        let succ_q = c.succ(q.clone());
        let mag_m = c.nmul(c.succ(n.clone()), succ_m.clone());
        let mag_q = c.nmul(c.succ(n.clone()), succ_q.clone());
        let body = same_sign_leaf(
            c,
            &qb,
            n,
            &outer,
            &inner_op,
            &h,
            &mag_m,
            &mag_q,
            &m,
            &q,
            LiftCtor::NegSucc,
        );
        let _ = &goal; // goal pinned by the kernel against the leaf's expected type.
        let lam = qb.mk_lam(h_id, BinderInfo::Default, h_type, body);
        qb.finish_child(lam_with_p(&qb, q_id, lam))
    };

    let inner_rec = Expr::apps(
        c.int_rec.clone(),
        [inner_motive, inner_ofnat, inner_negsucc],
    );
    let lam = mb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), inner_rec);
    mb.finish_child(lam)
}

/// Which constructor lifts the cancelled `Nat` equality back to `Int`.
#[derive(Clone, Copy)]
enum LiftCtor {
    OfNat,
    NegSucc,
}

/// Same-sign leaf: from `H : Eq Int (mul s outer) (mul s inner_op)` — which the
/// kernel reduces to `Eq Int (ofNat magA) (ofNat magB)` since a positive scalar
/// keeps both operands on the `ofNat` branch — extract the magnitude equality
/// via `Int.noConfusion`, cancel the positive factor via
/// `Nat.mul_left_cancel_succ`, then re-lift by `congrArg ctor`.
///
/// - `mag_a` / `mag_b` are the reduced magnitudes `(n+1) * cancel_factor`.
/// - `lift_a` / `lift_b` are the constructor operands of the *goal*
///   (`m`/`p` for `ofNat`, `m`/`q` for `negSucc`).
///   - `ofNat`: cancel factor is `lift_·` itself; `congrArg Int.ofNat` lifts
///     `lift_a = lift_b` to `ofNat lift_a = ofNat lift_b = goal`.
///   - `negSucc`: cancel factor is `Nat.succ lift_·` (the operand's magnitude),
///     so `Nat.mul_left_cancel_succ` yields `succ lift_a = succ lift_b`;
///     `Nat.succ_inj` strips to `lift_a = lift_b`, and `congrArg Int.negSucc`
///     lifts to `negSucc lift_a = negSucc lift_b = goal`.
#[allow(clippy::too_many_arguments)]
fn same_sign_leaf(
    c: &IntMulCancelConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    outer: &Expr,
    inner_op: &Expr,
    h: &Expr,
    mag_a: &Expr,
    mag_b: &Expr,
    lift_a: &Expr,
    lift_b: &Expr,
    lift: LiftCtor,
) -> Expr {
    let scale = c.of_nat(c.succ(n.clone()));
    let mul_lhs = c.imul(scale.clone(), outer.clone());
    let mul_rhs = c.imul(scale, inner_op.clone());

    // `Int.noConfusion` extracts the *constructor field* equality, i.e. the
    // equality of whatever `Int.mul s ·` reduces the constructor argument to:
    //
    // - `Int.mul s (ofNat ·)  ≡ Int.ofNat (Nat.mul (succ n) ·)`, so the
    //   `ofNat` field is exactly `mag_a` / `mag_b` (`Nat.mul (succ n) lift`).
    // - `Int.mul s (negSucc ·) ≡ Int.negSucc (Nat.pred (Nat.mul (succ n)
    //   (succ ·)))` — the positive scalar lands `negOfNat` on the `negSucc`
    //   branch, whose field is the *predecessor* of the magnitude. So the
    //   genuine `negSucc` field is `Nat.pred mag_a` / `Nat.pred mag_b`
    //   (def-eq to the reduced `Nat.rec` term `negOfNat` produces), NOT
    //   `mag_a` / `mag_b` themselves — those are off by one `Nat.succ`.
    //
    // Naming the field with the wrong magnitude is exactly what the pre-sound
    // kernel let slip; the now-sound kernel rejects it. We therefore extract
    // the *true* field equality and re-lift it by one `Nat.succ` for `negSucc`.
    let (field_a, field_b) = match lift {
        LiftCtor::OfNat => (mag_a.clone(), mag_b.clone()),
        LiftCtor::NegSucc => (c.pred(mag_a.clone()), c.pred(mag_b.clone())),
    };

    // mag_eq : Eq Nat field_a field_b
    //   = @Int.noConfusion.{0} (Eq Nat field_a field_b)
    //       (mul s outer) (mul s inner_op) H (λ e => e)
    let mag_eq_type = c.eq_nat(field_a.clone(), field_b.clone());
    let cont = {
        let mut cb = EnvDeclBuilder::child_of(parent);
        let (e_id, e) = cb.fresh_local(mag_eq_type.clone());
        let lam = cb.mk_lam(e_id, BinderInfo::Default, mag_eq_type.clone(), e);
        cb.finish_child(lam)
    };
    let mag_eq = Expr::apps(
        c.int_no_confusion.clone(),
        [mag_eq_type, mul_lhs, mul_rhs, h.clone(), cont],
    );

    match lift {
        LiftCtor::OfNat => {
            // The `ofNat` field equality `Eq Nat (mul (succ n) lift_a)
            // (mul (succ n) lift_b)` is already the cancellation hypothesis.
            // factor_eq : Eq Nat lift_a lift_b
            let factor_eq = c.nat_cancel(n.clone(), lift_a.clone(), lift_b.clone(), mag_eq);
            // congrArg Int.ofNat : Eq Int (ofNat lift_a) (ofNat lift_b) ≡ goal.
            c.congr_arg_nat_int(
                lift_a.clone(),
                lift_b.clone(),
                c.int_of_nat.clone(),
                factor_eq,
            )
        }
        LiftCtor::NegSucc => {
            // `mag_eq : Eq Nat (pred mag_a) (pred mag_b)` is the genuine
            // `negSucc` field equality. Re-lift by one `Nat.succ` to recover
            // the magnitude equality `Eq Nat (succ (pred mag_a)) (succ (pred
            // mag_b))`, which is def-eq to `Eq Nat mag_a mag_b` = `Eq Nat
            // (mul (succ n) (succ lift_a)) (mul (succ n) (succ lift_b))`.
            let mag_eq = c.congr_arg_nat_nat(
                c.pred(mag_a.clone()),
                c.pred(mag_b.clone()),
                c.nat_succ.clone(),
                mag_eq,
            );
            // cancel factors are succ lift_a / succ lift_b.
            let succ_a = c.succ(lift_a.clone());
            let succ_b = c.succ(lift_b.clone());
            // succ_eq : Eq Nat (succ lift_a) (succ lift_b)
            let succ_eq = c.nat_cancel(n.clone(), succ_a, succ_b, mag_eq);
            // field_eq : Eq Nat lift_a lift_b
            let field_eq = c.nat_succ_inj(lift_a.clone(), lift_b.clone(), succ_eq);
            // congrArg Int.negSucc : Eq Int (negSucc lift_a) (negSucc lift_b) ≡ goal.
            c.congr_arg_nat_int(
                lift_a.clone(),
                lift_b.clone(),
                c.int_neg_succ.clone(),
                field_eq,
            )
        }
    }
}

/// Mixed-sign leaf: the two products land on *different* `Int` constructors, so
/// `H : Eq Int mul_lhs mul_rhs` is impossible. `Int.noConfusionType (goal)
/// mul_lhs mul_rhs` reduces to the goal `P`, so `Int.noConfusion` discharges
/// the leaf directly (no continuation).
fn mixed_sign_leaf(
    c: &IntMulCancelConsts,
    goal: Expr,
    mul_lhs: Expr,
    mul_rhs: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(c.int_no_confusion.clone(), [goal, mul_lhs, mul_rhs, h])
}

/// Wrap an already-built inner-leaf lambda (over `H`) in the `Nat` field binder
/// `p`/`q` of the inner `Int.rec` constructor minor premise.
fn lam_with_p(parent: &EnvDeclBuilder, p_id: crate::expr::FVarId, body: Expr) -> Expr {
    let c_nat = Expr::const_(Name::from_string("Nat"), vec![]);
    parent.mk_lam(p_id, BinderInfo::Default, c_nat, body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn build_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_mul_left_cancel_ofnat_succ_proof()
            .expect("registration should succeed");
        env
    }

    /// The cancellation law is now a kernel-checked Theorem (not Axiom), and the
    /// registration is idempotent.
    #[test]
    fn test_int_mul_left_cancel_ofnat_succ_registered_as_theorem() {
        let mut env = build_env();
        env.register_int_mul_left_cancel_ofnat_succ_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_left_cancel_ofNat_succ"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Int.mul_left_cancel_ofNat_succ"),
                vec![],
            ))
            .expect("Int.mul_left_cancel_ofNat_succ should type-check");
    }

    /// After peeling four λ binders (n, a, b, H), the proof root is `Int.rec` —
    /// guards against an `Eq.refl` / axiom-reference masquerade.
    #[test]
    fn test_int_mul_left_cancel_ofnat_succ_proof_uses_rec() {
        let env = build_env();
        let info = env
            .get_const(&Name::from_string("Int.mul_left_cancel_ofNat_succ"))
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
            ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "Int.rec",
                "cancellation proof root must be Int.rec"
            ),
            k => panic!("expected Const(Int.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty — the proof depends only on generated reducible
    /// definitions (`Int.noConfusion`) and the constructive
    /// `Nat.mul_left_cancel_succ`.
    #[test]
    fn test_int_mul_left_cancel_ofnat_succ_axiom_deps_empty() {
        let env = build_env();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_left_cancel_ofNat_succ"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_left_cancel_ofNat_succ must have empty axiom closure, got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Int.mul_left_cancel_ofNat_succ"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive,
            "Int.mul_left_cancel_ofNat_succ must be Constructive"
        );
    }
}
