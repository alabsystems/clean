// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term for the interval *width* monotonicity lemma
//! `NNVerify.IntervalArith.interval_width_le_monotone`.
//!
//! This is the genuine numeric width-monotonicity statement:
//! a subset interval has pointwise-no-larger width, where
//! `width(B) i = B.upper i - B.lower i`
//! (the reducible definition `NNVerify.IntervalBounds.width`,
//! `fun i => Rat.sub (B.upper i) (B.lower i)`).
//!
//! It is the numeric companion of `interval_width_monotone` (which is the
//! *containment*-monotonicity lemma `subset B1 B2 → contains B1 x →
//! contains B2 x` — a different statement that happens to carry the
//! `interval_width_monotone` name for historical reasons).
//!
//! # Statement
//!
//! ```text
//! theorem interval_width_le_monotone {d : Nat}
//!   (B1 B2 : IntervalBounds d)
//!   (hsub : IntervalBounds.subset B1 B2)
//!   (i : Fin d) :
//!   IntervalBounds.width B1 i ≤ IntervalBounds.width B2 i
//! ```
//!
//! `subset` and `width` are reducible `Definition`s, so the goal/hypothesis
//! unfold to:
//!
//! ```text
//! subset B1 B2  ≡ ∀ i, B2.lower i ≤ B1.lower i ∧ B1.upper i ≤ B2.upper i
//! width B  i    ≡ B.upper i - B.lower i
//! ```
//!
//! The conclusion `width B1 i ≤ width B2 i` therefore delta-reduces to
//! `(B1.upper i - B1.lower i) ≤ (B2.upper i - B2.lower i)`.
//!
//! # Proof strategy
//!
//! For the fixed index `i : Fin d`:
//!
//! 1. Instantiate `hsub i : B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i`.
//!    Extract `h_lo : B2.lo i ≤ B1.lo i` via `And.left` and
//!    `h_hi : B1.hi i ≤ B2.hi i` via `And.right`.
//! 2. Apply `Rat.sub_le_sub`. Its registered type is
//!    `∀ (a b c d : Rat), a ≤ b → d ≤ c → (a - c) ≤ (b - d)`.
//!    Instantiate at
//!    `a = B1.hi i, b = B2.hi i, c = B1.lo i, d = B2.lo i`
//!    with `hab = h_hi : B1.hi i ≤ B2.hi i` and
//!    `hdc = h_lo : B2.lo i ≤ B1.lo i`, yielding
//!    `(B1.hi i - B1.lo i) ≤ (B2.hi i - B2.lo i)`,
//!    which is definitionally `width B1 i ≤ width B2 i`.
//!
//! # Axioms used (all pre-existing; no new axioms)
//!
//! Kernel primitives (not axioms):
//! * `And` / `And.left` / `And.right` (registered by `Environment::init_and`).
//!
//! Non-kernel reference:
//! * `Rat.sub_le_sub` — a kernel-checked `Declaration::Theorem`
//!   (`nn_verify_interval_arith_rat_sub_le_sub_proof`). Its transitive
//!   domain-axiom closure is empty (it reduces to `Rat.add_le_add` /
//!   `Rat.neg_le_neg`, both promoted to constructive theorems with empty
//!   domain-axiom closures after the `Rat.le_trans` elimination).
//!
//! Hence the transitive domain-axiom closure of this proof is empty and the
//! lemma classifies as `ProofQuality::Constructive`. Guarded by
//! `tests_nn_verify_interval_arith_width_le_monotone`.

use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `LE.le.{0} @Rat @instLERat lhs rhs`.
fn rat_le(rat: &Expr, inst_le_rat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
    Expr::apps(le_le, [rat.clone(), inst_le_rat.clone(), lhs, rhs])
}

/// Build `And.left p q h : p`.
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
    Expr::apps(and_left, [p, q, h])
}

/// Build `And.right p q h : q`.
fn and_right(p: Expr, q: Expr, h: Expr) -> Expr {
    let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
    Expr::apps(and_right, [p, q, h])
}

/// Build `Rat.sub_le_sub a b c d hab hdc : (a - c) ≤ (b - d)`
/// (registered type: `∀ a b c d, a ≤ b → d ≤ c → (a - c) ≤ (b - d)`).
fn sub_le_sub(a: Expr, b: Expr, c: Expr, d: Expr, hab: Expr, hdc: Expr) -> Expr {
    let sub_le_sub = Expr::const_(Name::from_string("Rat.sub_le_sub"), vec![]);
    Expr::apps(sub_le_sub, [a, b, c, d, hab, hdc])
}

/// Build the constructive proof term for
/// `NNVerify.IntervalArith.interval_width_le_monotone`:
///
/// ```text
/// fun {d : Nat} (B1 B2 : IB d) (hsub : subset B1 B2) (i : Fin d) =>
///   let hs    := hsub i                         -- B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i
///   let h_lo  := And.left  _ _ hs               -- B2.lo i ≤ B1.lo i
///   let h_hi  := And.right _ _ hs               -- B1.hi i ≤ B2.hi i
///   Rat.sub_le_sub (B1.hi i) (B2.hi i) (B1.lo i) (B2.lo i) h_hi h_lo
///     -- : (B1.hi i - B1.lo i) ≤ (B2.hi i - B2.lo i)
///     -- ≡ width B1 i ≤ width B2 i   (delta on reducible `width`)
/// ```
pub(super) fn build_interval_width_le_monotone_proof() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
    let ib = Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let subset_const = Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]);

    let mut b = EnvDeclBuilder::new();

    // Binders.
    let (d_id, d) = b.fresh_local(nat.clone());
    let ib_d = Expr::app(ib.clone(), d.clone());
    let fin_d = Expr::app(fin.clone(), d.clone());

    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());

    // hsub : subset B1 B2
    let hsub_ty = Expr::apps(subset_const, [d.clone(), b1.clone(), b2.clone()]);
    let (hsub_id, hsub) = b.fresh_local(hsub_ty.clone());

    // Inner body: for the fixed index i : Fin d, produce
    // `width B1 i ≤ width B2 i`.
    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        // Projections at i. Field 0 = lower, field 1 = upper.
        let b1_lo_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b1.clone()),
            i.clone(),
        );
        let b1_hi_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b1.clone()),
            i.clone(),
        );
        let b2_lo_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b2.clone()),
            i.clone(),
        );
        let b2_hi_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b2.clone()),
            i.clone(),
        );

        // hsub_i : B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i
        let hsub_i = Expr::app(hsub.clone(), i.clone());

        // Component propositions of the conjunction (for And.left/right).
        let lo_prop = rat_le(&rat, &inst_le_rat, b2_lo_i.clone(), b1_lo_i.clone());
        let hi_prop = rat_le(&rat, &inst_le_rat, b1_hi_i.clone(), b2_hi_i.clone());

        // h_lo : B2.lo i ≤ B1.lo i   (left conjunct)
        let h_lo = and_left(lo_prop.clone(), hi_prop.clone(), hsub_i.clone());
        // h_hi : B1.hi i ≤ B2.hi i   (right conjunct)
        let h_hi = and_right(lo_prop, hi_prop, hsub_i);

        // Rat.sub_le_sub (B1.hi i) (B2.hi i) (B1.lo i) (B2.lo i) h_hi h_lo
        //   : (B1.hi i - B1.lo i) ≤ (B2.hi i - B2.lo i)
        //   ≡ width B1 i ≤ width B2 i
        // hab = h_hi : B1.hi i ≤ B2.hi i,  hdc = h_lo : B2.lo i ≤ B1.lo i
        let body = sub_le_sub(b1_hi_i, b2_hi_i, b1_lo_i, b2_lo_i, h_hi, h_lo);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };

    // Wrap lambdas (outermost → innermost mirrors reverse binding order).
    let e = b.mk_lam(hsub_id, BinderInfo::Default, hsub_ty, inner);
    let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, nat, e);
    b.finish(e)
}
