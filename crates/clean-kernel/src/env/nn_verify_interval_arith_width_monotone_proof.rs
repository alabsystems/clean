// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term for T07 `NNVerify.IntervalArith.interval_width_monotone`
//! (#3541).
//!
//! Promotes T07 from `Declaration::Axiom` (via `register_helper_axiom`) to a
//! genuine `Declaration::Theorem` with a lambda proof term. Unlocks the
//! downstream interval-subset-monotonicity lemmas used by the CROWN/IBP
//! containment pipeline without introducing any new domain axioms.
//!
//! # Statement
//!
//! ```text
//! theorem interval_width_monotone {d : Nat}
//!   (B1 B2 : IntervalBounds d)
//!   (hsub : IntervalBounds.subset B1 B2)
//!   (x : NNVec d)
//!   (hx : IntervalBounds.contains B1 x) :
//!   IntervalBounds.contains B2 x
//! ```
//!
//! Here `subset` and `contains` unfold (both are reducible `Definition`s)
//! to:
//!
//! ```text
//! subset B1 B2   ≡ ∀ i, B2.lower i ≤ B1.lower i ∧ B1.upper i ≤ B2.upper i
//! contains B  x  ≡ ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i
//! ```
//!
//! # Proof strategy
//!
//! For each index `i : Fin d`:
//!
//! 1. Instantiate `hsub i : B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i`.
//!    Extract `hs_lo : B2.lo i ≤ B1.lo i` via `And.left` and
//!    `hs_hi : B1.hi i ≤ B2.hi i` via `And.right`.
//! 2. Instantiate `hx   i : B1.lo i ≤ x i ∧ x i ≤ B1.hi i`.
//!    Extract `hx_lo : B1.lo i ≤ x i` and `hx_hi : x i ≤ B1.hi i`.
//! 3. Chain `Rat.le_trans` to obtain:
//!    * `B2.lo i ≤ x i` from `hs_lo` and `hx_lo`.
//!    * `x i ≤ B2.hi i` from `hx_hi` and `hs_hi`.
//! 4. Combine both with `And.intro` and abstract over `i` to produce the
//!    pointwise `contains B2 x` witness.
//!
//! # Axioms used (all pre-existing; no new axioms)
//!
//! Foundational only:
//! * `Rat.le_trans` — listed in `FOUNDATIONAL_AXIOMS`.
//!
//! Kernel primitives (not axioms):
//! * `And` / `And.intro` / `And.left` / `And.right` (inductive + constructors
//!   registered by `Environment::init_and`).
//!
//! Because the only non-kernel reference is the foundational `Rat.le_trans`,
//! the transitive domain-axiom closure of this proof is **empty** — T07 is
//! eligible for `ProofQuality::Constructive` classification.  The closure
//! assertion is locked down by
//! `tests_nn_verify_interval_arith_width_monotone::test_t07_axiom_closure_allowed`.
//!
//! Part of #3541 (T07 unlock); companion of #3537 / #3538 / #3539.

use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `LE.le.{0} @Rat @instLERat lhs rhs`.
fn rat_le(rat: &Expr, inst_le_rat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
    Expr::apps(le_le, [rat.clone(), inst_le_rat.clone(), lhs, rhs])
}

/// Build `Rat.le_trans @a @b @c hab hbc : a ≤ c`.
fn rat_le_trans(a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
    let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
    Expr::apps(le_trans, [a, b, c, hab, hbc])
}

/// Build `And.intro p q hp hq : And p q`.
fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    Expr::apps(and_intro, [p, q, hp, hq])
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

/// Build the constructive proof term for T07
/// `NNVerify.IntervalArith.interval_width_monotone`:
///
/// ```text
/// fun {d : Nat} (B1 B2 : IB d) (hsub : subset B1 B2)
///     (x : NNVec d) (hx : contains B1 x) =>
///   fun (i : Fin d) =>
///     let hs  := hsub i     -- B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i
///     let hxi := hx   i     -- B1.lo i ≤ x i    ∧ x i      ≤ B1.hi i
///     let hs_lo := And.left  _ _ hs
///     let hs_hi := And.right _ _ hs
///     let hx_lo := And.left  _ _ hxi
///     let hx_hi := And.right _ _ hxi
///     let lo := Rat.le_trans (B2.lo i) (B1.lo i) (x i)      hs_lo hx_lo
///     let hi := Rat.le_trans (x i)     (B1.hi i) (B2.hi i)  hx_hi hs_hi
///     And.intro (B2.lo i ≤ x i) (x i ≤ B2.hi i) lo hi
/// ```
pub(super) fn build_interval_width_monotone_proof() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
    let ib = Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let subset_const = Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]);
    let contains_const = Expr::const_(
        Name::from_string("NNVerify.IntervalBounds.contains"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();

    // Binders.
    let (d_id, d) = b.fresh_local(nat.clone());
    let ib_d = Expr::app(ib.clone(), d.clone());
    let vec_d = Expr::app(nn_vec.clone(), d.clone());
    let fin_d = Expr::app(fin.clone(), d.clone());

    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());

    // hsub : subset B1 B2
    let hsub_ty = Expr::apps(subset_const, [d.clone(), b1.clone(), b2.clone()]);
    let (hsub_id, hsub) = b.fresh_local(hsub_ty.clone());

    let (x_id, x) = b.fresh_local(vec_d.clone());

    // hx : contains B1 x
    let hx_ty = Expr::apps(contains_const.clone(), [d.clone(), b1.clone(), x.clone()]);
    let (hx_id, hx) = b.fresh_local(hx_ty.clone());

    // Inner body: for each i : Fin d, produce the witness
    // `contains B2 x i` (which reduces to the And-pair).
    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        // Projections for B1 and B2 components at i.
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
        let x_i = Expr::app(x.clone(), i.clone());

        // Instantiate hsub and hx at i.
        // hsub_i : B2.lo i ≤ B1.lo i ∧ B1.hi i ≤ B2.hi i
        let hsub_i = Expr::app(hsub.clone(), i.clone());
        // hx_i   : B1.lo i ≤ x i    ∧ x i      ≤ B1.hi i
        let hx_i = Expr::app(hx.clone(), i.clone());

        // Component propositions (for And.left/right and And.intro arguments).
        let hs_lo_prop = rat_le(&rat, &inst_le_rat, b2_lo_i.clone(), b1_lo_i.clone());
        let hs_hi_prop = rat_le(&rat, &inst_le_rat, b1_hi_i.clone(), b2_hi_i.clone());
        let hx_lo_prop = rat_le(&rat, &inst_le_rat, b1_lo_i.clone(), x_i.clone());
        let hx_hi_prop = rat_le(&rat, &inst_le_rat, x_i.clone(), b1_hi_i.clone());

        // Extract component hypotheses.
        let hs_lo = and_left(hs_lo_prop.clone(), hs_hi_prop.clone(), hsub_i.clone());
        let hs_hi = and_right(hs_lo_prop, hs_hi_prop, hsub_i);
        let hx_lo = and_left(hx_lo_prop.clone(), hx_hi_prop.clone(), hx_i.clone());
        let hx_hi = and_right(hx_lo_prop, hx_hi_prop, hx_i);

        // Chain le_trans.
        // lo : B2.lo i ≤ x i
        let lo = rat_le_trans(b2_lo_i.clone(), b1_lo_i.clone(), x_i.clone(), hs_lo, hx_lo);
        // hi : x i ≤ B2.hi i
        let hi = rat_le_trans(x_i.clone(), b1_hi_i.clone(), b2_hi_i.clone(), hx_hi, hs_hi);

        // Goal: And (B2.lo i ≤ x i) (x i ≤ B2.hi i)
        let goal_lo = rat_le(&rat, &inst_le_rat, b2_lo_i, x_i.clone());
        let goal_hi = rat_le(&rat, &inst_le_rat, x_i, b2_hi_i);

        let body = and_intro(goal_lo, goal_hi, lo, hi);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };

    // Wrap lambdas (outermost → innermost mirrors reverse binding order).
    let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, inner);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_lam(hsub_id, BinderInfo::Default, hsub_ty, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, nat, e);
    b.finish(e)
}
