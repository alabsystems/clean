// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term for `Rat.neg_le_neg` (#3538).
//!
//! Promotes `Rat.neg_le_neg` from `Declaration::Axiom` to a genuine
//! `Declaration::Theorem` with a lambda proof term.  Unlocks the
//! downstream `NNVerify.IntervalArith.interval_neg_correct` (T11) native
//! save path once the parent register site is flipped to use this proof.
//!
//! # Statement
//!
//! ```text
//! Rat.neg_le_neg : ∀ (a b : Rat), a ≤ b → Rat.neg b ≤ Rat.neg a
//! ```
//!
//! # Proof strategy
//!
//! Given `h : a ≤ b`:
//!
//! 1. `h_sub   : 0 ≤ b - a`                   via `Rat.sub_nonneg_of_le a b h`.
//!    By delta on `Rat.sub`, this is `0 ≤ b + (-a)`.
//! 2. Show `b + (-a) = (-a) + (-(-b))`       via the chain
//!    * `e_bb  : -(-b) = b`                   (via the `add_right_cancel`
//!      cancellation trick used elsewhere in `mul_nonpos_le_left`).
//!    * `e_sb  : b = -(-b)`                   (Eq.symm of `e_bb`).
//!    * `e_l   : b + (-a) = -(-b) + (-a)`     via `congrArg (λ x, x + (-a)) e_sb`.
//!    * `e_c   : -(-b) + (-a) = (-a) + -(-b)` via `Rat.add_comm -(-b) (-a)`.
//!    * `e_chain : b + (-a) = (-a) + -(-b)`   via `Eq.trans e_l e_c`.
//! 3. Transport `h_sub` along `e_chain` with motive `λ x, 0 ≤ x`:
//!    `h_sub_flip : 0 ≤ (-a) + -(-b)`.
//!    By delta on `Rat.sub`, this is `0 ≤ (-a) - (-b)`.
//! 4. Apply `Rat.le_of_sub_nonneg (-b) (-a) h_sub_flip : -b ≤ -a`.  QED.
//!
//! # Axioms used (all pre-existing; no new axioms)
//!
//! Foundational (`FOUNDATIONAL_AXIOMS`):
//! * `Rat.add_le_add_left`         (used transitively by `sub_nonneg_of_le`)
//!
//! Rat field/order axioms (non-foundational but honest — same closure as the
//! sibling `Rat.sub_nonneg_of_le` / `Rat.le_of_sub_nonneg` theorems in
//! `nn_verify_rat_ordering.rs`):
//! * `Rat.add_left_neg`, `Rat.add_neg_self`
//! * `Rat.add_comm`, `Rat.add_zero`, `Rat.zero_add`
//! * `Rat.add_assoc`, `Rat.add_right_cancel`
//!
//! Kernel primitives: `Eq.refl`, `Eq.symm`, `Eq.trans`, `Eq.subst`, `congrArg`.
//!
//! Because the existing `Rat.sub_nonneg_of_le` / `Rat.le_of_sub_nonneg`
//! already transitively depend on the full Rat ordered-field axiom set,
//! this proof term introduces no new axiom dependencies beyond theirs.
//!
//! Part of #3538 (T11 unlock); companion of #3537 (`Rat.add_le_add`) and
//! #3539 (`Rat.sub_le_sub`).

use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a`.
fn eq_subst_rat(rat: &Expr, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_subst, [rat.clone(), motive, a, b, h_eq, h_motive_a])
}

/// Build `Eq.trans.{1} @Rat @a @b @c h1 h2`.
fn eq_trans_rat(rat: &Expr, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    let eq_trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_trans, [rat.clone(), a, b, c, h1, h2])
}

/// Build `Eq.symm.{1} @Rat @a @b h`.
fn eq_symm_rat(rat: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_symm, [rat.clone(), a, b, h])
}

/// Build `@congrArg.{1, 1} Rat Rat a b f h : f a = f b`.
fn congr_arg_rat_rat(rat: &Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]);
    Expr::apps(congr_arg, [rat.clone(), rat.clone(), a, b, f, h])
}

/// Build `LE.le.{0} @Rat @instLERat lhs rhs`.
fn rat_le(rat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
    let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
    Expr::apps(le_le, [rat.clone(), inst, lhs, rhs])
}

/// Build `Rat.add a b`.
fn rat_add(a: Expr, b: Expr) -> Expr {
    let add = Expr::const_(Name::from_string("Rat.add"), vec![]);
    Expr::apps(add, [a, b])
}

/// Build `Rat.neg a`.
fn rat_neg(a: Expr) -> Expr {
    let neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    Expr::app(neg, a)
}

/// Build the `e_bb : -(-x) = x` equality via the `add_right_cancel` trick:
///
/// * `h_lneg : -(-x) + (-x) = 0`       via `Rat.add_left_neg (-x)`.
/// * `h_rneg : x + (-x) = 0`           via `Rat.add_neg_self x`.
/// * `h_combine : -(-x) + (-x) = x + (-x)`  via `Eq.trans h_lneg (Eq.symm h_rneg)`.
/// * `e_bb = Rat.add_right_cancel (-(-x)) (-x) x h_combine : -(-x) = x`.
fn build_neg_neg_eq(rat: &Expr, x: Expr, rat_zero: Expr) -> Expr {
    let neg_x = rat_neg(x.clone());
    let neg_neg_x = rat_neg(neg_x.clone());

    let add_left_neg = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
    let add_right_cancel = Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]);

    // h_lneg : -(-x) + (-x) = 0   via  Rat.add_left_neg (-x)
    let h_lneg = Expr::app(add_left_neg, neg_x.clone());
    // h_rneg : x + (-x) = 0       via  Rat.add_neg_self x
    let h_rneg = Expr::app(add_neg_self, x.clone());
    // h_rneg_sym : 0 = x + (-x)
    let rhs_sum = rat_add(x.clone(), neg_x.clone());
    let h_rneg_sym = eq_symm_rat(rat, rhs_sum.clone(), rat_zero.clone(), h_rneg);
    // h_combine : -(-x) + (-x) = x + (-x)
    let lhs_sum = rat_add(neg_neg_x.clone(), neg_x.clone());
    let h_combine = eq_trans_rat(rat, lhs_sum, rat_zero, rhs_sum, h_lneg, h_rneg_sym);
    // e_bb : -(-x) = x
    Expr::apps(add_right_cancel, [neg_neg_x, neg_x, x, h_combine])
}

/// Build the constructive proof term for `Rat.neg_le_neg`:
/// `∀ (a b : Rat), a ≤ b → Rat.neg b ≤ Rat.neg a`.
///
/// Shape:
/// ```text
/// fun (a b : Rat) (h : a ≤ b) =>
///   let h_sub : 0 ≤ b + (-a) := Rat.sub_nonneg_of_le a b h
///   let e_bb   : -(-b) = b                      := <add_right_cancel trick>
///   let e_sb   : b = -(-b)                      := Eq.symm e_bb
///   let e_l    : b + (-a) = -(-b) + (-a)        := congrArg (λ x, x + (-a)) e_sb
///   let e_c    : -(-b) + (-a) = (-a) + -(-b)    := Rat.add_comm -(-b) (-a)
///   let e_chain: b + (-a) = (-a) + -(-b)        := Eq.trans e_l e_c
///   let h_flip : 0 ≤ (-a) + -(-b)               := Eq.subst (λ y, 0 ≤ y) e_chain h_sub
///   Rat.le_of_sub_nonneg (-b) (-a) h_flip       : -b ≤ -a
/// ```
pub(super) fn build_rat_neg_le_neg_proof() -> Expr {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(rat.clone());
    let (bv_id, bv) = b.fresh_local(rat.clone());

    // h : a ≤ b
    let h_ty = rat_le(&rat, a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // Common subterms.
    let neg_a = rat_neg(a.clone());
    let neg_b = rat_neg(bv.clone());
    let neg_neg_b = rat_neg(neg_b.clone());
    let b_plus_neg_a = rat_add(bv.clone(), neg_a.clone());
    let neg_neg_b_plus_neg_a = rat_add(neg_neg_b.clone(), neg_a.clone());
    let neg_a_plus_neg_neg_b = rat_add(neg_a.clone(), neg_neg_b.clone());

    // Step 1: h_sub : 0 ≤ Rat.sub b a   (≡ 0 ≤ b + (-a) by delta on Rat.sub).
    let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
    let h_sub = Expr::apps(sub_nonneg_of_le, [a.clone(), bv.clone(), h]);
    // h_sub has type `0 ≤ Rat.sub b a`. By delta on the reducible `Rat.sub`,
    // this is `0 ≤ b + (-a)`, which is the form we will rewrite.

    // Step 2a: e_bb : -(-b) = b
    let e_bb = build_neg_neg_eq(&rat, bv.clone(), rat_zero.clone());
    // Step 2b: e_sb : b = -(-b)
    let e_sb = eq_symm_rat(&rat, neg_neg_b.clone(), bv.clone(), e_bb);
    // Step 2c: e_l : b + (-a) = -(-b) + (-a)
    //           via congrArg (λ x, x + (-a)) e_sb.
    let f_l = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(rat.clone());
        let body = rat_add(x, neg_a.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, rat.clone(), body);
        ch.finish_child(r)
    };
    let e_l = congr_arg_rat_rat(&rat, bv.clone(), neg_neg_b.clone(), f_l, e_sb);
    // Step 2d: e_c : -(-b) + (-a) = (-a) + -(-b)  via Rat.add_comm -(-b) (-a).
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let e_c = Expr::apps(add_comm, [neg_neg_b.clone(), neg_a.clone()]);
    // Step 2e: e_chain : b + (-a) = (-a) + -(-b)  via Eq.trans e_l e_c.
    let e_chain = eq_trans_rat(
        &rat,
        b_plus_neg_a.clone(),
        neg_neg_b_plus_neg_a.clone(),
        neg_a_plus_neg_neg_b.clone(),
        e_l,
        e_c,
    );

    // Step 3: h_flip : 0 ≤ (-a) + -(-b)  via Eq.subst with motive `λ y, 0 ≤ y`.
    // NB: h_sub has type `0 ≤ Rat.sub b a`. By delta on Rat.sub this reduces
    // to `0 ≤ b + (-a)` so the subst step rewriting `b + (-a) → (-a) + -(-b)`
    // is accepted by the kernel against the motive `λ y, 0 ≤ y` applied at
    // `b + (-a)` and `(-a) + -(-b)`.
    let motive_flip = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = ch.fresh_local(rat.clone());
        let body = rat_le(&rat, rat_zero.clone(), y);
        let r = ch.mk_lam(y_id, BinderInfo::Default, rat.clone(), body);
        ch.finish_child(r)
    };
    let h_flip = eq_subst_rat(
        &rat,
        motive_flip,
        b_plus_neg_a,
        neg_a_plus_neg_neg_b,
        e_chain,
        h_sub,
    );
    // h_flip now has type `0 ≤ (-a) + -(-b)`, which by delta on Rat.sub is
    // `0 ≤ Rat.sub (-a) (-b)` — the precondition of Rat.le_of_sub_nonneg.

    // Step 4: apply Rat.le_of_sub_nonneg (-b) (-a) h_flip : -b ≤ -a.
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let body = Expr::apps(le_of_sub_nonneg, [neg_b, neg_a, h_flip]);

    // Wrap lambdas: fun (a b : Rat) (h : a ≤ b) => body
    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, rat, e);
    b.finish(e)
}
