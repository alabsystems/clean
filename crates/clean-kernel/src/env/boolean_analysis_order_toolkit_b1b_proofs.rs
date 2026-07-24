// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B1b lt↔sub bridge — proof-term builders.
//!
//! Split from `boolean_analysis_order_toolkit_b1b.rs` to keep each file under
//! the 500-line limit (mirrors the B1 `_proofs` split). The registration entry
//! points live in the parent module; this file holds the pure proof-term and
//! type construction the registrars consume.
//!
//! `Rat.lt` is a `Quot.lift` and is NEVER reduced for variable arguments — all
//! strict-order reasoning goes through `Rat.lt_iff_le_not_le` propositionally.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ---------------------------------------------------------------------------
// Small Prop-eliminator plumbing (And / Iff / Not / False) shared by builders
// ---------------------------------------------------------------------------

/// `Rat.lt a b` (stated; never reduced).
fn rat_lt(c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
}

/// `Not P ≡ P → False`.
fn not_(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}

/// `And P Q`.
fn and_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}

/// `@And.intro P Q hp hq : And P Q`.
fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [p, q, hp, hq],
    )
}

/// `@And.left P Q h : P`.
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}

/// `@And.right P Q h : Q`.
fn and_right(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [p, q, h],
    )
}

/// `@Iff.mp lhs rhs hiff hlhs : rhs`.
fn iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}

/// `@Iff.mpr lhs rhs hiff hrhs : lhs`.
fn iff_mpr(lhs: Expr, rhs: Expr, hiff: Expr, hrhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mpr"), vec![]),
        [lhs, rhs, hiff, hrhs],
    )
}

/// `Rat.lt_iff_le_not_le a b : Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))`.
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}

/// The RHS of `Rat.lt_iff_le_not_le a b`: `And (Rat.le a b) (Not (Rat.le b a))`.
fn lt_rhs(c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    and_(c.rat_le(a.clone(), b.clone()), not_(c.rat_le(b, a)))
}

// ---------------------------------------------------------------------------
// 1. Rat.sub_add_cancel : ∀ b c, (c − b) + b = c
// ---------------------------------------------------------------------------

/// Type of `Rat.sub_add_cancel`: `∀ b c : Rat, (c − b) + b = c`.
pub(super) fn sub_add_cancel_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let lhs = c.add(c.sub(cv.clone(), bv.clone()), bv.clone());
    let body = c.rat_eq(lhs, cv);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sub_add_cancel`.
///
/// `(c−b)+b ≡ (c+(-b))+b` (Rat.sub reducible). Chain:
///   `h_assoc : (c+(-b))+b = c+((-b)+b)`   [add_assoc c (-b) b]
///   `h_ln    : (-b)+b = 0`                [add_left_neg b]
///   subst h_assoc under `fun x => (c−b)+b = c+x` along h_ln ⇒ `(c−b)+b = c+0`
///   `h_az    : c+0 = c`                   [add_zero c]
///   trans ⇒ `(c−b)+b = c`.
pub(super) fn build_sub_add_cancel_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());

    let neg_b = c.neg(bv.clone());
    let c_sub_b = c.sub(cv.clone(), bv.clone()); // c − b  (≡ c + (-b))
    let lhs = c.add(c_sub_b.clone(), bv.clone()); // (c−b)+b
    let nb_plus_b = c.add(neg_b.clone(), bv.clone()); // (-b)+b
    let c_plus_zero = c.add(cv.clone(), c.rat_zero.clone()); // c + 0

    let add_assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
    let add_left_neg = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);

    // h_assoc : (c+(-b))+b = c+((-b)+b)  —  kernel sees LHS ≡ (c−b)+b.
    let h_assoc = Expr::apps(add_assoc, [cv.clone(), neg_b.clone(), bv.clone()]);
    // h_ln : (-b)+b = 0
    let h_ln = Expr::app(add_left_neg, bv.clone());
    // Transport h_assoc along h_ln under motive `fun x => (c−b)+b = c+x`.
    // subst : motive ((-b)+b) → motive 0.  motive ((-b)+b) = h_assoc's type.
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_eq(lhs.clone(), c.add(cv.clone(), x));
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // h_to_c0 : (c−b)+b = c+0
    let h_to_c0 = c.subst(motive, nb_plus_b.clone(), c.rat_zero.clone(), h_ln, h_assoc);
    // h_az : c+0 = c
    let h_az = Expr::app(add_zero, cv.clone());
    // body : (c−b)+b = c
    let body = c.trans(lhs, c_plus_zero, cv.clone(), h_to_c0, h_az);

    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 2. Rat.sub_pos_of_lt : ∀ b c, Rat.lt b c → Rat.lt 0 (c − b)
// ---------------------------------------------------------------------------

/// Type of `Rat.sub_pos_of_lt`: `∀ b c, Rat.lt b c → Rat.lt 0 (c − b)`.
pub(super) fn sub_pos_of_lt_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(c, bv.clone(), cv.clone());
    let concl = rat_lt(c, c.rat_zero.clone(), c.sub(cv.clone(), bv.clone()));
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sub_pos_of_lt`.
pub(super) fn build_sub_pos_of_lt_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(c, bv.clone(), cv.clone());
    let (h_id, h_lt) = b.fresh_local(h_ty.clone());

    let c_sub_b = c.sub(cv.clone(), bv.clone());
    let zero = c.rat_zero.clone();

    // mp : (b ≤ c) ∧ ¬(c ≤ b)
    let rhs_bc = lt_rhs(c, bv.clone(), cv.clone());
    let mp = iff_mp(
        rat_lt(c, bv.clone(), cv.clone()),
        rhs_bc.clone(),
        lt_iff(bv.clone(), cv.clone()),
        h_lt,
    );
    let le_bc = c.rat_le(bv.clone(), cv.clone());
    let not_le_cb = not_(c.rat_le(cv.clone(), bv.clone()));
    let h_le_bc = and_left(le_bc.clone(), not_le_cb.clone(), mp.clone()); // b ≤ c
    let h_not_le_cb = and_right(le_bc.clone(), not_le_cb.clone(), mp); // ¬(c ≤ b)

    // -------- le half: 0 ≤ c − b  via sub_nonneg_of_le b c (b ≤ c) --------
    let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
    let h_le_half = Expr::apps(sub_nonneg_of_le, [bv.clone(), cv.clone(), h_le_bc]);

    // -------- not-le half: ¬(c − b ≤ 0) --------
    //   λ (h0 : c−b ≤ 0) =>
    //     add_le_add (c−b) 0 b b h0 (le_refl b) : (c−b)+b ≤ 0+b
    //     rewrite LHS via sub_add_cancel b c : (c−b)+b = c
    //     rewrite RHS via zero_add b          : 0+b = b
    //     ⇒ c ≤ b ; apply h_not_le_cb ⇒ False.
    let le_cb_0 = c.rat_le(c_sub_b.clone(), zero.clone());
    let not_le_half = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h0_id, h0) = ch.fresh_local(le_cb_0.clone());
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        let add_le_add = Expr::const_(Name::from_string("Rat.add_le_add"), vec![]);
        // base : (c−b)+b ≤ 0+b
        let h_refl_b = Expr::app(le_refl, bv.clone());
        let base = Expr::apps(
            add_le_add,
            [
                c_sub_b.clone(),
                zero.clone(),
                bv.clone(),
                bv.clone(),
                h0,
                h_refl_b,
            ],
        );
        let lhs_cbb = c.add(c_sub_b.clone(), bv.clone()); // (c−b)+b
        let rhs_0b = c.add(zero.clone(), bv.clone()); // 0+b
                                                      // rewrite LHS (c−b)+b → c via sub_add_cancel b c
        let sub_add_cancel = Expr::const_(Name::from_string("Rat.sub_add_cancel"), vec![]);
        let h_sac = Expr::apps(sub_add_cancel, [bv.clone(), cv.clone()]); // (c−b)+b = c
        let motive_lhs = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(x, rhs_0b.clone());
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let step1 = c.subst(motive_lhs, lhs_cbb, cv.clone(), h_sac, base); // c ≤ 0+b
                                                                           // rewrite RHS 0+b → b via zero_add b
        let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
        let h_za = Expr::app(zero_add, bv.clone()); // 0+b = b
        let motive_rhs = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(cv.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let h_c_le_b = c.subst(motive_rhs, rhs_0b, bv.clone(), h_za, step1); // c ≤ b
                                                                             // h_not_le_cb (c ≤ b) : False
        let false_proof = Expr::app(h_not_le_cb, h_c_le_b);
        let lam = ch.mk_lam(h0_id, BinderInfo::Default, le_cb_0.clone(), false_proof);
        ch.finish_child(lam)
    };

    // Assemble: Iff.mpr (lt_iff 0 (c−b)) (And.intro (0 ≤ c−b) (¬(c−b ≤ 0)))
    let le_0cb = c.rat_le(zero.clone(), c_sub_b.clone());
    let not_le_cb0 = not_(le_cb_0.clone());
    let and_proof = and_intro(le_0cb.clone(), not_le_cb0.clone(), h_le_half, not_le_half);
    let body = iff_mpr(
        rat_lt(c, zero.clone(), c_sub_b.clone()),
        and_(le_0cb, not_le_cb0),
        lt_iff(zero, c_sub_b),
        and_proof,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 3. Rat.lt_of_sub_pos : ∀ b c, Rat.lt 0 (c − b) → Rat.lt b c
// ---------------------------------------------------------------------------

/// Type of `Rat.lt_of_sub_pos`: `∀ b c, Rat.lt 0 (c − b) → Rat.lt b c`.
pub(super) fn lt_of_sub_pos_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(c, c.rat_zero.clone(), c.sub(cv.clone(), bv.clone()));
    let concl = rat_lt(c, bv.clone(), cv.clone());
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.lt_of_sub_pos`.
///
/// Mirror of `sub_pos_of_lt`:
///   - mp on `0 < c−b` gives `(0 ≤ c−b) ∧ ¬(c−b ≤ 0)`.
///   - le half: `le_of_sub_nonneg b c (0 ≤ c−b) : b ≤ c`.
///   - ¬(c ≤ b) half: suppose `h : c ≤ b`. Then
///     `add_le_add c b (-b) (-b) h (le_refl (-b)) : c+(-b) ≤ b+(-b)`.
///     `c+(-b) ≡ c−b` (def); `b+(-b) = 0` (add_neg_self b). ⇒ `c−b ≤ 0`,
///     contradicting `¬(c−b ≤ 0)`.
///   - Iff.mpr (lt_iff b c) (And.intro (b ≤ c) (¬(c ≤ b))).
pub(super) fn build_lt_of_sub_pos_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let c_sub_b = c.sub(cv.clone(), bv.clone());
    let zero = c.rat_zero.clone();
    let h_ty = rat_lt(c, zero.clone(), c_sub_b.clone());
    let (h_id, h_lt) = b.fresh_local(h_ty.clone());

    // mp : (0 ≤ c−b) ∧ ¬(c−b ≤ 0)
    let rhs_0cb = lt_rhs(c, zero.clone(), c_sub_b.clone());
    let mp = iff_mp(
        rat_lt(c, zero.clone(), c_sub_b.clone()),
        rhs_0cb.clone(),
        lt_iff(zero.clone(), c_sub_b.clone()),
        h_lt,
    );
    let le_0cb = c.rat_le(zero.clone(), c_sub_b.clone());
    let not_le_cb0 = not_(c.rat_le(c_sub_b.clone(), zero.clone()));
    let h_le_0cb = and_left(le_0cb.clone(), not_le_cb0.clone(), mp.clone());
    let h_not_le_cb0 = and_right(le_0cb.clone(), not_le_cb0.clone(), mp);

    // le half: le_of_sub_nonneg b c (0 ≤ c−b) : b ≤ c
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let h_le_bc = Expr::apps(le_of_sub_nonneg, [bv.clone(), cv.clone(), h_le_0cb]);

    // ¬(c ≤ b) half:
    let le_cb = c.rat_le(cv.clone(), bv.clone());
    let not_le_half = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id2, h_cb) = ch.fresh_local(le_cb.clone());
        let neg_b = c.neg(bv.clone());
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        let add_le_add = Expr::const_(Name::from_string("Rat.add_le_add"), vec![]);
        // base : c+(-b) ≤ b+(-b)
        let h_refl_nb = Expr::app(le_refl, neg_b.clone());
        let base = Expr::apps(
            add_le_add,
            [
                cv.clone(),
                bv.clone(),
                neg_b.clone(),
                neg_b.clone(),
                h_cb,
                h_refl_nb,
            ],
        );
        // c+(-b) ≡ c−b (no rewrite needed on LHS — definitional).
        // rewrite RHS b+(-b) → 0 via add_neg_self b.
        let b_plus_nb = c.add(bv.clone(), neg_b.clone()); // b+(-b)
        let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
        let h_ans = Expr::app(add_neg_self, bv.clone()); // b+(-b) = 0
        let motive_rhs = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            // LHS stated as c−b so the resulting prop is exactly `c−b ≤ x`.
            let body = c.rat_le(c_sub_b.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        // base : c−b ≤ b+(-b)  (LHS c+(-b) ≡ c−b accepted by def-eq)
        let h_cb_le_0 = c.subst(motive_rhs, b_plus_nb, zero.clone(), h_ans, base); // c−b ≤ 0
        let false_proof = Expr::app(h_not_le_cb0, h_cb_le_0);
        let lam = ch.mk_lam(h_id2, BinderInfo::Default, le_cb.clone(), false_proof);
        ch.finish_child(lam)
    };

    // Iff.mpr (lt_iff b c) (And.intro (b ≤ c) (¬(c ≤ b)))
    let le_bc = c.rat_le(bv.clone(), cv.clone());
    let not_le_cb = not_(le_cb.clone());
    let and_proof = and_intro(le_bc.clone(), not_le_cb.clone(), h_le_bc, not_le_half);
    let body = iff_mpr(
        rat_lt(c, bv.clone(), cv.clone()),
        and_(le_bc, not_le_cb),
        lt_iff(bv.clone(), cv.clone()),
        and_proof,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 4. Rat.mul_lt_mul_of_pos_left : ∀ a b c, b<c → 0<a → a·b < a·c
// ---------------------------------------------------------------------------

/// Type of `Rat.mul_lt_mul_of_pos_left`:
/// `∀ a b c, Rat.lt b c → Rat.lt 0 a → Rat.lt (a·b) (a·c)`.
pub(super) fn mul_lt_mul_left_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = rat_lt(c, bv.clone(), cv.clone());
    let h_a_ty = rat_lt(c, c.rat_zero.clone(), a.clone());
    let concl = rat_lt(
        c,
        c.mul(a.clone(), bv.clone()),
        c.mul(a.clone(), cv.clone()),
    );
    let (ha_id, _) = b.fresh_local(h_a_ty.clone());
    let (hbc_id, _) = b.fresh_local(h_bc_ty.clone());
    let e = b.mk_pi(ha_id, BinderInfo::Default, h_a_ty, concl);
    let e = b.mk_pi(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.mul_lt_mul_of_pos_left`.
///
///   1. `sub_pos_of_lt b c h_bc : 0 < c−b`.
///   2. `mul_pos a (c−b) h_a (1) : 0 < a·(c−b)`.
///   3. `mul_sub a c b : a·(c−b) = a·c − a·b`, transported under `fun x => 0<x`
///      ⇒ `0 < a·c − a·b`.
///   4. `lt_of_sub_pos (a·b) (a·c) (3) : a·b < a·c`.
pub(super) fn build_mul_lt_mul_of_pos_left_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = rat_lt(c, bv.clone(), cv.clone());
    let h_a_ty = rat_lt(c, c.rat_zero.clone(), a.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());
    let (ha_id, h_a) = b.fresh_local(h_a_ty.clone());

    let zero = c.rat_zero.clone();
    let c_sub_b = c.sub(cv.clone(), bv.clone());
    let a_csb = c.mul(a.clone(), c_sub_b.clone());
    let ac = c.mul(a.clone(), cv.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let ac_sub_ab = c.sub(ac.clone(), ab.clone());

    // 1. sub_pos_of_lt b c h_bc : 0 < c−b
    let sub_pos_of_lt = Expr::const_(Name::from_string("Rat.sub_pos_of_lt"), vec![]);
    let h_cb_pos = Expr::apps(sub_pos_of_lt, [bv.clone(), cv.clone(), h_bc]);
    // 2. mul_pos a (c−b) h_a h_cb_pos : 0 < a·(c−b)
    let mul_pos = Expr::const_(Name::from_string("Rat.mul_pos"), vec![]);
    let h_prod_pos = Expr::apps(mul_pos, [a.clone(), c_sub_b.clone(), h_a, h_cb_pos]);
    // 3. mul_sub a c b : a·(c−b) = a·c − a·b ; subst under fun x => 0 < x
    let mul_sub = Expr::const_(Name::from_string("Rat.mul_sub"), vec![]);
    let h_dist = Expr::apps(mul_sub, [a.clone(), cv.clone(), bv.clone()]);
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = rat_lt(c, zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let h_acab_pos = c.subst(motive, a_csb, ac_sub_ab.clone(), h_dist, h_prod_pos); // 0 < a·c − a·b
                                                                                    // 4. lt_of_sub_pos (a·b) (a·c) h_acab_pos : a·b < a·c
    let lt_of_sub_pos = Expr::const_(Name::from_string("Rat.lt_of_sub_pos"), vec![]);
    let body = Expr::apps(lt_of_sub_pos, [ab, ac, h_acab_pos]);

    let e = b.mk_lam(ha_id, BinderInfo::Default, h_a_ty, body);
    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// `Rat.le_of_sq_le_sq` (deliverable 5) is deferred to run 5: it needs a strict
// `b·b < a·a` in the `b ≤ a` branch and hence `Rat.lt_of_lt_of_le`, which must
// be lifted from the constructive `Int.lt_cross_trans'` through the
// `Rat.effDenom`-positivity bridge. See parent module doc.
