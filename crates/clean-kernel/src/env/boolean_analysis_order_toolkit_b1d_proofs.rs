// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B1d square-root monotonicity — proof-term builders.
//!
//! Split from `boolean_analysis_order_toolkit_b1d.rs` to keep each file under
//! the 500-line limit (mirrors the B1 / B1b / B1c `_proofs` splits). The
//! registration entry points live in the parent module; this file holds the
//! pure proof-term and type construction the registrars consume.
//!
//! `Rat.lt` is a `Quot.lift` and is NEVER reduced for variable arguments — all
//! strict-order reasoning goes through `Rat.lt_iff_le_not_le` propositionally,
//! exactly as in the B1b / B1c layers.
//!
//! Two lemmas are built here:
//!
//! - `Rat.sq_lt_sq_of_lt_of_nonneg a b (hb : 0 ≤ b) (hba : b < a) : b·b < a·a`
//!     The contrapositive square-monotonicity step. From `mp hba` extract
//!     `b ≤ a`; `0 < a` via `lt_of_le_of_lt 0 b a hb hba`;
//!     `mul_le_mul_of_nonneg_right b b a (b≤a) hb : b·b ≤ a·b` and
//!     `mul_lt_mul_of_pos_left a b a hba (0<a) : a·b < a·a`; chained by
//!     `lt_of_le_of_lt (b·b) (a·b) (a·a)`.
//!
//! - `Rat.le_of_sq_le_sq a b (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a·a ≤ b·b) : a ≤ b`
//!     `Classical.em (a ≤ b)` splits into `a ≤ b` (done) and `¬(a ≤ b)`. In the
//!     negative branch, `le_total a b` re-splits: `a ≤ b` returns the witness,
//!     and `b ≤ a` builds `b < a` from `lt_iff.mpr ⟨b≤a, ¬(a≤b)⟩`, applies
//!     `sq_lt_sq_of_lt_of_nonneg a b hb (b<a) : b·b < a·a`, contradicts the
//!     hypothesis via `lt_of_lt_of_le (b·b) (a·a) (b·b) (b·b<a·a) h : b·b < b·b`,
//!     extracts `False` from `lt_iff.mp` (`And.right` applied to `And.left`),
//!     and closes with `False.elim`.
//!
//! Both classify `ProofQuality::Constructive`: `Classical.em`'s transitive
//! axiom closure is `⊆ FOUNDATIONAL_AXIOMS` (`{propext, funext,
//! Classical.choice}`), which `Environment::axiom_deps` filters out, so the
//! domain-axiom closure stays EMPTY.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Small Prop-eliminator plumbing (And / Iff / Or / False) shared by builders
// ---------------------------------------------------------------------------

/// `Rat.lt a b` (stated; never reduced).
fn rat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
}

/// `Not P ≡ P → False`, built as a `Pi` to match `Classical.em`'s negative
/// branch shape exactly (`Classical.em` unfolds `Not` to `p → False`).
fn not_pi(parent: &EnvDeclBuilder, p: Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let false_ = Expr::const_(Name::from_string("False"), vec![]);
    let (x_id, _) = ch.fresh_local(p.clone());
    let r = ch.mk_pi(x_id, BinderInfo::Default, p, false_);
    ch.finish_child(r)
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

/// `Rat.lt_iff_le_not_le a b : Iff (Rat.lt a b)(And (Rat.le a b)(Not (Rat.le b a)))`.
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}

/// The RHS of `Rat.lt_iff_le_not_le a b`: `And (Rat.le a b)(Not (Rat.le b a))`,
/// with the `Not` as a `Pi` so it matches the shape `Iff.mp`/`Iff.mpr` expect.
fn lt_rhs(parent: &EnvDeclBuilder, c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    and_(
        c.rat_le(a.clone(), b.clone()),
        not_pi(parent, c.rat_le(b, a)),
    )
}

/// `Rat.lt_of_le_of_lt a b c h1 h2 : Rat.lt a c`.
fn lt_of_le_of_lt(a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]),
        [a, b, cc, h1, h2],
    )
}

/// `Rat.lt_of_lt_of_le a b c h1 h2 : Rat.lt a c`.
fn lt_of_lt_of_le(a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]),
        [a, b, cc, h1, h2],
    )
}

/// `@False.elim.{0} goal h_false : goal`.
fn false_elim(goal: Expr, h_false: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal, h_false],
    )
}

/// Case-split on `h_or : Or p q` into a (non-dependent) `goal`, via
/// `@Or.rec p q (fun _ => goal) h_left h_right h_or`. `h_left` / `h_right` must
/// be functions `p → goal` / `q → goal`. `parent` is the builder whose fvar
/// scope `goal`/`h_*` live in.
fn or_elim(
    parent: &EnvDeclBuilder,
    p: Expr,
    q: Expr,
    goal: Expr,
    h_or: Expr,
    h_left: Expr,
    h_right: Expr,
) -> Expr {
    let or_c = Expr::const_(Name::from_string("Or"), vec![]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
        let (h_id, _) = m.fresh_local(or_ty.clone());
        let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, goal);
        m.finish_child(lam)
    };
    Expr::apps(or_rec, [p, q, motive, h_left, h_right, h_or])
}

/// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_a : Rat.le (b·a) (c·a)`.
/// Signature: `∀ a b c, b ≤ c → 0 ≤ a → b·a ≤ c·a`.
fn mul_le_right(a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
        [a, b, cc, h_bc, h_a],
    )
}

/// `Rat.mul_lt_mul_of_pos_left a b c h_bc h_a : Rat.lt (a·b) (a·c)`.
/// Signature: `∀ a b c, b < c → 0 < a → a·b < a·c`.
fn mul_lt_left(a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_lt_mul_of_pos_left"), vec![]),
        [a, b, cc, h_bc, h_a],
    )
}

// ---------------------------------------------------------------------------
// 1. Rat.sq_lt_sq_of_lt_of_nonneg : ∀ a b, 0 ≤ b → b < a → b·b < a·a
// ---------------------------------------------------------------------------

/// Type of `Rat.sq_lt_sq_of_lt_of_nonneg`:
/// `∀ a b, Rat.le 0 b → Rat.lt b a → Rat.lt (b·b) (a·a)`.
pub(super) fn sq_lt_sq_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_nn_ty = c.rat_le(c.rat_zero.clone(), bv.clone());
    let h_lt_ty = rat_lt(bv.clone(), a.clone());
    let concl = rat_lt(c.mul(bv.clone(), bv.clone()), c.mul(a.clone(), a.clone()));
    let (hnn_id, _) = b.fresh_local(h_nn_ty.clone());
    let (hlt_id, _) = b.fresh_local(h_lt_ty.clone());
    let e = b.mk_pi(hlt_id, BinderInfo::Default, h_lt_ty, concl);
    let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn_ty, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sq_lt_sq_of_lt_of_nonneg`.
pub(super) fn build_sq_lt_sq_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_nn_ty = c.rat_le(c.rat_zero.clone(), bv.clone());
    let h_lt_ty = rat_lt(bv.clone(), a.clone());
    let (hnn_id, h_nn) = b.fresh_local(h_nn_ty.clone());
    let (hlt_id, h_lt) = b.fresh_local(h_lt_ty.clone());

    // mp h_lt : (b ≤ a) ∧ ¬(a ≤ b)  ⇒  h_le_ba : b ≤ a
    let le_ba = c.rat_le(bv.clone(), a.clone());
    let not_le_ab = not_pi(&b, c.rat_le(a.clone(), bv.clone()));
    let rhs_ba = lt_rhs(&b, c, bv.clone(), a.clone());
    let mp = iff_mp(
        rat_lt(bv.clone(), a.clone()),
        rhs_ba,
        lt_iff(bv.clone(), a.clone()),
        h_lt.clone(),
    );
    let h_le_ba = and_left(le_ba, not_le_ab, mp); // b ≤ a

    // h_0a : 0 < a   [lt_of_le_of_lt 0 b a h_nn h_lt]
    let h_0a = lt_of_le_of_lt(
        c.rat_zero.clone(),
        bv.clone(),
        a.clone(),
        h_nn.clone(),
        h_lt.clone(),
    );

    let bb = c.mul(bv.clone(), bv.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let aa = c.mul(a.clone(), a.clone());

    // base_le : b·b ≤ a·b
    //   mul_le_mul_of_nonneg_right (a := b) (b := b) (c := a) (b≤a) (0≤b)
    let base_le = mul_le_right(bv.clone(), bv.clone(), a.clone(), h_le_ba, h_nn);
    // base_lt : a·b < a·a
    //   mul_lt_mul_of_pos_left (a := a) (b := b) (c := a) (b<a) (0<a)
    let base_lt = mul_lt_left(a.clone(), bv.clone(), a.clone(), h_lt, h_0a);

    // body : b·b < a·a   [lt_of_le_of_lt (b·b) (a·b) (a·a) base_le base_lt]
    let body = lt_of_le_of_lt(bb, ab, aa, base_le, base_lt);

    let e = b.mk_lam(hlt_id, BinderInfo::Default, h_lt_ty, body);
    let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 2. Rat.le_of_sq_le_sq : ∀ a b, 0 ≤ a → 0 ≤ b → a·a ≤ b·b → a ≤ b
// ---------------------------------------------------------------------------

/// Type of `Rat.le_of_sq_le_sq`:
/// `∀ a b, Rat.le 0 a → Rat.le 0 b → Rat.le (a·a) (b·b) → Rat.le a b`.
pub(super) fn le_of_sq_le_sq_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let h_b_ty = c.rat_le(c.rat_zero.clone(), bv.clone());
    let h_sq_ty = c.rat_le(c.mul(a.clone(), a.clone()), c.mul(bv.clone(), bv.clone()));
    let concl = c.rat_le(a.clone(), bv.clone());
    let (ha_id, _) = b.fresh_local(h_a_ty.clone());
    let (hb_id, _) = b.fresh_local(h_b_ty.clone());
    let (hsq_id, _) = b.fresh_local(h_sq_ty.clone());
    let e = b.mk_pi(hsq_id, BinderInfo::Default, h_sq_ty, concl);
    let e = b.mk_pi(hb_id, BinderInfo::Default, h_b_ty, e);
    let e = b.mk_pi(ha_id, BinderInfo::Default, h_a_ty, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.le_of_sq_le_sq`.
pub(super) fn build_le_of_sq_le_sq_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let h_b_ty = c.rat_le(c.rat_zero.clone(), bv.clone());
    let h_sq_ty = c.rat_le(c.mul(a.clone(), a.clone()), c.mul(bv.clone(), bv.clone()));
    let (ha_id, _h_a) = b.fresh_local(h_a_ty.clone());
    let (hb_id, h_b) = b.fresh_local(h_b_ty.clone());
    let (hsq_id, h_sq) = b.fresh_local(h_sq_ty.clone());

    let le_ab = c.rat_le(a.clone(), bv.clone()); // a ≤ b  (the goal)
    let not_le_ab = not_pi(&b, le_ab.clone()); // ¬(a ≤ b)
    let le_ba = c.rat_le(bv.clone(), a.clone()); // b ≤ a

    // em (a ≤ b) : Or (a ≤ b) (¬(a ≤ b))
    let em = Expr::const_(Name::from_string("Classical.em"), vec![]);
    let h_em = Expr::app(em, le_ab.clone());

    // Positive em branch: λ (h : a ≤ b) => h
    let em_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = ch.fresh_local(le_ab.clone());
        let lam = ch.mk_lam(h_id, BinderInfo::Default, le_ab.clone(), h);
        ch.finish_child(lam)
    };

    // Negative em branch: λ (hn : ¬(a ≤ b)) => <le_total split>
    let em_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hn_id, hn) = ch.fresh_local(not_le_ab.clone());

        // le_total a b : Or (a ≤ b) (b ≤ a)
        let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
        let h_total = Expr::apps(le_total, [a.clone(), bv.clone()]);

        // total-left branch: λ (h : a ≤ b) => h   (returns the witness)
        let tot_left = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (h_id, h) = d.fresh_local(le_ab.clone());
            let lam = d.mk_lam(h_id, BinderInfo::Default, le_ab.clone(), h);
            d.finish_child(lam)
        };

        // total-right branch: λ (hba : b ≤ a) => False.elim (a ≤ b) <False>
        let tot_right = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (hba_id, hba) = d.fresh_local(le_ba.clone());

            // h_lt_ba : b < a   [Iff.mpr (lt_iff b a) (And.intro (b≤a) (¬(a≤b)) hba hn)]
            let not_le_ab_d = not_pi(&d, le_ab.clone());
            let and_proof = and_intro(le_ba.clone(), not_le_ab_d.clone(), hba, hn.clone());
            let h_lt_ba = iff_mpr(
                rat_lt(bv.clone(), a.clone()),
                and_(le_ba.clone(), not_le_ab_d),
                lt_iff(bv.clone(), a.clone()),
                and_proof,
            );

            // h_bb_lt_aa : b·b < a·a   [sq_lt_sq_of_lt_of_nonneg a b h_b h_lt_ba]
            let sq_lt_sq = Expr::const_(Name::from_string("Rat.sq_lt_sq_of_lt_of_nonneg"), vec![]);
            let h_bb_lt_aa = Expr::apps(sq_lt_sq, [a.clone(), bv.clone(), h_b.clone(), h_lt_ba]);

            let bb = c.mul(bv.clone(), bv.clone());
            let aa = c.mul(a.clone(), a.clone());

            // h_bb_lt_bb : b·b < b·b   [lt_of_lt_of_le (b·b) (a·a) (b·b) h_bb_lt_aa h_sq]
            let h_bb_lt_bb = lt_of_lt_of_le(bb.clone(), aa, bb.clone(), h_bb_lt_aa, h_sq.clone());

            // mp h_bb_lt_bb : (b·b ≤ b·b) ∧ ¬(b·b ≤ b·b)
            let le_bbbb = c.rat_le(bb.clone(), bb.clone());
            let not_le_bbbb = not_pi(&d, le_bbbb.clone());
            let rhs_bb = lt_rhs(&d, c, bb.clone(), bb.clone());
            let mp_bb = iff_mp(
                rat_lt(bb.clone(), bb.clone()),
                rhs_bb,
                lt_iff(bb.clone(), bb.clone()),
                h_bb_lt_bb,
            );
            let h_le_bbbb = and_left(le_bbbb.clone(), not_le_bbbb.clone(), mp_bb.clone());
            let h_not_le_bbbb = and_right(le_bbbb.clone(), not_le_bbbb.clone(), mp_bb);
            // false : ¬(b·b ≤ b·b) applied to (b·b ≤ b·b)
            let h_false = Expr::app(h_not_le_bbbb, h_le_bbbb);

            let body = false_elim(le_ab.clone(), h_false);
            let lam = d.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), body);
            d.finish_child(lam)
        };

        let body = or_elim(
            &ch,
            le_ab.clone(),
            le_ba.clone(),
            le_ab.clone(),
            h_total,
            tot_left,
            tot_right,
        );
        let lam = ch.mk_lam(hn_id, BinderInfo::Default, not_le_ab.clone(), body);
        ch.finish_child(lam)
    };

    // Or.rec over em: motive (fun _ => a ≤ b). The em negative branch type is
    // `¬(a ≤ b)` (a `Pi`), so `or_elim`'s `q` is `not_le_ab`.
    let body = or_elim(
        &b,
        le_ab.clone(),
        not_le_ab.clone(),
        le_ab.clone(),
        h_em,
        em_pos,
        em_neg,
    );

    let e = b.mk_lam(hsq_id, BinderInfo::Default, h_sq_ty, body);
    let e = b.mk_lam(hb_id, BinderInfo::Default, h_b_ty, e);
    let e = b.mk_lam(ha_id, BinderInfo::Default, h_a_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
