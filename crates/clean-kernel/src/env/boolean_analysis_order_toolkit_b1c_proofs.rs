// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B1c mixed strict/non-strict transitivity — proof-term builders.
//!
//! Split from `boolean_analysis_order_toolkit_b1c.rs` to keep each file under
//! the 500-line limit (mirrors the B1 / B1b `_proofs` split). The registration
//! entry points live in the parent module; this file holds the pure proof-term
//! and type construction the registrars consume.
//!
//! `Rat.lt` is a `Quot.lift` and is NEVER reduced for variable arguments — all
//! strict-order reasoning goes through `Rat.lt_iff_le_not_le` propositionally,
//! exactly as in the B1b layer. The two mixed-transitivity lemmas built here
//! (`Rat.lt_of_le_of_lt`, `Rat.lt_of_lt_of_le`) are PURELY PROPOSITIONAL
//! consequences of `Rat.le_trans` + `Rat.lt_iff_le_not_le`:
//!
//! - `lt_of_le_of_lt a b c (hab : a ≤ b) (hbc : b < c) : a < c`
//!     le-half:     `le_trans a b c hab (And.left (mp hbc)) : a ≤ c`
//!     not-le half: `λ (h : c ≤ a) => (And.right (mp hbc)) (le_trans c a b h hab)`
//!                  — `c ≤ a` and `a ≤ b` give `c ≤ b`, contradicting `¬(c ≤ b)`.
//!
//! - `lt_of_lt_of_le a b c (hab : a < b) (hbc : b ≤ c) : a < c`
//!     le-half:     `le_trans a b c (And.left (mp hab)) hbc : a ≤ c`
//!     not-le half: `λ (h : c ≤ a) => (And.right (mp hab)) (le_trans b c a hbc h)`
//!                  — `b ≤ c` and `c ≤ a` give `b ≤ a`, contradicting `¬(b ≤ a)`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Small Prop-eliminator plumbing (And / Iff / Not) shared by builders
// ---------------------------------------------------------------------------

/// `Rat.lt a b` (stated; never reduced).
fn rat_lt(a: Expr, b: Expr) -> Expr {
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

/// `Rat.lt_iff_le_not_le a b : Iff (Rat.lt a b)(And (Rat.le a b)(Not (Rat.le b a)))`.
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}

/// The RHS of `Rat.lt_iff_le_not_le a b`: `And (Rat.le a b)(Not (Rat.le b a))`.
fn lt_rhs(c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    and_(c.rat_le(a.clone(), b.clone()), not_(c.rat_le(b, a)))
}

/// `Rat.le_trans a b c h1 h2 : Rat.le a c`.
fn le_trans(a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [a, b, cc, h1, h2],
    )
}

// ---------------------------------------------------------------------------
// Shared 3-Rat-binder + two-hypotheses scaffolding
// ---------------------------------------------------------------------------

/// Build the type `∀ a b c, H1 → H2 → (Rat.lt a c)` where `H1`/`H2` are the
/// per-lemma hypothesis-shape closures over `(a,b,c)`.
fn mixed_trans_type(
    c: &OrderConsts,
    h1_of: impl Fn(&Expr, &Expr, &Expr) -> Expr,
    h2_of: impl Fn(&Expr, &Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h1_ty = h1_of(&a, &bv, &cv);
    let h2_ty = h2_of(&a, &bv, &cv);
    let concl = rat_lt(a.clone(), cv.clone());
    let (h1_id, _) = b.fresh_local(h1_ty.clone());
    let (h2_id, _) = b.fresh_local(h2_ty.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 1. Rat.lt_of_le_of_lt : ∀ a b c, a ≤ b → b < c → a < c
// ---------------------------------------------------------------------------

/// Type of `Rat.lt_of_le_of_lt`: `∀ a b c, Rat.le a b → Rat.lt b c → Rat.lt a c`.
pub(super) fn lt_of_le_of_lt_type(c: &OrderConsts) -> Expr {
    mixed_trans_type(
        c,
        |a, bv, _cv| c.rat_le(a.clone(), bv.clone()),
        |_a, bv, cv| rat_lt(bv.clone(), cv.clone()),
    )
}

/// Build the proof term for `Rat.lt_of_le_of_lt`.
pub(super) fn build_lt_of_le_of_lt_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = c.rat_le(a.clone(), bv.clone());
    let h_bc_ty = rat_lt(bv.clone(), cv.clone());
    let (hab_id, h_ab) = b.fresh_local(h_ab_ty.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());

    // mp hbc : (b ≤ c) ∧ ¬(c ≤ b)
    let rhs_bc = lt_rhs(c, bv.clone(), cv.clone());
    let mp = iff_mp(
        rat_lt(bv.clone(), cv.clone()),
        rhs_bc.clone(),
        lt_iff(bv.clone(), cv.clone()),
        h_bc,
    );
    let le_bc = c.rat_le(bv.clone(), cv.clone());
    let not_le_cb = not_(c.rat_le(cv.clone(), bv.clone()));
    let h_le_bc = and_left(le_bc.clone(), not_le_cb.clone(), mp.clone()); // b ≤ c
    let h_not_le_cb = and_right(le_bc.clone(), not_le_cb.clone(), mp); // ¬(c ≤ b)

    // le half: a ≤ c  via le_trans a b c hab h_le_bc
    let h_le_ac = le_trans(a.clone(), bv.clone(), cv.clone(), h_ab.clone(), h_le_bc);

    // not-le half: λ (h : c ≤ a) => h_not_le_cb (le_trans c a b h hab) : False
    let le_ca = c.rat_le(cv.clone(), a.clone());
    let not_le_half = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h_ca) = ch.fresh_local(le_ca.clone());
        // c ≤ b  via le_trans c a b (c≤a) (a≤b)
        let h_cb = le_trans(cv.clone(), a.clone(), bv.clone(), h_ca, h_ab.clone());
        let false_proof = Expr::app(h_not_le_cb, h_cb);
        let lam = ch.mk_lam(h_id, BinderInfo::Default, le_ca.clone(), false_proof);
        ch.finish_child(lam)
    };

    // Iff.mpr (lt_iff a c) (And.intro (a ≤ c) (¬(c ≤ a)) ..)
    let le_ac = c.rat_le(a.clone(), cv.clone());
    let not_le_ca = not_(le_ca);
    let and_proof = and_intro(le_ac.clone(), not_le_ca.clone(), h_le_ac, not_le_half);
    let body = iff_mpr(
        rat_lt(a.clone(), cv.clone()),
        and_(le_ac, not_le_ca),
        lt_iff(a.clone(), cv.clone()),
        and_proof,
    );

    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 2. Rat.lt_of_lt_of_le : ∀ a b c, a < b → b ≤ c → a < c
// ---------------------------------------------------------------------------

/// Type of `Rat.lt_of_lt_of_le`: `∀ a b c, Rat.lt a b → Rat.le b c → Rat.lt a c`.
pub(super) fn lt_of_lt_of_le_type(c: &OrderConsts) -> Expr {
    mixed_trans_type(
        c,
        |a, bv, _cv| rat_lt(a.clone(), bv.clone()),
        |_a, bv, cv| c.rat_le(bv.clone(), cv.clone()),
    )
}

/// Build the proof term for `Rat.lt_of_lt_of_le`.
pub(super) fn build_lt_of_lt_of_le_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = rat_lt(a.clone(), bv.clone());
    let h_bc_ty = c.rat_le(bv.clone(), cv.clone());
    let (hab_id, h_ab) = b.fresh_local(h_ab_ty.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());

    // mp hab : (a ≤ b) ∧ ¬(b ≤ a)
    let rhs_ab = lt_rhs(c, a.clone(), bv.clone());
    let mp = iff_mp(
        rat_lt(a.clone(), bv.clone()),
        rhs_ab.clone(),
        lt_iff(a.clone(), bv.clone()),
        h_ab,
    );
    let le_ab = c.rat_le(a.clone(), bv.clone());
    let not_le_ba = not_(c.rat_le(bv.clone(), a.clone()));
    let h_le_ab = and_left(le_ab.clone(), not_le_ba.clone(), mp.clone()); // a ≤ b
    let h_not_le_ba = and_right(le_ab.clone(), not_le_ba.clone(), mp); // ¬(b ≤ a)

    // le half: a ≤ c  via le_trans a b c h_le_ab hbc
    let h_le_ac = le_trans(a.clone(), bv.clone(), cv.clone(), h_le_ab, h_bc.clone());

    // not-le half: λ (h : c ≤ a) => h_not_le_ba (le_trans b c a hbc h) : False
    let le_ca = c.rat_le(cv.clone(), a.clone());
    let not_le_half = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h_ca) = ch.fresh_local(le_ca.clone());
        // b ≤ a  via le_trans b c a (b≤c) (c≤a)
        let h_ba = le_trans(bv.clone(), cv.clone(), a.clone(), h_bc.clone(), h_ca);
        let false_proof = Expr::app(h_not_le_ba, h_ba);
        let lam = ch.mk_lam(h_id, BinderInfo::Default, le_ca.clone(), false_proof);
        ch.finish_child(lam)
    };

    // Iff.mpr (lt_iff a c) (And.intro (a ≤ c) (¬(c ≤ a)) ..)
    let le_ac = c.rat_le(a.clone(), cv.clone());
    let not_le_ca = not_(le_ca);
    let and_proof = and_intro(le_ac.clone(), not_le_ca.clone(), h_le_ac, not_le_half);
    let body = iff_mpr(
        rat_lt(a.clone(), cv.clone()),
        and_(le_ac, not_le_ca),
        lt_iff(a.clone(), cv.clone()),
        and_proof,
    );

    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// 3. Int.lt_or_eq_of_le : ∀ a b : Int, Int.le a b → Or (Int.lt a b) (Eq a b)
//    (the strictness splitter — Int-level core for run-6's Rat.le_of_sq_le_sq)
// ---------------------------------------------------------------------------

/// `Or P Q`.
fn or_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [p, q])
}

/// `@Or.inl P Q h : Or P Q`.
fn or_inl(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or.inl"), vec![]), [p, q, h])
}

/// `@Or.inr P Q h : Or P Q`.
fn or_inr(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or.inr"), vec![]), [p, q, h])
}

/// Type of `Int.lt_or_eq_of_le`:
/// `∀ a b : Int, Int.le a b → Or (Int.lt a b) (Eq Int a b)`.
pub(super) fn int_lt_or_eq_of_le_type() -> Expr {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    let le_c = Expr::const_(Name::from_string("Int.le"), vec![]);
    let lt_c = Expr::const_(Name::from_string("Int.lt"), vec![]);
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(int.clone());
    let (bv_id, bv) = b.fresh_local(int.clone());
    let h_ty = Expr::apps(le_c, [a.clone(), bv.clone()]);
    let eq_ab = Expr::apps(eq_c, [int.clone(), a.clone(), bv.clone()]);
    let goal = or_(Expr::apps(lt_c, [a.clone(), bv.clone()]), eq_ab);
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, goal);
    let e = b.mk_pi(bv_id, BinderInfo::Default, int.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, int, e);
    b.finish(e)
}

/// Build the proof term for `Int.lt_or_eq_of_le`.
///
/// Eliminate `Int.lt_trichotomy a b : Or (lt a b) (Or (Eq a b) (lt b a))`
/// with two nested `Or.rec`s (constant motive `Goal := Or (lt a b) (Eq a b)`):
///   - `lt a b`  → `Or.inl`.
///   - `Eq a b`  → `Or.inr`.
///   - `lt b a`  → impossible: `Int.lt_of_lt_of_le b a b hba h : lt b b`
///     contradicts `Int.lt_irrefl b`; `False.elim` closes the goal.
pub(super) fn build_int_lt_or_eq_of_le_proof() -> Expr {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    let le_c = Expr::const_(Name::from_string("Int.le"), vec![]);
    let lt_c = Expr::const_(Name::from_string("Int.lt"), vec![]);
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let trichotomy = Expr::const_(Name::from_string("Int.lt_trichotomy"), vec![]);
    let lt_of_lt_of_le = Expr::const_(Name::from_string("Int.lt_of_lt_of_le"), vec![]);
    let lt_irrefl = Expr::const_(Name::from_string("Int.lt_irrefl"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(int.clone());
    let (bv_id, bv) = b.fresh_local(int.clone());
    let h_ty = Expr::apps(le_c, [a.clone(), bv.clone()]);
    let (h_id, h_le) = b.fresh_local(h_ty.clone());

    let lt_ab = Expr::apps(lt_c.clone(), [a.clone(), bv.clone()]);
    let lt_ba = Expr::apps(lt_c, [bv.clone(), a.clone()]);
    let eq_ab = Expr::apps(eq_c, [int.clone(), a.clone(), bv.clone()]);
    let inner_or = or_(eq_ab.clone(), lt_ba.clone()); // Or (Eq a b) (lt b a)
    let goal = or_(lt_ab.clone(), eq_ab.clone()); // Or (lt a b) (Eq a b)

    // Constant motive for the OUTER Or.rec: fun (_ : Or (lt a b) inner) => goal.
    let outer_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let or_ty = or_(lt_ab.clone(), inner_or.clone());
        let (x_id, _x) = m.fresh_local(or_ty.clone());
        let lam = m.mk_lam(x_id, BinderInfo::Default, or_ty, goal.clone());
        m.finish_child(lam)
    };
    // Outer inl: fun (hlt : lt a b) => Or.inl (lt a b) (Eq a b) hlt.
    let outer_inl = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (hlt_id, hlt) = m.fresh_local(lt_ab.clone());
        let body = or_inl(lt_ab.clone(), eq_ab.clone(), hlt);
        let lam = m.mk_lam(hlt_id, BinderInfo::Default, lt_ab.clone(), body);
        m.finish_child(lam)
    };
    // Outer inr: fun (hor : Or (Eq a b) (lt b a)) => <inner Or.rec>.
    let outer_inr = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (hor_id, hor) = m.fresh_local(inner_or.clone());

        // Constant motive for the INNER Or.rec.
        let inner_motive = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (x_id, _x) = mm.fresh_local(inner_or.clone());
            let lam = mm.mk_lam(x_id, BinderInfo::Default, inner_or.clone(), goal.clone());
            mm.finish_child(lam)
        };
        // Inner inl: fun (heq : Eq a b) => Or.inr (lt a b) (Eq a b) heq.
        let inner_inl = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (heq_id, heq) = mm.fresh_local(eq_ab.clone());
            let body = or_inr(lt_ab.clone(), eq_ab.clone(), heq);
            let lam = mm.mk_lam(heq_id, BinderInfo::Default, eq_ab.clone(), body);
            mm.finish_child(lam)
        };
        // Inner inr: fun (hba : lt b a) =>
        //   False.elim goal (lt_irrefl b (lt_of_lt_of_le b a b hba h_le)).
        let inner_inr = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (hba_id, hba) = mm.fresh_local(lt_ba.clone());
            // lt b b  via Int.lt_of_lt_of_le b a b hba h_le
            let lt_bb = Expr::apps(
                lt_of_lt_of_le.clone(),
                [bv.clone(), a.clone(), bv.clone(), hba, h_le.clone()],
            );
            // False  via Int.lt_irrefl b (lt b b)
            let false_pf = Expr::apps(lt_irrefl.clone(), [bv.clone(), lt_bb]);
            let body = Expr::apps(false_elim.clone(), [goal.clone(), false_pf]);
            let lam = mm.mk_lam(hba_id, BinderInfo::Default, lt_ba.clone(), body);
            mm.finish_child(lam)
        };
        let inner_rec = Expr::apps(
            or_rec.clone(),
            [
                eq_ab.clone(),
                lt_ba.clone(),
                inner_motive,
                inner_inl,
                inner_inr,
                hor,
            ],
        );
        let lam = m.mk_lam(hor_id, BinderInfo::Default, inner_or.clone(), inner_rec);
        m.finish_child(lam)
    };

    let major = Expr::apps(trichotomy, [a.clone(), bv.clone()]);
    let body = Expr::apps(
        or_rec,
        [
            lt_ab.clone(),
            inner_or.clone(),
            outer_motive,
            outer_inl,
            outer_inr,
            major,
        ],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, int.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, int, e);
    b.finish(e)
}
