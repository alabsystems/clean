// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 blocker (#3503): proof-term builders for the Rat field→order
//! bridging lemmas.
//!
//! Extracted from `nn_verify_rat_ordering.rs` for file-size compliance
//! (500-line limit). Contains the two non-trivial proof-term builders
//! (`build_mul_sub_proof`, `build_le_of_sub_nonneg_proof`). The simpler
//! proofs (`build_sub_self_proof`, `build_sub_nonneg_of_le_proof`) stay
//! inline in the parent module.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_rat_ordering::RatOrdConsts;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build proof term for `Rat.mul_sub`:
///
/// `∀ a b c : Rat, Rat.mul a (Rat.sub b c) = Rat.sub (Rat.mul a b) (Rat.mul a c)`.
///
/// Both sides unfold via delta on `Rat.sub` to
/// `a * (b + (-c)) = (a*b) + (-(a*c))`.
///
/// Chain:
/// * `h1 : a * (b + (-c)) = (a*b) + (a*(-c))`  via `Rat.left_distrib`.
/// * `h2 : a * (-c) = -(a*c)`                   via `Rat.mul_neg`.
/// * `Eq.subst` with motive `λ x, a*(b+(-c)) = (a*b) + x` rewrites
///   h1's RHS from `a*(-c)` to `-(a*c)`.
pub(super) fn build_mul_sub_proof(c: &RatOrdConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());

    let a_b = c.mul(a.clone(), bv.clone());
    let a_c = c.mul(a.clone(), cv.clone());
    let neg_c = c.neg(cv.clone());
    let b_plus_negc = c.add(bv.clone(), neg_c.clone());
    let a_times_negc = c.mul(a.clone(), neg_c);
    let neg_ac = c.neg(a_c);

    // h1 : a * (b + (-c)) = (a*b) + (a*(-c))  via Rat.left_distrib.
    let left_distrib = Expr::const_(Name::from_string("Rat.left_distrib"), vec![]);
    let h1 = Expr::apps(left_distrib, [a.clone(), bv.clone(), c.neg(cv.clone())]);

    // h2 : a * (-c) = -(a*c)  via Rat.mul_neg.
    let mul_neg = Expr::const_(Name::from_string("Rat.mul_neg"), vec![]);
    let h2 = Expr::apps(mul_neg, [a.clone(), cv.clone()]);

    // motive : Rat → Prop = fun x => Eq Rat (a * (b + (-c))) ((a*b) + x)
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let lhs_eq = c.mul(a.clone(), b_plus_negc.clone());
        let rhs_eq = c.add(a_b.clone(), x);
        let body_eq = c.rat_eq(lhs_eq, rhs_eq);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body_eq);
        ch.finish_child(r)
    };

    // Eq.subst motive (a*(-c)) (-(a*c)) h2 h1 : Eq (a*(b+(-c))) ((a*b) + (-(a*c)))
    // which is definitionally `a * (b - c) = (a*b) - (a*c)` via delta on Rat.sub.
    let body = c.subst(motive, a_times_negc, neg_ac, h2, h1);

    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build proof term for `Rat.le_of_sub_nonneg`:
///
/// `∀ a b : Rat, Rat.le Rat.zero (Rat.sub b a) → Rat.le a b`.
///
/// Proof sketch:
///
/// 1. `h_add : Rat.le (a + 0) (a + (b + (-a)))` via
///    `Rat.add_le_add_left 0 (b + (-a)) h a`.
/// 2. Rewrite LHS `a + 0 → a` via `Rat.add_zero` + Eq.subst, giving
///    `Rat.le a (a + (b + (-a)))`.
/// 3. Compose a chain `h_simp : a + (b + (-a)) = b` via Eq.trans of
///    `add_comm`, `add_assoc` (symm), `add_neg_self`, and `zero_add`.
/// 4. Transport via Eq.subst with motive `λ x, Rat.le a x` yields
///    `Rat.le a b`. QED.
pub(super) fn build_le_of_sub_nonneg_proof(c: &RatOrdConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_ty = c.rat_le(c.rat_zero.clone(), c.sub(bv.clone(), a.clone()));
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let neg_a = c.neg(a.clone());
    let b_plus_nega = c.add(bv.clone(), neg_a.clone()); // = Rat.sub b a (defeq)
    let nega_plus_b = c.add(neg_a.clone(), bv.clone());
    let a_plus_zero = c.add(a.clone(), c.rat_zero.clone());
    let a_plus_bnega = c.add(a.clone(), b_plus_nega.clone());
    let a_plus_negab = c.add(a.clone(), nega_plus_b.clone());
    let a_plus_nega = c.add(a.clone(), neg_a.clone());
    let aplus_nega_plus_b = c.add(a_plus_nega.clone(), bv.clone());
    let zero_plus_b = c.add(c.rat_zero.clone(), bv.clone());

    // h_add : Rat.le (a + 0) (a + (b + (-a)))
    let add_le_add_left = Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]);
    let h_add = Expr::apps(
        add_le_add_left,
        [c.rat_zero.clone(), b_plus_nega.clone(), h, a.clone()],
    );

    // h_azero : a + 0 = a  via Rat.add_zero a.
    let add_zero_const = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
    let h_azero = Expr::app(add_zero_const, a.clone());

    // motive1 : Rat → Prop = fun x => Rat.le x (a + (b + (-a)))
    let motive1 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, a_plus_bnega.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // step1 : Rat.le a (a + (b + (-a)))
    let step1 = c.subst(motive1, a_plus_zero, a.clone(), h_azero, h_add);

    let h_simp = build_le_of_sub_nonneg_h_simp(
        c,
        &mut b,
        &a,
        &bv,
        &neg_a,
        &b_plus_nega,
        &nega_plus_b,
        &a_plus_bnega,
        &a_plus_negab,
        &a_plus_nega,
        &aplus_nega_plus_b,
        &zero_plus_b,
    );

    // motive_final : Rat → Prop = fun x => Rat.le a x
    let motive_final = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(a.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // Eq.subst motive_final (a + (b+(-a))) b h_simp step1 : Rat.le a b
    let body = c.subst(motive_final, a_plus_bnega, bv.clone(), h_simp, step1);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the inner `h_simp : a + (b + (-a)) = b` equality chain used by
/// `build_le_of_sub_nonneg_proof`. Extracted as a helper to keep the
/// parent function under the 80-line function-size limit.
fn build_le_of_sub_nonneg_h_simp(
    c: &RatOrdConsts,
    b: &mut EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    neg_a: &Expr,
    b_plus_nega: &Expr,
    nega_plus_b: &Expr,
    a_plus_bnega: &Expr,
    a_plus_negab: &Expr,
    a_plus_nega: &Expr,
    aplus_nega_plus_b: &Expr,
    zero_plus_b: &Expr,
) -> Expr {
    // e1 : b + (-a) = (-a) + b   via Rat.add_comm b (-a).
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let e1 = Expr::apps(add_comm, [bv.clone(), neg_a.clone()]);
    // motive_e1 : fun x => Eq Rat (a + (b+(-a))) (a + x)
    let motive_e1 = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let lhs = a_plus_bnega.clone();
        let rhs = c.add(a.clone(), x);
        let body = c.rat_eq(lhs, rhs);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let refl_a_bnega = c.refl(a_plus_bnega.clone());
    // eq1 : a + (b + (-a)) = a + ((-a) + b)
    let eq1 = c.subst(
        motive_e1,
        b_plus_nega.clone(),
        nega_plus_b.clone(),
        e1,
        refl_a_bnega,
    );

    // e2 : a + ((-a) + b) = (a + (-a)) + b
    //    = Eq.symm (Rat.add_assoc a (-a) b).
    let add_assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
    let assoc_a_nega_b = Expr::apps(add_assoc, [a.clone(), neg_a.clone(), bv.clone()]);
    let eq2 = c.symm(
        aplus_nega_plus_b.clone(),
        a_plus_negab.clone(),
        assoc_a_nega_b,
    );

    // e3 : (a + (-a)) + b = 0 + b
    //    - rewrite a + (-a) to 0 via Rat.add_neg_self under motive.
    let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
    let h_ans = Expr::app(add_neg_self, a.clone());
    let motive_e3 = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let lhs = aplus_nega_plus_b.clone();
        let rhs = c.add(x, bv.clone());
        let body = c.rat_eq(lhs, rhs);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let refl_aplusnega_b = c.refl(aplus_nega_plus_b.clone());
    let eq3 = c.subst(
        motive_e3,
        a_plus_nega.clone(),
        c.rat_zero.clone(),
        h_ans,
        refl_aplusnega_b,
    );

    // e4 : 0 + b = b   via Rat.zero_add b.
    let zero_add_const = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
    let eq4 = Expr::app(zero_add_const, bv.clone());

    // Compose: eq1 · eq2 · eq3 · eq4 via Eq.trans.
    let t1 = c.trans(
        a_plus_bnega.clone(),
        a_plus_negab.clone(),
        aplus_nega_plus_b.clone(),
        eq1,
        eq2,
    );
    let t2 = c.trans(
        a_plus_bnega.clone(),
        aplus_nega_plus_b.clone(),
        zero_plus_b.clone(),
        t1,
        eq3,
    );
    c.trans(
        a_plus_bnega.clone(),
        zero_plus_b.clone(),
        bv.clone(),
        t2,
        eq4,
    )
}
