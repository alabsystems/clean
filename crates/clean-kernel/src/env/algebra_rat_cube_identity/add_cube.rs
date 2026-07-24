// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 1 — `Rat.add_cube`, the cubic expansion in left-nested cube form.
//!
//! `((a+b)·(a+b))·(a+b) = a³ + (3·(a²b) + (3·(ab²) + b³))` with
//! `a³ = (a·a)·a`, `a²b = (a·a)·b`, `ab² = (a·b)·b`, `b³ = (b·b)·b`, `3 = (1+1)+1`.
//!
//! Derivation. Let `SQ := (a·a + (1+1)·(a·b)) + b·b` (`Rat.add_sq a b`):
//!   1. `cube(a+b) = SQ·(a+b)`            (congr `(·(a+b))` of `add_sq`)
//!   2. `SQ·(a+b) = SQ·a + SQ·b`          (`left_distrib SQ a b`)
//!   3. expand `SQ·a` and `SQ·b` by `right_distrib`, fold each `(1+1)·t·_` into
//!      `(1+1)·(…)`, then collect the two middle products into `3·(a²b)` and
//!      `3·(ab²)` and reassociate the whole sum into the canonical bracketing.
//!
//! All steps are pure `Rat` ring lemmas, so the closure is empty/foundational.

use super::CubeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl CubeConsts {
    /// `(1+1)·t = t + t`. `right_distrib 1 1 t` + two `one_mul`.
    fn two_mul_eq(&self, parent: &EnvDeclBuilder, t: &Expr) -> Expr {
        let one = self.rat_one.clone();
        let two = self.add(one.clone(), one.clone());
        let two_t = self.mul(two.clone(), t.clone());
        let one_t = self.mul(one.clone(), t.clone());
        let one_t_plus_one_t = self.add(one_t.clone(), one_t.clone());
        // d : (1+1)·t = 1·t + 1·t
        let d = self.right_distrib(one.clone(), one.clone(), t.clone());
        // left 1·t → t
        let f_l = self.f_add_right(parent, one_t.clone());
        let c1 = self.congr_arg(one_t.clone(), t.clone(), f_l, self.one_mul(t.clone()));
        let t_plus_one_t = self.add(t.clone(), one_t.clone());
        // right 1·t → t
        let f_r = self.f_add_left(parent, t.clone());
        let c2 = self.congr_arg(one_t.clone(), t.clone(), f_r, self.one_mul(t.clone()));
        let t_plus_t = self.add(t.clone(), t.clone());
        let s1 = self.trans(
            two_t.clone(),
            one_t_plus_one_t.clone(),
            t_plus_one_t.clone(),
            d,
            c1,
        );
        self.trans(two_t, t_plus_one_t, t_plus_t, s1, c2)
    }

    /// `3·t = (t + t) + t` where `3 = (1+1)+1`.
    /// `right_distrib (1+1) 1 t : ((1+1)+1)·t = (1+1)·t + 1·t`, then
    /// `(1+1)·t → t+t` (`two_mul_eq`) and `1·t → t` (`one_mul`).
    fn three_mul_eq(&self, parent: &EnvDeclBuilder, t: &Expr) -> Expr {
        let one = self.rat_one.clone();
        let two = self.add(one.clone(), one.clone());
        let three = self.three();
        let three_t = self.mul(three.clone(), t.clone());
        let two_t = self.mul(two.clone(), t.clone());
        let one_t = self.mul(one.clone(), t.clone());
        let two_t_plus_one_t = self.add(two_t.clone(), one_t.clone());
        // d : 3·t = (1+1)·t + 1·t
        let d = self.right_distrib(two.clone(), one.clone(), t.clone());
        // left (1+1)·t → t+t
        let t_plus_t = self.add(t.clone(), t.clone());
        let f_l = self.f_add_right(parent, one_t.clone());
        let c1 = self.congr_arg(
            two_t.clone(),
            t_plus_t.clone(),
            f_l,
            self.two_mul_eq(parent, t),
        );
        let tt_plus_one_t = self.add(t_plus_t.clone(), one_t.clone());
        // right 1·t → t
        let f_r = self.f_add_left(parent, t_plus_t.clone());
        let c2 = self.congr_arg(one_t.clone(), t.clone(), f_r, self.one_mul(t.clone()));
        let tt_plus_t = self.add(t_plus_t.clone(), t.clone());
        let s1 = self.trans(
            three_t.clone(),
            two_t_plus_one_t.clone(),
            tt_plus_one_t.clone(),
            d,
            c1,
        );
        self.trans(three_t, tt_plus_one_t, tt_plus_t, s1, c2)
    }

    /// `2·t + t = 3·t`. `(2·t+t) = ((t+t)+t)` (congr left `two_mul_eq`)
    /// `= 3·t` (symm `three_mul_eq`).
    pub(super) fn two_t_plus_t_eq_three_t(&self, parent: &EnvDeclBuilder, t: &Expr) -> Expr {
        let two = self.add(self.rat_one.clone(), self.rat_one.clone());
        let two_t = self.mul(two, t.clone());
        let three_t = self.mul(self.three(), t.clone());
        let t_plus_t = self.add(t.clone(), t.clone());
        let two_t_plus_t = self.add(two_t.clone(), t.clone());
        let tt_plus_t = self.add(t_plus_t.clone(), t.clone());
        // congr (·+t) two_mul_eq : (2·t+t) = ((t+t)+t)
        let f = self.f_add_right(parent, t.clone());
        let e1 = self.congr_arg(
            two_t.clone(),
            t_plus_t.clone(),
            f,
            self.two_mul_eq(parent, t),
        );
        // symm three_mul_eq : ((t+t)+t) = 3·t
        let e2 = self.symm(
            three_t.clone(),
            tt_plus_t.clone(),
            self.three_mul_eq(parent, t),
        );
        self.trans(two_t_plus_t, tt_plus_t, three_t, e1, e2)
    }

    /// `t + 2·t = 3·t`. `(t+2·t) = (t+(t+t))` (congr right `two_mul_eq`)
    /// `= ((t+t)+t)` (symm `add_assoc t t t`) `= 3·t` (symm `three_mul_eq`).
    pub(super) fn one_t_plus_two_t_eq_three_t(&self, parent: &EnvDeclBuilder, t: &Expr) -> Expr {
        let two = self.add(self.rat_one.clone(), self.rat_one.clone());
        let two_t = self.mul(two, t.clone());
        let three_t = self.mul(self.three(), t.clone());
        let t_plus_t = self.add(t.clone(), t.clone());
        let t_plus_two_t = self.add(t.clone(), two_t.clone());
        let t_plus_tt = self.add(t.clone(), t_plus_t.clone());
        let tt_plus_t = self.add(t_plus_t.clone(), t.clone());
        // congr (t+·) two_mul_eq : (t+2·t) = (t+(t+t))
        let f = self.f_add_left(parent, t.clone());
        let e1 = self.congr_arg(
            two_t.clone(),
            t_plus_t.clone(),
            f,
            self.two_mul_eq(parent, t),
        );
        // symm add_assoc t t t : (t+(t+t)) = ((t+t)+t)
        let e2 = self.symm(
            tt_plus_t.clone(),
            t_plus_tt.clone(),
            self.add_assoc(t.clone(), t.clone(), t.clone()),
        );
        // symm three_mul_eq : ((t+t)+t) = 3·t
        let e3 = self.symm(
            three_t.clone(),
            tt_plus_t.clone(),
            self.three_mul_eq(parent, t),
        );
        let s1 = self.trans(
            t_plus_two_t.clone(),
            t_plus_tt.clone(),
            tt_plus_t.clone(),
            e1,
            e2,
        );
        self.trans(t_plus_two_t, tt_plus_t, three_t, s1, e3)
    }

    /// The canonical RHS `a³ + (3·(a²b) + (3·(ab²) + b³))`.
    fn add_cube_rhs(&self, a: &Expr, b: &Expr) -> Expr {
        let a3 = self.cube(a.clone());
        let b3 = self.cube(b.clone());
        let a2b = self.mul(self.mul(a.clone(), a.clone()), b.clone()); // (a·a)·b
        let ab2 = self.mul(self.mul(a.clone(), b.clone()), b.clone()); // (a·b)·b
        let three = self.three();
        let three_a2b = self.mul(three.clone(), a2b);
        let three_ab2 = self.mul(three, ab2);
        let tail = self.add(three_ab2, b3);
        let mid = self.add(three_a2b, tail);
        self.add(a3, mid)
    }
}

impl Environment {
    /// `Rat.add_cube : ∀ a b, ((a+b)·(a+b))·(a+b)
    ///   = a³ + (3·(a²b) + (3·(ab²) + b³))`.
    pub(crate) fn register_rat_add_cube(&mut self, c: &CubeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let s = c.add(a.clone(), bv.clone());
            let lhs = c.mul(c.mul(s.clone(), s.clone()), s);
            let concl = c.eq(lhs, c.add_cube_rhs(&a, &bv));
            let e = b.mk_pi(
                bv_id,
                crate::expr::BinderInfo::Default,
                c.rat.clone(),
                concl,
            );
            b.finish(b.mk_pi(a_id, crate::expr::BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_add_cube_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun a b => <chain>`.
fn build_add_cube_value(c: &CubeConsts) -> Expr {
    use crate::expr::BinderInfo;
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let one = c.rat_one.clone();
    let two = c.add(one.clone(), one.clone());
    let s = c.add(a.clone(), bv.clone()); // a+b
    let aa = c.mul(a.clone(), a.clone()); // a·a
    let ab = c.mul(a.clone(), bv.clone()); // a·b
    let bb_ = c.mul(bv.clone(), bv.clone()); // b·b
    let two_ab = c.mul(two.clone(), ab.clone()); // (1+1)·(a·b)
                                                 // SQ := (a·a + (1+1)·(a·b)) + b·b
    let aa_plus_2ab = c.add(aa.clone(), two_ab.clone());
    let sq = c.add(aa_plus_2ab.clone(), bb_.clone());

    let cube_s = c.mul(c.mul(s.clone(), s.clone()), s.clone()); // (a+b)³ (cube form)
    let ss = c.mul(s.clone(), s.clone()); // (a+b)·(a+b)

    // step1 : cube_s = SQ·(a+b)   [congr (·(a+b)) (add_sq a b)]
    let h_addsq = c.add_sq(a.clone(), bv.clone()); // (a+b)·(a+b) = SQ
    let f_times_s = c.f_right(&b, s.clone());
    let step1 = c.congr_arg(ss.clone(), sq.clone(), f_times_s, h_addsq); // cube_s = SQ·(a+b)
    let sq_s = c.mul(sq.clone(), s.clone());

    // step2 : SQ·(a+b) = SQ·a + SQ·b   [left_distrib SQ a b]
    let step2 = c.left_distrib(sq.clone(), a.clone(), bv.clone());
    let sq_a = c.mul(sq.clone(), a.clone());
    let sq_b = c.mul(sq.clone(), bv.clone());
    let sqa_plus_sqb = c.add(sq_a.clone(), sq_b.clone());

    // ── expand SQ·a = ((a·a + 2ab) + b·b)·a ──
    // right_distrib (a·a+2ab) (b·b) a : SQ·a = (a·a+2ab)·a + (b·b)·a
    let e_sqa_1 = c.right_distrib(aa_plus_2ab.clone(), bb_.clone(), a.clone());
    let lead_a = c.mul(aa_plus_2ab.clone(), a.clone()); // (a·a+2ab)·a
    let bb_a = c.mul(bb_.clone(), a.clone()); // (b·b)·a
    let lead_a_plus_bba = c.add(lead_a.clone(), bb_a.clone());
    // right_distrib (a·a) 2ab a : (a·a+2ab)·a = (a·a)·a + (2ab)·a
    let e_lead_a = c.right_distrib(aa.clone(), two_ab.clone(), a.clone());
    let a3 = c.mul(aa.clone(), a.clone()); // (a·a)·a = a³
    let twoab_a = c.mul(two_ab.clone(), a.clone()); // ((1+1)(a·b))·a
    let a3_plus_twoab_a = c.add(a3.clone(), twoab_a.clone());
    // congr (·+ (b·b)·a) e_lead_a : (a·a+2ab)·a + (b·b)·a = (a³ + (2ab)·a) + (b·b)·a
    let f_l1 = c.f_add_right(&b, bb_a.clone());
    let c_sqa_2 = c.congr_arg(lead_a.clone(), a3_plus_twoab_a.clone(), f_l1, e_lead_a);
    let inner_a = c.add(a3_plus_twoab_a.clone(), bb_a.clone());
    // SQ·a = inner_a
    let h_sqa = c.trans(
        sq_a.clone(),
        lead_a_plus_bba.clone(),
        inner_a.clone(),
        e_sqa_1,
        c_sqa_2,
    );

    // ── expand SQ·b = ((a·a + 2ab) + b·b)·b ──
    let e_sqb_1 = c.right_distrib(aa_plus_2ab.clone(), bb_.clone(), bv.clone());
    let lead_b = c.mul(aa_plus_2ab.clone(), bv.clone()); // (a·a+2ab)·b
    let bb_b = c.mul(bb_.clone(), bv.clone()); // (b·b)·b = b³
    let lead_b_plus_bbb = c.add(lead_b.clone(), bb_b.clone());
    let e_lead_b = c.right_distrib(aa.clone(), two_ab.clone(), bv.clone());
    let aab = c.mul(aa.clone(), bv.clone()); // (a·a)·b = a²b
    let twoab_b = c.mul(two_ab.clone(), bv.clone()); // ((1+1)(a·b))·b
    let aab_plus_twoab_b = c.add(aab.clone(), twoab_b.clone());
    let f_l2 = c.f_add_right(&b, bb_b.clone());
    let c_sqb_2 = c.congr_arg(lead_b.clone(), aab_plus_twoab_b.clone(), f_l2, e_lead_b);
    let inner_b = c.add(aab_plus_twoab_b.clone(), bb_b.clone());
    let h_sqb = c.trans(
        sq_b.clone(),
        lead_b_plus_bbb.clone(),
        inner_b.clone(),
        e_sqb_1,
        c_sqb_2,
    );

    // step3 : SQ·a + SQ·b = inner_a + inner_b
    let f_left_sum = c.f_add_right(&b, sq_b.clone());
    let c_left = c.congr_arg(sq_a.clone(), inner_a.clone(), f_left_sum, h_sqa); // sq_a+sq_b = inner_a+sq_b
    let inner_a_plus_sqb = c.add(inner_a.clone(), sq_b.clone());
    let f_right_sum = c.f_add_left(&b, inner_a.clone());
    let c_right = c.congr_arg(sq_b.clone(), inner_b.clone(), f_right_sum, h_sqb); // inner_a+sq_b = inner_a+inner_b
    let inner_a_plus_inner_b = c.add(inner_a.clone(), inner_b.clone());
    let step3 = c.trans(
        sqa_plus_sqb.clone(),
        inner_a_plus_sqb.clone(),
        inner_a_plus_inner_b.clone(),
        c_left,
        c_right,
    );

    // Now: inner_a = (a³ + (2ab)·a) + (b·b)·a
    //      inner_b = (a²b + (2ab)·b) + b³
    // We have cube_s = inner_a + inner_b (by chain so far: step1;step2;step3).
    // Build h_pre : cube_s = inner_a + inner_b.
    let h_pre = {
        let t1 = c.trans(
            cube_s.clone(),
            sq_s.clone(),
            sqa_plus_sqb.clone(),
            step1,
            step2,
        );
        c.trans(
            cube_s.clone(),
            sqa_plus_sqb.clone(),
            inner_a_plus_inner_b.clone(),
            t1,
            step3,
        )
    };

    // ── Now rewrite the cross terms to collected normal form. We need:
    //   (2ab)·a → 3·(a²b)? NO. Recompute carefully:
    //   a³ term: (a·a)·a = a³  ✓ (already).
    //   (2ab)·a = ((1+1)(a·b))·a ; (b·b)·a ; a²b=(a·a)·b ; (2ab)·b=((1+1)(a·b))·b ; b³.
    // The three middle/tail summands of (a+b)³ are 3·a²b, 3·ab², b³.
    //   a²b appears as: (b·b)·a? no. Let's count a²b-type (two a's, one b):
    //     (2ab)·a = ((1+1)(a·b))·a = 2·((a·b)·a) and (a·b)·a is an a²b monomial.
    //     (a·a)·b = a²b directly.
    //   ab²-type (one a, two b's):
    //     (b·b)·a = ab² monomial ; (2ab)·b = 2·((a·b)·b) = 2·ab².
    //   So coefficient of a²b = 2+1 = 3 ; coefficient of ab² = 1+2 = 3. Good.
    //
    // Strategy to reach the canonical RHS a³ + (3·(a²b) + (3·(ab²) + b³)):
    //   We transform inner_a + inner_b stepwise into the target via subst with
    //   pure-ring equalities, building each equality with the helpers.
    //
    // (2ab)·a = 2·((a·b)·a)  [mul_assoc (1+1) (a·b) a : ((1+1)·(a·b))·a = (1+1)·((a·b)·a)]
    let e_2ab_a = c.mul_assoc(two.clone(), ab.clone(), a.clone()); // (2·ab)·a = 2·(ab·a)
    let ab_a = c.mul(ab.clone(), a.clone()); // (a·b)·a
    let two_ab_a = c.mul(two.clone(), ab_a.clone()); // 2·((a·b)·a)
                                                     // (a·b)·a = (a·a)·b  [a²b]:  ab·a = a·(b·a) = a·(a·b)?  Use mul_assoc + mul_comm.
                                                     //   ab·a = a·(b·a)  (mul_assoc a b a)
                                                     //   b·a = a·b       (mul_comm b a)
                                                     //   a·(a·b) ; and (a·a)·b = a·(a·b) (mul_assoc a a b). So ab·a = (a·a)·b via:
                                                     //   ab·a = a·(b·a) = a·(a·b) = (a·a)·b? mul_assoc a a b : (a·a)·b = a·(a·b),
                                                     //     so a·(a·b) = (a·a)·b by symm.
    let a_ba = c.mul(a.clone(), c.mul(bv.clone(), a.clone())); // a·(b·a)
    let e_aba_1 = c.mul_assoc(a.clone(), bv.clone(), a.clone()); // (a·b)·a = a·(b·a)
    let ba = c.mul(bv.clone(), a.clone());
    let f_a_left = c.f_left_mul(&b, a.clone());
    let e_aba_2 = c.congr_arg(
        ba.clone(),
        ab.clone(),
        f_a_left,
        c.mul_comm(bv.clone(), a.clone()),
    ); // a·(b·a) = a·(a·b)
    let a_ab = c.mul(a.clone(), ab.clone()); // a·(a·b)
    let e_aab = c.mul_assoc(a.clone(), a.clone(), bv.clone()); // (a·a)·b = a·(a·b)
    let e_aab_symm = c.symm(aab.clone(), a_ab.clone(), e_aab); // a·(a·b) = (a·a)·b
    let e_ab_a_chain = {
        let t1 = c.trans(ab_a.clone(), a_ba.clone(), a_ab.clone(), e_aba_1, e_aba_2);
        c.trans(ab_a.clone(), a_ab.clone(), aab.clone(), t1, e_aab_symm)
    }; // (a·b)·a = (a·a)·b = a²b

    // (a·b)·b = ab² directly (this IS our ab2 monomial). No rewrite needed.
    let ab2 = c.mul(ab.clone(), bv.clone()); // (a·b)·b
                                             // (2ab)·b = 2·((a·b)·b)  [mul_assoc (1+1) (a·b) b]
    let e_2ab_b = c.mul_assoc(two.clone(), ab.clone(), bv.clone()); // (2·ab)·b = 2·(ab·b)
    let two_ab2 = c.mul(two.clone(), ab2.clone()); // 2·((a·b)·b)

    // The remaining ab²-type term is (b·b)·a. We want it as (a·b)·b = ab2.
    //   (b·b)·a = a·(b·b)  (mul_comm (b·b) a)
    //           = (a·b)·b  (symm mul_assoc a b b : (a·b)·b = a·(b·b))
    let bba = bb_a.clone(); // (b·b)·a
    let a_bb = c.mul(a.clone(), bb_.clone()); // a·(b·b)
    let e_bba_1 = c.mul_comm(bb_.clone(), a.clone()); // (b·b)·a = a·(b·b)
    let e_abb = c.mul_assoc(a.clone(), bv.clone(), bv.clone()); // (a·b)·b = a·(b·b)
    let e_abb_symm = c.symm(ab2.clone(), a_bb.clone(), e_abb); // a·(b·b) = (a·b)·b
    let e_bba_chain = c.trans(bba.clone(), a_bb.clone(), ab2.clone(), e_bba_1, e_abb_symm); // (b·b)·a = ab²

    // Build the final assembly via build_collect (separate fn for clarity).
    let three = c.three();
    let _ = (
        &e_2ab_a,
        &two_ab_a,
        &e_ab_a_chain,
        &e_2ab_b,
        &two_ab2,
        &e_bba_chain,
        &three,
    );

    let final_eq = collect_to_canonical(
        c,
        &b,
        &a,
        &bv,
        &aab,
        &a3,
        &b3_of(c, &bv),
        &ab2,
        &two_ab,
        &bb_,
        &inner_a,
        &inner_b,
        &h_pre,
        &e_2ab_a,
        &e_ab_a_chain,
        &e_bba_chain,
        &e_2ab_b,
    );

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), final_eq);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn b3_of(c: &CubeConsts, bv: &Expr) -> Expr {
    c.cube(bv.clone())
}

/// Collect `inner_a + inner_b` into `a³ + (3·(a²b) + (3·(ab²) + b³))`.
///
/// `inner_a = (a³ + (2ab)·a) + (b·b)·a`
/// `inner_b = (a²b + (2ab)·b) + b³`
#[allow(clippy::too_many_arguments)]
fn collect_to_canonical(
    c: &CubeConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    aab: &Expr, // a²b = (a·a)·b
    a3: &Expr,  // a³ = (a·a)·a
    b3: &Expr,  // b³ = (b·b)·b
    ab2: &Expr, // ab² = (a·b)·b
    two_ab: &Expr,
    bb_: &Expr,
    inner_a: &Expr,
    inner_b: &Expr,
    h_pre: &Expr,        // cube_s = inner_a + inner_b
    e_2ab_a: &Expr,      // (2ab)·a = 2·((a·b)·a)
    e_ab_a_chain: &Expr, // (a·b)·a = a²b
    e_bba_chain: &Expr,  // (b·b)·a = ab²
    e_2ab_b: &Expr,      // (2ab)·b = 2·((a·b)·b)
) -> Expr {
    let two = c.add(c.rat_one.clone(), c.rat_one.clone());
    let three = c.three();
    let ab_a = c.mul(c.mul(a.clone(), bv.clone()), a.clone()); // (a·b)·a
    let two_ab_a = c.mul(two.clone(), ab_a.clone()); // 2·((a·b)·a)
    let two_ab2 = c.mul(two.clone(), ab2.clone()); // 2·((a·b)·b)
    let twoab_a = c.mul(two_ab.clone(), a.clone()); // (2ab)·a
    let twoab_b = c.mul(two_ab.clone(), bv.clone()); // (2ab)·b
    let bb_a = c.mul(bb_.clone(), a.clone()); // (b·b)·a

    // === Rewrite inner_a's middle/tail to a²b coefficients ===
    // inner_a = (a³ + (2ab)·a) + (b·b)·a
    //   (2ab)·a  → 2·((a·b)·a) → 2·a²b      [e_2ab_a then congr(2··) e_ab_a_chain]
    //   (b·b)·a  → ab²                        [e_bba_chain]
    // Rewrite (2ab)·a → 2·a²b:
    let f_two_left = c.f_left_mul(parent, two.clone());
    let e_two_aba = c.congr_arg(ab_a.clone(), aab.clone(), f_two_left, e_ab_a_chain.clone()); // 2·(ab·a) = 2·a²b
    let two_aab = c.mul(two.clone(), aab.clone()); // 2·a²b
    let e_twoab_a_full = c.trans(
        twoab_a.clone(),
        two_ab_a.clone(),
        two_aab.clone(),
        e_2ab_a.clone(),
        e_two_aba,
    ); // (2ab)·a = 2·a²b

    // inner_a -> ia1 := (a³ + 2·a²b) + (b·b)·a
    let a3_plus_twoab_a = c.add(a3.clone(), twoab_a.clone());
    let a3_plus_two_aab = c.add(a3.clone(), two_aab.clone());
    // congr ((a³+·)+(b·b)·a) of e_twoab_a_full : need nested congr.
    //   First on the left summand: (a³ + (2ab)·a) → (a³ + 2·a²b)
    let f_a3_left = c.f_add_left(parent, a3.clone());
    let e_left_a = c.congr_arg(twoab_a.clone(), two_aab.clone(), f_a3_left, e_twoab_a_full); // (a³+(2ab)·a) = (a³+2·a²b)
    let f_plus_bba = c.f_add_right(parent, bb_a.clone());
    let e_ia_step1 = c.congr_arg(
        a3_plus_twoab_a.clone(),
        a3_plus_two_aab.clone(),
        f_plus_bba,
        e_left_a,
    ); // inner_a = (a³+2·a²b)+(b·b)·a
    let ia1 = c.add(a3_plus_two_aab.clone(), bb_a.clone());
    //   Now (b·b)·a → ab²
    let f_plus_left_ia = c.f_add_left(parent, a3_plus_two_aab.clone());
    let e_ia_step2 = c.congr_arg(
        bb_a.clone(),
        ab2.clone(),
        f_plus_left_ia,
        e_bba_chain.clone(),
    ); // ia1 = (a³+2·a²b)+ab²
    let ia2 = c.add(a3_plus_two_aab.clone(), ab2.clone());
    let h_inner_a = c.trans(
        inner_a.clone(),
        ia1.clone(),
        ia2.clone(),
        e_ia_step1,
        e_ia_step2,
    ); // inner_a = (a³+2·a²b)+ab²

    // === Rewrite inner_b's middle to ab² coefficients ===
    // inner_b = (a²b + (2ab)·b) + b³
    //   (2ab)·b → 2·((a·b)·b) = 2·ab²
    let e_twoab_b_full = e_2ab_b.clone(); // (2ab)·b = 2·ab² (ab·b IS ab2)
    let a2b_plus_twoab_b = c.add(aab.clone(), twoab_b.clone());
    let a2b_plus_two_ab2 = c.add(aab.clone(), two_ab2.clone());
    let f_a2b_left = c.f_add_left(parent, aab.clone());
    let e_left_b = c.congr_arg(twoab_b.clone(), two_ab2.clone(), f_a2b_left, e_twoab_b_full); // (a²b+(2ab)·b)=(a²b+2·ab²)
    let f_plus_b3 = c.f_add_right(parent, b3.clone());
    let e_ib_step1 = c.congr_arg(
        a2b_plus_twoab_b.clone(),
        a2b_plus_two_ab2.clone(),
        f_plus_b3,
        e_left_b,
    ); // inner_b = (a²b+2·ab²)+b³
    let ib1 = c.add(a2b_plus_two_ab2.clone(), b3.clone());
    let h_inner_b = e_ib_step1; // inner_b = (a²b+2·ab²)+b³
    let _ = &ib1;

    // === Rewrite the whole sum: inner_a + inner_b = ia2 + ib1 ===
    let f_sum_left = c.f_add_right(parent, inner_b.clone());
    let c_sum_l = c.congr_arg(inner_a.clone(), ia2.clone(), f_sum_left, h_inner_a); // (inner_a+inner_b)=(ia2+inner_b)
    let ia2_plus_inner_b = c.add(ia2.clone(), inner_b.clone());
    let f_sum_right = c.f_add_left(parent, ia2.clone());
    let c_sum_r = c.congr_arg(inner_b.clone(), ib1.clone(), f_sum_right, h_inner_b); // (ia2+inner_b)=(ia2+ib1)
    let ia2_plus_ib1 = c.add(ia2.clone(), ib1.clone());
    let h_sum = c.trans(
        c.add(inner_a.clone(), inner_b.clone()),
        ia2_plus_inner_b.clone(),
        ia2_plus_ib1.clone(),
        c_sum_l,
        c_sum_r,
    ); // (inner_a+inner_b) = ia2 + ib1

    // Now ia2 + ib1 = ((a³+2·a²b)+ab²) + ((a²b+2·ab²)+b³).
    // Target canonical: a³ + (3·a²b + (3·ab² + b³)).
    // We finish by a pure-ring reassociation/collection equality `h_reassoc`
    // proven via the associativity/commutativity backbone in finish_reassoc.
    let h_reassoc = finish_reassoc(c, parent, a3, aab, ab2, b3, &three);
    // h_reassoc : ia2 + ib1 = a³ + (3·a²b + (3·ab² + b³))
    let target = {
        let three_a2b = c.mul(three.clone(), aab.clone());
        let three_ab2 = c.mul(three.clone(), ab2.clone());
        let tail = c.add(three_ab2, b3.clone());
        let mid = c.add(three_a2b, tail);
        c.add(a3.clone(), mid)
    };

    // assemble: cube_s = (inner_a+inner_b) = (ia2+ib1) = target.
    let cube_s = {
        let s = c.add(a.clone(), bv.clone());
        c.mul(c.mul(s.clone(), s.clone()), s)
    };
    let inner_sum = c.add(inner_a.clone(), inner_b.clone());
    let t1 = c.trans(
        cube_s.clone(),
        inner_sum.clone(),
        ia2_plus_ib1.clone(),
        h_pre.clone(),
        h_sum,
    );
    c.trans(cube_s, ia2_plus_ib1, target, t1, h_reassoc)
}

/// Prove `((a³+2·a²b)+ab²) + ((a²b+2·ab²)+b³) = a³ + (3·a²b + (3·ab² + b³))`
/// from pure additive associativity/commutativity (treating the five
/// monomials `a³, a²b, ab², b³` and coefficients abstractly), with
/// `2·t + t = 3·t` and `t + 2·t = 3·t` discharged by `three_mul_eq`/`two_mul_eq`.
fn finish_reassoc(
    c: &CubeConsts,
    parent: &EnvDeclBuilder,
    a3: &Expr,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
    three: &Expr,
) -> Expr {
    let two = c.add(c.rat_one.clone(), c.rat_one.clone());
    let two_a2b = c.mul(two.clone(), a2b.clone());
    let two_ab2 = c.mul(two.clone(), ab2.clone());
    let three_a2b = c.mul(three.clone(), a2b.clone());
    let three_ab2 = c.mul(three.clone(), ab2.clone());

    // LHS := (L) + (R) where L = (a³ + 2·a²b) + ab², R = (a²b + 2·ab²) + b³.
    let l = c.add(c.add(a3.clone(), two_a2b.clone()), ab2.clone());
    let r = c.add(c.add(a2b.clone(), two_ab2.clone()), b3.clone());
    let lhs = c.add(l.clone(), r.clone());

    // We build the target a³ + (3·a²b + (3·ab² + b³)) by a sequence of
    // associativity/commutativity rewrites. Because monomials are opaque, we
    // do this with the `add_assoc`/`add_comm` backbone term-by-term.
    //
    // Rather than a long associativity dance, observe the cleanest plan: prove
    // both sides equal a common fully-right-associated 6-term list, then chain.
    //
    // canon6 V := a³ + (2·a²b + (ab² + (a²b + (2·ab² + b³))))
    //   LHS = (a³+2·a²b)+ab² + ((a²b+2·ab²)+b³) → reassociate fully right.
    let two_ab2_plus_b3 = c.add(two_ab2.clone(), b3.clone());
    let a2b_plus_rest = c.add(a2b.clone(), two_ab2_plus_b3.clone());
    let ab2_plus_a2brest = c.add(ab2.clone(), a2b_plus_rest.clone());
    let twoa2b_plus = c.add(two_a2b.clone(), ab2_plus_a2brest.clone());
    let canon6 = c.add(a3.clone(), twoa2b_plus.clone());

    // Step A: LHS = canon6  (pure add_assoc reassociation).
    let h_lhs_canon = reassoc_lhs_to_canon6(c, parent, a3, a2b, ab2, b3, &two);

    // Step B: canon6 = target, by reordering the inner additions:
    //   inner I := 2·a²b + (ab² + (a²b + (2·ab² + b³)))
    //   want J := 3·a²b + (3·ab² + b³).
    // First collect a²b: move the inner a²b next to 2·a²b.
    //   ab² + (a²b + X) = a²b? need add_comm/assoc to bring a²b forward.
    // Build inner equality h_inner : I = 3·a²b + (3·ab² + b³).
    let h_inner = collect_inner(c, parent, a2b, ab2, b3, three, &two);
    let target_inner = {
        let three_ab2_b3 = c.add(three_ab2.clone(), b3.clone());
        c.add(three_a2b.clone(), three_ab2_b3)
    };
    let f_a3_left = c.f_add_left(parent, a3.clone());
    let h_canon_target = c.congr_arg(
        twoa2b_plus.clone(),
        target_inner.clone(),
        f_a3_left,
        h_inner,
    );
    let target = c.add(a3.clone(), target_inner.clone());

    c.trans(lhs, canon6.clone(), target, h_lhs_canon, h_canon_target)
}

/// Reassociate `((a³+2·a²b)+ab²) + ((a²b+2·ab²)+b³)` fully to the right:
/// `a³ + (2·a²b + (ab² + (a²b + (2·ab² + b³))))`.
fn reassoc_lhs_to_canon6(
    c: &CubeConsts,
    parent: &EnvDeclBuilder,
    a3: &Expr,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
    two: &Expr,
) -> Expr {
    let two_a2b = c.mul(two.clone(), a2b.clone());
    let two_ab2 = c.mul(two.clone(), ab2.clone());
    // L = (a³+2·a²b)+ab² ; R = (a²b+2·ab²)+b³.
    let a3_2a2b = c.add(a3.clone(), two_a2b.clone());
    let l = c.add(a3_2a2b.clone(), ab2.clone());
    let a2b_2ab2 = c.add(a2b.clone(), two_ab2.clone());
    let r = c.add(a2b_2ab2.clone(), b3.clone());
    let lhs = c.add(l.clone(), r.clone());

    // Step 1: (L)+(R) = a³ + (2·a²b + ((ab²) + R))? Use add_assoc twice.
    //   add_assoc L? L = (a3_2a2b)+ab². So lhs = ((a3_2a2b)+ab²) + R.
    //   add_assoc (a3_2a2b) ab² R : (((a3_2a2b)+ab²)+R) = (a3_2a2b)+(ab²+R).
    let ab2_plus_r = c.add(ab2.clone(), r.clone());
    let s1 = c.add_assoc(a3_2a2b.clone(), ab2.clone(), r.clone()); // lhs = (a3_2a2b)+(ab²+R)
    let mid1 = c.add(a3_2a2b.clone(), ab2_plus_r.clone());
    //   add_assoc a³ (2·a²b) (ab²+R) : ((a³+2·a²b)+(ab²+R)) = a³+(2·a²b+(ab²+R)).
    let twoa2b_plus = c.add(two_a2b.clone(), ab2_plus_r.clone());
    let s2 = c.add_assoc(a3.clone(), two_a2b.clone(), ab2_plus_r.clone()); // mid1 = a³+(2·a²b+(ab²+R))
    let mid2 = c.add(a3.clone(), twoa2b_plus.clone());
    //   Now expand R inside: ab²+R = ab² + ((a²b+2·ab²)+b³).
    //     add_assoc (a2b_2ab2) b3? R itself = (a2b_2ab2)+b3 ; we want
    //     a²b + (2·ab² + b³) inside. First add_assoc a²b (2·ab²) b³ :
    //       ((a²b+2·ab²)+b³) = a²b+(2·ab²+b³)  → R = a²b+(2·ab²+b³).
    let two_ab2_b3 = c.add(two_ab2.clone(), b3.clone());
    let a2b_rest = c.add(a2b.clone(), two_ab2_b3.clone());
    let e_r = c.add_assoc(a2b.clone(), two_ab2.clone(), b3.clone()); // R = a²b+(2·ab²+b³)
                                                                     // congr (ab²+·) e_r : (ab²+R) = ab²+(a²b+(2·ab²+b³)).
    let f_ab2_left = c.f_add_left(parent, ab2.clone());
    let e_ab2r = c.congr_arg(r.clone(), a2b_rest.clone(), f_ab2_left, e_r); // (ab²+R)=ab²+(a²b+(2·ab²+b³))
    let ab2_rest = c.add(ab2.clone(), a2b_rest.clone());
    // congr (2·a²b + ·) : (2·a²b+(ab²+R)) = 2·a²b+(ab²+(a²b+(2·ab²+b³))).
    let f_2a2b_left = c.f_add_left(parent, two_a2b.clone());
    let e_2a2b = c.congr_arg(ab2_plus_r.clone(), ab2_rest.clone(), f_2a2b_left, e_ab2r);
    let twoa2b_plus2 = c.add(two_a2b.clone(), ab2_rest.clone());
    // congr (a³ + ·):
    let f_a3_left = c.f_add_left(parent, a3.clone());
    let e_final = c.congr_arg(twoa2b_plus.clone(), twoa2b_plus2.clone(), f_a3_left, e_2a2b);
    let canon6 = c.add(a3.clone(), twoa2b_plus2.clone());

    // chain: lhs = mid1 (s1) = mid2 (s2) = canon6 (e_final).
    let t1 = c.trans(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
    c.trans(lhs, mid2, canon6, t1, e_final)
}

/// Prove `2·a²b + (ab² + (a²b + (2·ab² + b³))) = 3·a²b + (3·ab² + b³)`.
fn collect_inner(
    c: &CubeConsts,
    parent: &EnvDeclBuilder,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
    three: &Expr,
    two: &Expr,
) -> Expr {
    let two_a2b = c.mul(two.clone(), a2b.clone());
    let two_ab2 = c.mul(two.clone(), ab2.clone());
    let three_a2b = c.mul(three.clone(), a2b.clone());
    let three_ab2 = c.mul(three.clone(), ab2.clone());

    // I = 2·a²b + (ab² + (a²b + (2·ab² + b³)))
    let two_ab2_b3 = c.add(two_ab2.clone(), b3.clone());
    let a2b_rest = c.add(a2b.clone(), two_ab2_b3.clone());
    let ab2_rest = c.add(ab2.clone(), a2b_rest.clone());
    let i = c.add(two_a2b.clone(), ab2_rest.clone());

    // Move a²b in front of ab²:  ab² + (a²b + Y) = a²b + (ab² + Y)
    //   where Y := (2·ab²+b³).
    //   add_comm + add_assoc: ab²+(a²b+Y)
    //     = (ab²+a²b)+Y    (symm add_assoc ab² a²b Y)
    //     = (a²b+ab²)+Y    (congr (·+Y) add_comm ab² a²b)
    //     = a²b+(ab²+Y)    (add_assoc a²b ab² Y)
    let y = two_ab2_b3.clone();
    let ab2_a2b = c.add(ab2.clone(), a2b.clone());
    let a2b_ab2 = c.add(a2b.clone(), ab2.clone());
    let e_s1 = c.symm(
        c.add(ab2_a2b.clone(), y.clone()),
        ab2_rest.clone(),
        c.add_assoc(ab2.clone(), a2b.clone(), y.clone()),
    ); // ab²+(a²b+Y) = (ab²+a²b)+Y
    let f_plus_y = c.f_add_right(parent, y.clone());
    let e_s2 = c.congr_arg(
        ab2_a2b.clone(),
        a2b_ab2.clone(),
        f_plus_y,
        c.mul_comm_add(parent, ab2, a2b),
    ); // (ab²+a²b)+Y = (a²b+ab²)+Y
    let a2b_ab2_y = c.add(a2b_ab2.clone(), y.clone());
    let ab2_plus_y = c.add(ab2.clone(), y.clone());
    let e_s3 = c.add_assoc(a2b.clone(), ab2.clone(), y.clone()); // (a²b+ab²)+Y = a²b+(ab²+Y)
    let a2b_plus_ab2y = c.add(a2b.clone(), ab2_plus_y.clone());
    let e_move = {
        let t1 = c.trans(
            ab2_rest.clone(),
            c.add(ab2_a2b.clone(), y.clone()),
            a2b_ab2_y.clone(),
            e_s1,
            e_s2,
        );
        c.trans(
            ab2_rest.clone(),
            a2b_ab2_y.clone(),
            a2b_plus_ab2y.clone(),
            t1,
            e_s3,
        )
    }; // (ab² + (a²b+Y)) = a²b + (ab²+Y)

    // congr (2·a²b + ·) e_move : I = 2·a²b + (a²b + (ab²+Y))
    let f_2a2b_left = c.f_add_left(parent, two_a2b.clone());
    let e_i1 = c.congr_arg(ab2_rest.clone(), a2b_plus_ab2y.clone(), f_2a2b_left, e_move);
    let i1 = c.add(two_a2b.clone(), a2b_plus_ab2y.clone());

    // (2·a²b) + (a²b + Z) = (2·a²b + a²b) + Z   (symm add_assoc), Z := ab²+Y.
    let z = ab2_plus_y.clone();
    let two_a2b_plus_a2b = c.add(two_a2b.clone(), a2b.clone());
    let e_i2 = c.symm(
        c.add(two_a2b_plus_a2b.clone(), z.clone()),
        i1.clone(),
        c.add_assoc(two_a2b.clone(), a2b.clone(), z.clone()),
    ); // I1 = (2·a²b+a²b)+Z
    let i2 = c.add(two_a2b_plus_a2b.clone(), z.clone());

    // 2·a²b + a²b = 3·a²b   [three_mul as 2t+t]:
    //   three_mul_eq gives 3·t = (t+t)+t. We need 2·t + t = 3·t.
    //   2·t = t+t (two_mul_eq), so 2·t+t = (t+t)+t = 3·t (symm three_mul_eq).
    let e_coeff_a2b = c.two_t_plus_t_eq_three_t(parent, a2b);
    let f_plus_z = c.f_add_right(parent, z.clone());
    let e_i3 = c.congr_arg(
        two_a2b_plus_a2b.clone(),
        three_a2b.clone(),
        f_plus_z,
        e_coeff_a2b,
    ); // (2·a²b+a²b)+Z = 3·a²b+Z
    let i3 = c.add(three_a2b.clone(), z.clone());

    // Z = ab²+(2·ab²+b³). Want 3·ab²+b³.
    //   ab²+(2·ab²+b³) = (ab²+2·ab²)+b³ (symm add_assoc) = (3·ab²)+b³.
    let ab2_2ab2 = c.add(ab2.clone(), two_ab2.clone());
    let e_z1 = c.symm(
        c.add(ab2_2ab2.clone(), b3.clone()),
        z.clone(),
        c.add_assoc(ab2.clone(), two_ab2.clone(), b3.clone()),
    ); // Z = (ab²+2·ab²)+b³
    let e_coeff_ab2 = c.one_t_plus_two_t_eq_three_t(parent, ab2); // ab²+2·ab² = 3·ab²
    let f_plus_b3 = c.f_add_right(parent, b3.clone());
    let e_z2 = c.congr_arg(ab2_2ab2.clone(), three_ab2.clone(), f_plus_b3, e_coeff_ab2); // (ab²+2·ab²)+b³=3·ab²+b³
    let three_ab2_b3 = c.add(three_ab2.clone(), b3.clone());
    let e_z = c.trans(
        z.clone(),
        c.add(ab2_2ab2.clone(), b3.clone()),
        three_ab2_b3.clone(),
        e_z1,
        e_z2,
    ); // Z = 3·ab²+b³

    // congr (3·a²b + ·) e_z : (3·a²b + Z) = 3·a²b + (3·ab²+b³) = target.
    let f_3a2b_left = c.f_add_left(parent, three_a2b.clone());
    let e_i4 = c.congr_arg(z.clone(), three_ab2_b3.clone(), f_3a2b_left, e_z);
    let target = c.add(three_a2b.clone(), three_ab2_b3.clone());

    // chain: I = i1 (e_i1) = i2 (e_i2) = i3 (e_i3) = target (e_i4).
    let t1 = c.trans(i.clone(), i1.clone(), i2.clone(), e_i1, e_i2);
    let t2 = c.trans(i.clone(), i2.clone(), i3.clone(), t1, e_i3);
    c.trans(i, i3, target, t2, e_i4)
}
