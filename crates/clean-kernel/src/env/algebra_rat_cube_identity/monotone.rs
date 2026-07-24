// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 2 helpers — cube monotonicity at the `Rat` level.
//!
//! - `Rat.cube_lt_cube_of_lt_of_nonneg : ∀ a b, 0≤b → b<a → (b·b)·b < (a·a)·a`
//!   `(b·b)·b ≤ (a·a)·b` (`mul_le_right` of `b·b ≤ a·a`, the latter from
//!   `sq_lt_sq_of_lt_of_nonneg` + `le_of_lt`) and `(a·a)·b < (a·a)·a`
//!   (`mul_lt_mul_of_pos_left` with `0 < a·a` from `mul_pos`); chained by
//!   `lt_of_le_of_lt`.
//!
//! - `Rat.le_of_cube_le_cube : ∀ a b, 0≤a → 0≤b → (a·a)·a ≤ (b·b)·b → a ≤ b`
//!   `Classical.em (a ≤ b)` + `le_total` contradiction skeleton, identical in
//!   shape to `Rat.le_of_sq_le_sq`, using `cube_lt_cube_of_lt_of_nonneg`.

use super::CubeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl CubeConsts {
    /// Case-split `h_or : Or p q` into non-dependent `goal` via `Or.rec`.
    fn or_elim(
        &self,
        parent: &EnvDeclBuilder,
        p: Expr,
        q: Expr,
        goal: Expr,
        h_or: Expr,
        h_left: Expr,
        h_right: Expr,
    ) -> Expr {
        let or_c = Expr::const_(Name::from_string("Or"), vec![]);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
            let (h_id, _) = m.fresh_local(or_ty.clone());
            let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, goal);
            m.finish_child(lam)
        };
        Expr::apps(self.or_rec.clone(), [p, q, motive, h_left, h_right, h_or])
    }
    fn le_total(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_total.clone(), [a, b])
    }
}

impl Environment {
    /// `Rat.cube_lt_cube_of_lt_of_nonneg : ∀ a b, 0≤b → b<a → (b·b)·b < (a·a)·a`.
    pub(crate) fn register_rat_cube_lt_cube(&mut self, c: &CubeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cube_lt_cube_of_lt_of_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nn = c.le(c.rat_zero.clone(), bv.clone());
            let (hnn_id, _) = b.fresh_local(h_nn.clone());
            let h_lt = c.lt(bv.clone(), a.clone());
            let (hlt_id, _) = b.fresh_local(h_lt.clone());
            let concl = c.lt(c.cube(bv.clone()), c.cube(a.clone()));
            let e = b.mk_pi(hlt_id, BinderInfo::Default, h_lt, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nn_ty = c.le(c.rat_zero.clone(), bv.clone());
            let (hnn_id, h_nn) = b.fresh_local(h_nn_ty.clone());
            let h_lt_ty = c.lt(bv.clone(), a.clone());
            let (hlt_id, h_lt) = b.fresh_local(h_lt_ty.clone());

            let aa = c.mul(a.clone(), a.clone());
            let bb = c.mul(bv.clone(), bv.clone());
            let b3 = c.mul(bb.clone(), bv.clone()); // (b·b)·b
            let a3 = c.mul(aa.clone(), a.clone()); // (a·a)·a
            let aa_b = c.mul(aa.clone(), bv.clone()); // (a·a)·b

            // 0 < a  [lt_of_le_of_lt 0 b a (0≤b)(b<a)]
            let h_0a = c.lt_of_le_of_lt(
                c.rat_zero.clone(),
                bv.clone(),
                a.clone(),
                h_nn.clone(),
                h_lt.clone(),
            );
            // 0 < a·a  [mul_pos a a (0<a)(0<a)]
            let h_0aa = c.mul_pos(a.clone(), a.clone(), h_0a.clone(), h_0a.clone());
            // b·b < a·a  [sq_lt_sq a b (0≤b)(b<a)]; then le_of_lt → b·b ≤ a·a.
            let h_bb_lt_aa = c.sq_lt_sq(a.clone(), bv.clone(), h_nn.clone(), h_lt.clone());
            let h_bb_le_aa = c.le_of_lt_generic(bb.clone(), aa.clone(), h_bb_lt_aa);
            // (b·b)·b ≤ (a·a)·b  [mul_le_right b (b·b)(a·a)(b·b≤a·a)(0≤b)]
            let h_step1 = c.mul_le_right(bv.clone(), bb.clone(), aa.clone(), h_bb_le_aa, h_nn);
            // (a·a)·b < (a·a)·a  [mul_lt_left (a·a) b a (b<a)(0<a·a)]
            let h_step2 = c.mul_lt_left(aa.clone(), bv.clone(), a.clone(), h_lt, h_0aa);
            // (b·b)·b < (a·a)·a
            let body = c.lt_of_le_of_lt(b3, aa_b, a3, h_step1, h_step2);

            let e = b.mk_lam(hlt_id, BinderInfo::Default, h_lt_ty, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn_ty, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_of_cube_le_cube : ∀ a b, 0≤a → 0≤b → (a·a)·a ≤ (b·b)·b → a ≤ b`.
    pub(crate) fn register_rat_le_of_cube_le_cube(
        &mut self,
        c: &CubeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_cube_le_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_a = c.le(c.rat_zero.clone(), a.clone());
            let (ha_id, _) = b.fresh_local(h_a.clone());
            let h_b = c.le(c.rat_zero.clone(), bv.clone());
            let (hb_id, _) = b.fresh_local(h_b.clone());
            let h_cube = c.le(c.cube(a.clone()), c.cube(bv.clone()));
            let (hc_id, _) = b.fresh_local(h_cube.clone());
            let concl = c.le(a.clone(), bv.clone());
            let e = b.mk_pi(hc_id, BinderInfo::Default, h_cube, concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, h_b, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, h_a, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_le_of_cube_le_cube(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Proof term for `Rat.le_of_cube_le_cube` (mirrors `Rat.le_of_sq_le_sq`).
fn build_le_of_cube_le_cube(c: &CubeConsts) -> Expr {
    let cube_lt_cube = Expr::const_(
        Name::from_string("Rat.cube_lt_cube_of_lt_of_nonneg"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_a_ty = c.le(c.rat_zero.clone(), a.clone());
    let (ha_id, _h_a) = b.fresh_local(h_a_ty.clone());
    let h_b_ty = c.le(c.rat_zero.clone(), bv.clone());
    let (hb_id, h_b) = b.fresh_local(h_b_ty.clone());
    let h_cube_ty = c.le(c.cube(a.clone()), c.cube(bv.clone()));
    let (hc_id, h_cube) = b.fresh_local(h_cube_ty.clone());

    let le_ab = c.le(a.clone(), bv.clone()); // a ≤ b  (goal)
    let not_le_ab = c.not_pi(&b, le_ab.clone()); // ¬(a ≤ b)
    let le_ba = c.le(bv.clone(), a.clone()); // b ≤ a

    // Classical.em (a ≤ b)
    let h_em = Expr::app(c.classical_em.clone(), le_ab.clone());

    // positive: λ h => h
    let em_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = ch.fresh_local(le_ab.clone());
        ch.finish_child(ch.mk_lam(h_id, BinderInfo::Default, le_ab.clone(), h))
    };

    // negative: λ hn => le_total split
    let em_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hn_id, hn) = ch.fresh_local(not_le_ab.clone());

        let h_total = c.le_total(a.clone(), bv.clone());

        // total-left: λ (h:a≤b) => h
        let tot_left = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (h_id, h) = d.fresh_local(le_ab.clone());
            d.finish_child(d.mk_lam(h_id, BinderInfo::Default, le_ab.clone(), h))
        };

        // total-right: λ (hba:b≤a) => False.elim ...
        let tot_right = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (hba_id, hba) = d.fresh_local(le_ba.clone());

            // h_lt_ba : b < a  [Iff.mpr (lt_iff b a) (And.intro (b≤a)(¬(a≤b)) hba hn)]
            let not_le_ab_d = c.not_pi(&d, le_ab.clone());
            let and_ty = c.and_ty(le_ba.clone(), not_le_ab_d.clone());
            let and_proof = c.and_intro(le_ba.clone(), not_le_ab_d.clone(), hba, hn.clone());
            let h_lt_ba = c.iff_mpr(
                c.lt(bv.clone(), a.clone()),
                and_ty,
                c.lt_iff(bv.clone(), a.clone()),
                and_proof,
            );

            // h_bbb_lt_aaa : b³ < a³  [cube_lt_cube a b h_b h_lt_ba]
            let h_bbb_lt_aaa = Expr::apps(
                cube_lt_cube.clone(),
                [a.clone(), bv.clone(), h_b.clone(), h_lt_ba],
            );

            let b3 = c.cube(bv.clone());
            let a3 = c.cube(a.clone());

            // h_b3_lt_b3 : b³ < b³  [lt_of_lt_of_le b³ a³ b³ (b³<a³)(a³≤b³)]
            let h_b3_lt_b3 =
                c.lt_of_lt_of_le(b3.clone(), a3, b3.clone(), h_bbb_lt_aaa, h_cube.clone());

            // mp h_b3_lt_b3 : (b³≤b³) ∧ ¬(b³≤b³)
            let le_b3b3 = c.le(b3.clone(), b3.clone());
            let not_le_b3b3 = c.not_pi(&d, le_b3b3.clone());
            let rhs_b3 = c.and_ty(le_b3b3.clone(), not_le_b3b3.clone());
            let mp_b3 = c.iff_mp(
                c.lt(b3.clone(), b3.clone()),
                rhs_b3,
                c.lt_iff(b3.clone(), b3.clone()),
                h_b3_lt_b3,
            );
            let h_le = c.and_left(le_b3b3.clone(), not_le_b3b3.clone(), mp_b3.clone());
            let h_not_le = c.and_right(le_b3b3.clone(), not_le_b3b3.clone(), mp_b3);
            let h_false = Expr::app(h_not_le, h_le);

            let body = c.false_elim(le_ab.clone(), h_false);
            d.finish_child(d.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), body))
        };

        let body = c.or_elim(
            &ch,
            le_ab.clone(),
            le_ba.clone(),
            le_ab.clone(),
            h_total,
            tot_left,
            tot_right,
        );
        ch.finish_child(ch.mk_lam(hn_id, BinderInfo::Default, not_le_ab.clone(), body))
    };

    let body = c.or_elim(
        &b,
        le_ab.clone(),
        not_le_ab.clone(),
        le_ab.clone(),
        h_em,
        em_pos,
        em_neg,
    );

    let e = b.mk_lam(hc_id, BinderInfo::Default, h_cube_ty, body);
    let e = b.mk_lam(hb_id, BinderInfo::Default, h_b_ty, e);
    let e = b.mk_lam(ha_id, BinderInfo::Default, h_a_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
