// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared constants and helpers for T81 (IBP ReLU soundness) proofs.
//!
//! `T81Consts` centralizes all constant `Expr` references needed by the
//! constructive proof builders in `nn_verify_relu_builders`.
//!
//! Part of #3220, #3254.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for T81 proof construction.
pub(super) struct T81Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) ib_mk: Expr,
    pub(super) relu: Expr,
    pub(super) relu_vec: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_le: Expr,
    pub(super) le_total: Expr,
    pub(super) le_refl: Expr,
    pub(super) or: Expr,
    pub(super) or_rec: Expr,
    pub(super) and_intro: Expr,
    pub(super) and_left: Expr,
    pub(super) and_right: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_subst: Expr,
    pub(super) contains: Expr,
    pub(super) ibp_relu_bounds: Expr,
    pub(super) relu_of_nonneg_c: Expr,
    pub(super) relu_of_nonpos_c: Expr,
    pub(super) relu_monotone_c: Expr,
}

impl T81Consts {
    pub(super) fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
            relu: Expr::const_(Name::from_string("NNVerify.relu"), vec![]),
            relu_vec: Expr::const_(Name::from_string("NNVerify.relu_vec"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_le: Expr::const_(Name::from_string("Rat.le"), vec![]),
            le_total: Expr::const_(Name::from_string("Rat.le_total"), vec![]),
            le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            or: Expr::const_(Name::from_string("Or"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
            contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            ibp_relu_bounds: Expr::const_(Name::from_string("NNVerify.ibp_relu_bounds"), vec![]),
            relu_of_nonneg_c: Expr::const_(Name::from_string("NNVerify.relu_of_nonneg"), vec![]),
            relu_of_nonpos_c: Expr::const_(Name::from_string("NNVerify.relu_of_nonpos"), vec![]),
            relu_monotone_c: Expr::const_(Name::from_string("NNVerify.relu_monotone"), vec![]),
        }
    }

    /// `Rat.le a b`
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_le.clone(), a), b)
    }

    /// `Eq.symm @Rat @a @b h`
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.eq_symm.clone(), self.rat.clone()), a),
                b,
            ),
            h,
        )
    }

    /// `Eq.subst @Rat @motive @a @b h_eq h_ma`
    pub(super) fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(self.eq_subst.clone(), self.rat.clone()), motive),
                        a,
                    ),
                    b,
                ),
                h_eq,
            ),
            h_ma,
        )
    }

    /// Build `Or.rec @a @b @motive case_inl case_inr major`
    pub(super) fn or_rec_app(
        &self,
        a_prop: Expr,
        b_prop: Expr,
        motive: Expr,
        case_inl: Expr,
        case_inr: Expr,
        major: Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(self.or_rec.clone(), a_prop), b_prop),
                        motive,
                    ),
                    case_inl,
                ),
                case_inr,
            ),
            major,
        )
    }

    /// Constant Or.rec motive: `fun (_ : Or a b) => goal`
    pub(super) fn const_motive(
        &self,
        outer: &EnvDeclBuilder,
        a_prop: &Expr,
        b_prop: &Expr,
        goal: &Expr,
    ) -> Expr {
        let or_ab = Expr::app(Expr::app(self.or.clone(), a_prop.clone()), b_prop.clone());
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (h_id, _) = ch.fresh_local(or_ab.clone());
        let r = ch.mk_lam(h_id, BinderInfo::Default, or_ab, goal.clone());
        ch.finish_child(r)
    }

    /// `NNVerify.relu x`
    pub(super) fn relu_app(&self, x: Expr) -> Expr {
        Expr::app(self.relu.clone(), x)
    }

    /// `Rat.le_total a b`
    pub(super) fn le_total_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.le_total.clone(), a), b)
    }

    /// `Rat.le_refl a`
    pub(super) fn le_refl_app(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }

    /// `Rat.le_trans a b c hab hbc`
    pub(super) fn le_trans_app(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(le_trans, a), b), c), hab),
            hbc,
        )
    }

    /// `And.intro @a @b ha hb`
    pub(super) fn and_intro_app(&self, a_prop: Expr, b_prop: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.and_intro.clone(), a_prop), b_prop),
                ha,
            ),
            hb,
        )
    }

    /// `And.left @a @b h`
    pub(super) fn and_left_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_left.clone(), a), b), h)
    }

    /// `And.right @a @b h`
    pub(super) fn and_right_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_right.clone(), a), b), h)
    }

    /// Transport inequality through two equality proofs.
    ///
    /// Given `eq_lhs : Eq (relu x) x_val`, `eq_rhs : Eq (relu y) y_val`,
    /// `h_le : x_val <= y_val`, produces `relu(x) <= relu(y)`.
    pub(super) fn transport_le(
        &self,
        outer: &EnvDeclBuilder,
        relu_x: &Expr,
        relu_y: &Expr,
        x_val: &Expr,
        y_val: &Expr,
        eq_lhs: Expr,
        eq_rhs: Expr,
        h_le: Expr,
    ) -> Expr {
        let sym_lhs = self.symm(relu_x.clone(), x_val.clone(), eq_lhs);
        let motive1 = {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let (z_id, z) = ch.fresh_local(self.rat.clone());
            let body = self.le(z, y_val.clone());
            let r = ch.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(r)
        };
        let step2 = self.subst(motive1, x_val.clone(), relu_x.clone(), sym_lhs, h_le);

        let sym_rhs = self.symm(relu_y.clone(), y_val.clone(), eq_rhs);
        let motive2 = {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let (z_id, z) = ch.fresh_local(self.rat.clone());
            let body = self.le(relu_x.clone(), z);
            let r = ch.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(r)
        };
        self.subst(motive2, y_val.clone(), relu_y.clone(), sym_rhs, step2)
    }
}
