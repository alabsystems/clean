// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term builders for the constructive Farkas-combination theorems.
//!
//! Split out of `nn_verify_foundation_theorems_farkas_constructive.rs` to
//! keep that module under the 500-line limit, matching the existing
//! `nn_verify_ibp_linear_add_le.rs` / `nn_verify_ibp_linear_mul_le.rs`
//! pattern. Hosts the shared `FarkasConsts` term builders and the two
//! `build_*` proof-term constructors.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constant builders for the constructive Farkas combination proofs.
pub(super) struct FarkasConsts {
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) mul_nonneg_le_left: Expr,
    pub(super) add_le_add: Expr,
    pub(super) le_trans: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
}

impl FarkasConsts {
    pub(super) fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            mul_nonneg_le_left: Expr::const_(
                Name::from_string("NNVerify.mul_nonneg_le_left"),
                vec![],
            ),
            add_le_add: Expr::const_(Name::from_string("NNVerify.add_le_add"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
        }
    }

    pub(super) fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    /// `NNVerify.mul_nonneg_le_left w a b h_w_nn h_ab : w*a ≤ w*b`.
    pub(super) fn scale(&self, w: Expr, a: Expr, b: Expr, h_w_nn: Expr, h_ab: Expr) -> Expr {
        Expr::apps(self.mul_nonneg_le_left.clone(), [w, a, b, h_w_nn, h_ab])
    }

    /// `NNVerify.add_le_add a1 b1 a2 b2 h1 h2 : a1+a2 ≤ b1+b2`.
    pub(super) fn add_le(
        &self,
        a1: Expr,
        b1: Expr,
        a2: Expr,
        b2: Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a1, b1, a2, b2, h1, h2])
    }

    /// `Rat.le_trans a b c hab hbc : a ≤ c`.
    pub(super) fn trans(&self, a: Expr, b: Expr, cv: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cv, hab, hbc])
    }
}

/// Proof term for `farkas_combine_2`.
///
/// ```text
/// fun mu1 mu2 a1 b1 a2 b2 h_mu1 h_mu2 h_ab1 h_ab2 =>
///   add_le_add (mu1*a1) (mu1*b1) (mu2*a2) (mu2*b2)
///     (mul_nonneg_le_left mu1 a1 b1 h_mu1 h_ab1)
///     (mul_nonneg_le_left mu2 a2 b2 h_mu2 h_ab2)
/// ```
pub(super) fn build_farkas_combine_2_proof(c: &FarkasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (mu1_id, mu1) = b.fresh_local(c.rat.clone());
    let (mu2_id, mu2) = b.fresh_local(c.rat.clone());
    let (a1_id, a1) = b.fresh_local(c.rat.clone());
    let (b1_id, b1v) = b.fresh_local(c.rat.clone());
    let (a2_id, a2) = b.fresh_local(c.rat.clone());
    let (b2_id, b2v) = b.fresh_local(c.rat.clone());
    let h_mu1 = c.rat_le(c.rat_zero.clone(), mu1.clone());
    let h_mu2 = c.rat_le(c.rat_zero.clone(), mu2.clone());
    let h_ab1 = c.rat_le(a1.clone(), b1v.clone());
    let h_ab2 = c.rat_le(a2.clone(), b2v.clone());
    let (hmu1_id, hmu1) = b.fresh_local(h_mu1.clone());
    let (hmu2_id, hmu2) = b.fresh_local(h_mu2.clone());
    let (hab1_id, hab1) = b.fresh_local(h_ab1.clone());
    let (hab2_id, hab2) = b.fresh_local(h_ab2.clone());

    let scaled1 = c.scale(mu1.clone(), a1.clone(), b1v.clone(), hmu1, hab1);
    let scaled2 = c.scale(mu2.clone(), a2.clone(), b2v.clone(), hmu2, hab2);
    let mu1a1 = c.mul(mu1.clone(), a1.clone());
    let mu1b1 = c.mul(mu1.clone(), b1v.clone());
    let mu2a2 = c.mul(mu2.clone(), a2.clone());
    let mu2b2 = c.mul(mu2.clone(), b2v.clone());
    let body = c.add_le(mu1a1, mu1b1, mu2a2, mu2b2, scaled1, scaled2);

    let e = b.mk_lam(hab2_id, BinderInfo::Default, h_ab2, body);
    let e = b.mk_lam(hab1_id, BinderInfo::Default, h_ab1, e);
    let e = b.mk_lam(hmu2_id, BinderInfo::Default, h_mu2, e);
    let e = b.mk_lam(hmu1_id, BinderInfo::Default, h_mu1, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(mu2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(mu1_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Proof term for `farkas_combine_2_le_bound`.
///
/// ```text
/// fun mu1 mu2 a1 b1 a2 b2 bound h_mu1 h_mu2 h_ab1 h_ab2 h_dom =>
///   Rat.le_trans
///     (mu1*a1 + mu2*a2) (mu1*b1 + mu2*b2) bound
///     (add_le_add … : mu1*a1+mu2*a2 ≤ mu1*b1+mu2*b2)
///     h_dom                            -- mu1*b1+mu2*b2 ≤ bound
/// ```
pub(super) fn build_farkas_combine_2_le_bound_proof(c: &FarkasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (mu1_id, mu1) = b.fresh_local(c.rat.clone());
    let (mu2_id, mu2) = b.fresh_local(c.rat.clone());
    let (a1_id, a1) = b.fresh_local(c.rat.clone());
    let (b1_id, b1v) = b.fresh_local(c.rat.clone());
    let (a2_id, a2) = b.fresh_local(c.rat.clone());
    let (b2_id, b2v) = b.fresh_local(c.rat.clone());
    let (bound_id, bound) = b.fresh_local(c.rat.clone());
    let h_mu1 = c.rat_le(c.rat_zero.clone(), mu1.clone());
    let h_mu2 = c.rat_le(c.rat_zero.clone(), mu2.clone());
    let h_ab1 = c.rat_le(a1.clone(), b1v.clone());
    let h_ab2 = c.rat_le(a2.clone(), b2v.clone());
    let mu1a1 = c.mul(mu1.clone(), a1.clone());
    let mu1b1 = c.mul(mu1.clone(), b1v.clone());
    let mu2a2 = c.mul(mu2.clone(), a2.clone());
    let mu2b2 = c.mul(mu2.clone(), b2v.clone());
    let lower = c.add(mu1a1.clone(), mu2a2.clone());
    let upper = c.add(mu1b1.clone(), mu2b2.clone());
    let h_dom_ty = c.rat_le(upper.clone(), bound.clone());

    let (hmu1_id, hmu1) = b.fresh_local(h_mu1.clone());
    let (hmu2_id, hmu2) = b.fresh_local(h_mu2.clone());
    let (hab1_id, hab1) = b.fresh_local(h_ab1.clone());
    let (hab2_id, hab2) = b.fresh_local(h_ab2.clone());
    let (hdom_id, hdom) = b.fresh_local(h_dom_ty.clone());

    // combined : lower ≤ upper, via add_le_add of the two scalings.
    let scaled1 = c.scale(mu1.clone(), a1.clone(), b1v.clone(), hmu1, hab1);
    let scaled2 = c.scale(mu2.clone(), a2.clone(), b2v.clone(), hmu2, hab2);
    let combined = c.add_le(
        mu1a1.clone(),
        mu1b1.clone(),
        mu2a2.clone(),
        mu2b2.clone(),
        scaled1,
        scaled2,
    );

    // Rat.le_trans lower upper bound combined h_dom : lower ≤ bound.
    let body = c.trans(lower, upper, bound.clone(), combined, hdom);

    let e = b.mk_lam(hdom_id, BinderInfo::Default, h_dom_ty, body);
    let e = b.mk_lam(hab2_id, BinderInfo::Default, h_ab2, e);
    let e = b.mk_lam(hab1_id, BinderInfo::Default, h_ab1, e);
    let e = b.mk_lam(hmu2_id, BinderInfo::Default, h_mu2, e);
    let e = b.mk_lam(hmu1_id, BinderInfo::Default, h_mu1, e);
    let e = b.mk_lam(bound_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(mu2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(mu1_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
