// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal constructive order layer shared by IBP and the Farkas anchor.
//!
//! TrustIR only needs `NNVerify.mul_nonneg_le_left` and
//! `NNVerify.add_le_add` before it can register the three constructive Farkas
//! theorems. Keeping those two declarations here prevents the production
//! Farkas feature from compiling or initializing the much larger IBP and NN
//! foundation suites.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Constants shared by the two constructive Rat order proof builders.
pub(super) struct RatOrderConsts {
    pub(super) rat: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) eq: Expr,
}

impl RatOrderConsts {
    pub(super) fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            #[cfg(test)]
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), lhs, rhs],
        )
    }

    pub(super) fn add(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [lhs, rhs])
    }

    pub(super) fn mul(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [lhs, rhs])
    }
}

impl Environment {
    /// Initialize exactly the two constructive order theorems required by the
    /// Farkas anchor.
    pub(super) fn init_nn_verify_farkas_order(&mut self) -> Result<(), EnvError> {
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_rat_linear_order()?;
        self.init_eq()?;
        self.init_nn_verify_rat_ordering()?;

        let c = RatOrderConsts::new();
        self.register_mul_nonneg_le_left(&c)?;
        self.register_add_le_add(&c)
    }

    /// Register `0 ≤ w → a ≤ b → w*a ≤ w*b` constructively.
    pub(super) fn register_mul_nonneg_le_left(
        &mut self,
        c: &RatOrderConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.mul_nonneg_le_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nonneg = c.rat_le(c.rat_zero.clone(), w.clone());
            let h_le = c.rat_le(a.clone(), bv.clone());
            let concl = c.rat_le(c.mul(w.clone(), a), c.mul(w, bv));
            let (h2_id, _) = b.fresh_local(h_le.clone());
            let (h1_id, _) = b.fresh_local(h_nonneg.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_nonneg, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_mul_le::build_mul_nonneg_le_left_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register monotonicity of Rat addition constructively.
    pub(super) fn register_add_le_add(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.add_le_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a1_id, a1) = b.fresh_local(c.rat.clone());
            let (b1_id, b1v) = b.fresh_local(c.rat.clone());
            let (a2_id, a2) = b.fresh_local(c.rat.clone());
            let (b2_id, b2v) = b.fresh_local(c.rat.clone());
            let h1 = c.rat_le(a1.clone(), b1v.clone());
            let h2 = c.rat_le(a2.clone(), b2v.clone());
            let concl = c.rat_le(c.add(a1, a2), c.add(b1v, b2v));
            let (h2_id, _) = b.fresh_local(h2.clone());
            let (h1_id, _) = b.fresh_local(h1.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1, e);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a1_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_add_le::build_add_le_add_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
