// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level ReLU definitions and IBP ReLU soundness (T81).
//!
//! Registers the ReLU activation function and the constructive proof of
//! T81 (IBP ReLU soundness) for Publication Target 1 (CAV/TACAS/ICML 2027).
//!
//! ## Definitions
//!
//! - `NNVerify.relu : Rat -> Rat` := `Rat.max Rat.zero x`
//! - `NNVerify.relu_vec : (d : Nat) -> NNVec d -> NNVec d` := element-wise ReLU
//!
//! ## Sub-Lemmas (constructive proofs via `Rat.max_def`/`max_def'`)
//!
//! - `NNVerify.relu_nonneg`: relu(x) >= 0 (via Or.rec on le_total)
//! - `NNVerify.relu_of_nonneg`: x >= 0 -> relu(x) = x (via max_def)
//! - `NNVerify.relu_of_nonpos`: x <= 0 -> relu(x) = 0 (via max_def')
//! - `NNVerify.relu_monotone`: x <= y -> relu(x) <= relu(y) (3-case Or.rec)
//!
//! ## T81 Theorem
//!
//! - `NNVerify.ibp_relu_bounds`: IBP bound computation (Definition)
//! - `NNVerify.ibp_relu_soundness`: soundness theorem (constructive proof)
//!
//! ## Axiom Budget
//!
//! 6 axioms eliminated: relu_nonneg, relu_of_nonneg, relu_of_nonpos,
//! relu_monotone, ibp_relu_bounds, ibp_relu_soundness. Zero new axioms.
//!
//! Part of #3220, #3254.

use crate::env::nn_verify_relu_builders as builders;
use crate::env::nn_verify_relu_proofs::T81Consts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize ReLU definitions and T81 (IBP ReLU soundness) proofs.
    pub fn init_nn_verify_relu(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_relu_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_minmax()?;
        self.init_rat_linear_order()?;
        self.init_or()?;
        self.init_eq()?;
        self.init_and()?;

        self.register_relu_def()?;
        self.register_relu_vec_def()?;
        self.register_relu_of_nonneg_thm()?;
        self.register_relu_of_nonpos_thm()?;
        self.register_relu_nonneg_thm()?;
        self.register_relu_monotone_thm()?;
        self.register_ibp_relu_bounds_def()?;
        self.register_ibp_relu_soundness_thm()?;

        self.nn_verify_relu_init = true;
        Ok(())
    }

    /// Check if ReLU definitions and T81 have been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_relu(&self) -> bool {
        self.nn_verify_relu_init
    }

    /// `NNVerify.relu (x : Rat) : Rat := Rat.max Rat.zero x`
    fn register_relu_def(&mut self) -> Result<(), EnvError> {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let relu_type = Expr::pi(BinderInfo::Default, rat.clone(), rat.clone());
        let relu_value = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            let body = Expr::app(Expr::app(rat_max, rat_zero), x);
            let e = b.mk_lam(x_id, BinderInfo::Default, rat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.relu"),
            level_params: vec![],
            type_: relu_type,
            value: relu_value,
            is_reducible: true,
        })
    }

    /// `NNVerify.relu_vec (d : Nat) (x : NNVec d) : NNVec d`
    fn register_relu_vec_def(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
        let relu = Expr::const_(Name::from_string("NNVerify.relu"), vec![]);
        let relu_vec_type = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(nat.clone());
            let nn_vec_d = Expr::app(nn_vec.clone(), d.clone());
            let (_x_id, _x) = b.fresh_local(nn_vec_d.clone());
            let r = b.mk_pi(_x_id, BinderInfo::Default, nn_vec_d.clone(), nn_vec_d);
            let r = b.mk_pi(d_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };
        let relu_vec_value = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(nat.clone());
            let nn_vec_d = Expr::app(nn_vec, d.clone());
            let (x_id, x) = b.fresh_local(nn_vec_d.clone());
            let fin_d = Expr::app(fin, d);
            let inner = {
                let mut ch = crate::env::decl_builder::EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = Expr::app(relu, Expr::app(x.clone(), i));
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, body);
                ch.finish_child(r)
            };
            let e = b.mk_lam(x_id, BinderInfo::Default, nn_vec_d, inner);
            let e = b.mk_lam(d_id, BinderInfo::Default, nat, e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.relu_vec"),
            level_params: vec![],
            type_: relu_vec_type,
            value: relu_vec_value,
            is_reducible: true,
        })
    }

    /// `relu_of_nonneg : forall x, 0 <= x -> relu x = x`
    fn register_relu_of_nonneg_thm(&mut self) -> Result<(), EnvError> {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let relu = Expr::const_(Name::from_string("NNVerify.relu"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
        let ty = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            let le_0_x = Expr::app(Expr::app(rat_le.clone(), rat_zero.clone()), x.clone());
            let (h_id, _) = b.fresh_local(le_0_x.clone());
            let eq_relu_x = Expr::app(
                Expr::app(Expr::app(eq_c, rat.clone()), Expr::app(relu, x.clone())),
                x,
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_0_x, eq_relu_x);
            let e = b.mk_pi(x_id, BinderInfo::Default, rat, e);
            b.finish(e)
        };
        let value = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let rat = Expr::const_(Name::from_string("Rat"), vec![]);
            let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
            let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
            let (x_id, x) = b.fresh_local(rat.clone());
            let le_0_x = Expr::app(Expr::app(rat_le, rat_zero.clone()), x.clone());
            let (h_id, h) = b.fresh_local(le_0_x.clone());
            let body = Expr::app(Expr::app(Expr::app(max_def, rat_zero), x), h);
            let e = b.mk_lam(h_id, BinderInfo::Default, le_0_x, body);
            let e = b.mk_lam(x_id, BinderInfo::Default, rat, e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.relu_of_nonneg"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `relu_of_nonpos : forall x, x <= 0 -> relu x = 0`
    fn register_relu_of_nonpos_thm(&mut self) -> Result<(), EnvError> {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let relu = Expr::const_(Name::from_string("NNVerify.relu"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let max_def_alt = Expr::const_(Name::from_string("Rat.max_def'"), vec![]);
        let ty = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(rat.clone());
            let le_x_0 = Expr::app(Expr::app(rat_le.clone(), x.clone()), rat_zero.clone());
            let (h_id, _) = b.fresh_local(le_x_0.clone());
            let eq_relu_0 = Expr::app(
                Expr::app(Expr::app(eq_c, rat.clone()), Expr::app(relu, x)),
                rat_zero,
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_x_0, eq_relu_0);
            let e = b.mk_pi(x_id, BinderInfo::Default, rat, e);
            b.finish(e)
        };
        let value = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let rat = Expr::const_(Name::from_string("Rat"), vec![]);
            let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
            let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
            let (x_id, x) = b.fresh_local(rat.clone());
            let le_x_0 = Expr::app(Expr::app(rat_le, x.clone()), rat_zero.clone());
            let (h_id, h) = b.fresh_local(le_x_0.clone());
            let body = Expr::app(Expr::app(Expr::app(max_def_alt, rat_zero), x), h);
            let e = b.mk_lam(h_id, BinderInfo::Default, le_x_0, body);
            let e = b.mk_lam(x_id, BinderInfo::Default, rat, e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.relu_of_nonpos"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `relu_nonneg : forall x, 0 <= relu(x)` — delegates to builder.
    fn register_relu_nonneg_thm(&mut self) -> Result<(), EnvError> {
        let c = T81Consts::new();
        let (ty, value) = builders::build_relu_nonneg_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.relu_nonneg"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `relu_monotone : forall x y, x <= y -> relu x <= relu y`
    fn register_relu_monotone_thm(&mut self) -> Result<(), EnvError> {
        let c = T81Consts::new();
        let (ty, value) = builders::build_relu_monotone_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.relu_monotone"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `ibp_relu_bounds` as a Definition (element-wise relu on bounds).
    fn register_ibp_relu_bounds_def(&mut self) -> Result<(), EnvError> {
        let c = T81Consts::new();
        let ibp_type = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let (_b_id, _bv) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(_b_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let ibp_value = builders::build_ibp_relu_bounds_value(&c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.ibp_relu_bounds"),
            level_params: vec![],
            type_: ibp_type,
            value: ibp_value,
            is_reducible: true,
        })
    }

    /// T81: `ibp_relu_soundness` — delegates to builder.
    fn register_ibp_relu_soundness_thm(&mut self) -> Result<(), EnvError> {
        let c = T81Consts::new();
        let t81_type = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let nn_vec_d = Expr::app(c.nn_vec.clone(), d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(nn_vec_d.clone());
            let contains_b_x = Expr::app(
                Expr::app(Expr::app(c.contains.clone(), d.clone()), bv.clone()),
                x.clone(),
            );
            let ibp_result = Expr::app(Expr::app(c.ibp_relu_bounds.clone(), d.clone()), bv);
            let relu_result = Expr::app(Expr::app(c.relu_vec.clone(), d.clone()), x);
            let contains_out = Expr::app(
                Expr::app(Expr::app(c.contains.clone(), d), ibp_result),
                relu_result,
            );
            let (h_id, _) = b.fresh_local(contains_b_x.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, contains_b_x, contains_out);
            let e = b.mk_pi(x_id, BinderInfo::Default, nn_vec_d, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let t81_value = builders::build_t81_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ibp_relu_soundness"),
            level_params: vec![],
            type_: t81_type,
            value: t81_value,
        })
    }
}
