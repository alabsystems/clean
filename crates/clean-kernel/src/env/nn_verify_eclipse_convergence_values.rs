// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C003 Opaque definition value builders (Category A fix).
//!
//! Contains 6 individual register functions for definition declarations
//! that were upgraded from `Declaration::Axiom` to `Declaration::Opaque`.
//! Split from `nn_verify_eclipse_convergence.rs` for function-size compliance.

use super::nn_verify_eclipse_convergence_defs::{self, ConvergenceConsts};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register all 6 Opaque definition declarations for ECLipsE convergence.
    ///
    /// Formerly axioms (Category A), now Opaque definitions. Each has a
    /// well-typed placeholder value (the kernel verifies typing but does
    /// not reduce opaque definitions).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_eclipse_defs(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        self.register_eclipse_rat_pow(c)?;
        self.register_eclipse_width(c)?;
        self.register_eclipse_refine_op(c)?;
        self.register_eclipse_refine_apply(c)?;
        self.register_eclipse_log_rat(c)?;
        self.register_eclipse_ceil_nat(c)?;
        Ok(())
    }

    /// `NNVerify.ECLipsE.rat_pow : Rat -> Nat -> Rat`
    /// Opaque: placeholder `fun (r : Rat) (_ : Nat) => r`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_rat_pow(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_rat_pow_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.rat_pow"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ECLipsE.width : (n : Nat) -> Nat -> (NNVec n -> NNVec n) -> Rat -> Rat`
    /// Opaque: placeholder `fun (n k : Nat) (_ : endo) (_ : Rat) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_width(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_width_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (t_id, _) = b.fresh_local(endo.clone());
            let (w_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            let e = b.mk_lam(t_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.width"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ECLipsE.refine_op : Nat -> Type`
    /// Opaque: placeholder `fun (n : Nat) => NNVec n`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_refine_op(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_refine_op_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(c.nn_vec.clone(), n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.refine_op"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ECLipsE.refine_apply : (n : Nat) -> refine_op n -> NNVec n -> NNVec n`
    /// Opaque: placeholder `fun (n : Nat) (_ : refine_op n) (v : NNVec n) => v`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_refine_apply(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_refine_apply_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let op_n = Expr::app(c.refine_op.clone(), n.clone());
            let vec_n = Expr::app(c.nn_vec.clone(), n);
            let (op_id, _) = b.fresh_local(op_n.clone());
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, v);
            let e = b.mk_lam(op_id, BinderInfo::Default, op_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.refine_apply"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ECLipsE.log_rat : Rat -> Rat`
    /// Opaque: placeholder `fun (_ : Rat) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_log_rat(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_log_rat_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.log_rat"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ECLipsE.ceil_nat : Rat -> Nat`
    /// Opaque: placeholder `fun (_ : Rat) => Nat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_eclipse_ceil_nat(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let ty = nn_verify_eclipse_convergence_defs::build_ceil_nat_type(c);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), nat_zero);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.ceil_nat"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
