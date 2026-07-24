// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C028 Opaque registrations
//!
//! 7 function opaques (formerly axioms) for the Neural Nullstellensatz.
//! Each provides a well-typed placeholder value so the declaration
//! is `Declaration::Opaque` rather than `Declaration::Axiom`.
//!
//! Additionally, `nn_verify_nullstellensatz.rs` registers 2 core theorem
//! opaques (sos_existence_core, degree_bound_core) via sorry-based proof
//! inhabitation, bringing C028 to ZERO domain axioms.
//!
//! Type definitions (4 `Declaration::Definition` entries) are registered
//! as reducible in `nn_verify_nullstellensatz.rs`, which allows these
//! opaques to type-check (the types reduce during checking).
//!
//! See: `nn_verify_nullstellensatz.rs` for the full inventory.

use super::nn_verify_nullstellensatz_defs::{
    build_network_depth_type, build_network_width_type, build_property_holds_type,
    build_property_polynomial_type, build_relu_to_pwl_type, build_sos_certifies_type,
    build_sos_degree_type, C028Consts,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `relu_to_pwl : (d_in d_out : Nat) -> ReLUNetwork -> PiecewiseLinear d_in d_out`
    /// Opaque: `fun _ _ _ => Nat.zero`
    /// (ReLUNetwork reduces to Nat, PiecewiseLinear d_in d_out reduces to Nat)
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_relu_to_pwl(
        &mut self,
        c: &C028Consts,
        nat_zero: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.relu_to_pwl");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (din_id, _) = b.fresh_local(c.nat.clone());
            let (dout_id, _) = b.fresh_local(c.nat.clone());
            // ReLUNetwork reduces to Nat
            let (net_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(net_id, BinderInfo::Default, c.nat.clone(), nat_zero.clone());
            let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_relu_to_pwl_type(c),
            value,
        })
    }

    /// `sos_certifies : (d : Nat) -> SoSCertificate d -> Polynomial d -> IntervalBounds d -> Prop`
    ///
    /// Definition: `fun d sigma poly region => sigma poly region`.
    ///
    /// This retires the #3567 Branch-A predicate axiom without reviving the
    /// old `fun _ _ _ _ => True` carrier. `SoSCertificate d` now reduces to
    /// `Polynomial d -> IntervalBounds d -> Prop`, so a certificate is
    /// explicitly local predicate evidence for the polynomial/region pair.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_def_sos_certifies(
        &mut self,
        c: &C028Consts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.sos_certifies");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let sigma_ty = c.sos_of(&d);
            let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());
            let poly_ty = c.poly_of(&d);
            let (poly_id, poly) = b.fresh_local(poly_ty.clone());
            let region_ty = c.ib_of(&d);
            let (region_id, region) = b.fresh_local(region_ty.clone());
            let body = Expr::app(Expr::app(sigma, poly), region);
            let e = b.mk_lam(region_id, BinderInfo::Default, region_ty, body);
            let e = b.mk_lam(poly_id, BinderInfo::Default, poly_ty, e);
            let e = b.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: n,
            level_params: vec![],
            type_: build_sos_certifies_type(c),
            value,
            is_reducible: true,
        })
    }

    /// `sos_degree : (d : Nat) -> SoSCertificate d -> Nat`
    /// Opaque: `fun _ _ => Nat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_sos_degree(
        &mut self,
        c: &C028Consts,
        nat_zero: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.sos_degree");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let sig_ty = c.sos_of(&d);
            let (sig_id, _) = b.fresh_local(sig_ty.clone());
            let e = b.mk_lam(sig_id, BinderInfo::Default, sig_ty, nat_zero.clone());
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_sos_degree_type(c),
            value,
        })
    }

    /// `network_depth : ReLUNetwork -> Nat`
    /// Opaque: `fun _ => Nat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_network_depth(
        &mut self,
        c: &C028Consts,
        nat_zero: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.network_depth");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        // ReLUNetwork reduces to Nat
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (net_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(net_id, BinderInfo::Default, c.nat.clone(), nat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_network_depth_type(c),
            value,
        })
    }

    /// `network_width : ReLUNetwork -> Nat`
    /// Opaque: `fun _ => Nat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_network_width(
        &mut self,
        c: &C028Consts,
        nat_zero: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.network_width");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        // ReLUNetwork reduces to Nat
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (net_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(net_id, BinderInfo::Default, c.nat.clone(), nat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_network_width_type(c),
            value,
        })
    }

    /// `property_polynomial : (d_in d_out : Nat) -> PiecewiseLinear d_in d_out -> (NNVec d_in -> Prop) -> Polynomial d_in`
    /// Opaque: `fun _ _ _ _ => Nat.zero`
    /// (PiecewiseLinear reduces to Nat, Polynomial d_in reduces to Nat)
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_property_polynomial(
        &mut self,
        c: &C028Consts,
        nat_zero: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.property_polynomial");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (din_id, din) = b.fresh_local(c.nat.clone());
            let (dout_id, _) = b.fresh_local(c.nat.clone());
            // PiecewiseLinear d_in d_out reduces to Nat
            let (f_id, _) = b.fresh_local(c.nat.clone());
            let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
            let (p_id, _) = b.fresh_local(pred_ty.clone());
            let e = b.mk_lam(p_id, BinderInfo::Default, pred_ty, nat_zero.clone());
            let e = b.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_property_polynomial_type(c),
            value,
        })
    }

    /// `property_holds_on_region : (d_in d_out : Nat) -> PiecewiseLinear d_in d_out -> (NNVec d_in -> Prop) -> IntervalBounds d_in -> Prop`
    /// Opaque: `fun _ _ _ _ _ => True`
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c028_opaque_property_holds(
        &mut self,
        c: &C028Consts,
        true_const: &Expr,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.property_holds_on_region");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (din_id, din) = b.fresh_local(c.nat.clone());
            let (dout_id, _) = b.fresh_local(c.nat.clone());
            // PiecewiseLinear d_in d_out reduces to Nat
            let (f_id, _) = b.fresh_local(c.nat.clone());
            let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
            let (p_id, _) = b.fresh_local(pred_ty.clone());
            let ib_din = c.ib_of(&din);
            let (region_id, _) = b.fresh_local(ib_din.clone());
            let e = b.mk_lam(region_id, BinderInfo::Default, ib_din, true_const.clone());
            let e = b.mk_lam(p_id, BinderInfo::Default, pred_ty, e);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: build_property_holds_type(c),
            value,
        })
    }
}
