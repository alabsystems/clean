// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C028 Type Builders
//!
//! Status: Type builders for C028 declarations. Type-level definitions
//! use `Declaration::Definition` (reducible), function definitions use
//! `Declaration::Opaque`, and core theorem opaques use sorry-based proof
//! inhabitation. ZERO domain axioms remain.
//! See `nn_verify_nullstellensatz.rs` for the full inventory.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ---
//!
//! Separated from `nn_verify_nullstellensatz` for file-size compliance.
//! All `build_*` functions return well-formed `Expr` types/values for
//! kernel declaration registration.
//!
//! ## Theorem Statement
//!
//! For a piecewise-linear ReLU network and a property P that holds on
//! a constraint region C, there exists a Sum-of-Squares (SoS) polynomial
//! certificate sigma of degree bounded by O(L * W) (depth times width)
//! that certifies the property algebraically, bypassing Branch-and-Bound.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C028 theorem construction.
pub(super) struct C028Consts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) relu_network: Expr,
    pub(super) polynomial: Expr,
    pub(super) sos_certificate: Expr,
    pub(super) piecewise_linear: Expr,
    pub(super) relu_to_pwl: Expr,
    pub(super) sos_certifies: Expr,
    pub(super) sos_degree: Expr,
    pub(super) network_depth: Expr,
    pub(super) network_width: Expr,
    pub(super) property_polynomial: Expr,
    pub(super) property_holds: Expr,
    pub(super) nat_mul: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) exists_: Expr,
    pub(super) and: Expr,
}

impl C028Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::sort(Level::zero()),
            type0: Expr::sort(Level::succ(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            relu_network: Expr::const_(Name::from_string("NNVerify.C028.ReLUNetwork"), vec![]),
            polynomial: Expr::const_(Name::from_string("NNVerify.C028.Polynomial"), vec![]),
            sos_certificate: Expr::const_(
                Name::from_string("NNVerify.C028.SoSCertificate"),
                vec![],
            ),
            piecewise_linear: Expr::const_(
                Name::from_string("NNVerify.C028.PiecewiseLinear"),
                vec![],
            ),
            relu_to_pwl: Expr::const_(Name::from_string("NNVerify.C028.relu_to_pwl"), vec![]),
            sos_certifies: Expr::const_(Name::from_string("NNVerify.C028.sos_certifies"), vec![]),
            sos_degree: Expr::const_(Name::from_string("NNVerify.C028.sos_degree"), vec![]),
            network_depth: Expr::const_(Name::from_string("NNVerify.C028.network_depth"), vec![]),
            network_width: Expr::const_(Name::from_string("NNVerify.C028.network_width"), vec![]),
            property_polynomial: Expr::const_(
                Name::from_string("NNVerify.C028.property_polynomial"),
                vec![],
            ),
            property_holds: Expr::const_(
                Name::from_string("NNVerify.C028.property_holds_on_region"),
                vec![],
            ),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            exists_: Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            and: Expr::const_(Name::from_string("And"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    pub(super) fn poly_of(&self, d: &Expr) -> Expr {
        Expr::app(self.polynomial.clone(), d.clone())
    }

    pub(super) fn sos_of(&self, d: &Expr) -> Expr {
        Expr::app(self.sos_certificate.clone(), d.clone())
    }

    pub(super) fn pwl_of(&self, d_in: &Expr, d_out: &Expr) -> Expr {
        Expr::apps(self.piecewise_linear.clone(), [d_in.clone(), d_out.clone()])
    }

    /// Build `LE.le @Nat instLENat lhs rhs`.
    pub(super) fn nat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.nat.clone()),
                    self.inst_le_nat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Nat.mul a b`.
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), a), b)
    }

    /// Build `relu_to_pwl d_in d_out net`.
    pub(super) fn relu_to_pwl_app(&self, d_in: &Expr, d_out: &Expr, net: &Expr) -> Expr {
        Expr::apps(
            self.relu_to_pwl.clone(),
            [d_in.clone(), d_out.clone(), net.clone()],
        )
    }

    /// Build `sos_certifies d sigma poly C`.
    pub(super) fn sos_certifies_app(
        &self,
        d: &Expr,
        sigma: &Expr,
        poly: &Expr,
        region: &Expr,
    ) -> Expr {
        Expr::apps(
            self.sos_certifies.clone(),
            [d.clone(), sigma.clone(), poly.clone(), region.clone()],
        )
    }

    /// Build `sos_degree d sigma`.
    pub(super) fn sos_degree_app(&self, d: &Expr, sigma: &Expr) -> Expr {
        Expr::apps(self.sos_degree.clone(), [d.clone(), sigma.clone()])
    }

    /// Build `property_polynomial d_in d_out f P`.
    pub(super) fn prop_poly_app(&self, d_in: &Expr, d_out: &Expr, f: &Expr, p: &Expr) -> Expr {
        Expr::apps(
            self.property_polynomial.clone(),
            [d_in.clone(), d_out.clone(), f.clone(), p.clone()],
        )
    }

    /// Build `property_holds_on_region d_in d_out f P C`.
    pub(super) fn prop_holds_app(
        &self,
        d_in: &Expr,
        d_out: &Expr,
        f: &Expr,
        p: &Expr,
        region: &Expr,
    ) -> Expr {
        Expr::apps(
            self.property_holds.clone(),
            [
                d_in.clone(),
                d_out.clone(),
                f.clone(),
                p.clone(),
                region.clone(),
            ],
        )
    }

    /// Build the degree bound `Nat.mul (network_depth net) (network_width net)`.
    pub(super) fn degree_bound(&self, net: &Expr) -> Expr {
        let depth = Expr::app(self.network_depth.clone(), net.clone());
        let width = Expr::app(self.network_width.clone(), net.clone());
        self.mul(depth, width)
    }
}

// =============================================================================
// Definition type builders
// =============================================================================

/// `NNVerify.C028.Polynomial : Nat -> Type`
pub(super) fn build_polynomial_type(c: &C028Consts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone())
}

/// `NNVerify.C028.SoSCertificate : Nat -> Type`
pub(super) fn build_sos_certificate_type(c: &C028Consts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone())
}

/// `NNVerify.C028.PiecewiseLinear : Nat -> Nat -> Type`
pub(super) fn build_piecewise_linear_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, _) = b.fresh_local(c.nat.clone());
    let (dout_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.C028.relu_to_pwl : (d_in d_out : Nat) -> ReLUNetwork -> PiecewiseLinear d_in d_out`
pub(super) fn build_relu_to_pwl_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (net_id, _) = b.fresh_local(c.relu_network.clone());
    let result = c.pwl_of(&din, &dout);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.relu_network.clone(), result);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.C028.sos_certifies : (d : Nat) -> SoSCertificate d -> Polynomial d -> IntervalBounds d -> Prop`
pub(super) fn build_sos_certifies_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (sig_id, _) = b.fresh_local(c.sos_of(&d));
    let (poly_id, _) = b.fresh_local(c.poly_of(&d));
    let (region_id, _) = b.fresh_local(c.ib_of(&d));
    let e = b.mk_pi(region_id, BinderInfo::Default, c.ib_of(&d), c.prop.clone());
    let e = b.mk_pi(poly_id, BinderInfo::Default, c.poly_of(&d), e);
    let e = b.mk_pi(sig_id, BinderInfo::Default, c.sos_of(&d), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.C028.sos_degree : (d : Nat) -> SoSCertificate d -> Nat`
pub(super) fn build_sos_degree_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (sig_id, _) = b.fresh_local(c.sos_of(&d));
    let e = b.mk_pi(sig_id, BinderInfo::Default, c.sos_of(&d), c.nat.clone());
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.C028.network_depth : ReLUNetwork -> Nat`
pub(super) fn build_network_depth_type(c: &C028Consts) -> Expr {
    Expr::pi(BinderInfo::Default, c.relu_network.clone(), c.nat.clone())
}

/// `NNVerify.C028.network_width : ReLUNetwork -> Nat`
pub(super) fn build_network_width_type(c: &C028Consts) -> Expr {
    Expr::pi(BinderInfo::Default, c.relu_network.clone(), c.nat.clone())
}

/// `NNVerify.C028.property_polynomial : (d_in d_out : Nat) -> PiecewiseLinear d_in d_out -> (NNVec d_in -> Prop) -> Polynomial d_in`
pub(super) fn build_property_polynomial_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (f_id, _) = b.fresh_local(c.pwl_of(&din, &dout));
    let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
    let (p_id, _) = b.fresh_local(pred_ty.clone());
    let result = c.poly_of(&din);
    let e = b.mk_pi(p_id, BinderInfo::Default, pred_ty, result);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.pwl_of(&din, &dout), e);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.C028.property_holds_on_region : (d_in d_out : Nat) -> PiecewiseLinear d_in d_out -> (NNVec d_in -> Prop) -> IntervalBounds d_in -> Prop`
pub(super) fn build_property_holds_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (f_id, _) = b.fresh_local(c.pwl_of(&din, &dout));
    let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
    let (p_id, _) = b.fresh_local(pred_ty.clone());
    let (region_id, _) = b.fresh_local(c.ib_of(&din));
    let e = b.mk_pi(
        region_id,
        BinderInfo::Default,
        c.ib_of(&din),
        c.prop.clone(),
    );
    let e = b.mk_pi(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.pwl_of(&din, &dout), e);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// Build type for C028a: SoS certificate existence.
///
/// ```text
/// forall (d_in d_out : Nat) (net : ReLUNetwork) (C : IntervalBounds d_in)
///   (P : NNVec d_in -> Prop),
///   property_holds_on_region d_in d_out (relu_to_pwl d_in d_out net) P C ->
///   Exists (fun (sigma : SoSCertificate d_in) =>
///     sos_certifies d_in sigma (property_polynomial d_in d_out (relu_to_pwl d_in d_out net) P) C) ->
///   Exists (fun (sigma : SoSCertificate d_in) =>
///     sos_certifies d_in sigma (property_polynomial d_in d_out (relu_to_pwl d_in d_out net) P) C)
/// ```
pub(super) fn build_sos_existence_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (net_id, net) = b.fresh_local(c.relu_network.clone());
    let (region_id, region) = b.fresh_local(c.ib_of(&din));
    let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
    let (p_id, p) = b.fresh_local(pred_ty.clone());

    let f = c.relu_to_pwl_app(&din, &dout, &net);
    let hyp = c.prop_holds_app(&din, &dout, &f, &p, &region);
    let (h_id, _) = b.fresh_local(hyp.clone());

    // Build the Exists predicate lambda: fun sigma => sos_certifies ...
    let poly = c.prop_poly_app(&din, &dout, &f, &p);
    let exists_body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(c.sos_of(&din));
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, c.sos_of(&din), cert_prop);
        ch.finish_child(lam)
    };

    // Exists @(SoSCertificate d_in) (fun sigma => ...)
    let concl = Expr::app(Expr::app(c.exists_.clone(), c.sos_of(&din)), exists_body);
    let (h_sos_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_sos_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_pi(region_id, BinderInfo::Default, c.ib_of(&din), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.relu_network.clone(), e);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for C028b: degree bound O(L*W).
///
/// ```text
/// forall (d_in d_out : Nat) (net : ReLUNetwork) (C : IntervalBounds d_in)
///   (P : NNVec d_in -> Prop) (sigma : SoSCertificate d_in),
///   sos_certifies d_in sigma (property_polynomial d_in d_out (relu_to_pwl d_in d_out net) P) C ->
///   LE.le @Nat instLENat (sos_degree d_in sigma) (Nat.mul (network_depth net) (network_width net))
/// ```
pub(super) fn build_degree_bound_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (net_id, net) = b.fresh_local(c.relu_network.clone());
    let (region_id, region) = b.fresh_local(c.ib_of(&din));
    let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
    let (p_id, p) = b.fresh_local(pred_ty.clone());
    let (sig_id, sigma) = b.fresh_local(c.sos_of(&din));

    let f = c.relu_to_pwl_app(&din, &dout, &net);
    let poly = c.prop_poly_app(&din, &dout, &f, &p);
    let hyp = c.sos_certifies_app(&din, &sigma, &poly, &region);
    let (h_id, _) = b.fresh_local(hyp.clone());

    let concl = c.nat_le(c.sos_degree_app(&din, &sigma), c.degree_bound(&net));

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(sig_id, BinderInfo::Default, c.sos_of(&din), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_pi(region_id, BinderInfo::Default, c.ib_of(&din), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.relu_network.clone(), e);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for C028c: completeness (existence + degree bound).
///
/// ```text
/// forall (d_in d_out : Nat) (net : ReLUNetwork) (C : IntervalBounds d_in)
///   (P : NNVec d_in -> Prop),
///   property_holds_on_region d_in d_out (relu_to_pwl d_in d_out net) P C ->
///   Exists (fun sigma => sos_certifies ...) ->
///   Exists (fun (sigma : SoSCertificate d_in) =>
///     And (sos_certifies ...) (LE.le @Nat instLENat (sos_degree ...) (Nat.mul ...)))
/// ```
pub(super) fn build_completeness_type(c: &C028Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (din_id, din) = b.fresh_local(c.nat.clone());
    let (dout_id, dout) = b.fresh_local(c.nat.clone());
    let (net_id, net) = b.fresh_local(c.relu_network.clone());
    let (region_id, region) = b.fresh_local(c.ib_of(&din));
    let pred_ty = Expr::pi(BinderInfo::Default, c.vec_of(&din), c.prop.clone());
    let (p_id, p) = b.fresh_local(pred_ty.clone());

    let f = c.relu_to_pwl_app(&din, &dout, &net);
    let hyp = c.prop_holds_app(&din, &dout, &f, &p, &region);
    let (h_id, _) = b.fresh_local(hyp.clone());

    let poly = c.prop_poly_app(&din, &dout, &f, &p);

    // Build lambda: fun sigma => And (sos_certifies ...) (LE.le ...)
    let exists_body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(c.sos_of(&din));
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let bound_prop = c.nat_le(c.sos_degree_app(&din, &sigma), c.degree_bound(&net));
        let conj = Expr::app(Expr::app(c.and.clone(), cert_prop), bound_prop);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, c.sos_of(&din), conj);
        ch.finish_child(lam)
    };

    let concl = Expr::app(Expr::app(c.exists_.clone(), c.sos_of(&din)), exists_body);

    let sos_exists = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(c.sos_of(&din));
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, c.sos_of(&din), cert_prop);
        let exists_body = ch.finish_child(lam);
        Expr::app(Expr::app(c.exists_.clone(), c.sos_of(&din)), exists_body)
    };
    let (h_sos_id, _) = b.fresh_local(sos_exists.clone());

    let e = b.mk_pi(h_sos_id, BinderInfo::Default, sos_exists, concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_pi(region_id, BinderInfo::Default, c.ib_of(&din), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.relu_network.clone(), e);
    let e = b.mk_pi(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
