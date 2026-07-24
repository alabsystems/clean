// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof builders for C028: Neural Nullstellensatz.
//!
//! # Proof Strategy
//!
//! C028c (completeness) is the conjunction of C028a (SoS existence) and
//! C028b (degree bound). We eliminate `completeness_core` by composing
//! `sos_existence` and `degree_bound` via `Exists.elim`, `Exists.intro`,
//! and `And.intro`.
//!
//! ## Mathematical Sketch
//!
//! Given:
//! - `sos_existence` (C028a, `Declaration::Axiom` since #3567):
//!   `property_holds -> Exists (fun sigma => sos_certifies ...)`
//! - `degree_bound` (C028b): `sos_certifies ... -> sos_degree sigma <= depth*width`
//!
//! Proof of completeness:
//! ```text
//! fun d_in d_out net C P h =>
//!   Exists.elim (sos_existence d_in d_out net C P h)
//!     (fun sigma h_cert =>
//!       Exists.intro sigma (And.intro h_cert (degree_bound ... sigma h_cert)))
//! ```
//!
//! The `completeness` theorem remains `Declaration::Theorem` with a real
//! constructive proof term — `sos_existence` is now referenced as a
//! `Declaration::Axiom` (#3567 Branch A). `completeness`'s transitive
//! axiom closure therefore includes the C028 axioms `sos_certifies`
//! and `sos_existence` plus the sorry-inhabited `degree_bound_core`.
//!
//! # Historical note
//!
//! Before #3567, this module also housed `build_sos_existence_proof`,
//! which produced the proof term `fun _ _ _ _ _ _ => @Exists.intro _ _
//! Nat.zero True.intro`. That proof type-checked only through
//! delta-collapse of the reducible `sos_certifies = fun _ _ _ _ => True`
//! carrier — a MASQUERADE (Rules M2 + M4 in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`). #3567 Branch A
//! demoted both `sos_certifies` and `sos_existence` to
//! `Declaration::Axiom`. On 2026-04-27 both names were retired from the
//! C028 domain-axiom row by making missing evidence explicit locally.
//!
//! Part of #3377, #3466, #3567.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

use super::nn_verify_nullstellensatz_defs::C028Consts;

/// Build the hypothesis-wrapped proof for `NNVerify.C028.sos_existence`.
///
/// Proof:
/// ```text
/// fun d_in d_out net C P _h h_sos => h_sos
/// ```
pub(super) fn build_sos_existence_proof(c: &C028Consts) -> Expr {
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

    let exists_prop = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(c.sos_of(&din));
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, c.sos_of(&din), cert_prop);
        let exists_body = ch.finish_child(lam);
        Expr::app(Expr::app(c.exists_.clone(), c.sos_of(&din)), exists_body)
    };
    let (h_sos_id, h_sos) = b.fresh_local(exists_prop.clone());

    let e = b.mk_lam(h_sos_id, BinderInfo::Default, exists_prop, h_sos);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_lam(region_id, BinderInfo::Default, c.ib_of(&din), e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.relu_network.clone(), e);
    let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build constructive proof for `NNVerify.C028.completeness`.
///
/// Composes `sos_existence` (C028a) and `degree_bound` (C028b) to prove
/// the combined statement without the `completeness_core` axiom.
///
/// Type:
/// ```text
/// forall (d_in d_out : Nat) (net : ReLUNetwork) (C : IntervalBounds d_in)
///   (P : NNVec d_in -> Prop),
///   property_holds_on_region d_in d_out (relu_to_pwl d_in d_out net) P C ->
///   Exists (fun (sigma : SoSCertificate d_in) =>
///     And (sos_certifies d_in sigma poly C) (LE.le ... (sos_degree d_in sigma) ...))
/// ```
///
/// Proof:
/// ```text
/// fun d_in d_out net C P h =>
///   @Exists.elim (SoSCertificate d_in)
///     (fun sigma => sos_certifies d_in sigma poly C)
///     (Exists (fun sigma => And (sos_certifies ...) (LE.le ...)))
///     (sos_existence d_in d_out net C P h)
///     (fun sigma h_cert =>
///       @Exists.intro (SoSCertificate d_in)
///         (fun sigma => And (sos_certifies ...) (LE.le ...))
///         sigma
///         (And.intro (sos_certifies ...) (LE.le ...)
///           h_cert
///           (degree_bound d_in d_out net C P sigma h_cert)))
/// ```
pub(super) fn build_completeness_proof(c: &C028Consts) -> Expr {
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

    // degree_bound : ... -> sos_certifies ... -> LE.le ...
    let degree_bound_const = Expr::const_(Name::from_string("NNVerify.C028.degree_bound"), vec![]);

    // Exists.elim : {alpha} -> {p} -> {b} -> Exists p -> (forall x, p x -> b) -> b
    let exists_elim_const = Expr::const_(
        Name::from_string("Exists.elim"),
        vec![Level::succ(Level::zero())],
    );
    // Exists.intro : {alpha} -> (p : alpha -> Prop) -> (w : alpha) -> p w -> Exists p
    let exists_intro_const = Expr::const_(
        Name::from_string("Exists.intro"),
        vec![Level::succ(Level::zero())],
    );
    // And.intro : (a b : Prop) -> a -> b -> And a b
    let and_intro_const = Expr::const_(Name::from_string("And.intro"), vec![]);

    let sos_cert_din = c.sos_of(&din);

    // --- Build the elimination predicate for C028a ---
    // pred_a = fun sigma : SoSCertificate d_in => sos_certifies d_in sigma poly C
    let pred_a = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(sos_cert_din.clone());
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, sos_cert_din.clone(), cert_prop);
        ch.finish_child(lam)
    };

    // --- Build the completeness predicate ---
    // pred_c = fun sigma : SoSCertificate d_in =>
    //   And (sos_certifies d_in sigma poly C) (LE.le @Nat instLENat (sos_degree d_in sigma) (Nat.mul ...))
    let pred_c = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(sos_cert_din.clone());
        let cert_prop = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let bound_prop = c.nat_le(c.sos_degree_app(&din, &sigma), c.degree_bound(&net));
        let conj = Expr::app(Expr::app(c.and.clone(), cert_prop), bound_prop);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, sos_cert_din.clone(), conj);
        ch.finish_child(lam)
    };

    // --- The conclusion type (for Exists.elim's {b} parameter) ---
    // b = Exists (fun sigma => And (sos_certifies ...) (LE.le ...))
    let conclusion_type = Expr::app(
        Expr::app(c.exists_.clone(), sos_cert_din.clone()),
        pred_c.clone(),
    );
    let h_sos_ty = Expr::app(
        Expr::app(c.exists_.clone(), sos_cert_din.clone()),
        pred_a.clone(),
    );
    let (h_sos_id, h_sos) = b.fresh_local(h_sos_ty.clone());

    // --- Step 2: Build the elim callback ---
    // fun (sigma : SoSCertificate d_in) (h_cert : sos_certifies d_in sigma poly C) =>
    //   Exists.intro @{SoSCertificate d_in} pred_c sigma
    //     (And.intro cert_prop bound_prop h_cert (degree_bound ... sigma h_cert))
    let elim_callback = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (sig_id, sigma) = ch.fresh_local(sos_cert_din.clone());
        let cert_prop_inst = c.sos_certifies_app(&din, &sigma, &poly, &region);
        let (hcert_id, h_cert) = ch.fresh_local(cert_prop_inst.clone());

        // Apply degree_bound to get the LE proof
        let bound_proof = Expr::apps(
            degree_bound_const,
            [
                din.clone(),
                dout.clone(),
                net.clone(),
                region.clone(),
                p.clone(),
                sigma.clone(),
                h_cert.clone(),
            ],
        );

        let bound_prop_inst = c.nat_le(c.sos_degree_app(&din, &sigma), c.degree_bound(&net));

        // And.intro cert_prop bound_prop h_cert bound_proof
        let and_proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(and_intro_const, cert_prop_inst.clone()),
                    bound_prop_inst,
                ),
                h_cert,
            ),
            bound_proof,
        );

        // Exists.intro @{SoSCertificate d_in} pred_c sigma and_proof
        let intro = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(exists_intro_const, sos_cert_din.clone()),
                    pred_c.clone(),
                ),
                sigma,
            ),
            and_proof,
        );

        let lam = ch.mk_lam(hcert_id, BinderInfo::Default, cert_prop_inst, intro);
        let lam = ch.mk_lam(sig_id, BinderInfo::Default, sos_cert_din.clone(), lam);
        ch.finish_child(lam)
    };

    // --- Step 3: Assemble Exists.elim ---
    // Exists.elim @{SoSCertificate d_in} @{pred_a} @{conclusion_type}
    //   h_sos elim_callback
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(exists_elim_const, sos_cert_din), pred_a),
                conclusion_type,
            ),
            h_sos,
        ),
        elim_callback,
    );

    // --- Abstract over all parameters ---
    let e = b.mk_lam(h_sos_id, BinderInfo::Default, h_sos_ty, body);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(p_id, BinderInfo::Default, pred_ty, e);
    let e = b.mk_lam(region_id, BinderInfo::Default, c.ib_of(&din), e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.relu_network.clone(), e);
    let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
