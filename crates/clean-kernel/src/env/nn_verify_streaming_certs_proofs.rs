// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C007 type and proof term builders.
//!
//! Contains the six builder functions for C007a/b/c theorem types and their
//! proof terms. Split from `nn_verify_streaming_certs_defs.rs` for file-size
//! compliance.
//!
//! **Note:** Proof terms either transport explicit local evidence or forward to
//! the corresponding still-opaque helper declaration. After #3568/#2026-04-27
//! the helpers split into:
//!
//! - `merge_sound_helper`: hypothesis-wrapped `Declaration::Theorem`.
//! - `restrict_refines_helper`, `incremental_cost_helper`:
//!   `Declaration::Opaque` with `sorry_inhabit_pi` bodies (#3381),
//!   still pending their own remediation slices.
//!
//! The old hypothesis-free merge proof was deleted in #3568 because it only
//! type-checked under the MASQUERADE `cert_sound = True` reducible carrier.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//! See: designs/2026-04-19-demasquerade-cxxx-pattern.md
//!
//! Part of #3312, #3150, #3568.

use super::nn_verify_streaming_certs_defs::C007Consts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// ---------------------------------------------------------------
// C007a: Compositionality — merge(Cert(P1), Cert(P2)) is sound for P0
// ---------------------------------------------------------------

/// Build C007a type: merge compositionality.
///
/// ```text
/// forall (d : Nat) (B0 B1 B2 : IntervalBounds d)
///   (c1 c2 : BaBCert d),
///   disjoint_cover d B1 B2 B0 ->
///   cert_sound d B1 c1 ->
///   cert_sound d B2 c2 ->
///   cert_sound d B0 (merge_cert d c1 c2) ->
///   cert_sound d B0 (merge_cert d c1 c2)
/// ```
pub(super) fn build_c007a_type(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (b0_id, b0) = b.fresh_local(ib_d.clone());
    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());
    let (c1_id, c1) = b.fresh_local(cert_d.clone());
    let (c2_id, c2) = b.fresh_local(cert_d.clone());

    let h_cover = c.disj_cover(&d, &b1, &b2, &b0);
    let h_s1 = c.sound(&d, &b1, &c1);
    let h_s2 = c.sound(&d, &b2, &c2);
    let merged = c.merge(&d, &c1, &c2);
    let concl = c.sound(&d, &b0, &merged);

    let (hs2_id, _) = b.fresh_local(h_s2.clone());
    let (hs1_id, _) = b.fresh_local(h_s1.clone());
    let (hc_id, _) = b.fresh_local(h_cover.clone());
    let (hm_id, _) = b.fresh_local(concl.clone());

    let r = b.mk_pi(hm_id, BinderInfo::Default, concl.clone(), concl);
    let r = b.mk_pi(hs2_id, BinderInfo::Default, h_s2, r);
    let r = b.mk_pi(hs1_id, BinderInfo::Default, h_s1, r);
    let r = b.mk_pi(hc_id, BinderInfo::Default, h_cover, r);
    let r = b.mk_pi(c2_id, BinderInfo::Default, cert_d.clone(), r);
    let r = b.mk_pi(c1_id, BinderInfo::Default, cert_d, r);
    let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), r);
    let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d.clone(), r);
    let r = b.mk_pi(b0_id, BinderInfo::Default, ib_d, r);
    let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build C007a proof term by transporting explicit local merge evidence.
///
/// ```text
/// fun (d : Nat) (B0 B1 B2 : IB d) (c1 c2 : BaBCert d)
///     (hcover : disjoint_cover ..) (hs1 : cert_sound ..) (hs2 : cert_sound ..)
///     (hmerge : cert_sound d B0 (merge_cert d c1 c2)) =>
///   hmerge
/// ```
pub(super) fn build_c007a_proof(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (b0_id, b0) = b.fresh_local(ib_d.clone());
    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());
    let (c1_id, c1v) = b.fresh_local(cert_d.clone());
    let (c2_id, c2v) = b.fresh_local(cert_d.clone());

    let h_cover = c.disj_cover(&d, &b1, &b2, &b0);
    let h_s1 = c.sound(&d, &b1, &c1v);
    let h_s2 = c.sound(&d, &b2, &c2v);
    let merged = c.merge(&d, &c1v, &c2v);
    let h_merge = c.sound(&d, &b0, &merged);

    let (hc_id, _) = b.fresh_local(h_cover.clone());
    let (hs1_id, _) = b.fresh_local(h_s1.clone());
    let (hs2_id, _) = b.fresh_local(h_s2.clone());
    let (hm_id, hm) = b.fresh_local(h_merge.clone());

    let e = b.mk_lam(hm_id, BinderInfo::Default, h_merge, hm);
    let e = b.mk_lam(hs2_id, BinderInfo::Default, h_s2, e);
    let e = b.mk_lam(hs1_id, BinderInfo::Default, h_s1, e);
    let e = b.mk_lam(hc_id, BinderInfo::Default, h_cover, e);
    let e = b.mk_lam(c2_id, BinderInfo::Default, cert_d.clone(), e);
    let e = b.mk_lam(c1_id, BinderInfo::Default, cert_d, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b0_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------
// C007b: Incremental cost bound
// ---------------------------------------------------------------

/// Build C007b type: incremental update cost is bounded by delta cost.
///
/// ```text
/// forall (d : Nat) (B B_sub : IntervalBounds d) (c : BaBCert d),
///   subset d B_sub B ->
///   cert_sound d B c ->
///   LE.le @Nat instLENat
///     (cert_cost d (restrict_cert d c B_sub))
///     (Nat.add (delta_cost d c (restrict_cert d c B_sub)) (cert_cost d c))
/// ```
pub(super) fn build_c007b_type(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (bsub_id, bsub) = b.fresh_local(ib_d.clone());
    let (cv_id, cv) = b.fresh_local(cert_d.clone());

    let h_sub = c.subset(&d, &bsub, &bnd);
    let h_sound = c.sound(&d, &bnd, &cv);
    let restricted = c.restrict(&d, &cv, &bsub);
    let lhs = c.cost(&d, &restricted);
    let delta = c.dcost(&d, &cv, &restricted);
    let rhs = c.add_nat(delta, c.cost(&d, &cv));
    let concl = c.nat_le(lhs, rhs);

    let (hs_id, _) = b.fresh_local(h_sound.clone());
    let (hsub_id, _) = b.fresh_local(h_sub.clone());

    let r = b.mk_pi(hs_id, BinderInfo::Default, h_sound, concl);
    let r = b.mk_pi(hsub_id, BinderInfo::Default, h_sub, r);
    let r = b.mk_pi(cv_id, BinderInfo::Default, cert_d, r);
    let r = b.mk_pi(bsub_id, BinderInfo::Default, ib_d.clone(), r);
    let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, r);
    let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build C007b proof term. Delegates to `incremental_cost_helper` Opaque.
pub(super) fn build_c007b_proof(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (bsub_id, bsub) = b.fresh_local(ib_d.clone());
    let (cv_id, cv) = b.fresh_local(cert_d.clone());

    let h_sub = c.subset(&d, &bsub, &bnd);
    let h_sound = c.sound(&d, &bnd, &cv);

    let (hsub_id, hsub) = b.fresh_local(h_sub.clone());
    let (hs_id, hs) = b.fresh_local(h_sound.clone());

    // incremental_cost_helper d B B_sub c hsub hs
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(c.incremental_cost_helper.clone(), d.clone()),
                        bnd.clone(),
                    ),
                    bsub.clone(),
                ),
                cv.clone(),
            ),
            hsub,
        ),
        hs,
    );

    let e = b.mk_lam(hs_id, BinderInfo::Default, h_sound, body);
    let e = b.mk_lam(hsub_id, BinderInfo::Default, h_sub, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, cert_d, e);
    let e = b.mk_lam(bsub_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// ---------------------------------------------------------------
// C007c: Refinement monotonicity — restriction preserves soundness
// ---------------------------------------------------------------

/// Build C007c type: restriction to sub-region preserves soundness.
///
/// ```text
/// forall (d : Nat) (B B_sub : IntervalBounds d) (c : BaBCert d),
///   subset d B_sub B ->
///   cert_sound d B c ->
///   cert_sound d B_sub (restrict_cert d c B_sub)
/// ```
pub(super) fn build_c007c_type(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (bsub_id, bsub) = b.fresh_local(ib_d.clone());
    let (cv_id, cv) = b.fresh_local(cert_d.clone());

    let h_sub = c.subset(&d, &bsub, &bnd);
    let h_sound = c.sound(&d, &bnd, &cv);
    let restricted = c.restrict(&d, &cv, &bsub);
    let concl = c.sound(&d, &bsub, &restricted);

    let (hs_id, _) = b.fresh_local(h_sound.clone());
    let (hsub_id, _) = b.fresh_local(h_sub.clone());

    let r = b.mk_pi(hs_id, BinderInfo::Default, h_sound, concl);
    let r = b.mk_pi(hsub_id, BinderInfo::Default, h_sub, r);
    let r = b.mk_pi(cv_id, BinderInfo::Default, cert_d, r);
    let r = b.mk_pi(bsub_id, BinderInfo::Default, ib_d.clone(), r);
    let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, r);
    let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

// NOTE (#3568/#2026-04-27): the old hypothesis-free
// `build_merge_sound_helper_constructive_proof` was removed here. The former
// builder emitted
//   `fun d B0 B1 B2 c1 c2 _hcover _hs1 _hs2 => True.intro`
// which only type-checked because `cert_sound` was a reducible
// `Declaration::Definition` with body `fun _ _ _ => True`. The current C007a
// proof keeps merge soundness explicit as a local hypothesis instead.

/// Build C007c proof term. Delegates to `restrict_refines_helper` Opaque.
pub(super) fn build_c007c_proof(c: &C007Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_of(&d);
    let cert_d = c.cert_of(&d);

    let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
    let (bsub_id, bsub) = b.fresh_local(ib_d.clone());
    let (cv_id, cv) = b.fresh_local(cert_d.clone());

    let h_sub = c.subset(&d, &bsub, &bnd);
    let h_sound = c.sound(&d, &bnd, &cv);

    let (hsub_id, hsub) = b.fresh_local(h_sub.clone());
    let (hs_id, hs) = b.fresh_local(h_sound.clone());

    // restrict_refines_helper d B B_sub c hsub hs
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(c.restrict_refines_helper.clone(), d.clone()),
                        bnd.clone(),
                    ),
                    bsub.clone(),
                ),
                cv.clone(),
            ),
            hsub,
        ),
        hs,
    );

    let e = b.mk_lam(hs_id, BinderInfo::Default, h_sound, body);
    let e = b.mk_lam(hsub_id, BinderInfo::Default, h_sub, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, cert_d, e);
    let e = b.mk_lam(bsub_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
