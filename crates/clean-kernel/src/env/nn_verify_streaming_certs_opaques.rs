// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C007 Opaque foundation registrations.
//!
//! Contains `register_c007_foundation_opaques`, which registers the 7
//! C007-specific foundation types/operations plus `Nat.add` as
//! `Declaration::Opaque`. `instLENat` is now a no-op here since `init_le()`
//! provides it as a proper Definition before this function is called.
//!
//! Split from `nn_verify_streaming_certs.rs` for file-size compliance.
//! Part of #3312, #3150.

use super::nn_verify_streaming_certs_defs::C007Consts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Register foundational Opaque definitions for C007 certificate types and operations.
///
/// These were formerly axioms; now Opaque with well-typed placeholder values.
/// The kernel verifies typing but does not reduce opaque definitions.
/// Registered directly to avoid deep init chains (#3304).
#[cfg(any(test, feature = "math-overlays"))]
pub(super) fn register_c007_foundation_opaques(
    env: &mut Environment,
    c: &C007Consts,
) -> Result<(), EnvError> {
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    register_bab_cert(env, c)?;
    register_cert_sound(env, c)?;
    register_merge_cert(env, c)?;
    register_restrict_cert(env, c)?;
    register_cert_cost(env, c, &nat_zero)?;
    register_delta_cost(env, c, &nat_zero)?;
    register_disjoint_cover(env, c)?;
    register_inst_le_nat(env, c)?;
    register_nat_add(env, c)?;

    Ok(())
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_bab_cert(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.BaBCert"))
        .is_some()
    {
        return Ok(());
    }
    let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let body = c.ib_of(&d);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), body);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.BaBCert"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_cert_sound(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.cert_sound"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let ib_d = c.ib_of(&d);
        let cert_d = c.cert_of(&d);
        let (bnd_id, _) = b.fresh_local(ib_d.clone());
        let (cv_id, _) = b.fresh_local(cert_d.clone());
        let r = b.mk_pi(cv_id, BinderInfo::Default, cert_d, c.prop.clone());
        let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, r);
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let ib_d = c.ib_of(&d);
        let cert_d = c.cert_of(&d);
        let (bnd_id, _) = b.fresh_local(ib_d.clone());
        let (cv_id, _) = b.fresh_local(cert_d.clone());
        let e = b.mk_lam(cv_id, BinderInfo::Default, cert_d, true_const);
        let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_d, e);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    // Reverted from reducible Definition back to Opaque (#3568 demasquerade).
    //
    // Rationale (#3568): the reducible-Definition promotion from #3461
    // was a MASQUERADE enabler. With `cert_sound = fun _ _ _ => True`
    // and `is_reducible: true`, any claim `cert_sound d B c` delta-
    // reduced to `True`, letting `merge_sound_helper` close via a
    // vacuous `True.intro` proof. Per
    // `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rule M1+M4, this
    // is an alias-collapse masquerade. Flipping `cert_sound` back to
    // `Declaration::Opaque` closes that reduction path so no future
    // `cert_sound` proposition can be discharged by `True.intro`.
    //
    // The stored body (`fun _ _ _ => True`) is kept on the Opaque so
    // typing still resolves through the placeholder; the kernel simply
    // does not unfold Opaques during `def_eq`, which is exactly the
    // property we need. A faithful `cert_sound` predicate (Branch B)
    // remains future work.
    //
    // Part of #3568.
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.cert_sound"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_merge_cert(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.merge_cert"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (c1_id, _) = b.fresh_local(cert_d.clone());
        let (c2_id, _) = b.fresh_local(cert_d.clone());
        let r = b.mk_pi(c2_id, BinderInfo::Default, cert_d.clone(), cert_d.clone());
        let r = b.mk_pi(c1_id, BinderInfo::Default, cert_d, r);
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (c1_id, c1v) = b.fresh_local(cert_d.clone());
        let (c2_id, _) = b.fresh_local(cert_d.clone());
        let e = b.mk_lam(c2_id, BinderInfo::Default, cert_d.clone(), c1v);
        let e = b.mk_lam(c1_id, BinderInfo::Default, cert_d, e);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.merge_cert"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_restrict_cert(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.restrict_cert"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let ib_d = c.ib_of(&d);
        let (cv_id, _) = b.fresh_local(cert_d.clone());
        let (bsub_id, _) = b.fresh_local(ib_d.clone());
        let r = b.mk_pi(bsub_id, BinderInfo::Default, ib_d, cert_d.clone());
        let r = b.mk_pi(cv_id, BinderInfo::Default, cert_d, r);
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let ib_d = c.ib_of(&d);
        let (cv_id, cvv) = b.fresh_local(cert_d.clone());
        let (bsub_id, _) = b.fresh_local(ib_d.clone());
        let e = b.mk_lam(bsub_id, BinderInfo::Default, ib_d, cvv);
        let e = b.mk_lam(cv_id, BinderInfo::Default, cert_d, e);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.restrict_cert"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_cert_cost(
    env: &mut Environment,
    c: &C007Consts,
    nat_zero: &Expr,
) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.cert_cost"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (cv_id, _) = b.fresh_local(cert_d.clone());
        let r = b.mk_pi(cv_id, BinderInfo::Default, cert_d, c.nat.clone());
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (cv_id, _) = b.fresh_local(cert_d.clone());
        let e = b.mk_lam(cv_id, BinderInfo::Default, cert_d, nat_zero.clone());
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.cert_cost"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_delta_cost(
    env: &mut Environment,
    c: &C007Consts,
    nat_zero: &Expr,
) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.delta_cost"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (c1_id, _) = b.fresh_local(cert_d.clone());
        let (c2_id, _) = b.fresh_local(cert_d.clone());
        let r = b.mk_pi(c2_id, BinderInfo::Default, cert_d.clone(), c.nat.clone());
        let r = b.mk_pi(c1_id, BinderInfo::Default, cert_d, r);
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let cert_d = c.cert_of(&d);
        let (c1_id, _) = b.fresh_local(cert_d.clone());
        let (c2_id, _) = b.fresh_local(cert_d.clone());
        let e = b.mk_lam(c2_id, BinderInfo::Default, cert_d.clone(), nat_zero.clone());
        let e = b.mk_lam(c1_id, BinderInfo::Default, cert_d, e);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.delta_cost"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_disjoint_cover(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("NNVerify.C007.disjoint_cover"))
        .is_some()
    {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let ib_d = c.ib_of(&d);
        let (b1_id, _) = b.fresh_local(ib_d.clone());
        let (b2_id, _) = b.fresh_local(ib_d.clone());
        let (b0_id, _) = b.fresh_local(ib_d.clone());
        let r = b.mk_pi(b0_id, BinderInfo::Default, ib_d.clone(), c.prop.clone());
        let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), r);
        let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d, r);
        let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        let ib_d = c.ib_of(&d);
        let (b1_id, _) = b.fresh_local(ib_d.clone());
        let (b2_id, _) = b.fresh_local(ib_d.clone());
        let (b0_id, _) = b.fresh_local(ib_d.clone());
        let e = b.mk_lam(b0_id, BinderInfo::Default, ib_d.clone(), true_const);
        let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), e);
        let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d, e);
        let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("NNVerify.C007.disjoint_cover"),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_inst_le_nat(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string("instLENat")).is_some() {
        return Ok(());
    }
    let le_type = Expr::const_(Name::from_string("LE"), vec![Level::zero()]);
    let ty = Expr::app(le_type, c.nat.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("instLENat"),
        level_params: vec![],
        type_: ty,
    })
}

#[cfg(any(test, feature = "math-overlays"))]
fn register_nat_add(env: &mut Environment, c: &C007Consts) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string("Nat.add")).is_some() {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, _) = b.fresh_local(c.nat.clone());
        let (bv_id, _) = b.fresh_local(c.nat.clone());
        let r = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
        let r = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, _) = b.fresh_local(c.nat.clone());
        let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), a);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("Nat.add"),
        level_params: vec![],
        type_: ty,
        value,
    })
}
