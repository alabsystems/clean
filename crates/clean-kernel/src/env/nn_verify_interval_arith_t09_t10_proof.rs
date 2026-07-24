// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat min/max ordering axioms and constructive T09/T10 interval arithmetic proofs.
//!
//! Registers six small Rat ordering axioms for `Rat.min` / `Rat.max`, then
//! uses them to construct kernel-checkable proofs for:
//!
//! - `NNVerify.IntervalArith.interval_intersection_sound`
//! - `NNVerify.IntervalArith.interval_union_sound`

use super::nn_verify_interval_arith_t09_t10_helpers::{
    and_app, and_intro_app, and_left_app, and_right_app, contains_app, fin_of, interval_bounds_of,
    lower_at, nat, nnvec_of, rat, rat_le, rat_le_max_left_app, rat_le_min_app, rat_le_trans_app,
    rat_max_app, rat_max_le_app, rat_min_app, rat_min_le_left_app, register_axiom_if_missing,
    upper_at,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

fn build_rat_le_max_left_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let body = rat_le(a.clone(), rat_max_app(a, bv.clone()));
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_rat_le_max_right_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let body = rat_le(bv.clone(), rat_max_app(a, bv));
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_rat_min_le_left_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let body = rat_le(rat_min_app(a.clone(), bv), a);
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_rat_min_le_right_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let body = rat_le(rat_min_app(a, bv.clone()), bv);
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_rat_max_le_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let (c_id, c) = b.fresh_local(rat_ty.clone());

    let h1_ty = rat_le(a.clone(), c.clone());
    let h2_ty = rat_le(bv.clone(), c.clone());
    let (h1_id, _) = b.fresh_local(h1_ty.clone());
    let (h2_id, _) = b.fresh_local(h2_ty.clone());

    let concl = rat_le(rat_max_app(a, bv), c);
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(c_id, BinderInfo::Default, rat_ty.clone(), e);
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_rat_le_min_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let rat_ty = rat();
    let (a_id, a) = b.fresh_local(rat_ty.clone());
    let (b_id, bv) = b.fresh_local(rat_ty.clone());
    let (c_id, c) = b.fresh_local(rat_ty.clone());

    let h1_ty = rat_le(c.clone(), a.clone());
    let h2_ty = rat_le(c.clone(), bv.clone());
    let (h1_id, _) = b.fresh_local(h1_ty.clone());
    let (h2_id, _) = b.fresh_local(h2_ty.clone());

    let concl = rat_le(c, rat_min_app(a, bv));
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(c_id, BinderInfo::Default, rat_ty.clone(), e);
    let e = b.mk_pi(b_id, BinderInfo::Default, rat_ty.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, rat_ty, e);
    b.finish(e)
}

fn build_interval_intersection_sound_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(nat());
    let ib_d = interval_bounds_of(&d);
    let vec_d = nnvec_of(&d);

    let (a_id, a) = b.fresh_local(ib_d.clone());
    let (b_id, bv) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(vec_d.clone());

    let hx_a_ty = contains_app(&d, &a, &x);
    let hx_b_ty = contains_app(&d, &bv, &x);
    let (hx_a_id, _) = b.fresh_local(hx_a_ty.clone());
    let (hx_b_id, _) = b.fresh_local(hx_b_ty.clone());

    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_d = fin_of(&d);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        let a_lo_i = lower_at(&a, i.clone());
        let b_lo_i = lower_at(&bv, i.clone());
        let a_hi_i = upper_at(&a, i.clone());
        let b_hi_i = upper_at(&bv, i.clone());
        let x_i = Expr::app(x.clone(), i.clone());

        let lower_prop = rat_le(rat_max_app(a_lo_i, b_lo_i), x_i.clone());
        let upper_prop = rat_le(x_i, rat_min_app(a_hi_i, b_hi_i));
        let body = and_app(lower_prop, upper_prop);

        let e = ch.mk_pi(i_id, BinderInfo::Default, fin_d, body);
        ch.finish_child(e)
    };

    let e = b.mk_pi(hx_b_id, BinderInfo::Default, hx_b_ty, body);
    let e = b.mk_pi(hx_a_id, BinderInfo::Default, hx_a_ty, e);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_pi(b_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Implicit, nat(), e);
    b.finish(e)
}

fn build_interval_intersection_sound_proof() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(nat());
    let ib_d = interval_bounds_of(&d);
    let vec_d = nnvec_of(&d);

    let (a_id, a) = b.fresh_local(ib_d.clone());
    let (b_id, bv) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(vec_d.clone());

    let hx_a_ty = contains_app(&d, &a, &x);
    let hx_b_ty = contains_app(&d, &bv, &x);
    let (hx_a_id, hx_a) = b.fresh_local(hx_a_ty.clone());
    let (hx_b_id, hx_b) = b.fresh_local(hx_b_ty.clone());

    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_d = fin_of(&d);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        let a_lo_i = lower_at(&a, i.clone());
        let b_lo_i = lower_at(&bv, i.clone());
        let a_hi_i = upper_at(&a, i.clone());
        let b_hi_i = upper_at(&bv, i.clone());
        let x_i = Expr::app(x.clone(), i.clone());

        let h_a_i = Expr::app(hx_a.clone(), i.clone());
        let h_a_lo_prop = rat_le(a_lo_i.clone(), x_i.clone());
        let h_a_hi_prop = rat_le(x_i.clone(), a_hi_i.clone());
        let h_a_lo = and_left_app(h_a_lo_prop.clone(), h_a_hi_prop.clone(), h_a_i.clone());
        let h_a_hi = and_right_app(h_a_lo_prop, h_a_hi_prop, h_a_i);

        let h_b_i = Expr::app(hx_b.clone(), i.clone());
        let h_b_lo_prop = rat_le(b_lo_i.clone(), x_i.clone());
        let h_b_hi_prop = rat_le(x_i.clone(), b_hi_i.clone());
        let h_b_lo = and_left_app(h_b_lo_prop.clone(), h_b_hi_prop.clone(), h_b_i.clone());
        let h_b_hi = and_right_app(h_b_lo_prop, h_b_hi_prop, h_b_i);

        let lower_prop = rat_le(rat_max_app(a_lo_i.clone(), b_lo_i.clone()), x_i.clone());
        let upper_prop = rat_le(x_i.clone(), rat_min_app(a_hi_i.clone(), b_hi_i.clone()));

        let lower_goal = rat_max_le_app(a_lo_i, b_lo_i, x_i.clone(), h_a_lo, h_b_lo);
        let upper_goal = rat_le_min_app(a_hi_i, b_hi_i, x_i, h_a_hi, h_b_hi);

        let proof = and_intro_app(lower_prop, upper_prop, lower_goal, upper_goal);
        let e = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(e)
    };

    let e = b.mk_lam(hx_b_id, BinderInfo::Default, hx_b_ty, body);
    let e = b.mk_lam(hx_a_id, BinderInfo::Default, hx_a_ty, e);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_lam(b_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, nat(), e);
    b.finish(e)
}

fn build_interval_union_sound_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(nat());
    let ib_d = interval_bounds_of(&d);
    let vec_d = nnvec_of(&d);

    let (a_id, a) = b.fresh_local(ib_d.clone());
    let (b_id, bv) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(vec_d.clone());

    let hx_a_ty = contains_app(&d, &a, &x);
    let (hx_a_id, _) = b.fresh_local(hx_a_ty.clone());

    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_d = fin_of(&d);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        let a_lo_i = lower_at(&a, i.clone());
        let b_lo_i = lower_at(&bv, i.clone());
        let a_hi_i = upper_at(&a, i.clone());
        let b_hi_i = upper_at(&bv, i.clone());
        let x_i = Expr::app(x.clone(), i.clone());

        let lower_prop = rat_le(rat_min_app(a_lo_i, b_lo_i), x_i.clone());
        let upper_prop = rat_le(x_i, rat_max_app(a_hi_i, b_hi_i));
        let body = and_app(lower_prop, upper_prop);

        let e = ch.mk_pi(i_id, BinderInfo::Default, fin_d, body);
        ch.finish_child(e)
    };

    let e = b.mk_pi(hx_a_id, BinderInfo::Default, hx_a_ty, body);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_pi(b_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Implicit, nat(), e);
    b.finish(e)
}

fn build_interval_union_sound_proof() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(nat());
    let ib_d = interval_bounds_of(&d);
    let vec_d = nnvec_of(&d);

    let (a_id, a) = b.fresh_local(ib_d.clone());
    let (b_id, bv) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(vec_d.clone());

    let hx_a_ty = contains_app(&d, &a, &x);
    let (hx_a_id, hx_a) = b.fresh_local(hx_a_ty.clone());

    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_d = fin_of(&d);
        let (i_id, i) = ch.fresh_local(fin_d.clone());

        let a_lo_i = lower_at(&a, i.clone());
        let b_lo_i = lower_at(&bv, i.clone());
        let a_hi_i = upper_at(&a, i.clone());
        let b_hi_i = upper_at(&bv, i.clone());
        let x_i = Expr::app(x.clone(), i.clone());

        let h_a_i = Expr::app(hx_a.clone(), i.clone());
        let h_a_lo_prop = rat_le(a_lo_i.clone(), x_i.clone());
        let h_a_hi_prop = rat_le(x_i.clone(), a_hi_i.clone());
        let h_a_lo = and_left_app(h_a_lo_prop.clone(), h_a_hi_prop.clone(), h_a_i.clone());
        let h_a_hi = and_right_app(h_a_lo_prop, h_a_hi_prop, h_a_i);

        let min_le_a_lo = rat_min_le_left_app(a_lo_i.clone(), b_lo_i.clone());
        let a_hi_le_max = rat_le_max_left_app(a_hi_i.clone(), b_hi_i.clone());

        let lower_prop = rat_le(rat_min_app(a_lo_i.clone(), b_lo_i), x_i.clone());
        let upper_prop = rat_le(x_i.clone(), rat_max_app(a_hi_i.clone(), b_hi_i));

        let lower_goal = rat_le_trans_app(
            rat_min_app(a_lo_i.clone(), lower_at(&bv, i.clone())),
            a_lo_i,
            x_i.clone(),
            min_le_a_lo,
            h_a_lo,
        );
        let upper_goal = rat_le_trans_app(
            x_i,
            a_hi_i,
            rat_max_app(upper_at(&a, i.clone()), upper_at(&bv, i)),
            h_a_hi,
            a_hi_le_max,
        );

        let proof = and_intro_app(lower_prop, upper_prop, lower_goal, upper_goal);
        let e = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(e)
    };

    let e = b.mk_lam(hx_a_id, BinderInfo::Default, hx_a_ty, body);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
    let e = b.mk_lam(b_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, nat(), e);
    b.finish(e)
}

pub(crate) fn register_rat_min_max_lemmas(env: &mut Environment) -> Result<(), EnvError> {
    if env
        .get_const(&Name::from_string("Rat.le_max_left"))
        .is_some()
        && env
            .get_const(&Name::from_string("Rat.le_max_right"))
            .is_some()
        && env
            .get_const(&Name::from_string("Rat.min_le_left"))
            .is_some()
        && env
            .get_const(&Name::from_string("Rat.min_le_right"))
            .is_some()
        && env.get_const(&Name::from_string("Rat.max_le")).is_some()
        && env.get_const(&Name::from_string("Rat.le_min")).is_some()
    {
        return Ok(());
    }

    // WS-B: register the constructive quotient-carrier lattice lemmas
    // (`Rat.le_max_left` / `le_max_right` / `min_le_left` / `min_le_right` /
    // `max_le` / `le_min`) as kernel-checked Theorems FIRST. Each
    // `register_axiom_if_missing` below already guards on `get_const`, so once
    // the Theorems are present the opaque axioms are never registered. See
    // `algebra_rat_minmax_proof.rs`.
    env.register_rat_minmax_proofs()?;

    register_axiom_if_missing(env, "Rat.le_max_left", build_rat_le_max_left_type())?;
    register_axiom_if_missing(env, "Rat.le_max_right", build_rat_le_max_right_type())?;
    register_axiom_if_missing(env, "Rat.min_le_left", build_rat_min_le_left_type())?;
    register_axiom_if_missing(env, "Rat.min_le_right", build_rat_min_le_right_type())?;
    register_axiom_if_missing(env, "Rat.max_le", build_rat_max_le_type())?;
    register_axiom_if_missing(env, "Rat.le_min", build_rat_le_min_type())?;
    Ok(())
}

pub(super) fn register_interval_intersection_sound(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string("NNVerify.IntervalArith.interval_intersection_sound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    register_rat_min_max_lemmas(env)?;

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_: build_interval_intersection_sound_type(),
        value: build_interval_intersection_sound_proof(),
    })
}

pub(super) fn register_interval_union_sound(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string("NNVerify.IntervalArith.interval_union_sound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    register_rat_min_max_lemmas(env)?;

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_: build_interval_union_sound_type(),
        value: build_interval_union_sound_proof(),
    })
}
