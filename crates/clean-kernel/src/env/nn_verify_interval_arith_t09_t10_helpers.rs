// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper constructors shared by the T09/T10 proof module.
//!
//! Extracted so the proof/registration module stays under the 500-line
//! cap. These are thin wrappers over `Expr::const_` / `Expr::apps` /
//! `Expr::proj` to keep the proof builder readable.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

pub(super) fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

pub(super) fn rat() -> Expr {
    Expr::const_(Name::from_string("Rat"), vec![])
}

pub(super) fn fin_of(d: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), d.clone())
}

pub(super) fn interval_bounds_of(d: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        d.clone(),
    )
}

pub(super) fn nnvec_of(d: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
        d.clone(),
    )
}

pub(super) fn contains_app(d: &Expr, bounds: &Expr, x: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("NNVerify.IntervalBounds.contains"),
            vec![],
        ),
        [d.clone(), bounds.clone(), x.clone()],
    )
}

pub(super) fn lower_proj(bounds: &Expr) -> Expr {
    Expr::proj(
        Name::from_string("NNVerify.IntervalBounds"),
        0,
        bounds.clone(),
    )
}

pub(super) fn upper_proj(bounds: &Expr) -> Expr {
    Expr::proj(
        Name::from_string("NNVerify.IntervalBounds"),
        1,
        bounds.clone(),
    )
}

pub(super) fn lower_at(bounds: &Expr, i: Expr) -> Expr {
    Expr::app(lower_proj(bounds), i)
}

pub(super) fn upper_at(bounds: &Expr, i: Expr) -> Expr {
    Expr::app(upper_proj(bounds), i)
}

pub(super) fn rat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        [
            rat(),
            Expr::const_(Name::from_string("instLERat"), vec![]),
            lhs,
            rhs,
        ],
    )
}

pub(super) fn rat_max_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.max"), vec![]), [a, b])
}

pub(super) fn rat_min_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.min"), vec![]), [a, b])
}

pub(super) fn and_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}

pub(super) fn and_intro_app(a_prop: Expr, b_prop: Expr, ha: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [a_prop, b_prop, ha, hb],
    )
}

pub(super) fn and_left_app(a_prop: Expr, b_prop: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [a_prop, b_prop, h],
    )
}

pub(super) fn and_right_app(a_prop: Expr, b_prop: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [a_prop, b_prop, h],
    )
}

pub(super) fn rat_le_trans_app(a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [a, b, c, hab, hbc],
    )
}

pub(super) fn rat_max_le_app(a: Expr, b: Expr, c: Expr, hac: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.max_le"), vec![]),
        [a, b, c, hac, hbc],
    )
}

pub(super) fn rat_le_min_app(a: Expr, b: Expr, c: Expr, hca: Expr, hcb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_min"), vec![]),
        [a, b, c, hca, hcb],
    )
}

pub(super) fn rat_min_le_left_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.min_le_left"), vec![]),
        [a, b],
    )
}

pub(super) fn rat_le_max_left_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_max_left"), vec![]),
        [a, b],
    )
}

pub(super) fn register_axiom_if_missing(
    env: &mut Environment,
    name: &str,
    type_: Expr,
) -> Result<(), EnvError> {
    let name = Name::from_string(name);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Axiom {
        name,
        level_params: vec![],
        type_,
    })
}
