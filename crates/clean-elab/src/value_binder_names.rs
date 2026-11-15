// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `∀` binder names of a surface `def`'s value, for named arguments on a head
//! whose TYPE unfolds to that value (`h (a₁ := x)` with `h : Injective f`).
//! The table and its reason live in `clean_kernel::env::value_binder_names`;
//! the importer fills it for `.olean` definitions, this module for the ones
//! Clean elaborates itself.

use clean_kernel::{BinderInfo, Expr, ExprKind, Name};
use clean_parser::{SurfaceDecl, SurfaceExpr};

use crate::infer::{convert_binder_info, ElabResult};

/// The binders of a surface `∀`/`→` telescope: `∀ ⦃a₁ a₂⦄, p → q` gives
/// `[a₁ ⦃⦄, a₂ ⦃⦄, <anonymous> ()]`. An arrow's binder has no name a named
/// argument could spell, so it is recorded anonymous.
pub(crate) fn surface_forall_telescope(ty: &SurfaceExpr) -> Vec<(Name, BinderInfo)> {
    let mut out = Vec::new();
    let mut e = ty;
    loop {
        match e {
            SurfaceExpr::Paren(_, inner) => e = inner,
            SurfaceExpr::Pi(_, binders, body) => {
                out.extend(
                    binders
                        .iter()
                        .map(|b| (b.name.name().clone(), convert_binder_info(b.info))),
                );
                e = body;
            }
            SurfaceExpr::Arrow(_, _, codomain) => {
                out.push((Name::anon(), BinderInfo::Default));
                e = codomain;
            }
            _ => return out,
        }
    }
}

/// The binders of the `∀`/`→` telescope a surface value consists of, after
/// its leading `fun` binders: `fun f => ∀ ⦃a₁ a₂⦄, p → q` gives
/// `[a₁ ⦃⦄, a₂ ⦃⦄, <anonymous> ()]`.
fn surface_forall_binders(value: &SurfaceExpr) -> Vec<(Name, BinderInfo)> {
    let mut e = value;
    loop {
        match e {
            SurfaceExpr::Paren(_, inner) => e = inner,
            SurfaceExpr::Lambda(_, _, body) => e = body,
            _ => return surface_forall_telescope(e),
        }
    }
}

/// Record, for a surface `def` that was just elaborated, the names of the `∀`
/// binders its value consists of under its leading lambdas.
///
/// The lambda count is read off the KERNEL value (it also counts section
/// variables and auto-bound implicits, which the surface binder list does
/// not), and the surface telescope is recorded only when the kernel value
/// really has a `∀` of the same binder kind at every position. Anything else
/// (a value the elaborator wrapped or rewrote) records nothing, and a named
/// argument on such a head stays the loud refusal it was.
pub(crate) fn register_value_forall_binder_names(
    env: &mut clean_kernel::Environment,
    decl: &SurfaceDecl,
    result: &ElabResult,
) {
    let SurfaceDecl::Def {
        val: surface_value, ..
    } = decl
    else {
        return;
    };
    // The declaration itself, also when it lifted `where` / `let rec`
    // helpers (`ElabResult::primary_leaf`).
    let Some(ElabResult::Definition { name, val, .. }) = result.primary_leaf() else {
        return;
    };
    let binders = surface_forall_binders(surface_value);
    if binders.is_empty() {
        return;
    }
    let mut lambdas = 0;
    let mut cur: &Expr = val;
    while let ExprKind::Lam(_, _, body) = cur.kind() {
        lambdas += 1;
        cur = body;
    }
    for (_, info) in &binders {
        let ExprKind::Pi(bi, _, body) = cur.kind() else {
            return;
        };
        if bi.info != *info {
            return;
        }
        cur = body;
    }
    env.record_value_forall_binder_names(
        name.clone(),
        lambdas,
        binders.into_iter().map(|(n, _)| n).collect(),
    );
}
