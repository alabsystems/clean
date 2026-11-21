// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Over-applied branch forms inside a recursive function's arm (X4, R1.6).
//!
//! A `match` that generalises over an induction hypothesis elaborates to a
//! case analysis whose motive returns a function, applied past its arity to
//! the IH (and anything else it generalises): `(casesOn x alt₀ alt₁) ih`. The
//! exact-arity recognizers of `lower::lower_code` decline that spine, so the
//! case analysis became an opaque call and the IH call inside each
//! alternative never reached tail position.
//!
//! This module applies the commuting conversion
//! `(case x of alts) e = case x of (alt e)`: each extra argument is bound
//! once, before the case analysis (where LCNF evaluates it anyway), and each
//! alternative `fun fields => body` becomes `fun fields => body e`, beta
//! reduced. No work is duplicated: an extra is a variable by the time it is
//! pushed into the alternatives. It fires only when an extra argument IS an
//! IH placeholder (`rec_ih`), the shape this conversion exists for; every
//! other over-applied spine keeps its lowering.

use super::lower::{collect_app_args, expr_to_arg};
use super::rec_ih;
use super::LcnfContext;
use crate::error::CompilerError;
use crate::lcnf::Arg;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};

/// The layout of a recognized case-analysis head: its exact arity and, per
/// alternative, the argument index and the number of fields it binds.
struct Layout {
    arity: usize,
    alts: Vec<(usize, usize)>,
}

fn layout(env: &Environment, head: &Name) -> Option<Layout> {
    let fixed = |arity, alts: &[(usize, usize)]| {
        Some(Layout {
            arity,
            alts: alts.to_vec(),
        })
    };
    match head.to_string().as_str() {
        // ite α c inst t e / dite α c inst (fun h => t) (fun h => e)
        "ite" => return fixed(5, &[(3, 0), (4, 0)]),
        "dite" => return fixed(5, &[(3, 1), (4, 1)]),
        // cond α c t e
        "cond" => return fixed(4, &[(2, 0), (3, 0)]),
        // Bool.casesOn motive c f t
        "Bool.casesOn" => return fixed(4, &[(2, 0), (3, 0)]),
        // Nat.casesOn motive n zero (fun pred => succ)
        "Nat.casesOn" => return fixed(4, &[(2, 0), (3, 1)]),
        _ => {}
    }
    if head.last_component().as_deref() != Some("casesOn") {
        return None;
    }
    let ind_name = Name::from_string(head.to_string().rsplit_once('.')?.0);
    let ind = env.get_inductive(&ind_name)?;
    // The generic `casesOn` lowering's scope: non-indexed, not mutual.
    if ind.num_indices > 0 || ind.all_names.len() > 1 {
        return None;
    }
    let params = ind.num_params as usize;
    let mut alts = Vec::with_capacity(ind.constructor_names.len());
    for (i, ctor) in ind.constructor_names.iter().enumerate() {
        let fields = env.get_constructor(ctor)?.num_fields as usize;
        alts.push((params + 2 + i, fields));
    }
    Some(Layout {
        arity: params + 2 + alts.len(),
        alts,
    })
}

/// `e` applied to `args`, head beta reduced.
fn beta_apps(e: &Expr, args: &[Expr]) -> Expr {
    let mut cur = e.strip_mdata().clone();
    let mut rest = args;
    while let (ExprKind::Lam(_, _, body), Some((first, tail))) = (cur.kind(), rest.split_first()) {
        cur = body.instantiate(first).strip_mdata().clone();
        rest = tail;
    }
    Expr::apps(cur, rest.to_vec())
}

/// `fun x₁ … xₙ => body e…` for an alternative `fun x₁ … xₙ => body`, or
/// `None` when it does not bind its `n` fields syntactically.
fn push_into_alt(alt: &Expr, fields: usize, extras: &[Expr]) -> Option<Expr> {
    if fields == 0 {
        return Some(beta_apps(alt, extras));
    }
    let ExprKind::Lam(info, ty, body) = alt.strip_mdata().kind() else {
        return None;
    };
    let inner = push_into_alt(body, fields - 1, extras)?;
    Some(Expr::lam(*info, ty.as_ref().clone(), inner))
}

/// The IH placeholder `e` names, if it names one.
fn ih_ref(ctx: &LcnfContext<'_>, e: &Expr) -> Option<FVarId> {
    let fvar = match e.strip_mdata().kind() {
        ExprKind::FVar(id) => Some(*id),
        ExprKind::BVar(idx) => ctx.lookup_bvar(*idx),
        _ => None,
    }?;
    rec_ih::is_ih(ctx, fvar).then_some(fvar)
}

/// The exact-arity case analysis `expr` commutes to, with its extra
/// arguments bound in the current scope and pushed into every alternative,
/// or `None` when `expr` is not an over-applied case analysis passing an IH.
pub(super) fn commute_over_applied_cases(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
) -> Result<Option<Expr>, CompilerError> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.strip_mdata().kind() else {
        return Ok(None);
    };
    let Some(layout) = layout(ctx.env, name) else {
        return Ok(None);
    };
    if args.len() <= layout.arity {
        return Ok(None);
    }
    let (core, extras) = args.split_at(layout.arity);
    if !extras.iter().any(|e| ih_ref(ctx, e).is_some()) {
        return Ok(None);
    }
    // Every alternative must bind its fields syntactically (checked before
    // anything is bound, so a decline leaves the scope untouched). The
    // placeholder stands for itself here, so the check uses a stand-in.
    let probe = vec![Expr::const_str("_"); extras.len()];
    if layout
        .alts
        .iter()
        .any(|(idx, fields)| push_into_alt(core[*idx], *fields, &probe).is_none())
    {
        return Ok(None);
    }
    // Bind each extra once: an IH placeholder passes through as itself (it is
    // resolved where the alternative applies it), anything else becomes a
    // variable (or, erased, the erased stand-in).
    let mut bound: Vec<Expr> = Vec::with_capacity(extras.len());
    for extra in extras {
        if let Some(ph) = ih_ref(ctx, extra) {
            bound.push(Expr::fvar(ph));
            continue;
        }
        bound.push(match expr_to_arg(ctx, extra)? {
            Arg::FVar(id) => Expr::fvar(id),
            Arg::Erased | Arg::Type(_) | Arg::Index(_) => {
                let erased = ctx.add_let(
                    Name::anon(),
                    Expr::const_str("_"),
                    crate::lcnf::LetValue::Erased,
                );
                Expr::fvar(erased)
            }
        });
    }
    let mut new_args: Vec<Expr> = core.iter().map(|a| (*a).clone()).collect();
    for (idx, fields) in &layout.alts {
        new_args[*idx] = push_into_alt(core[*idx], *fields, &bound).ok_or_else(|| {
            CompilerError::InvalidExpr("an alternative lost its field binders".into())
        })?;
    }
    Ok(Some(Expr::apps(head.clone(), new_args)))
}
