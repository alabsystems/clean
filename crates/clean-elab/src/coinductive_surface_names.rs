// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Structural identity and binder-aware identifier analysis for coinductive lowering.

use super::*;

/// Does `expr` mention `name` as a free identifier or structural name prefix?
/// Uses the same binder-scoped identifier census as the free-variable checks;
/// unanalysed expression shapes conservatively count as a possible occurrence.
pub(super) fn mentions(expr: &SurfaceExpr, name: &SurfaceName) -> bool {
    let mut bound: Vec<&SurfaceName> = Vec::new();
    let mut fvs: Vec<&SurfaceName> = Vec::new();
    if all_predicate_idents(expr, name, &mut bound, &mut fvs).is_err() {
        // A form this module cannot analyse is treated as possibly mentioning
        // the name; the caller rejects either way.
        return true;
    }
    fvs.iter().any(|id| id.has_prefix(name))
}

/// The parser represents a qualified reference as named projections. Fold
/// only that syntactic chain, preserving each typed component; ordinary
/// projections are NOT globally converted into constant references.
pub(super) fn reference_name(expr: &SurfaceExpr) -> Option<SurfaceName> {
    match strip_parens(expr) {
        SurfaceExpr::Ident(_, id) if !id.is_relative_constructor() => Some(id.clone()),
        SurfaceExpr::Proj(_, base, clean_parser::Projection::Named(field))
            if !field.is_relative_constructor() =>
        {
            Some(reference_name(base)?.append(field))
        }
        _ => None,
    }
}

pub(super) fn is_predicate_head(expr: &SurfaceExpr, name: &SurfaceName) -> bool {
    !name.is_relative_constructor() && reference_name(expr).as_ref() == Some(name)
}

/// Owner-aware census used by positivity and capture validation. The exact
/// qualified predicate projection contributes its complete identity, not
/// merely the first component. Other projections keep the existing local
/// base walk. A local prefix makes this interpretation ambiguous and refuses.
pub(super) fn all_predicate_idents<'a>(
    expr: &'a SurfaceExpr,
    predicate: &'a SurfaceName,
    bound: &mut Vec<&'a SurfaceName>,
    out: &mut Vec<&'a SurfaceName>,
) -> Result<(), &'static str> {
    collect_idents(expr, Some(predicate), bound, out)
}

/// Collect the FREE identifiers of `expr`, honouring lambda/Pi binder scope.
///
/// Returns `Err(label)` for a surface form this module refuses to analyse.
pub(super) fn all_idents<'a>(
    expr: &'a SurfaceExpr,
    bound: &mut Vec<&'a SurfaceName>,
    out: &mut Vec<&'a SurfaceName>,
) -> Result<(), &'static str> {
    collect_idents(expr, None, bound, out)
}

fn collect_idents<'a>(
    expr: &'a SurfaceExpr,
    predicate: Option<&'a SurfaceName>,
    bound: &mut Vec<&'a SurfaceName>,
    out: &mut Vec<&'a SurfaceName>,
) -> Result<(), &'static str> {
    if let Some(predicate) = predicate {
        if matches!(expr, SurfaceExpr::Proj(..)) && is_predicate_head(expr, predicate) {
            if bound.iter().any(|local| predicate.has_prefix(local)) {
                return Err("local shadows qualified predicate reference");
            }
            if !out.contains(&predicate) {
                out.push(predicate);
            }
            return Ok(());
        }
    }
    match expr {
        SurfaceExpr::Ident(_, id) => {
            if id.is_relative_constructor() {
                return Err("relative constructor selector");
            }
            if !bound.contains(&id) && !out.contains(&id) {
                out.push(id);
            }
        }
        SurfaceExpr::Lit(..) | SurfaceExpr::Universe(..) | SurfaceExpr::Hole(..) => {}
        SurfaceExpr::App(_, h, args) => {
            collect_idents(h, predicate, bound, out)?;
            for a in args {
                collect_idents(&a.expr, predicate, bound, out)?;
            }
        }
        SurfaceExpr::Arrow(_, a, b) => {
            collect_idents(a, predicate, bound, out)?;
            collect_idents(b, predicate, bound, out)?;
        }
        SurfaceExpr::Lambda(_, bs, body) | SurfaceExpr::Pi(_, bs, body) => {
            let depth = bound.len();
            for b in bs {
                if let Some(t) = &b.ty {
                    collect_idents(t, predicate, bound, out)?;
                }
                bound.push(&b.name);
            }
            collect_idents(body, predicate, bound, out)?;
            bound.truncate(depth);
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::UniverseInst(_, e, _) => collect_idents(e, predicate, bound, out)?,
        SurfaceExpr::Ascription(_, e, t) => {
            collect_idents(e, predicate, bound, out)?;
            collect_idents(t, predicate, bound, out)?;
        }
        other => return Err(variant_label(other)),
    }
    Ok(())
}

/// Is `id` already a constant of `env`? Used only to tell "constant" from
/// "stray free variable"; an unknown name rejects rather than being
/// auto-bound into the generated functor's signature.
pub(super) fn known_constant(env: &Environment, id: &SurfaceName) -> bool {
    !id.is_relative_constructor()
        && env
            .get_const(id.qualify_under(&SurfaceName::default()).name())
            .is_some()
}
