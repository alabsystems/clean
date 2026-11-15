// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_parser::{SurfaceExpr, SurfaceName};

/// A recursive call's argument as the structural lowering reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ScopedArg {
    /// A bare identifier.
    Var(SurfaceName),
    /// An identifier in parentheses: the lowering reads it as the
    /// identifier, the decreasing-argument detector as a compound term.
    ParenVar(SurfaceName),
    /// Anything else — a literal, an application, a projection — which the
    /// lowering never resolves to an induction hypothesis.
    NonVar,
    /// Application of a potential function-valued recursive field.
    AppliedField(SurfaceName),
}

pub(super) fn scoped_arg(expr: &SurfaceExpr) -> ScopedArg {
    fn unparen(expr: &SurfaceExpr) -> &SurfaceExpr {
        match expr {
            SurfaceExpr::Paren(_, inner) => unparen(inner),
            other => other,
        }
    }
    match (expr, unparen(expr)) {
        (SurfaceExpr::Ident(_, name), _) => ScopedArg::Var(name.clone()),
        (_, SurfaceExpr::Ident(_, name)) => ScopedArg::ParenVar(name.clone()),
        (_, value) => applied_field_head(value)
            .map(ScopedArg::AppliedField)
            .unwrap_or(ScopedArg::NonVar),
    }
}

/// Surface head of a nonempty unnamed application whose head could be a
/// pattern-bound constructor field: an atomic source identifier. A
/// compiler-authored global head (`HAdd.hAdd` of `n + 1`, the anonymous
/// constructor of `⟨y, x⟩`), a qualified name and a relative constructor
/// (`.node`) never name a local, so such an application stays
/// [`ScopedArg::NonVar`] / `RecursiveArg::Other`. Its constructor-field
/// provenance and complete dependent type are checked by recursive lowering.
pub(super) fn applied_field_head(expr: &SurfaceExpr) -> Option<SurfaceName> {
    let mut head = expr;
    let mut applied = false;
    loop {
        match head {
            SurfaceExpr::Paren(_, inner) => head = inner,
            SurfaceExpr::App(_, function, args)
                if !args.is_empty() && args.iter().all(|a| a.name.is_none()) =>
            {
                applied = true;
                head = function;
            }
            SurfaceExpr::Ident(_, name)
                if applied
                    && name.component_text().is_some()
                    && !name.is_global_reference()
                    && !name.is_relative_constructor() =>
            {
                return Some(name.clone())
            }
            _ => return None,
        }
    }
}
