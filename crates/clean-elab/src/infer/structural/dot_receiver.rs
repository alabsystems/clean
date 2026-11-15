// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Method-dot self-calls (`recv.f a…`) as the recursion detector reads them.
//!
//! Lean 4.8.0 elaborates `recv.f a₁ … aₙ` by inserting the receiver at the
//! first explicit parameter of `f` whose type is `f`'s namespace type
//! (`addLValArg`, `src/Lean/Elab/App.lean`). The detector (`detect.rs`) records
//! such a call as ONE recursive call with the receiver at that position when
//! the caller knows it (`RecursionNameParts::receiver_pos`), so the decreasing
//! argument it picks is the one the elaborated call actually passes.

use clean_parser::{Projection, SurfaceExpr, SurfaceName};

use super::detect::matches_full;
use super::{normalize_root_prefix, qualified_name_from_proj, RecursionNameParts};

/// The receiver of a method-dot self-call head `recv.f`: a plain variable
/// projected by the function's short name, not shadowed, and not the
/// namespace-qualified spelling of the function itself (that is a constant
/// reference, recorded by the `App` arm as an ordinary call).
pub(super) fn method_dot_receiver<'e>(
    func_name: &RecursionNameParts,
    expr: &'e SurfaceExpr,
    shadowed_short: bool,
    shadowed_base: bool,
) -> Option<&'e SurfaceName> {
    let SurfaceExpr::Proj(_, base, Projection::Named(field)) = expr else {
        return None;
    };
    let SurfaceExpr::Ident(_, recv) = base.as_ref() else {
        return None;
    };
    (!shadowed_base
        && !shadowed_short
        && field == func_name.short()
        && qualified_name_from_proj(expr)
            .is_none_or(|name| !matches_full(&normalize_root_prefix(&name), func_name)))
    .then_some(recv)
}

/// Where an applied method-dot self-call `recv.f a₁ … aₙ` puts its receiver,
/// when the caller supplied the definition's receiver position and Lean fills
/// that position positionally (`addLValArg` inserts at an index `≤ n`; past
/// it the receiver becomes a named argument, which this reading leaves to the
/// legacy path).
pub(super) fn placed_receiver<'e>(
    func_name: &RecursionNameParts,
    head: &'e SurfaceExpr,
    supplied: usize,
    shadowed_short: bool,
    shadowed_base: bool,
) -> Option<(usize, &'e SurfaceName)> {
    let pos = func_name.receiver_pos().filter(|&pos| pos <= supplied)?;
    method_dot_receiver(func_name, head, shadowed_short, shadowed_base).map(|recv| (pos, recv))
}
