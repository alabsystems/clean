// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Analysis utilities for the L5IR inlining pass.
//!
//! Provides size estimation, call counting, recursion detection, and
//! max-VarId computation used by the inliner to make decisions and
//! avoid variable collisions.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr};
use clean_kernel::Name;
use std::collections::HashMap;

// -----------------------------------------------------------------------
// Size estimation
// -----------------------------------------------------------------------

/// Count IR nodes in a function body for size-based inline decisions.
///
/// Each `VDecl`, `JDecl`, `Inc`, `Dec`, `Set`, `SetTag`, `USet`, `SSet`,
/// `Case`, `Jmp`, `Ret`, and `Unreachable` counts as one node.
/// Case alternatives add their body sizes.
pub(crate) fn estimate_size(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. } => 1 + estimate_size(rest),
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => 1 + estimate_size(jp_body) + estimate_size(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + estimate_size(rest),
        IRBody::Case { alts, default, .. } => {
            let alt_size: usize = alts.iter().map(|a| estimate_size(&a.body)).sum();
            let def_size = default.as_ref().map_or(0, |d| estimate_size(d));
            1 + alt_size + def_size
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

// -----------------------------------------------------------------------
// Call counting
// -----------------------------------------------------------------------

/// Count how many times each function name is called across all declarations.
pub(crate) fn compute_call_counts(decls: &[IRDecl]) -> HashMap<Name, usize> {
    let mut counts: HashMap<Name, usize> = HashMap::new();
    for decl in decls {
        count_calls_in_body(&decl.body, &mut counts);
    }
    counts
}

fn count_calls_in_body(body: &IRBody, counts: &mut HashMap<Name, usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            count_calls_in_expr(value, counts);
            count_calls_in_body(rest, counts);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            count_calls_in_body(jp_body, counts);
            count_calls_in_body(rest, counts);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            count_calls_in_body(rest, counts);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                count_calls_in_body(&alt.body, counts);
            }
            if let Some(d) = default {
                count_calls_in_body(d, counts);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn count_calls_in_expr(expr: &IRExpr, counts: &mut HashMap<Name, usize>) {
    match expr {
        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
            *counts.entry(fn_id.0.clone()).or_insert(0) += 1;
        }
        _ => {}
    }
}

// -----------------------------------------------------------------------
// Recursion detection
// -----------------------------------------------------------------------

/// Check whether `decl` directly calls itself (direct recursion).
pub(crate) fn is_recursive(decl: &IRDecl) -> bool {
    body_references_name(&decl.body, &decl.name)
}

/// Check whether `body` contains any call to the given `name`.
pub(crate) fn body_references_name(body: &IRBody, name: &Name) -> bool {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            expr_references_name(value, name) || body_references_name(rest, name)
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => body_references_name(jp_body, name) || body_references_name(rest, name),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => body_references_name(rest, name),
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|a| body_references_name(&a.body, name))
                || default
                    .as_ref()
                    .is_some_and(|d| body_references_name(d, name))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}

fn expr_references_name(expr: &IRExpr, name: &Name) -> bool {
    match expr {
        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => fn_id.0 == *name,
        _ => false,
    }
}

// -----------------------------------------------------------------------
// Max VarId computation
// -----------------------------------------------------------------------

/// Find the maximum `VarId` used anywhere in a body.
pub(crate) fn max_var_id(body: &IRBody) -> u32 {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            let expr_max = max_var_id_expr(value);
            var.0.max(expr_max).max(max_var_id(rest))
        }
        IRBody::JDecl {
            params,
            body: jp_body,
            rest,
            ..
        } => {
            let param_max = params.iter().map(|(v, _)| v.0).max().unwrap_or(0);
            param_max.max(max_var_id(jp_body)).max(max_var_id(rest))
        }
        IRBody::Inc { var, rest, .. } => var.0.max(max_var_id(rest)),
        IRBody::Dec { var, rest } => var.0.max(max_var_id(rest)),
        IRBody::Set {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_id(rest)),
        IRBody::SetTag { var, rest, .. } => var.0.max(max_var_id(rest)),
        IRBody::USet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_id(rest)),
        IRBody::SSet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_id(rest)),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let alt_max = alts.iter().map(|a| max_var_id(&a.body)).max().unwrap_or(0);
            let def_max = default.as_ref().map_or(0, |d| max_var_id(d));
            scrutinee.0.max(alt_max).max(def_max)
        }
        IRBody::Jmp { args, .. } => max_var_id_args(args),
        IRBody::Ret(arg) => max_var_id_arg(arg),
        IRBody::Unreachable => 0,
    }
}

fn max_var_id_arg(arg: &IRArg) -> u32 {
    match arg {
        IRArg::Var(v) => v.0,
        IRArg::Erased => 0,
    }
}

fn max_var_id_args(args: &[IRArg]) -> u32 {
    args.iter().map(max_var_id_arg).max().unwrap_or(0)
}

fn max_var_id_expr(expr: &IRExpr) -> u32 {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => max_var_id_args(args),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => max_var_id_arg(arg),
        IRExpr::ClosureApply { closure, args } => {
            max_var_id_arg(closure).max(max_var_id_args(args))
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => var.0,
        IRExpr::Reuse { var, args, .. } => var.0.max(max_var_id_args(args)),
        IRExpr::Lit(_) | IRExpr::String(_) => 0,
    }
}
