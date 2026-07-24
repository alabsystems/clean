// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Free Variable Analysis for L5IR
//!
//! Computes the set of VarIds that are referenced but not locally bound
//! within an IRBody or IRExpr. Used by the closure conversion pass to
//! determine which variables need to be captured in closure environments.
//!
//! Part of #3084 - Runtime closure support.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, VarId};
use std::collections::HashSet;

/// Compute free variables in an IRBody.
///
/// Returns the set of VarIds that are referenced but not bound within `body`.
#[must_use]
pub(crate) fn free_vars_body(body: &IRBody, bound: &HashSet<VarId>) -> HashSet<VarId> {
    let mut free = HashSet::new();
    collect_free_body(body, bound, &mut free);
    free
}

/// Collect free variables from an IRBody.
fn collect_free_body(body: &IRBody, bound: &HashSet<VarId>, free: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            collect_free_expr(value, bound, free);
            let mut new_bound = bound.clone();
            new_bound.insert(*var);
            collect_free_body(rest, &new_bound, free);
        }
        IRBody::JDecl {
            jp: _,
            params,
            body: jp_body,
            rest,
        } => {
            let mut inner = bound.clone();
            for (v, _) in params {
                inner.insert(*v);
            }
            collect_free_body(jp_body, &inner, free);
            collect_free_body(rest, bound, free);
        }
        IRBody::Inc { var, rest, .. } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::Dec { var, rest } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            if !bound.contains(value) {
                free.insert(*value);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::SetTag { var, rest, .. } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::USet {
            var, value, rest, ..
        } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            if !bound.contains(value) {
                free.insert(*value);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            if !bound.contains(value) {
                free.insert(*value);
            }
            collect_free_body(rest, bound, free);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            if !bound.contains(scrutinee) {
                free.insert(*scrutinee);
            }
            for alt in alts {
                collect_free_body(&alt.body, bound, free);
            }
            if let Some(def) = default {
                collect_free_body(def, bound, free);
            }
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
        IRBody::Ret(arg) => {
            collect_free_arg(arg, bound, free);
        }
        IRBody::Unreachable => {}
    }
}

/// Collect free variables from an IRExpr.
fn collect_free_expr(expr: &IRExpr, bound: &HashSet<VarId>, free: &mut HashSet<VarId>) {
    match expr {
        IRExpr::Ctor { args, .. } => {
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
        IRExpr::Proj { arg, .. } => collect_free_arg(arg, bound, free),
        IRExpr::Tag(arg) => collect_free_arg(arg, bound, free),
        IRExpr::Box { arg, .. } => collect_free_arg(arg, bound, free),
        IRExpr::Unbox { arg, .. } => collect_free_arg(arg, bound, free),
        IRExpr::Lit(_) | IRExpr::String(_) => {}
        IRExpr::Apply { args, .. } => {
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
        IRExpr::PartialApply { args, .. } => {
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            collect_free_arg(closure, bound, free);
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
        IRExpr::UProj { var, .. } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
        }
        IRExpr::SProj { var, .. } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
        }
        IRExpr::IsShared(var) => {
            if !bound.contains(var) {
                free.insert(*var);
            }
        }
        IRExpr::Reset(var) => {
            if !bound.contains(var) {
                free.insert(*var);
            }
        }
        IRExpr::Reuse { var, args, .. } => {
            if !bound.contains(var) {
                free.insert(*var);
            }
            for arg in args {
                collect_free_arg(arg, bound, free);
            }
        }
    }
}

/// Collect free variable from an IRArg.
fn collect_free_arg(arg: &IRArg, bound: &HashSet<VarId>, free: &mut HashSet<VarId>) {
    if let IRArg::Var(v) = arg {
        if !bound.contains(v) {
            free.insert(*v);
        }
    }
}

/// Build the bound variable set from an IRDecl's parameters.
#[must_use]
pub(crate) fn bound_from_params(decl: &IRDecl) -> HashSet<VarId> {
    decl.params.iter().map(|(v, _)| *v).collect()
}

/// Find the maximum VarId used across all declarations.
pub(super) fn find_max_var_id(decls: &[IRDecl]) -> u32 {
    let mut max = 0u32;
    for decl in decls {
        for (v, _) in &decl.params {
            max = max.max(v.0);
        }
        max_var_in_body(&decl.body, &mut max);
    }
    max
}

/// Recursively find maximum VarId in an IRBody.
fn max_var_in_body(body: &IRBody, max: &mut u32) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            *max = (*max).max(var.0);
            max_var_in_expr(value, max);
            max_var_in_body(rest, max);
        }
        IRBody::JDecl {
            params,
            body: jp_body,
            rest,
            ..
        } => {
            for (v, _) in params {
                *max = (*max).max(v.0);
            }
            max_var_in_body(jp_body, max);
            max_var_in_body(rest, max);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
            *max = (*max).max(var.0);
            max_var_in_body(rest, max);
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        } => {
            *max = (*max).max(var.0);
            *max = (*max).max(value.0);
            max_var_in_body(rest, max);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            *max = (*max).max(var.0);
            *max = (*max).max(value.0);
            max_var_in_body(rest, max);
        }
        IRBody::SetTag { var, rest, .. } => {
            *max = (*max).max(var.0);
            max_var_in_body(rest, max);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            *max = (*max).max(scrutinee.0);
            for alt in alts {
                max_var_in_body(&alt.body, max);
            }
            if let Some(def) = default {
                max_var_in_body(def, max);
            }
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                if let IRArg::Var(v) = arg {
                    *max = (*max).max(v.0);
                }
            }
        }
        IRBody::Ret(arg) => {
            if let IRArg::Var(v) = arg {
                *max = (*max).max(v.0);
            }
        }
        IRBody::Unreachable => {}
    }
}

/// Recursively find maximum VarId in an IRExpr.
fn max_var_in_expr(expr: &IRExpr, max: &mut u32) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => {
            for arg in args {
                if let IRArg::Var(v) = arg {
                    *max = (*max).max(v.0);
                }
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            if let IRArg::Var(v) = closure {
                *max = (*max).max(v.0);
            }
            for arg in args {
                if let IRArg::Var(v) = arg {
                    *max = (*max).max(v.0);
                }
            }
        }
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            if let IRArg::Var(v) = arg {
                *max = (*max).max(v.0);
            }
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            *max = (*max).max(var.0);
        }
        IRExpr::Reuse { var, args, .. } => {
            *max = (*max).max(var.0);
            for arg in args {
                if let IRArg::Var(v) = arg {
                    *max = (*max).max(v.0);
                }
            }
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}
