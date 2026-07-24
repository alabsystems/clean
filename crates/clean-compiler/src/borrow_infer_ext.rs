// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Borrow Inference with Escape Analysis and Alias Tracking
//!
//! Adds escape analysis (classifies *why* ownership is needed), alias tracking
//! (follows data flow through projections), and cross-function fixpoint
//! propagation on top of the base `borrow_infer` module.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, VarId};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub(crate) struct BorrowInferExtConfig {
    pub(crate) max_iterations: usize,
    pub(crate) enable_escape_analysis: bool,
    pub(crate) enable_alias_tracking: bool,
    pub(crate) pessimistic_extern: bool,
}

impl Default for BorrowInferExtConfig {
    fn default() -> Self {
        Self {
            max_iterations: 20,
            enable_escape_analysis: true,
            enable_alias_tracking: true,
            pessimistic_extern: true,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BorrowInferExtStats {
    pub(crate) params_borrowed: usize,
    pub(crate) params_owned: usize,
    pub(crate) iterations: usize,
    pub(crate) aliases_tracked: usize,
    pub(crate) escapes_detected: usize,
}

/// Ownership status for a parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum Ownership {
    Borrowed,
    Owned,
    #[default]
    Unknown,
}

/// Reason a variable escapes its local scope, requiring ownership.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EscapeReason {
    ReturnedDirectly,
    StoredInCtor,
    PassedToExtern,
    PassedOwned,
    CapturedInClosure,
}

#[derive(Clone, Debug)]
pub(crate) struct BorrowResult {
    pub(crate) param_ownership: Vec<(VarId, Ownership)>,
    pub(crate) fn_ownership: HashMap<FnId, Vec<Ownership>>,
    pub(crate) stats: BorrowInferExtStats,
}

pub(crate) fn infer_borrows_ext_default(decls: &[IRDecl]) -> BorrowResult {
    infer_borrows_ext(decls, &BorrowInferExtConfig::default())
}

/// Whole-program extended borrow inference with escape analysis and alias tracking.
pub(crate) fn infer_borrows_ext(decls: &[IRDecl], config: &BorrowInferExtConfig) -> BorrowResult {
    let mut stats = BorrowInferExtStats::default();

    // Phase 1: Initialize ownership map. Object params start Unknown; scalars are Owned.
    let mut fn_ownership: HashMap<FnId, Vec<Ownership>> = HashMap::new();
    for decl in decls {
        let ownership: Vec<Ownership> = decl
            .params
            .iter()
            .map(|(_, ty)| {
                if ty.is_scalar() || ty.is_void() || matches!(ty, crate::ir::IRType::Erased) {
                    Ownership::Owned
                } else {
                    Ownership::Unknown
                }
            })
            .collect();
        fn_ownership.insert(FnId(decl.name.clone()), ownership);
    }

    // Phase 2: Per-function escape analysis + alias tracking
    let known_fns: HashSet<FnId> = decls.iter().map(|decl| FnId(decl.name.clone())).collect();
    let mut fn_escapes: HashMap<FnId, Vec<(VarId, EscapeReason)>> = HashMap::new();
    let mut fn_aliases: HashMap<FnId, HashMap<VarId, Vec<VarId>>> = HashMap::new();

    for decl in decls {
        let fn_id = FnId(decl.name.clone());
        let params: Vec<VarId> = decl.params.iter().map(|(v, _)| *v).collect();

        let escapes = if config.enable_escape_analysis {
            analyze_escapes_with_known_callees(&decl.body, &params, Some(&known_fns))
        } else {
            Vec::new()
        };
        stats.escapes_detected += escapes.len();
        fn_escapes.insert(fn_id.clone(), escapes);

        let aliases = if config.enable_alias_tracking {
            let a = track_aliases(&decl.body);
            stats.aliases_tracked += a.values().map(|v| v.len()).sum::<usize>();
            a
        } else {
            HashMap::new()
        };
        fn_aliases.insert(fn_id, aliases);
    }

    // Phase 3: Compute initial per-function ownership from escapes + aliases
    for decl in decls {
        let fn_id = FnId(decl.name.clone());
        let escapes = fn_escapes.get(&fn_id).cloned().unwrap_or_default();
        let aliases = fn_aliases.get(&fn_id).cloned().unwrap_or_default();
        let ownership =
            compute_param_ownership_with_known_callees(decl, &escapes, &aliases, Some(&known_fns));
        fn_ownership.insert(fn_id, ownership.iter().map(|(_, o)| *o).collect());
    }

    // Phase 4: Cross-function fixpoint propagation
    let mut iteration = 0usize;
    loop {
        iteration += 1;
        if iteration > config.max_iterations {
            break;
        }
        let changed = propagate_ownership(decls, &mut fn_ownership, config.pessimistic_extern);
        if !changed {
            break;
        }
    }
    stats.iterations = iteration;

    // Phase 5: Collect results
    let mut param_ownership = Vec::new();
    for decl in decls {
        let fn_id = FnId(decl.name.clone());
        if let Some(ownership) = fn_ownership.get(&fn_id) {
            for (idx, (var, _)) in decl.params.iter().enumerate() {
                let o = ownership.get(idx).copied().unwrap_or(Ownership::Unknown);
                let resolved = match o {
                    Ownership::Unknown => Ownership::Borrowed,
                    other => other,
                };
                param_ownership.push((*var, resolved));
                match resolved {
                    Ownership::Borrowed => stats.params_borrowed += 1,
                    Ownership::Owned => stats.params_owned += 1,
                    Ownership::Unknown => stats.params_borrowed += 1,
                }
            }
        }
    }

    // Resolve Unknown -> Borrowed in fn_ownership for final output
    for ownership in fn_ownership.values_mut() {
        for o in ownership.iter_mut() {
            if *o == Ownership::Unknown {
                *o = Ownership::Borrowed;
            }
        }
    }

    BorrowResult {
        param_ownership,
        fn_ownership,
        stats,
    }
}

/// Analyze which parameters escape their scope and why.
pub(crate) fn analyze_escapes(body: &IRBody, params: &[VarId]) -> Vec<(VarId, EscapeReason)> {
    analyze_escapes_with_known_callees(body, params, None)
}

fn analyze_escapes_with_known_callees(
    body: &IRBody,
    params: &[VarId],
    known_callees: Option<&HashSet<FnId>>,
) -> Vec<(VarId, EscapeReason)> {
    let mut escapes = Vec::new();
    collect_escapes(body, params, known_callees, &mut escapes);
    escapes
}

/// Push escape if var is a tracked param.
fn push_if_param(
    v: VarId,
    reason: EscapeReason,
    params: &[VarId],
    out: &mut Vec<(VarId, EscapeReason)>,
) {
    if params.contains(&v) {
        out.push((v, reason));
    }
}

/// Push escape for each Var arg that is a tracked param.
fn push_args(
    args: &[IRArg],
    reason: EscapeReason,
    params: &[VarId],
    out: &mut Vec<(VarId, EscapeReason)>,
) {
    for arg in args {
        if let IRArg::Var(v) = arg {
            push_if_param(*v, reason.clone(), params, out);
        }
    }
}

fn collect_escapes(
    body: &IRBody,
    params: &[VarId],
    known_callees: Option<&HashSet<FnId>>,
    esc: &mut Vec<(VarId, EscapeReason)>,
) {
    match body {
        IRBody::Ret(IRArg::Var(v)) => {
            push_if_param(*v, EscapeReason::ReturnedDirectly, params, esc)
        }
        IRBody::Ret(IRArg::Erased) | IRBody::Unreachable => {}
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { args, .. } | IRExpr::Reuse { args, .. } => {
                    push_args(args, EscapeReason::StoredInCtor, params, esc)
                }
                IRExpr::PartialApply { args, .. } => {
                    push_args(args, EscapeReason::CapturedInClosure, params, esc)
                }
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        push_if_param(*v, EscapeReason::PassedToExtern, params, esc);
                    }
                    push_args(args, EscapeReason::PassedToExtern, params, esc);
                }
                IRExpr::Apply { fn_id, args }
                    if known_callees.is_none_or(|known| !known.contains(fn_id)) =>
                {
                    push_args(args, EscapeReason::PassedOwned, params, esc)
                }
                IRExpr::Box {
                    arg: IRArg::Var(v), ..
                } => {
                    push_if_param(*v, EscapeReason::StoredInCtor, params, esc);
                }
                IRExpr::Reset(v) => push_if_param(*v, EscapeReason::PassedOwned, params, esc),
                _ => {}
            }
            collect_escapes(rest, params, known_callees, esc);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            push_if_param(*var, EscapeReason::PassedOwned, params, esc);
            push_if_param(*value, EscapeReason::StoredInCtor, params, esc);
            collect_escapes(rest, params, known_callees, esc);
        }
        IRBody::SetTag { var, rest, .. } => {
            push_if_param(*var, EscapeReason::PassedOwned, params, esc);
            collect_escapes(rest, params, known_callees, esc);
        }
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            push_if_param(*var, EscapeReason::PassedOwned, params, esc);
            push_if_param(*value, EscapeReason::StoredInCtor, params, esc);
            collect_escapes(rest, params, known_callees, esc);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => {
            collect_escapes(rest, params, known_callees, esc)
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_escapes(body, params, known_callees, esc);
            collect_escapes(rest, params, known_callees, esc);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_escapes(&alt.body, params, known_callees, esc);
            }
            if let Some(def) = default {
                collect_escapes(def, params, known_callees, esc);
            }
        }
        IRBody::Jmp { args, .. } => push_args(args, EscapeReason::PassedOwned, params, esc),
    }
}

/// Build alias graph: maps source var -> vars derived via Proj/UProj/SProj.
pub(crate) fn track_aliases(body: &IRBody) -> HashMap<VarId, Vec<VarId>> {
    let mut aliases: HashMap<VarId, Vec<VarId>> = HashMap::new();
    collect_aliases(body, &mut aliases);
    aliases
}

fn collect_aliases(body: &IRBody, aliases: &mut HashMap<VarId, Vec<VarId>>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            match value {
                IRExpr::Proj {
                    arg: IRArg::Var(src),
                    ..
                } => {
                    aliases.entry(*src).or_default().push(*var);
                }
                IRExpr::UProj { var: src, .. } | IRExpr::SProj { var: src, .. } => {
                    aliases.entry(*src).or_default().push(*var);
                }
                _ => {}
            }
            collect_aliases(rest, aliases);
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => {
            collect_aliases(rest, aliases);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_aliases(body, aliases);
            collect_aliases(rest, aliases);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_aliases(&alt.body, aliases);
            }
            if let Some(def) = default {
                collect_aliases(def, aliases);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Compute per-parameter ownership from escape reasons and alias graph.
pub(crate) fn compute_param_ownership(
    decl: &IRDecl,
    escapes: &[(VarId, EscapeReason)],
    aliases: &HashMap<VarId, Vec<VarId>>,
) -> Vec<(VarId, Ownership)> {
    compute_param_ownership_with_known_callees(decl, escapes, aliases, None)
}

fn compute_param_ownership_with_known_callees(
    decl: &IRDecl,
    escapes: &[(VarId, EscapeReason)],
    aliases: &HashMap<VarId, Vec<VarId>>,
    known_callees: Option<&HashSet<FnId>>,
) -> Vec<(VarId, Ownership)> {
    let mut escaped_vars: HashSet<VarId> = escapes.iter().map(|(v, _)| *v).collect();
    collect_escaping_var_uses(&decl.body, known_callees, &mut escaped_vars);

    decl.params
        .iter()
        .map(|(var, ty)| {
            if ty.is_scalar()
                || ty.is_void()
                || matches!(ty, crate::ir::IRType::Erased)
                || escaped_vars.contains(var)
                || alias_chain_escapes(*var, aliases, &escaped_vars)
            {
                (*var, Ownership::Owned)
            } else {
                (*var, Ownership::Unknown)
            }
        })
        .collect()
}

fn push_arg_var(arg: &IRArg, out: &mut HashSet<VarId>) {
    if let IRArg::Var(v) = arg {
        out.insert(*v);
    }
}

fn push_arg_vars(args: &[IRArg], out: &mut HashSet<VarId>) {
    for arg in args {
        push_arg_var(arg, out);
    }
}

fn collect_escaping_var_uses(
    body: &IRBody,
    known_callees: Option<&HashSet<FnId>>,
    out: &mut HashSet<VarId>,
) {
    match body {
        IRBody::Ret(arg) => push_arg_var(arg, out),
        IRBody::Unreachable => {}
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { args, .. } | IRExpr::Reuse { args, .. } => {
                    push_arg_vars(args, out);
                }
                IRExpr::PartialApply { args, .. } => push_arg_vars(args, out),
                IRExpr::ClosureApply { closure, args } => {
                    push_arg_var(closure, out);
                    push_arg_vars(args, out);
                }
                IRExpr::Apply { fn_id, args } => {
                    if known_callees.is_none_or(|known| !known.contains(fn_id)) {
                        push_arg_vars(args, out);
                    }
                }
                IRExpr::Box { arg, .. } => push_arg_var(arg, out),
                IRExpr::Reset(v) => {
                    out.insert(*v);
                }
                IRExpr::Proj { .. }
                | IRExpr::Tag(_)
                | IRExpr::Unbox { .. }
                | IRExpr::Lit(_)
                | IRExpr::UProj { .. }
                | IRExpr::SProj { .. }
                | IRExpr::IsShared(_)
                | IRExpr::String(_) => {}
            }
            collect_escaping_var_uses(rest, known_callees, out);
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            out.insert(*var);
            out.insert(*value);
            collect_escaping_var_uses(rest, known_callees, out);
        }
        IRBody::SetTag { var, rest, .. } => {
            out.insert(*var);
            collect_escaping_var_uses(rest, known_callees, out);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => {
            collect_escaping_var_uses(rest, known_callees, out);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_escaping_var_uses(body, known_callees, out);
            collect_escaping_var_uses(rest, known_callees, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_escaping_var_uses(&alt.body, known_callees, out);
            }
            if let Some(def) = default {
                collect_escaping_var_uses(def, known_callees, out);
            }
        }
        IRBody::Jmp { args, .. } => push_arg_vars(args, out),
    }
}

/// Check if any alias of `var` (transitively) is in the escaped set.
fn alias_chain_escapes(
    var: VarId,
    aliases: &HashMap<VarId, Vec<VarId>>,
    escaped: &HashSet<VarId>,
) -> bool {
    let mut visited = HashSet::new();
    let mut stack = vec![var];
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if let Some(targets) = aliases.get(&current) {
            for target in targets {
                if escaped.contains(target) {
                    return true;
                }
                stack.push(*target);
            }
        }
    }
    false
}

/// Cross-function fixpoint: propagate callee ownership requirements to callers.
/// Returns true if any ownership changed.
pub(crate) fn propagate_ownership(
    decls: &[IRDecl],
    results: &mut HashMap<FnId, Vec<Ownership>>,
    pessimistic_extern: bool,
) -> bool {
    let mut changed = false;
    // Build param index maps
    let param_maps: Vec<(FnId, HashMap<VarId, usize>)> = decls
        .iter()
        .map(|d| {
            let fn_id = FnId(d.name.clone());
            let map: HashMap<VarId, usize> = d
                .params
                .iter()
                .enumerate()
                .map(|(i, (v, _))| (*v, i))
                .collect();
            (fn_id, map)
        })
        .collect();

    for (decl_idx, decl) in decls.iter().enumerate() {
        let (ref fn_id, ref param_map) = param_maps[decl_idx];
        propagate_body(
            &decl.body,
            fn_id,
            param_map,
            results,
            pessimistic_extern,
            &mut changed,
        );
    }
    changed
}

fn propagate_body(
    body: &IRBody,
    caller_fn: &FnId,
    param_map: &HashMap<VarId, usize>,
    results: &mut HashMap<FnId, Vec<Ownership>>,
    pessimistic_extern: bool,
    changed: &mut bool,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply {
                fn_id: callee,
                args,
            } = value
            {
                // Get a snapshot of callee ownership to avoid borrow conflict
                let callee_ownership: Option<Vec<Ownership>> = results.get(callee).cloned();
                if let Some(callee_own) = callee_ownership {
                    for (idx, arg) in args.iter().enumerate() {
                        if let IRArg::Var(v) = arg {
                            if idx < callee_own.len() && callee_own[idx] == Ownership::Owned {
                                if let Some(param_idx) = param_map.get(v) {
                                    mark_owned(results, caller_fn, *param_idx, changed);
                                }
                            }
                        }
                    }
                } else if pessimistic_extern {
                    // Unknown callee: treat all args as owned
                    for arg in args {
                        if let IRArg::Var(v) = arg {
                            if let Some(param_idx) = param_map.get(v) {
                                mark_owned(results, caller_fn, *param_idx, changed);
                            }
                        }
                    }
                }
            }
            propagate_body(
                rest,
                caller_fn,
                param_map,
                results,
                pessimistic_extern,
                changed,
            );
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => {
            propagate_body(
                rest,
                caller_fn,
                param_map,
                results,
                pessimistic_extern,
                changed,
            );
        }
        IRBody::JDecl { body, rest, .. } => {
            propagate_body(
                body,
                caller_fn,
                param_map,
                results,
                pessimistic_extern,
                changed,
            );
            propagate_body(
                rest,
                caller_fn,
                param_map,
                results,
                pessimistic_extern,
                changed,
            );
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                propagate_body(
                    &alt.body,
                    caller_fn,
                    param_map,
                    results,
                    pessimistic_extern,
                    changed,
                );
            }
            if let Some(def) = default {
                propagate_body(
                    def,
                    caller_fn,
                    param_map,
                    results,
                    pessimistic_extern,
                    changed,
                );
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Mark a parameter as Owned in the results map. Returns true via `changed` if modified.
fn mark_owned(
    results: &mut HashMap<FnId, Vec<Ownership>>,
    fn_id: &FnId,
    idx: usize,
    changed: &mut bool,
) {
    if let Some(ownership) = results.get_mut(fn_id) {
        if idx < ownership.len() && ownership[idx] != Ownership::Owned {
            ownership[idx] = Ownership::Owned;
            *changed = true;
        }
    }
}

#[cfg(test)]
#[path = "borrow_infer_ext_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "borrow_infer_ext_infer_tests.rs"]
mod infer_tests;
