// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Borrow Inference for L5IR Parameters
//!
//! Determines which function parameters should be borrowed vs owned at the
//! L5IR level, minimizing reference counting overhead. Operates after `to_ir`
//! conversion and reset/reuse insertion, before explicit boxing and RC insertion.
//!
//! Algorithm (Ullrich & de Moura, "Counting Immutable Beans" IFL 2020):
//! 1. Initialize all object-typed parameters as Borrowed
//! 2. Scan bodies for consuming uses (ctor storage, owned callee params,
//!    reset/reuse, mutable set, closure capture)
//! 3. Propagate ownership backward through projections
//! 4. Cross-function propagation via callee param requirements
//! 5. Fixed-point iteration until stable (monotonicity guarantees termination)
//!
//! `rc::borrow` operates on L5CNF (high-level). This module operates on L5IR
//! (low-level) where explicit `Proj`, `Reset`, `Reuse`, `Set`, `ClosureApply`
//! nodes exist, enabling more precise ownership decisions.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, VarId};
use std::collections::{HashMap, HashSet};

/// Ownership status for a parameter at the L5IR level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum ParamOwnership {
    /// Caller transfers ownership; callee must consume (dec on all paths).
    Owned,
    /// Caller retains ownership; callee must not dec.
    #[default]
    Borrowed,
}

/// Borrow annotations for one L5IR function.
#[derive(Clone, Debug)]
pub(crate) struct IRFnBorrow {
    /// Ownership for each parameter, indexed by position.
    pub(crate) params: Vec<ParamOwnership>,
}

impl IRFnBorrow {
    fn all_borrowed(n: usize) -> Self {
        Self {
            params: vec![ParamOwnership::Borrowed; n],
        }
    }

    /// Mark parameter at `idx` as owned. Returns true if changed.
    fn mark_owned(&mut self, idx: usize) -> bool {
        if idx < self.params.len() && self.params[idx] == ParamOwnership::Borrowed {
            self.params[idx] = ParamOwnership::Owned;
            true
        } else {
            false
        }
    }

    pub(crate) fn borrowed_count(&self) -> usize {
        self.params
            .iter()
            .filter(|o| **o == ParamOwnership::Borrowed)
            .count()
    }

    pub(crate) fn owned_count(&self) -> usize {
        self.params
            .iter()
            .filter(|o| **o == ParamOwnership::Owned)
            .count()
    }
}

/// Map from function ID to its borrow annotations.
#[derive(Clone, Debug, Default)]
pub(crate) struct IRBorrowMap {
    fns: HashMap<FnId, IRFnBorrow>,
}

impl IRBorrowMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn get(&self, fn_id: &FnId) -> Option<&IRFnBorrow> {
        self.fns.get(fn_id)
    }

    pub(crate) fn insert(&mut self, fn_id: FnId, borrow: IRFnBorrow) {
        self.fns.insert(fn_id, borrow);
    }

    fn mark_owned(&mut self, fn_id: &FnId, idx: usize) -> bool {
        if let Some(borrow) = self.fns.get_mut(fn_id) {
            borrow.mark_owned(idx)
        } else {
            false
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.fns.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&FnId, &IRFnBorrow)> {
        self.fns.iter()
    }
}

/// Configuration for borrow inference.
#[derive(Clone, Debug)]
pub(crate) struct BorrowInferConfig {
    /// Maximum fixed-point iterations (safety bound; convergence is typically fast).
    pub(crate) max_iterations: u32,
    /// When disabled, all params are conservatively marked Owned.
    pub(crate) enabled: bool,
}

impl Default for BorrowInferConfig {
    fn default() -> Self {
        Self {
            max_iterations: 1000,
            enabled: true,
        }
    }
}

/// Statistics from a borrow inference run.
#[derive(Clone, Debug, Default)]
pub(crate) struct BorrowStats {
    pub(crate) total_params: usize,
    pub(crate) borrowed: usize,
    pub(crate) owned: usize,
    pub(crate) iterations: u32,
    pub(crate) functions: usize,
    pub(crate) scalar_skipped: usize,
}

/// Infer borrow annotations for a list of IR declarations.
///
/// Guaranteed to terminate: ownership only transitions Borrowed -> Owned (monotone).
/// With N total parameters, at most N transitions and N+1 iterations.
pub(crate) fn infer_ir_borrow(
    decls: &[IRDecl],
    config: &BorrowInferConfig,
) -> (IRBorrowMap, BorrowStats) {
    let mut stats = BorrowStats {
        functions: decls.len(),
        ..Default::default()
    };

    if !config.enabled {
        return make_all_owned(decls, &mut stats);
    }

    let mut borrow_map = IRBorrowMap::new();

    // Phase 1: Initialize. Object params start Borrowed; scalars start Owned (no RC).
    for decl in decls {
        let n = decl.params.len();
        let mut fn_borrow = IRFnBorrow::all_borrowed(n);
        for (idx, (_var, ty)) in decl.params.iter().enumerate() {
            stats.total_params += 1;
            if ty.is_scalar() || ty.is_void() || matches!(ty, crate::ir::IRType::Erased) {
                fn_borrow.params[idx] = ParamOwnership::Owned;
                stats.scalar_skipped += 1;
            }
        }
        borrow_map.insert(FnId(decl.name.clone()), fn_borrow);
    }

    // Build VarId -> param index lookup per decl
    let param_maps: Vec<HashMap<VarId, usize>> = decls
        .iter()
        .map(|d| {
            d.params
                .iter()
                .enumerate()
                .map(|(i, (v, _))| (*v, i))
                .collect()
        })
        .collect();

    // Phase 2: Fixed-point iteration
    let mut iteration = 0u32;
    while iteration < config.max_iterations {
        iteration += 1;
        let mut changed = false;

        for (decl_idx, decl) in decls.iter().enumerate() {
            let fn_id = FnId(decl.name.clone());
            let mut owned_vars: HashSet<VarId> = HashSet::new();
            collect_owned_vars(&decl.body, &borrow_map, &mut owned_vars);

            for (var, idx) in &param_maps[decl_idx] {
                if owned_vars.contains(var) && borrow_map.mark_owned(&fn_id, *idx) {
                    changed = true;
                }
            }

            promote_tail_call_params(
                &decl.body,
                &fn_id,
                &owned_vars,
                &param_maps[decl_idx],
                &mut borrow_map,
                &mut changed,
            );
        }

        if !changed {
            break;
        }
    }

    stats.iterations = iteration;
    for (_, fb) in borrow_map.iter() {
        stats.borrowed += fb.borrowed_count();
        stats.owned += fb.owned_count();
    }
    (borrow_map, stats)
}

/// Infer borrow annotations for a single declaration.
pub(crate) fn infer_ir_borrow_single(decl: &IRDecl) -> IRFnBorrow {
    let config = BorrowInferConfig::default();
    let (map, _) = infer_ir_borrow(std::slice::from_ref(decl), &config);
    let fn_id = FnId(decl.name.clone());
    map.get(&fn_id)
        .cloned()
        .unwrap_or_else(|| IRFnBorrow::all_borrowed(decl.params.len()))
}

/// When inference is disabled, mark all params as owned (conservative).
fn make_all_owned(decls: &[IRDecl], stats: &mut BorrowStats) -> (IRBorrowMap, BorrowStats) {
    let mut map = IRBorrowMap::new();
    for decl in decls {
        let n = decl.params.len();
        stats.total_params += n;
        stats.owned += n;
        map.insert(
            FnId(decl.name.clone()),
            IRFnBorrow {
                params: vec![ParamOwnership::Owned; n],
            },
        );
    }
    stats.iterations = 0;
    (map, stats.clone())
}

/// Collect VarIds that must be owned in a function body.
///
/// Ownership sources: ctor storage, reuse, reset, mutable set/uset/sset,
/// partial/closure apply, box, owned callee params, return, jmp args.
/// Backward propagation: proj/uproj/sproj from owned result.
fn collect_owned_vars(body: &IRBody, borrow_map: &IRBorrowMap, owned: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            collect_owned_vars(rest, borrow_map, owned);
            match value {
                IRExpr::Proj { arg, .. } => {
                    if owned.contains(var) {
                        if let IRArg::Var(src) = arg {
                            owned.insert(*src);
                        }
                    }
                }
                IRExpr::UProj { var: src, .. } | IRExpr::SProj { var: src, .. } => {
                    if owned.contains(var) {
                        owned.insert(*src);
                    }
                }
                IRExpr::Tag(_) | IRExpr::IsShared(_) | IRExpr::Unbox { .. } => {}
                IRExpr::Ctor { args, .. } => {
                    insert_var_args(args, owned);
                }
                IRExpr::Reuse {
                    var: slot, args, ..
                } => {
                    owned.insert(*slot);
                    insert_var_args(args, owned);
                }
                IRExpr::Apply { fn_id, args } => {
                    if let Some(fn_borrow) = borrow_map.get(fn_id) {
                        for (idx, arg) in args.iter().enumerate() {
                            if let IRArg::Var(v) = arg {
                                if idx < fn_borrow.params.len()
                                    && fn_borrow.params[idx] == ParamOwnership::Owned
                                {
                                    owned.insert(*v);
                                }
                            }
                        }
                    } else {
                        insert_var_args(args, owned);
                    }
                }
                IRExpr::PartialApply { args, .. } => {
                    insert_var_args(args, owned);
                }
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        owned.insert(*v);
                    }
                    insert_var_args(args, owned);
                }
                IRExpr::Reset(v) => {
                    owned.insert(*v);
                }
                IRExpr::Box { arg, .. } => {
                    if let IRArg::Var(v) = arg {
                        owned.insert(*v);
                    }
                }
                IRExpr::Lit(_) | IRExpr::String(_) => {}
            }
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            owned.insert(*var);
            owned.insert(*value);
            collect_owned_vars(rest, borrow_map, owned);
        }
        IRBody::SetTag { var, rest, .. } => {
            owned.insert(*var);
            collect_owned_vars(rest, borrow_map, owned);
        }
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            owned.insert(*var);
            owned.insert(*value);
            collect_owned_vars(rest, borrow_map, owned);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => {
            collect_owned_vars(rest, borrow_map, owned);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_owned_vars(body, borrow_map, owned);
            collect_owned_vars(rest, borrow_map, owned);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_owned_vars(&alt.body, borrow_map, owned);
            }
            if let Some(def) = default {
                collect_owned_vars(def, borrow_map, owned);
            }
        }
        IRBody::Jmp { args, .. } => {
            insert_var_args(args, owned);
        }
        IRBody::Ret(arg) => {
            if let IRArg::Var(v) = arg {
                owned.insert(*v);
            }
        }
        IRBody::Unreachable => {}
    }
}

/// Helper: insert all `Var` arguments into the owned set.
fn insert_var_args(args: &[IRArg], owned: &mut HashSet<VarId>) {
    for arg in args {
        if let IRArg::Var(v) = arg {
            owned.insert(*v);
        }
    }
}

/// Promote callee params to owned when a self-recursive tail call passes
/// an already-owned variable at that position (preserves tail-call optimization).
fn promote_tail_call_params(
    body: &IRBody,
    fn_id: &FnId,
    owned_vars: &HashSet<VarId>,
    param_map: &HashMap<VarId, usize>,
    borrow_map: &mut IRBorrowMap,
    changed: &mut bool,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::Apply {
                fn_id: callee,
                args,
            } = value
            {
                if callee == fn_id && is_ir_tail_call(rest, *var) {
                    for (idx, arg) in args.iter().enumerate() {
                        if let IRArg::Var(v) = arg {
                            let is_owned = (param_map.contains_key(v) && owned_vars.contains(v))
                                || owned_vars.contains(v);
                            if is_owned && borrow_map.mark_owned(fn_id, idx) {
                                *changed = true;
                            }
                        }
                    }
                }
            }
            promote_tail_call_params(rest, fn_id, owned_vars, param_map, borrow_map, changed);
        }
        IRBody::JDecl { body, rest, .. } => {
            promote_tail_call_params(body, fn_id, owned_vars, param_map, borrow_map, changed);
            promote_tail_call_params(rest, fn_id, owned_vars, param_map, borrow_map, changed);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                promote_tail_call_params(
                    &alt.body, fn_id, owned_vars, param_map, borrow_map, changed,
                );
            }
            if let Some(def) = default {
                promote_tail_call_params(def, fn_id, owned_vars, param_map, borrow_map, changed);
            }
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            promote_tail_call_params(rest, fn_id, owned_vars, param_map, borrow_map, changed);
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Check if a VDecl result is returned directly (tail position).
fn is_ir_tail_call(rest: &IRBody, result_var: VarId) -> bool {
    matches!(rest, IRBody::Ret(IRArg::Var(v)) if *v == result_var)
}

#[cfg(test)]
#[path = "borrow_infer_tests.rs"]
mod tests;
