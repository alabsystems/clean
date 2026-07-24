// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced local dead code elimination for L5IR function bodies.
//!
//! Extends `dce_local` with liveness analysis, unreachable branch pruning,
//! known-tag case folding, inc/dec cleanup, and chain simplification.
//! Iterates to fixpoint for cascading dead code removal.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::dce_local::{collect_used, collect_used_expr};
use crate::ir::{IRAlt, IRArg, IRBody, IRExpr, IRLiteral, IRType, JoinPointId, VarId};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

/// Errors from DCE validation.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub(crate) enum DceValidationError {
    /// A variable reference was found with no preceding definition.
    #[error("dangling variable reference: VarId({0})")]
    DanglingVarRef(u32),
    /// A join point jump targets a join point that was not declared.
    #[error("dangling join point reference: JoinPointId({0})")]
    DanglingJoinRef(u32),
}

/// Configuration for the enhanced local DCE pass.
#[derive(Debug, Clone)]
pub(crate) struct ExtDceConfig {
    pub(crate) eliminate_dead_bindings: bool,
    pub(crate) eliminate_dead_joins: bool,
    pub(crate) prune_unreachable_branches: bool,
    pub(crate) fold_known_tags: bool,
    pub(crate) cleanup_dead_rc: bool,
    pub(crate) simplify_single_alt: bool,
    pub(crate) max_iterations: usize,
}

impl Default for ExtDceConfig {
    fn default() -> Self {
        Self {
            eliminate_dead_bindings: true,
            eliminate_dead_joins: true,
            prune_unreachable_branches: true,
            fold_known_tags: true,
            cleanup_dead_rc: true,
            simplify_single_alt: true,
            max_iterations: 20,
        }
    }
}

/// Statistics from the enhanced local DCE pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ExtDceStats {
    pub(crate) bindings_removed: usize,
    pub(crate) joins_removed: usize,
    pub(crate) branches_pruned: usize,
    pub(crate) cases_folded: usize,
    pub(crate) rc_ops_removed: usize,
    pub(crate) chains_simplified: usize,
    pub(crate) params_eliminated: usize,
    pub(crate) iterations: usize,
}

impl ExtDceStats {
    pub(crate) fn total(&self) -> usize {
        self.bindings_removed
            + self.joins_removed
            + self.branches_pruned
            + self.cases_folded
            + self.rc_ops_removed
            + self.chains_simplified
            + self.params_eliminated
    }
}

// -----------------------------------------------------------------------
// Liveness analysis
// -----------------------------------------------------------------------

/// Compute the set of variables that are live somewhere in `body` via
/// backward dataflow: a variable is live if it is used before redefinition.
pub(crate) fn compute_live_vars(body: &IRBody) -> HashSet<VarId> {
    let mut live = HashSet::new();
    compute_live_inner(body, &mut live);
    live
}

fn compute_live_inner(body: &IRBody, live: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            compute_live_inner(rest, live);
            if live.contains(var) {
                collect_used_expr(value, live);
            }
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            compute_live_inner(rest, live);
            compute_live_inner(jp, live);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            compute_live_inner(rest, live);
            live.insert(*var);
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
            compute_live_inner(rest, live);
            live.insert(*var);
            live.insert(*value);
        }
        IRBody::SetTag { var, rest, .. } => {
            compute_live_inner(rest, live);
            live.insert(*var);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            for alt in alts {
                compute_live_inner(&alt.body, live);
            }
            if let Some(d) = default {
                compute_live_inner(d, live);
            }
            live.insert(*scrutinee);
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                if let IRArg::Var(v) = arg {
                    live.insert(*v);
                }
            }
        }
        IRBody::Ret(IRArg::Var(v)) => {
            live.insert(*v);
        }
        IRBody::Ret(IRArg::Erased) | IRBody::Unreachable => {}
    }
}

// -----------------------------------------------------------------------
// Known-tag environment
// -----------------------------------------------------------------------

struct TagEnv(HashMap<u32, u32>);

impl TagEnv {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn record(&mut self, var: VarId, expr: &IRExpr) {
        match expr {
            IRExpr::Ctor { info, .. } => {
                self.0.insert(var.0, info.tag);
            }
            IRExpr::Lit(IRLiteral::Bool(b)) => {
                self.0.insert(var.0, u32::from(*b));
            }
            _ => {}
        }
    }

    fn get_tag(&self, var: VarId) -> Option<u32> {
        self.0.get(&var.0).copied()
    }
    fn fork(&self) -> Self {
        Self(self.0.clone())
    }
}

// -----------------------------------------------------------------------
// Core transform
// -----------------------------------------------------------------------

/// Run the enhanced local DCE pass on a single function body.
/// Iterates to fixpoint until no further transformations are possible.
#[must_use]
pub(crate) fn eliminate_dead_locals_ext(
    body: &IRBody,
    config: &ExtDceConfig,
) -> (IRBody, ExtDceStats) {
    let mut stats = ExtDceStats::default();
    let mut current = body.clone();

    for _ in 0..config.max_iterations {
        stats.iterations += 1;
        let mut round = ExtDceStats::default();
        let mut used_vars = HashSet::new();
        let mut used_jps = HashSet::new();
        collect_used(&current, &mut used_vars, &mut used_jps);

        let mut tag_env = TagEnv::new();
        let new_body = transform(
            &current,
            &used_vars,
            &used_jps,
            &mut tag_env,
            config,
            &mut round,
        );
        let changed = round.total() > 0;
        stats.bindings_removed += round.bindings_removed;
        stats.joins_removed += round.joins_removed;
        stats.branches_pruned += round.branches_pruned;
        stats.cases_folded += round.cases_folded;
        stats.rc_ops_removed += round.rc_ops_removed;
        stats.chains_simplified += round.chains_simplified;
        current = new_body;
        if !changed {
            break;
        }
    }
    (current, stats)
}

/// Run with default config.
#[must_use]
pub(crate) fn eliminate_dead_locals_ext_default(body: &IRBody) -> (IRBody, ExtDceStats) {
    eliminate_dead_locals_ext(body, &ExtDceConfig::default())
}

fn transform(
    body: &IRBody,
    uv: &HashSet<VarId>,
    uj: &HashSet<JoinPointId>,
    te: &mut TagEnv,
    cfg: &ExtDceConfig,
    st: &mut ExtDceStats,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            te.record(*var, value);
            if cfg.eliminate_dead_bindings && !uv.contains(var) && is_pure_expr(value) {
                st.bindings_removed += 1;
                return transform(rest, uv, uj, te, cfg, st);
            }
            let new_rest = transform(rest, uv, uj, te, cfg, st);
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(new_rest),
            }
        }

        IRBody::JDecl {
            jp,
            params,
            body: jpb,
            rest,
        } => {
            if cfg.eliminate_dead_joins && !uj.contains(jp) {
                st.joins_removed += 1;
                return transform(rest, uv, uj, te, cfg, st);
            }
            let mut jte = te.fork();
            let new_jpb = transform(jpb, uv, uj, &mut jte, cfg, st);
            let new_rest = transform(rest, uv, uj, te, cfg, st);
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(new_jpb),
                rest: Box::new(new_rest),
            }
        }

        IRBody::Inc { var, n, rest } => {
            if cfg.cleanup_dead_rc && !is_var_used_in(rest, *var) {
                st.rc_ops_removed += 1;
                return transform(rest, uv, uj, te, cfg, st);
            }
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::Inc {
                var: *var,
                n: *n,
                rest: Box::new(r),
            }
        }

        IRBody::Dec { var, rest } => {
            if cfg.cleanup_dead_rc && !is_var_used_in(rest, *var) {
                st.rc_ops_removed += 1;
                return transform(rest, uv, uj, te, cfg, st);
            }
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::Dec {
                var: *var,
                rest: Box::new(r),
            }
        }

        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            // Known-tag branch folding
            if cfg.fold_known_tags {
                if let Some(tag) = te.get_tag(*scrutinee) {
                    for alt in alts {
                        if alt.ctor.tag == tag {
                            st.cases_folded += 1;
                            let mut ae = te.fork();
                            return transform(&alt.body, uv, uj, &mut ae, cfg, st);
                        }
                    }
                    if let Some(d) = default {
                        st.cases_folded += 1;
                        let mut de = te.fork();
                        return transform(d, uv, uj, &mut de, cfg, st);
                    }
                }
            }
            // Prune unreachable branches
            let mut new_alts: Vec<IRAlt> = Vec::with_capacity(alts.len());
            for alt in alts {
                if cfg.prune_unreachable_branches && is_unreachable(&alt.body) {
                    st.branches_pruned += 1;
                    continue;
                }
                let mut ae = te.fork();
                let nb = transform(&alt.body, uv, uj, &mut ae, cfg, st);
                new_alts.push(IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(nb),
                });
            }
            let new_def = match default {
                Some(d) if cfg.prune_unreachable_branches && is_unreachable(d) => {
                    st.branches_pruned += 1;
                    None
                }
                Some(d) => {
                    let mut de = te.fork();
                    Some(Box::new(transform(d, uv, uj, &mut de, cfg, st)))
                }
                None => None,
            };
            // Single-alt simplification
            if cfg.simplify_single_alt && new_alts.len() == 1 && new_def.is_none() {
                st.chains_simplified += 1;
                return *new_alts
                    .into_iter()
                    .next()
                    .expect("invariant: checked len == 1")
                    .body;
            }
            if cfg.simplify_single_alt && new_alts.is_empty() {
                if let Some(def) = new_def {
                    st.chains_simplified += 1;
                    return *def;
                }
            }
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: new_def,
            }
        }

        // Pass-through nodes: recurse into rest
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::Set {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(r),
            }
        }
        IRBody::SetTag { var, tag, rest } => {
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::SetTag {
                var: *var,
                tag: *tag,
                rest: Box::new(r),
            }
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::USet {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(r),
            }
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let r = transform(rest, uv, uj, te, cfg, st);
            IRBody::SSet {
                var: *var,
                n: *n,
                offset: *offset,
                value: *value,
                ty: ty.clone(),
                rest: Box::new(r),
            }
        }
        // Terminals
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

/// Pure expressions can safely be eliminated when their result is unused.
fn is_pure_expr(expr: &IRExpr) -> bool {
    matches!(
        expr,
        IRExpr::Lit(_)
            | IRExpr::String(_)
            | IRExpr::Proj { .. }
            | IRExpr::Tag(_)
            | IRExpr::Box { .. }
            | IRExpr::Unbox { .. }
            | IRExpr::UProj { .. }
            | IRExpr::SProj { .. }
            | IRExpr::IsShared(_)
            | IRExpr::Ctor { .. }
    )
}

/// Check if a body is `Unreachable` (possibly after inc/dec chains).
fn is_unreachable(body: &IRBody) -> bool {
    match body {
        IRBody::Unreachable => true,
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => is_unreachable(rest),
        _ => false,
    }
}

/// Check if `target` is used anywhere in `body`.
fn is_var_used_in(body: &IRBody, target: VarId) -> bool {
    let mut used_vars = HashSet::new();
    let mut used_jps = HashSet::new();
    collect_used(body, &mut used_vars, &mut used_jps);
    used_vars.contains(&target)
}

// -----------------------------------------------------------------------
// Unused parameter detection
// -----------------------------------------------------------------------

/// Detect function parameters that are never referenced in `body`.
/// Returns the indices of unused parameters in the `params` slice.
#[must_use]
pub(crate) fn detect_unused_params(params: &[(VarId, IRType)], body: &IRBody) -> Vec<usize> {
    let mut used_vars = HashSet::new();
    let mut used_jps = HashSet::new();
    collect_used(body, &mut used_vars, &mut used_jps);
    params
        .iter()
        .enumerate()
        .filter_map(|(i, (v, _))| (!used_vars.contains(v)).then_some(i))
        .collect()
}

// -----------------------------------------------------------------------
// Validation — verify no live ref points to eliminated code
// -----------------------------------------------------------------------

/// Validate that no variable or join point reference in `body` is dangling.
/// `initial_vars` contains VarIds in scope before the body (e.g., params).
/// Used after DCE to confirm the transform did not break references.
pub(crate) fn validate_elimination(
    body: &IRBody,
    initial_vars: &HashSet<VarId>,
    initial_jps: &HashSet<JoinPointId>,
) -> Result<(), DceValidationError> {
    vwalk(body, initial_vars, initial_jps)
}

fn vchk(var: VarId, s: &HashSet<VarId>) -> Result<(), DceValidationError> {
    if s.contains(&var) {
        Ok(())
    } else {
        Err(DceValidationError::DanglingVarRef(var.0))
    }
}

fn vchk_arg(arg: &IRArg, s: &HashSet<VarId>) -> Result<(), DceValidationError> {
    if let IRArg::Var(v) = arg {
        vchk(*v, s)
    } else {
        Ok(())
    }
}

fn vchk_args(args: &[IRArg], s: &HashSet<VarId>) -> Result<(), DceValidationError> {
    for a in args {
        vchk_arg(a, s)?;
    }
    Ok(())
}

fn vchk_expr(e: &IRExpr, s: &HashSet<VarId>) -> Result<(), DceValidationError> {
    match e {
        IRExpr::Ctor { args, .. } => vchk_args(args, s),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => vchk_arg(arg, s),
        IRExpr::Lit(_) | IRExpr::String(_) => Ok(()),
        IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => vchk_args(args, s),
        IRExpr::ClosureApply { closure, args } => {
            vchk_arg(closure, s)?;
            vchk_args(args, s)
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => vchk(*var, s),
        IRExpr::Reuse { var, args, .. } => {
            vchk(*var, s)?;
            vchk_args(args, s)
        }
    }
}

fn vwalk(
    body: &IRBody,
    vs: &HashSet<VarId>,
    js: &HashSet<JoinPointId>,
) -> Result<(), DceValidationError> {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            vchk_expr(value, vs)?;
            let mut nv = vs.clone();
            nv.insert(*var);
            vwalk(rest, &nv, js)
        }
        IRBody::JDecl {
            jp,
            params,
            body: jpb,
            rest,
        } => {
            let mut nj = js.clone();
            nj.insert(*jp);
            let mut jv = vs.clone();
            for (v, _) in params {
                jv.insert(*v);
            }
            vwalk(jpb, &jv, &nj)?;
            vwalk(rest, vs, &nj)
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            vchk(*var, vs)?;
            vwalk(rest, vs, js)
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
            vchk(*var, vs)?;
            vchk(*value, vs)?;
            vwalk(rest, vs, js)
        }
        IRBody::SetTag { var, rest, .. } => {
            vchk(*var, vs)?;
            vwalk(rest, vs, js)
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            vchk(*scrutinee, vs)?;
            for a in alts {
                vwalk(&a.body, vs, js)?;
            }
            if let Some(d) = default {
                vwalk(d, vs, js)?;
            }
            Ok(())
        }
        IRBody::Jmp { jp, args } => {
            if !js.contains(jp) {
                return Err(DceValidationError::DanglingJoinRef(jp.0));
            }
            vchk_args(args, vs)
        }
        IRBody::Ret(arg) => vchk_arg(arg, vs),
        IRBody::Unreachable => Ok(()),
    }
}
