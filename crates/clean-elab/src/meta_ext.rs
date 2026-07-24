// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended metavariable management for the elaborator.
//!
//! Builds on `MetaState` / `MetaCtx` to provide scoped creation, validated
//! assignment, delayed assignment, synthetic metas, dependency ordering,
//! scope checking, abstraction, statistics, pretty printing, and solve budget.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::fmt;

use clean_kernel::name::Name;
use clean_kernel::{BinderData, Expr, ExprKind, ExprVisitor, FVarId};

use crate::unify::{MetaId, MetaState};

/// Configuration for extended metavariable management.
#[derive(Debug, Clone)]
pub(crate) struct MetaExtConfig {
    pub(crate) max_metas: usize,
    pub(crate) solve_budget: usize,
    pub(crate) validate_on_assign: bool,
}

impl Default for MetaExtConfig {
    fn default() -> Self {
        Self {
            max_metas: 10_000,
            solve_budget: 100_000,
            validate_on_assign: true,
        }
    }
}

/// The kind of a synthetic metavariable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SyntheticKind {
    /// Ordinary placeholder.
    Placeholder,
    /// Type class instance goal.
    TypeClass,
    /// Tactic goal.
    Tactic,
}

/// A deferred assignment: value is known but substitution is postponed.
#[derive(Debug, Clone)]
pub(crate) struct DelayedAssignment {
    pub(crate) meta_id: MetaId,
    pub(crate) value: Expr,
    pub(crate) pending_fvars: Vec<FVarId>,
}

/// Aggregate statistics for metavariable operations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct MetaStats {
    pub(crate) created: usize,
    pub(crate) assigned: usize,
    pub(crate) delayed: usize,
    pub(crate) solve_steps: usize,
}

impl fmt::Display for MetaStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "metas(created={}, assigned={}, delayed={}, steps={})",
            self.created, self.assigned, self.delayed, self.solve_steps,
        )
    }
}

/// Errors specific to extended metavariable operations.
#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum MetaExtError {
    #[error("metavariable budget exhausted (limit {limit})")]
    BudgetExhausted { limit: usize },
    #[error("metavariable creation limit reached (limit {limit})")]
    CreationLimitReached { limit: usize },
    #[error("assignment validation failed for ?{meta}: {reason}")]
    ValidationFailed { meta: u64, reason: String },
    #[error("escaping local variable {fvar} in metavariable ?{meta}")]
    EscapingLocal { meta: u64, fvar: u64 },
    #[error("metavariable ?{0} not found")]
    NotFound(u64),
    #[error("metavariable ?{0} already assigned")]
    AlreadyAssigned(u64),
}

/// Extended metavariable context layered on top of `MetaState`.
///
/// Tracks synthetic kind, delayed assignments, and local scope snapshots
/// that the base `MetaState` does not carry.
pub(crate) struct MetaExtCtx<'a> {
    metas: &'a mut MetaState,
    synthetic: BTreeMap<MetaId, SyntheticKind>,
    local_contexts: BTreeMap<MetaId, Vec<(Name, FVarId, Expr)>>,
    delayed: Vec<DelayedAssignment>,
    stats: MetaStats,
    config: MetaExtConfig,
}

impl<'a> MetaExtCtx<'a> {
    pub(crate) fn new(metas: &'a mut MetaState) -> Self {
        Self {
            metas,
            synthetic: BTreeMap::new(),
            local_contexts: BTreeMap::new(),
            delayed: Vec::new(),
            stats: MetaStats::default(),
            config: MetaExtConfig::default(),
        }
    }

    pub(crate) fn with_config(metas: &'a mut MetaState, config: MetaExtConfig) -> Self {
        Self {
            metas,
            synthetic: BTreeMap::new(),
            local_contexts: BTreeMap::new(),
            delayed: Vec::new(),
            stats: MetaStats::default(),
            config,
        }
    }

    /// Create a fresh metavariable that records its local context.
    pub(crate) fn create_with_context(
        &mut self,
        ty: Expr,
        locals: Vec<(Name, FVarId, Expr)>,
    ) -> Result<MetaId, MetaExtError> {
        if self.stats.created >= self.config.max_metas {
            return Err(MetaExtError::CreationLimitReached {
                limit: self.config.max_metas,
            });
        }
        let state_locals: Vec<(String, FVarId, Expr)> = locals
            .iter()
            .map(|(n, fv, e)| (n.to_string(), *fv, e.clone()))
            .collect();
        let id = self.metas.fresh_with_locals(ty, state_locals);
        self.local_contexts.insert(id, locals);
        self.stats.created += 1;
        Ok(id)
    }

    /// Create a synthetic metavariable (e.g. for type class resolution).
    pub(crate) fn create_synthetic(
        &mut self,
        ty: Expr,
        kind: SyntheticKind,
        locals: Vec<(Name, FVarId, Expr)>,
    ) -> Result<MetaId, MetaExtError> {
        let id = self.create_with_context(ty, locals)?;
        self.synthetic.insert(id, kind);
        Ok(id)
    }

    /// Assign a value to a metavariable with scope validation.
    pub(crate) fn assign_checked(&mut self, id: MetaId, value: Expr) -> Result<(), MetaExtError> {
        let meta = self
            .metas
            .get(id)
            .ok_or(MetaExtError::NotFound(id.as_u64()))?;
        if meta.assignment.is_some() {
            return Err(MetaExtError::AlreadyAssigned(id.as_u64()));
        }
        if let Some(ctx) = self.local_contexts.get(&id) {
            let allowed: HashSet<FVarId> = ctx.iter().map(|(_, fv, _)| *fv).collect();
            if let Some(bad) = find_escaping_fvar(&value, &allowed) {
                return Err(MetaExtError::EscapingLocal {
                    meta: id.as_u64(),
                    fvar: bad.as_u64(),
                });
            }
        }
        if !self.metas.assign(id, value) {
            return Err(MetaExtError::ValidationFailed {
                meta: id.as_u64(),
                reason: "occurs check failed".into(),
            });
        }
        self.stats.assigned += 1;
        Ok(())
    }

    /// Register a delayed assignment: the value will be substituted later.
    pub(crate) fn assign_delayed(
        &mut self,
        id: MetaId,
        value: Expr,
        pending_fvars: Vec<FVarId>,
    ) -> Result<(), MetaExtError> {
        if self.metas.get(id).is_none() {
            return Err(MetaExtError::NotFound(id.as_u64()));
        }
        self.delayed.push(DelayedAssignment {
            meta_id: id,
            value,
            pending_fvars,
        });
        self.stats.delayed += 1;
        Ok(())
    }

    /// Flush delayed assignments whose pending fvars are resolved.
    pub(crate) fn flush_delayed(&mut self) -> Vec<MetaExtError> {
        let mut errors = Vec::new();
        let mut remaining = Vec::new();
        for da in std::mem::take(&mut self.delayed) {
            let resolved = da.pending_fvars.iter().all(|fv| {
                MetaState::from_fvar(*fv)
                    .map(|mid| self.metas.is_assigned(mid))
                    .unwrap_or(true)
            });
            if resolved {
                let value = self.metas.instantiate(&da.value);
                if self.metas.assign(da.meta_id, value) {
                    self.stats.assigned += 1;
                } else {
                    errors.push(MetaExtError::ValidationFailed {
                        meta: da.meta_id.as_u64(),
                        reason: "delayed assignment failed".into(),
                    });
                }
            } else {
                remaining.push(da);
            }
        }
        self.delayed = remaining;
        errors
    }

    /// Return metavariables in natural (dependency) order via topological sort.
    pub(crate) fn natural_order(&self) -> Vec<MetaId> {
        let unassigned = self.metas.unassigned();
        let mut deps: BTreeMap<MetaId, Vec<MetaId>> = BTreeMap::new();
        let mut in_deg: BTreeMap<MetaId, usize> = BTreeMap::new();
        for &id in &unassigned {
            in_deg.entry(id).or_insert(0);
            if let Some(meta) = self.metas.get(id) {
                for dep in collect_meta_refs(&meta.ty) {
                    if unassigned.contains(&dep) && dep != id {
                        deps.entry(dep).or_default().push(id);
                        *in_deg.entry(id).or_insert(0) += 1;
                    }
                }
            }
        }
        let mut queue: VecDeque<MetaId> = in_deg
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(&id, _)| id)
            .collect();
        let mut order = Vec::with_capacity(unassigned.len());
        while let Some(id) = queue.pop_front() {
            order.push(id);
            for &dep in deps.get(&id).unwrap_or(&Vec::new()) {
                if let Some(d) = in_deg.get_mut(&dep) {
                    *d = d.saturating_sub(1);
                    if *d == 0 {
                        queue.push_back(dep);
                    }
                }
            }
        }
        for &id in &unassigned {
            if !order.contains(&id) {
                order.push(id);
            }
        }
        order
    }

    /// Check that `expr` does not reference fvars outside the meta's context.
    pub(crate) fn check_scope(&self, meta_id: MetaId, expr: &Expr) -> Result<(), MetaExtError> {
        let allowed: HashSet<FVarId> = self
            .local_contexts
            .get(&meta_id)
            .map(|ctx| ctx.iter().map(|(_, fv, _)| *fv).collect())
            .unwrap_or_default();
        if let Some(bad) = find_escaping_fvar(expr, &allowed) {
            return Err(MetaExtError::EscapingLocal {
                meta: meta_id.as_u64(),
                fvar: bad.as_u64(),
            });
        }
        Ok(())
    }

    /// Abstract over the local context of `meta_id` to produce a closed term.
    pub(crate) fn abstract_meta(&self, meta_id: MetaId, body: &Expr) -> Result<Expr, MetaExtError> {
        let ctx = self
            .local_contexts
            .get(&meta_id)
            .ok_or(MetaExtError::NotFound(meta_id.as_u64()))?;
        if ctx.is_empty() {
            return Ok(body.clone());
        }
        let mut result = body.clone();
        for (i, (_, fv, _)) in ctx.iter().enumerate().rev() {
            result = replace_fvar_with_bvar(&result, *fv, (ctx.len() - 1 - i) as u32);
        }
        for (_name, _, ty) in ctx.iter().rev() {
            result = Expr::lam(BinderData::default(), ty.clone(), result);
        }
        Ok(result)
    }

    pub(crate) fn stats(&self) -> &MetaStats {
        &self.stats
    }
    pub(crate) fn unresolved_count(&self) -> usize {
        self.metas.unassigned().len()
    }

    /// Render a human-readable summary of a single metavariable.
    pub(crate) fn pretty_meta(&self, id: MetaId) -> String {
        let Some(meta) = self.metas.get(id) else {
            return format!("?{} (not found)", id.as_u64());
        };
        let status = if meta.assignment.is_some() {
            "assigned"
        } else {
            "unassigned"
        };
        let kind = self
            .synthetic
            .get(&id)
            .map(|k| match k {
                SyntheticKind::Placeholder => "placeholder",
                SyntheticKind::TypeClass => "typeclass",
                SyntheticKind::Tactic => "tactic",
            })
            .unwrap_or("natural");
        let ctx_len = self.local_contexts.get(&id).map(|c| c.len()).unwrap_or(0);
        format!("?{} [{status}, {kind}, ctx={ctx_len}]", id.as_u64())
    }

    /// Render a summary of all metavariables.
    pub(crate) fn pretty_all(&self) -> String {
        let mut ids: Vec<MetaId> = self.metas.iter().map(|(id, _)| id).collect();
        ids.sort_by_key(|id| id.as_u64());
        ids.iter()
            .map(|id| self.pretty_meta(*id))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Record a solve step; returns error if budget is exhausted.
    pub(crate) fn tick_solve(&mut self) -> Result<(), MetaExtError> {
        self.stats.solve_steps += 1;
        if self.stats.solve_steps > self.config.solve_budget {
            return Err(MetaExtError::BudgetExhausted {
                limit: self.config.solve_budget,
            });
        }
        Ok(())
    }

    pub(crate) fn remaining_budget(&self) -> usize {
        self.config
            .solve_budget
            .saturating_sub(self.stats.solve_steps)
    }

    pub(crate) fn meta_state(&self) -> &MetaState {
        self.metas
    }
    pub(crate) fn synthetic_kind(&self, id: MetaId) -> Option<SyntheticKind> {
        self.synthetic.get(&id).copied()
    }
    pub(crate) fn local_context(&self, id: MetaId) -> Option<&[(Name, FVarId, Expr)]> {
        self.local_contexts.get(&id).map(|v| v.as_slice())
    }
    pub(crate) fn delayed_count(&self) -> usize {
        self.delayed.len()
    }
    pub(crate) fn config(&self) -> &MetaExtConfig {
        &self.config
    }
}

// -- helpers ----------------------------------------------------------------

/// Collect all metavariable references in an expression.
fn collect_meta_refs(expr: &Expr) -> Vec<MetaId> {
    struct Collector(Vec<MetaId>);
    impl ExprVisitor for Collector {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if let Some(mid) = MetaState::from_fvar(id) {
                if !self.0.contains(&mid) {
                    self.0.push(mid);
                }
            }
        }
    }
    let mut c = Collector(Vec::new());
    c.visit_expr(expr);
    c.0
}

/// Find a free variable in `expr` that is NOT in `allowed` and NOT a meta-fvar.
fn find_escaping_fvar(expr: &Expr, allowed: &HashSet<FVarId>) -> Option<FVarId> {
    struct Finder<'a> {
        allowed: &'a HashSet<FVarId>,
        found: Option<FVarId>,
    }
    impl ExprVisitor for Finder<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if MetaState::from_fvar(id).is_some() {
                return;
            }
            if self.found.is_none() && !self.allowed.contains(&id) {
                self.found = Some(id);
            }
        }
    }
    let mut f = Finder {
        allowed,
        found: None,
    };
    f.visit_expr(expr);
    f.found
}

/// Replace occurrences of `fvar` in `expr` with `Expr::bvar(idx)`.
fn replace_fvar_with_bvar(expr: &Expr, fvar: FVarId, idx: u32) -> Expr {
    match expr.kind() {
        ExprKind::FVar(id) if *id == fvar => Expr::bvar(idx),
        ExprKind::App(f, a) => Expr::app(
            replace_fvar_with_bvar(f, fvar, idx),
            replace_fvar_with_bvar(a, fvar, idx),
        ),
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            replace_fvar_with_bvar(ty, fvar, idx),
            replace_fvar_with_bvar(body, fvar, idx + 1),
        ),
        ExprKind::Pi(bd, dom, cod) => Expr::pi(
            *bd,
            replace_fvar_with_bvar(dom, fvar, idx),
            replace_fvar_with_bvar(cod, fvar, idx + 1),
        ),
        ExprKind::Let(n, ty, val, body, non_dep) => Expr::let_named(
            n.clone(),
            replace_fvar_with_bvar(ty, fvar, idx),
            replace_fvar_with_bvar(val, fvar, idx),
            replace_fvar_with_bvar(body, fvar, idx + 1),
            *non_dep,
        ),
        _ => expr.clone(),
    }
}
