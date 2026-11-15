// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in observations of actual term elaboration, separate from hole metadata.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use clean_kernel::{Environment, Expr};
use clean_parser::Span;

use crate::tactic::display::{format_local_context, ExprFormatter};
use crate::tactic::LocalDecl;

/// A frontend-local expected-sort constraint, separate from kernel metavariables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SortGoalId(u64);

/// A source term in the local/metavariable context that elaborated it.
/// These observations do not change registration or assert proof validity.
#[derive(Debug, Clone)]
pub struct TermContext {
    pub expr: Expr,
    /// The actual target supplied to elaboration or its accepted body check.
    pub expected_type: Option<Expr>,
    /// An unresolved expected sort retained by a literal-sort elaborator.
    /// `type_` still records the independently inferred type.
    pub unresolved_sort_goal: Option<SortGoalId>,
    /// The instantiated expected type, or the inferred type of `expr`.
    pub type_: Expr,
    /// Original identities/types/values, with source-backed presentation names
    /// for inaccessible implicit-lambda locals.
    pub local_context: Vec<LocalDecl>,
    /// The expression declares the last local, which is hidden in its goal.
    pub is_binder: bool,
}

impl TermContext {
    /// Render the same captured identities in hypotheses and target.
    #[must_use]
    pub fn render_goal(&self, env: &Environment) -> String {
        let locals = if self.is_binder {
            &self.local_context[..self.local_context.len().saturating_sub(1)]
        } else {
            &self.local_context
        };
        let config = ExprFormatter::default().with_local_names(
            locals
                .iter()
                .map(|local| (local.fvar, local.name.to_string())),
        );
        let context = format_local_context(locals, env, &config);
        let target = self.unresolved_sort_goal.map_or_else(
            || config.format(&self.type_),
            |id| format!("Sort ?u.{}", id.0),
        );
        if context.is_empty() {
            format!("⊢ {target}")
        } else {
            format!("{context}\n⊢ {target}")
        }
    }
}

/// One actual source-info node. Non-term nodes prevent a surrounding term
/// from answering at tactic syntax; parent links retain elaboration structure.
#[derive(Debug, Clone)]
pub struct SourceInfo {
    pub id: u64,
    pub parent_id: Option<u64>,
    pub span: Span,
    /// An identifier application head whose own goal is superseded by the app.
    pub application_head: Option<Span>,
    pub is_variable: bool,
    pub is_partial: bool,
    pub term: Option<TermContext>,
}

/// One frontend's collection, absent from ordinary compiler/checker runs.
#[derive(Debug, Clone, Default)]
pub struct TermInfoCapture {
    infos: Arc<Mutex<Vec<SourceInfo>>>,
    next_id: Arc<AtomicU64>,
    next_sort_goal: Arc<AtomicU64>,
}

#[derive(Debug, thiserror::Error)]
#[error("term-info observation collector is poisoned")]
pub struct TermInfoCaptureError;

impl TermInfoCapture {
    pub(crate) fn declaration_scope(&self) -> Self {
        Self {
            infos: Arc::clone(&self.infos),
            next_id: Arc::clone(&self.next_id),
            next_sort_goal: Arc::new(AtomicU64::new(0)),
        }
    }

    pub(crate) fn fresh_sort_goal(&self) -> Option<SortGoalId> {
        let mut previous = self.next_sort_goal.load(Ordering::Relaxed);
        loop {
            let next = previous.checked_add(1)?;
            match self.next_sort_goal.compare_exchange_weak(
                previous,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Some(SortGoalId(next)),
                Err(actual) => previous = actual,
            }
        }
    }

    pub(crate) fn fresh_id(&self) -> u64 {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }

    pub(crate) fn record(&self, infos: Vec<SourceInfo>) {
        // A poisoned display collector must not change an elaboration verdict.
        // take() retains its unavailable state rather than reporting success.
        if let Ok(mut captured) = self.infos.lock() {
            captured.extend(infos);
        }
    }

    /// Drain this run's finalized observations.
    pub fn take(&self) -> Result<Vec<SourceInfo>, TermInfoCaptureError> {
        let mut infos = self.infos.lock().map_err(|_| TermInfoCaptureError)?;
        Ok(std::mem::take(&mut *infos))
    }
}
