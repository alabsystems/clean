// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! User-extensible elaboration hook system for Lean 5.
//!
//! Provides a phase-based hook registry that allows user-defined callbacks to
//! intercept and customize the elaboration pipeline. Hooks fire at five phases:
//! pre-elaborate, post-elaborate, pre-type-check, post-type-check, and on-error.
//!
//! Each hook receives an [`ElabHookContext`] describing the current elaboration
//! state and returns an [`ElabHookResult`] controlling pipeline flow: continue
//! normally, replace the expression, abort with an error, or skip remaining
//! hooks in the current phase.
//!
//! # Architecture
//!
//! The [`ElabHookRegistry`] stores [`ElabHookEntry`] values in a
//! `HashMap<ElabPhase, Vec<_>>` keyed by phase. Within each phase, hooks are
//! sorted by ascending priority (lower numeric value = runs first). When
//! multiple hooks are registered for the same phase, [`run_hooks`] executes
//! them in order and respects flow-control results.
//!
//! This complements the syntax-kind-based [`TermElabRegistry`] by providing
//! cross-cutting interception points that fire regardless of syntax kind.
//!
//! [`TermElabRegistry`]: crate::term_elab_registry::TermElabRegistry
//! [`run_hooks`]: ElabHookRegistry::run_hooks
//!
//! # Example
//!
//! ```
//! use clean_elab::elab_hooks::{
//!     ElabHookContext, ElabHookEntry, ElabHookRegistry, ElabHookResult, ElabPhase,
//! };
//! use std::sync::Arc;
//!
//! let mut registry = ElabHookRegistry::new();
//! registry.register(ElabHookEntry {
//!     name: "my_hook".to_owned(),
//!     phase: ElabPhase::PreElaborate,
//!     priority: 100,
//!     hook: Arc::new(|_ctx| ElabHookResult::Continue),
//! });
//! assert!(registry.has_hooks(&ElabPhase::PreElaborate));
//! assert_eq!(registry.hook_count(), 1);
//! ```

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::Expr;

// ---------------------------------------------------------------------------
// ElabPhase
// ---------------------------------------------------------------------------

/// A phase in the elaboration pipeline where hooks can fire.
///
/// Phases are ordered to match the natural flow of elaboration:
/// 1. [`PreElaborate`] — before any elaboration begins
/// 2. [`PostElaborate`] — after elaboration, before type checking
/// 3. [`PreTypeCheck`] — before kernel type check
/// 4. [`PostTypeCheck`] — after kernel type check passes
/// 5. [`OnError`] — when elaboration encounters an error
///
/// [`PreElaborate`]: ElabPhase::PreElaborate
/// [`PostElaborate`]: ElabPhase::PostElaborate
/// [`PreTypeCheck`]: ElabPhase::PreTypeCheck
/// [`PostTypeCheck`]: ElabPhase::PostTypeCheck
/// [`OnError`]: ElabPhase::OnError
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ElabPhase {
    /// Before any elaboration begins.
    PreElaborate,
    /// After elaboration, before type checking.
    PostElaborate,
    /// Before kernel type check.
    PreTypeCheck,
    /// After kernel type check passes.
    PostTypeCheck,
    /// When elaboration encounters an error.
    OnError,
}

impl ElabPhase {
    /// All phase variants, useful for iteration.
    pub(crate) const ALL: &'static [ElabPhase] = &[
        ElabPhase::PreElaborate,
        ElabPhase::PostElaborate,
        ElabPhase::PreTypeCheck,
        ElabPhase::PostTypeCheck,
        ElabPhase::OnError,
    ];
}

impl std::fmt::Display for ElabPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PreElaborate => write!(f, "PreElaborate"),
            Self::PostElaborate => write!(f, "PostElaborate"),
            Self::PreTypeCheck => write!(f, "PreTypeCheck"),
            Self::PostTypeCheck => write!(f, "PostTypeCheck"),
            Self::OnError => write!(f, "OnError"),
        }
    }
}

// ---------------------------------------------------------------------------
// ElabHookFn / ElabHookResult
// ---------------------------------------------------------------------------

/// Callback type for elaboration hooks.
///
/// Receives a shared reference to the hook context and returns a result
/// controlling pipeline flow. Callbacks must be `Send + Sync` so registries
/// can be shared across threads.
pub type ElabHookFn = Arc<dyn Fn(&ElabHookContext) -> ElabHookResult + Send + Sync>;

/// Result from a hook invocation, controlling pipeline flow.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ElabHookResult {
    /// Proceed normally; do not alter the expression.
    Continue,
    /// Replace the current expression with the given one.
    Replace(Expr),
    /// Abort elaboration with the given error message.
    Error(String),
    /// Skip remaining hooks in this phase and proceed.
    Skip,
}

// ---------------------------------------------------------------------------
// ElabHookContext
// ---------------------------------------------------------------------------

/// Context passed to elaboration hooks.
///
/// Contains the current expression, expected type, declaration name, and
/// source span (if available). All fields are optional because not every
/// phase has all information available.
#[derive(Debug, Clone)]
pub struct ElabHookContext {
    /// The phase that triggered this hook.
    pub phase: ElabPhase,
    /// The current expression being elaborated, if available.
    pub expr: Option<Expr>,
    /// The expected type for bidirectional checking, if available.
    pub expected_type: Option<Expr>,
    /// The name of the declaration being elaborated, if available.
    pub decl_name: Option<String>,
    /// Source span `(start, end)` of the expression, if available.
    pub source_span: Option<(usize, usize)>,
}

impl ElabHookContext {
    /// Create a minimal context for the given phase.
    #[must_use]
    pub fn new(phase: ElabPhase) -> Self {
        Self {
            phase,
            expr: None,
            expected_type: None,
            decl_name: None,
            source_span: None,
        }
    }

    /// Builder: set the expression.
    #[must_use]
    pub fn with_expr(mut self, expr: Expr) -> Self {
        self.expr = Some(expr);
        self
    }

    /// Builder: set the expected type.
    #[must_use]
    pub fn with_expected_type(mut self, ty: Expr) -> Self {
        self.expected_type = Some(ty);
        self
    }

    /// Builder: set the declaration name.
    #[must_use]
    pub fn with_decl_name(mut self, name: impl Into<String>) -> Self {
        self.decl_name = Some(name.into());
        self
    }

    /// Builder: set the source span.
    #[must_use]
    pub fn with_source_span(mut self, start: usize, end: usize) -> Self {
        self.source_span = Some((start, end));
        self
    }
}

// ---------------------------------------------------------------------------
// ElabHookEntry
// ---------------------------------------------------------------------------

/// A registered elaboration hook entry.
///
/// Each entry associates a named hook with a phase, a priority, and a
/// callback. Within a phase, hooks with lower priority values run first
/// (ascending order).
pub struct ElabHookEntry {
    /// Unique name for this hook (used for removal).
    pub name: String,
    /// The phase at which this hook fires.
    pub phase: ElabPhase,
    /// Priority for execution ordering. Lower values run first.
    pub priority: u32,
    /// The hook callback function.
    pub hook: ElabHookFn,
}

impl Clone for ElabHookEntry {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            phase: self.phase,
            priority: self.priority,
            hook: Arc::clone(&self.hook),
        }
    }
}

impl std::fmt::Debug for ElabHookEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ElabHookEntry")
            .field("name", &self.name)
            .field("phase", &self.phase)
            .field("priority", &self.priority)
            .field("hook", &"<fn>")
            .finish()
    }
}

// ---------------------------------------------------------------------------
// ElabHookRegistry
// ---------------------------------------------------------------------------

/// Registry of user-extensible elaboration hooks, keyed by phase.
///
/// Hooks are stored per-phase in ascending priority order (lower runs first).
/// The registry provides registration, removal, querying, and execution of
/// hooks across the elaboration pipeline.
pub struct ElabHookRegistry {
    hooks: HashMap<ElabPhase, Vec<ElabHookEntry>>,
}

impl std::fmt::Debug for ElabHookRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ElabHookRegistry")
            .field("phase_count", &self.hooks.len())
            .field("total_hooks", &self.hook_count())
            .finish()
    }
}

impl Default for ElabHookRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl ElabHookRegistry {
    /// Create a new, empty hook registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            hooks: HashMap::new(),
        }
    }

    /// Register a hook entry.
    ///
    /// The hook is inserted into the list for its phase, maintaining ascending
    /// priority order (lower priority values run first). If two hooks have the
    /// same priority, the newly registered one is placed after existing ones
    /// (stable insertion).
    pub fn register(&mut self, entry: ElabHookEntry) {
        let phase_hooks = self.hooks.entry(entry.phase).or_default();
        // Insert maintaining ascending priority order (lower = first).
        // Use position of first element with strictly greater priority for
        // stable ordering among equal priorities.
        let pos = phase_hooks
            .iter()
            .position(|e| e.priority > entry.priority)
            .unwrap_or(phase_hooks.len());
        phase_hooks.insert(pos, entry);
    }

    /// Run all hooks for the given phase with the provided context.
    ///
    /// Hooks execute in ascending priority order. Processing stops early on:
    /// - [`ElabHookResult::Replace`] — returns the replacement immediately
    /// - [`ElabHookResult::Error`] — returns the error immediately
    /// - [`ElabHookResult::Skip`] — stops processing, returns `Continue`
    /// - [`ElabHookResult::Continue`] — proceeds to the next hook
    ///
    /// If no hooks are registered for the phase, or all hooks return
    /// `Continue`, the overall result is `Continue`.
    #[must_use]
    pub fn run_hooks(&self, phase: ElabPhase, ctx: &ElabHookContext) -> ElabHookResult {
        let Some(phase_hooks) = self.hooks.get(&phase) else {
            return ElabHookResult::Continue;
        };

        for entry in phase_hooks {
            let result = (entry.hook)(ctx);
            match &result {
                ElabHookResult::Continue => continue,
                ElabHookResult::Replace(_) | ElabHookResult::Error(_) => return result,
                ElabHookResult::Skip => return ElabHookResult::Continue,
            }
        }

        ElabHookResult::Continue
    }

    /// Remove a hook by name.
    ///
    /// Searches all phases and removes the first hook with the given name.
    /// Returns `true` if a hook was found and removed, `false` otherwise.
    pub fn remove(&mut self, name: &str) -> bool {
        for phase_hooks in self.hooks.values_mut() {
            if let Some(pos) = phase_hooks.iter().position(|e| e.name == name) {
                phase_hooks.remove(pos);
                return true;
            }
        }
        false
    }

    /// Get all hooks registered for a phase, in priority order.
    #[must_use]
    pub fn hooks_for_phase(&self, phase: &ElabPhase) -> Vec<&ElabHookEntry> {
        self.hooks
            .get(phase)
            .map(|hooks| hooks.iter().collect())
            .unwrap_or_default()
    }

    /// Check if any hooks are registered for a phase.
    #[must_use]
    pub fn has_hooks(&self, phase: &ElabPhase) -> bool {
        self.hooks.get(phase).is_some_and(|hooks| !hooks.is_empty())
    }

    /// Remove all hooks from the registry.
    pub fn clear(&mut self) {
        self.hooks.clear();
    }

    /// Total number of hooks across all phases.
    #[must_use]
    pub fn hook_count(&self) -> usize {
        self.hooks.values().map(|v| v.len()).sum()
    }
}

#[cfg(test)]
#[path = "elab_hooks_tests.rs"]
mod tests;
