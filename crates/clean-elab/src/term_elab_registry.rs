// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! User-defined term elaborator registration for Lean 5.
//!
//! Provides a registry for custom term elaborators, enabling users to extend
//! how expressions are elaborated via `@[term_elab myKind]`. Each syntax kind
//! can have multiple handlers sorted by priority (higher priority first).
//!
//! # Architecture
//!
//! The registry stores [`TermElabEntry`] values in a `HashMap<String, Vec<_>>`
//! keyed by syntax kind name. When elaboration encounters a syntax kind with
//! registered handlers, it tries each handler in priority order until one
//! succeeds.
//!
//! This mirrors Lean 4's `@[term_elab]` attribute from
//! `Lean.Elab.Term.Basic` where multiple elaborators can be registered for the
//! same syntax kind and are tried in priority order.
//!
//! # Example
//!
//! ```
//! use clean_elab::term_elab_registry::{TermElabRegistry, TermElabEntry};
//! use std::sync::Arc;
//!
//! let mut registry = TermElabRegistry::new();
//! registry.register("myKind", TermElabEntry {
//!     syntax_kind: "myKind".to_owned(),
//!     handler: Arc::new(|_expr, _expected_ty, _ctx| {
//!         Err(clean_elab::ElabError::NotImplemented("demo".into()))
//!     }),
//!     priority: 1000,
//! });
//! assert!(registry.is_registered("myKind"));
//! ```

use std::collections::HashMap;
use std::sync::Arc;

use crate::infer::ElabCtx;
use crate::ElabError;
use clean_kernel::Expr;
use clean_parser::SurfaceExpr;

/// Callback type for user-defined term elaborators.
///
/// Parameters:
/// - `expr`: the surface expression to elaborate
/// - `expected_type`: optional expected type for bidirectional checking
/// - `ctx`: the mutable elaboration context
///
/// Returns the elaborated kernel `Expr` on success, or an `ElabError` on
/// failure. When a handler returns an error, the registry tries the next
/// handler in priority order.
pub type TermElabFn =
    dyn Fn(&SurfaceExpr, Option<&Expr>, &mut ElabCtx<'_>) -> Result<Expr, ElabError> + Send + Sync;

/// A registered term elaborator entry.
///
/// Each entry associates a syntax kind with a handler function and a priority.
/// Multiple entries can share the same syntax kind; they are tried in
/// descending priority order (higher numeric value = tried first).
pub struct TermElabEntry {
    /// The syntax kind this elaborator handles (e.g., `"myKind"`).
    pub syntax_kind: String,
    /// The elaboration handler function.
    pub handler: Arc<TermElabFn>,
    /// Priority for dispatch ordering. Higher values are tried first.
    /// Default priority for builtin elaborators is 1000.
    pub priority: u32,
}

impl Clone for TermElabEntry {
    fn clone(&self) -> Self {
        Self {
            syntax_kind: self.syntax_kind.clone(),
            handler: Arc::clone(&self.handler),
            priority: self.priority,
        }
    }
}

impl std::fmt::Debug for TermElabEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TermElabEntry")
            .field("syntax_kind", &self.syntax_kind)
            .field("priority", &self.priority)
            .field("handler", &"<fn>")
            .finish()
    }
}

/// Default priority for builtin term elaborators.
pub(crate) const DEFAULT_PRIORITY: u32 = 1000;

/// Registry of user-defined term elaborators, keyed by syntax kind.
///
/// Constructed via [`TermElabRegistry::new`] which pre-registers handlers for
/// common syntax kinds (ident, app, lambda, etc.). Users can register
/// additional handlers via [`TermElabRegistry::register`].
///
/// When multiple handlers are registered for the same kind, they are stored
/// in descending priority order and tried sequentially during elaboration.
pub struct TermElabRegistry {
    entries: HashMap<String, Vec<TermElabEntry>>,
}

impl std::fmt::Debug for TermElabRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TermElabRegistry")
            .field("kind_count", &self.entries.len())
            .field("kinds", &self.entries.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl TermElabRegistry {
    /// Create a new registry with builtin elaborators pre-registered.
    ///
    /// Pre-registers handlers for common syntax kinds at [`DEFAULT_PRIORITY`]:
    /// `ident`, `app`, `lambda`, `pi`, `arrow`, `let`, `lit`, `hole`,
    /// `if`, `match`, `do`, `byTactic`.
    #[must_use]
    pub fn new() -> Self {
        let mut registry = Self {
            entries: HashMap::new(),
        };
        register_builtin_elaborators(&mut registry);
        registry
    }

    /// Register a term elaborator for a given syntax kind.
    ///
    /// Inserts the entry into the handler list for `kind`, maintaining
    /// descending priority order. Multiple handlers per kind are supported.
    ///
    /// # Arguments
    ///
    /// - `kind`: the syntax kind to register for
    /// - `entry`: the elaborator entry (must have `syntax_kind` matching `kind`)
    pub fn register(&mut self, kind: &str, entry: TermElabEntry) {
        let handlers = self.entries.entry(kind.to_owned()).or_default();
        // Insert maintaining descending priority order
        let pos = handlers
            .iter()
            .position(|e| e.priority < entry.priority)
            .unwrap_or(handlers.len());
        handlers.insert(pos, entry);
    }

    /// Try to elaborate an expression using registered handlers for `kind`.
    ///
    /// Tries each handler in descending priority order. Returns the result
    /// from the first handler that succeeds. If all handlers fail, returns
    /// the error from the last handler tried. If no handlers are registered,
    /// returns `None`.
    ///
    /// # Arguments
    ///
    /// - `kind`: the syntax kind to look up
    /// - `expr`: the surface expression to elaborate
    /// - `expected_type`: optional expected type for bidirectional checking
    /// - `ctx`: the mutable elaboration context
    #[must_use = "elaboration result should be checked"]
    pub fn elaborate(
        &self,
        kind: &str,
        expr: &SurfaceExpr,
        expected_type: Option<&Expr>,
        ctx: &mut ElabCtx<'_>,
    ) -> Option<Result<Expr, ElabError>> {
        let handlers = self.entries.get(kind)?;
        if handlers.is_empty() {
            return None;
        }

        let mut last_err = None;
        for entry in handlers {
            match (entry.handler)(expr, expected_type, ctx) {
                Ok(result) => return Some(Ok(result)),
                Err(e) => last_err = Some(e),
            }
        }

        // All handlers failed; return the last error
        last_err.map(Err)
    }

    /// Check whether any handlers are registered for a syntax kind.
    #[must_use]
    pub fn is_registered(&self, kind: &str) -> bool {
        self.entries.get(kind).is_some_and(|v| !v.is_empty())
    }

    /// Look up all handlers for a syntax kind, in priority order.
    #[must_use]
    pub fn get_handlers(&self, kind: &str) -> Option<&[TermElabEntry]> {
        self.entries.get(kind).map(|v| v.as_slice())
    }

    /// Number of distinct syntax kinds with registered handlers.
    #[must_use]
    pub fn kind_count(&self) -> usize {
        self.entries.len()
    }

    /// Total number of registered handler entries across all kinds.
    #[must_use]
    pub fn handler_count(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Iterate over all registered syntax kinds.
    pub fn kinds(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(|s| s.as_str())
    }

    /// Get the highest-priority user handler for a syntax kind, if any exist
    /// above the default builtin priority.
    ///
    /// Returns a cloned `Arc` to the handler function so the caller can drop
    /// the borrow on the registry before invoking the handler with `&mut ElabCtx`.
    /// This avoids the borrow conflict between registry lookup and mutable context.
    ///
    /// Returns `None` if no handlers above `DEFAULT_PRIORITY` are registered,
    /// meaning only builtin stubs exist and the hardcoded dispatch should proceed.
    #[must_use]
    pub fn get_user_handler(&self, kind: &str) -> Option<Arc<TermElabFn>> {
        let handlers = self.entries.get(kind)?;
        // Handlers are sorted by descending priority. The first handler with
        // priority > DEFAULT_PRIORITY is a user override.
        handlers
            .first()
            .filter(|e| e.priority > DEFAULT_PRIORITY)
            .map(|e| Arc::clone(&e.handler))
    }
}

impl Default for TermElabRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Builtin syntax kinds pre-registered at construction.
///
/// These correspond to the `SurfaceExpr` variants handled by the hardcoded
/// dispatch in `ElabCtx::elaborate_surface_inner`. The builtin handlers
/// return `NotImplemented` -- actual elaboration is still handled by the
/// hardcoded match. The entries exist so that `is_registered` returns `true`
/// and user-defined handlers at higher priority can override them.
///
/// The naming convention follows Lean 4's syntax node kinds (lowercase,
/// camelCase) as mapped by `surface_expr_kind_name()` in `infer/mod.rs`.
pub(crate) const BUILTIN_KINDS: &[&str] = &[
    "ident",
    "syntheticSorry",
    "universe",
    "app",
    "lambda",
    "patternMatchLambda",
    "pi",
    "arrow",
    "let",
    "letRec",
    "letPattern",
    "lit",
    "paren",
    "hole",
    "ascription",
    "outParam",
    "semiOutParam",
    "if",
    "ifLet",
    "ifDecidable",
    "match",
    "proj",
    "universeInst",
    "namedArg",
    "syntaxQuote",
    "qQuotation",
    "qAntiquot",
    "explicit",
    "structLit",
    "byTactic",
    "calcBlock",
    "do",
    "liftMethod",
    "interpolatedStr",
];

/// Register the builtin elaborator stubs for common syntax kinds.
///
/// Each stub returns `ElabError::NotImplemented`, signalling that the
/// hardcoded `ElabCtx::elaborate` dispatch should proceed as normal.
/// User-registered handlers at higher priority will be tried first.
fn register_builtin_elaborators(registry: &mut TermElabRegistry) {
    for &kind in BUILTIN_KINDS {
        let kind_owned = kind.to_owned();
        registry.register(
            kind,
            TermElabEntry {
                syntax_kind: kind_owned.clone(),
                handler: Arc::new(move |_expr, _expected_ty, _ctx| {
                    Err(ElabError::NotImplemented(format!(
                        "builtin term_elab fallback for '{kind_owned}'"
                    )))
                }),
                priority: DEFAULT_PRIORITY,
            },
        );
    }
}

#[cfg(test)]
#[path = "term_elab_registry_tests.rs"]
mod tests;
