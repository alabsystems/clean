// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command elaborator registry.
//!
//! Mirrors Lean 4's `CommandElab` workflow: handlers are registered by syntax
//! kind and priority, and the registry dispatches to the highest-priority
//! handler for each incoming command syntax node.
//!
//! # Example
//!
//! ```
//! use clean_elab::command_elab::{
//!     CommandElabCtx, CommandElabRegistry, Syntax, SyntaxArg,
//! };
//!
//! let mut registry = CommandElabRegistry::new();
//! registry.register("def", |_ctx, _stx| Ok(()), 1000);
//!
//! let ctx = CommandElabCtx::new();
//! let stx = Syntax::new("def", vec![SyntaxArg::Atom("foo".into())]);
//! registry.elaborate(&ctx, &stx).expect("should dispatch to def handler");
//! ```

use crate::error::ElabError;

// =============================================================================
// Syntax representation
// =============================================================================

/// Minimal command syntax tree node.
///
/// Each node carries a `kind` tag (matching Lean 4's `SyntaxNodeKind`) and
/// a list of arguments that are either atomic tokens or nested nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syntax {
    kind: String,
    args: Vec<SyntaxArg>,
}

impl Syntax {
    /// Create a new syntax node.
    #[must_use]
    pub fn new(kind: impl Into<String>, args: Vec<SyntaxArg>) -> Self {
        Self {
            kind: kind.into(),
            args,
        }
    }

    /// The syntax kind tag (e.g. `"def"`, `"theorem"`, `"#check"`).
    #[must_use]
    pub fn kind(&self) -> &str {
        &self.kind
    }

    /// Child arguments of this node.
    #[must_use]
    pub fn args(&self) -> &[SyntaxArg] {
        &self.args
    }
}

/// A single argument inside a [`Syntax`] node.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SyntaxArg {
    /// Leaf token (identifier, literal, keyword, etc.).
    Atom(String),
    /// Nested syntax subtree.
    Node(Syntax),
}

// =============================================================================
// Elaboration context
// =============================================================================

/// Context passed to every command elaboration handler.
///
/// Provides read-only access to the kernel environment and elaboration
/// options. This is the lightweight context for registered command handlers
/// that do not need mutable access to the full `ElabCtx`.
///
/// For handlers that need mutable elaboration context (e.g., `def`, `theorem`),
/// the hardcoded `elab_decl_inner` dispatch in `elaborate_decl.rs` calls
/// `ElabCtx` methods directly.
#[derive(Debug, Clone)]
pub struct CommandElabCtx {
    /// Name of the current environment (for diagnostic messages).
    /// Will be replaced with `&Environment` reference when command handlers
    /// are upgraded to take full environment access.
    pub env_name: String,
    /// Placeholder for elaboration options.
    pub options: (),
}

impl Default for CommandElabCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl CommandElabCtx {
    /// Create a context with default fields.
    #[must_use]
    pub fn new() -> Self {
        Self {
            env_name: String::new(),
            options: (),
        }
    }
}

// =============================================================================
// Handler type and registry entry
// =============================================================================

/// Handler function signature for command elaboration.
///
/// Receives an immutable context and a reference to the syntax node,
/// returning `Ok(())` on success or an [`ElabError`] on failure.
pub type CommandElabHandler = fn(&CommandElabCtx, &Syntax) -> Result<(), ElabError>;

/// A registered command elaboration entry.
///
/// Associates a handler function with its syntax kind and a numeric priority.
/// When multiple handlers are registered for the same kind, the entry with
/// the highest priority value wins.
#[derive(Clone)]
pub struct CommandElabEntry {
    syntax_kind: String,
    handler: CommandElabHandler,
    priority: u32,
}

impl CommandElabEntry {
    /// The syntax kind this entry handles.
    #[must_use]
    pub fn syntax_kind(&self) -> &str {
        &self.syntax_kind
    }

    /// The handler function pointer.
    #[must_use]
    pub fn handler(&self) -> CommandElabHandler {
        self.handler
    }

    /// Numeric priority (higher = preferred).
    #[must_use]
    pub fn priority(&self) -> u32 {
        self.priority
    }
}

// Manual Debug: fn pointers don't derive Debug well.
impl std::fmt::Debug for CommandElabEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CommandElabEntry")
            .field("syntax_kind", &self.syntax_kind)
            .field("priority", &self.priority)
            .finish_non_exhaustive()
    }
}

// =============================================================================
// Registry
// =============================================================================

/// Registry of command elaboration handlers, keyed by syntax kind.
///
/// Handlers are stored in a `Vec` per kind and sorted so that the
/// highest-priority entry is always at index 0.
#[derive(Debug, Clone, Default)]
pub struct CommandElabRegistry {
    /// Map from syntax kind to entries sorted by descending priority.
    entries: hashbrown::HashMap<String, Vec<CommandElabEntry>>,
}

impl CommandElabRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a command elaboration handler.
    ///
    /// If multiple handlers share the same `kind`, the one with the highest
    /// `priority` value will be returned by [`get_elaborator`](Self::get_elaborator).
    pub fn register(
        &mut self,
        kind: impl Into<String>,
        handler: CommandElabHandler,
        priority: u32,
    ) {
        let kind = kind.into();
        let entry = CommandElabEntry {
            syntax_kind: kind.clone(),
            handler,
            priority,
        };
        let bucket = self.entries.entry(kind).or_default();
        bucket.push(entry);
        // Keep highest priority at front.
        bucket.sort_by_key(|b| std::cmp::Reverse(b.priority));
    }

    /// Look up the highest-priority elaboration entry for `kind`.
    #[must_use]
    pub fn get_elaborator(&self, kind: &str) -> Option<&CommandElabEntry> {
        self.entries.get(kind).and_then(|v| v.first())
    }

    /// Dispatch to the registered handler for `syntax.kind()`.
    ///
    /// Returns [`ElabError::NotImplemented`] when no handler is registered
    /// for the syntax kind.
    pub fn elaborate(&self, ctx: &CommandElabCtx, syntax: &Syntax) -> Result<(), ElabError> {
        let entry = self.get_elaborator(syntax.kind()).ok_or_else(|| {
            ElabError::NotImplemented(format!(
                "no command elaborator registered for kind '{}'",
                syntax.kind()
            ))
        })?;
        (entry.handler)(ctx, syntax)
    }

    /// Total number of registered syntax kinds.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the registry contains any handlers.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Total number of handler entries across all kinds.
    ///
    /// Useful for diagnostics; counts duplicate-kind registrations.
    #[must_use]
    pub fn total_entries(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }

    /// Iterator over all registered syntax kinds.
    pub fn kinds(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(String::as_str)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -- helpers --------------------------------------------------------------

    fn noop_handler(_ctx: &CommandElabCtx, _stx: &Syntax) -> Result<(), ElabError> {
        Ok(())
    }

    fn failing_handler(_ctx: &CommandElabCtx, _stx: &Syntax) -> Result<(), ElabError> {
        Err(ElabError::NotImplemented("intentional test failure".into()))
    }

    fn make_syntax(kind: &str) -> Syntax {
        Syntax::new(kind, vec![])
    }

    // -- construction ---------------------------------------------------------

    #[test]
    fn test_syntax_new_and_accessors() {
        let stx = Syntax::new(
            "theorem",
            vec![
                SyntaxArg::Atom("my_thm".into()),
                SyntaxArg::Node(Syntax::new("type", vec![])),
            ],
        );
        assert_eq!(stx.kind(), "theorem");
        assert_eq!(stx.args().len(), 2);
        assert_eq!(stx.args()[0], SyntaxArg::Atom("my_thm".into()));
    }

    #[test]
    fn test_command_elab_ctx_default() {
        let ctx = CommandElabCtx::default();
        assert!(ctx.env_name.is_empty());
        assert_eq!(ctx.options, ());
    }

    #[test]
    fn test_command_elab_entry_accessors() {
        let mut reg = CommandElabRegistry::new();
        reg.register("def", noop_handler, 500);
        let entry = reg.get_elaborator("def").expect("should find def");
        assert_eq!(entry.syntax_kind(), "def");
        assert_eq!(entry.priority(), 500);
        // Round-trip the handler: calling it should succeed.
        let ctx = CommandElabCtx::new();
        let stx = make_syntax("def");
        (entry.handler())(&ctx, &stx).expect("noop should succeed");
    }

    // -- registration ---------------------------------------------------------

    #[test]
    fn test_register_single_handler() {
        let mut reg = CommandElabRegistry::new();
        assert!(reg.is_empty());
        assert_eq!(reg.len(), 0);

        reg.register("def", noop_handler, 1000);
        assert!(!reg.is_empty());
        assert_eq!(reg.len(), 1);
        assert_eq!(reg.total_entries(), 1);
    }

    #[test]
    fn test_register_multiple_distinct_kinds() {
        let mut reg = CommandElabRegistry::new();
        reg.register("def", noop_handler, 1000);
        reg.register("theorem", noop_handler, 1000);
        reg.register("#check", noop_handler, 500);

        assert_eq!(reg.len(), 3);
        assert_eq!(reg.total_entries(), 3);
        assert!(reg.get_elaborator("def").is_some());
        assert!(reg.get_elaborator("theorem").is_some());
        assert!(reg.get_elaborator("#check").is_some());
    }

    // -- priority ordering ----------------------------------------------------

    #[test]
    fn test_priority_highest_wins() {
        let mut reg = CommandElabRegistry::new();

        // Register a failing handler at low priority, then a noop at high priority.
        reg.register("def", failing_handler, 100);
        reg.register("def", noop_handler, 999);

        assert_eq!(reg.len(), 1); // One kind.
        assert_eq!(reg.total_entries(), 2); // Two entries.

        let entry = reg.get_elaborator("def").expect("should find def");
        assert_eq!(entry.priority(), 999);

        // Dispatching should use the high-priority noop, not the failing one.
        let ctx = CommandElabCtx::new();
        let stx = make_syntax("def");
        reg.elaborate(&ctx, &stx)
            .expect("high-priority noop should win");
    }

    #[test]
    fn test_priority_order_independent_of_insertion() {
        // Insert high priority first, then low.
        let mut reg = CommandElabRegistry::new();
        reg.register("theorem", noop_handler, 2000);
        reg.register("theorem", failing_handler, 100);

        let entry = reg.get_elaborator("theorem").expect("should find theorem");
        assert_eq!(entry.priority(), 2000);
    }

    // -- dispatch -------------------------------------------------------------

    #[test]
    fn test_elaborate_dispatches_to_handler() {
        let mut reg = CommandElabRegistry::new();
        reg.register("def", noop_handler, 1000);

        let ctx = CommandElabCtx::new();
        let stx = make_syntax("def");
        reg.elaborate(&ctx, &stx)
            .expect("noop handler should succeed");
    }

    #[test]
    fn test_elaborate_propagates_handler_error() {
        let mut reg = CommandElabRegistry::new();
        reg.register("bad", failing_handler, 1000);

        let ctx = CommandElabCtx::new();
        let stx = make_syntax("bad");
        let err = reg.elaborate(&ctx, &stx).unwrap_err();
        assert!(matches!(err, ElabError::NotImplemented(_)));
    }

    #[test]
    fn test_elaborate_missing_handler_returns_error() {
        let reg = CommandElabRegistry::new();
        let ctx = CommandElabCtx::new();
        let stx = make_syntax("nonexistent");

        let err = reg.elaborate(&ctx, &stx).unwrap_err();
        match &err {
            ElabError::NotImplemented(msg) => {
                assert!(
                    msg.contains("nonexistent"),
                    "error should mention the missing kind: {msg}",
                );
            }
            other => panic!("expected NotImplemented, got {other:?}"),
        }
    }

    // -- kinds iterator -------------------------------------------------------

    #[test]
    fn test_kinds_iterator() {
        let mut reg = CommandElabRegistry::new();
        reg.register("def", noop_handler, 1000);
        reg.register("theorem", noop_handler, 1000);

        let mut kinds: Vec<&str> = reg.kinds().collect();
        kinds.sort();
        assert_eq!(kinds, vec!["def", "theorem"]);
    }

    // -- Debug ----------------------------------------------------------------

    #[test]
    fn test_entry_debug_does_not_panic() {
        let mut reg = CommandElabRegistry::new();
        reg.register("def", noop_handler, 42);
        let entry = reg.get_elaborator("def").unwrap();
        let dbg = format!("{entry:?}");
        assert!(dbg.contains("def"));
        assert!(dbg.contains("42"));
    }

    // -- Syntax equality ------------------------------------------------------

    #[test]
    fn test_syntax_eq() {
        let a = Syntax::new("def", vec![SyntaxArg::Atom("x".into())]);
        let b = Syntax::new("def", vec![SyntaxArg::Atom("x".into())]);
        let c = Syntax::new("def", vec![SyntaxArg::Atom("y".into())]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn test_syntax_arg_node_variant() {
        let inner = Syntax::new("type", vec![]);
        let arg = SyntaxArg::Node(inner.clone());
        assert_eq!(arg, SyntaxArg::Node(inner));
    }
}
