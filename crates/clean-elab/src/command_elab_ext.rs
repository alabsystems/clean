// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended command elaboration: attribute processing, mutual grouping,
//! scoping, deferral, error recovery, doc comments, tracing, visibility,
//! noncomputable handling, and ordering validation.
//!
//! Lean 4 reference: `src/Lean/Elab/Command.lean`.

use clean_kernel::Name;

use crate::error::ElabError;

// =============================================================================
// Declaration attributes
// =============================================================================

/// Known declaration attributes from Lean 4's `@[...]` syntax.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum DeclAttribute {
    /// `@[simp]` with optional priority.
    Simp(Option<u32>),
    /// `@[inline]`
    Inline,
    /// `@[reducible]`
    Reducible,
    /// `@[irreducible]`
    Irreducible,
    /// `@[instance]` with optional priority.
    Instance(Option<u32>),
    /// `@[extern "name"]`
    Extern(String),
    /// `@[specialize]`
    Specialize,
    /// `@[nospecialize]`
    Nospecialize,
    /// `@[macro_inline]`
    MacroInline,
    /// `@[csimp]`
    Csimp,
    /// Unknown / user-defined attribute.
    Custom(String),
}

/// Parse an attribute name and optional arguments into a [`DeclAttribute`].
#[must_use]
pub(crate) fn parse_attribute(name: &str, args: &[String]) -> DeclAttribute {
    match name {
        "simp" => {
            let prio = args.first().and_then(|s| s.parse::<u32>().ok());
            DeclAttribute::Simp(prio)
        }
        "inline" => DeclAttribute::Inline,
        "reducible" => DeclAttribute::Reducible,
        "irreducible" => DeclAttribute::Irreducible,
        "instance" => {
            let prio = args.first().and_then(|s| s.parse::<u32>().ok());
            DeclAttribute::Instance(prio)
        }
        "extern" => {
            let extern_name = args.first().cloned().unwrap_or_default();
            DeclAttribute::Extern(extern_name)
        }
        "specialize" => DeclAttribute::Specialize,
        "nospecialize" => DeclAttribute::Nospecialize,
        "macro_inline" => DeclAttribute::MacroInline,
        "csimp" => DeclAttribute::Csimp,
        other => DeclAttribute::Custom(other.to_owned()),
    }
}

/// Validate that a set of attributes has no conflicts.
pub(crate) fn validate_attributes(attrs: &[DeclAttribute]) -> Result<(), ElabError> {
    let has_reducible = attrs.iter().any(|a| matches!(a, DeclAttribute::Reducible));
    let has_irreducible = attrs
        .iter()
        .any(|a| matches!(a, DeclAttribute::Irreducible));
    if has_reducible && has_irreducible {
        return Err(ElabError::Unsupported {
            feature: "conflicting attributes: @[reducible] and @[irreducible]".to_owned(),
        });
    }
    let has_specialize = attrs.iter().any(|a| matches!(a, DeclAttribute::Specialize));
    let has_nospecialize = attrs
        .iter()
        .any(|a| matches!(a, DeclAttribute::Nospecialize));
    if has_specialize && has_nospecialize {
        return Err(ElabError::Unsupported {
            feature: "conflicting attributes: @[specialize] and @[nospecialize]".to_owned(),
        });
    }
    Ok(())
}

// =============================================================================
// Mutual declaration grouping
// =============================================================================

/// Kind of declaration that participates in mutual blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MutualDeclKind {
    Def,
    Theorem,
    Inductive,
}

/// A declaration header for mutual-block detection.
#[derive(Debug, Clone)]
pub(crate) struct DeclHeader {
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) name: String,
    pub(crate) kind: MutualDeclKind,
}

/// Group consecutive declaration headers of the same kind into mutual blocks.
#[must_use]
pub(crate) fn group_mutual_decls(headers: &[DeclHeader]) -> Vec<Vec<usize>> {
    if headers.is_empty() {
        return Vec::new();
    }
    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut current_group = vec![0usize];
    let mut current_kind = headers[0].kind;

    for (i, header) in headers.iter().enumerate().skip(1) {
        if header.kind == current_kind {
            current_group.push(i);
        } else {
            groups.push(std::mem::take(&mut current_group));
            current_group.push(i);
            current_kind = header.kind;
        }
    }
    if !current_group.is_empty() {
        groups.push(current_group);
    }
    groups
}

// =============================================================================
// Section / namespace scoping
// =============================================================================

/// Apply a namespace prefix to a declaration name.
///
/// If `ns` is empty or anonymous, returns the name unchanged.
#[must_use]
pub(crate) fn apply_namespace_prefix(ns: &Name, decl_name: &Name) -> Name {
    if ns.is_anon() {
        return decl_name.clone();
    }
    let qualified = format!("{ns}.{decl_name}");
    Name::from_string(&qualified)
}

/// Return the section variable names relevant for scoped declarations.
#[must_use]
pub(crate) fn section_variable_names(section_vars: &[String], _ns: &Name) -> Vec<String> {
    section_vars.to_vec()
}

// =============================================================================
// Deferred elaboration
// =============================================================================

/// A deferred command waiting for later elaboration.
#[derive(Debug, Clone)]
pub(crate) struct DeferredCommand {
    /// Unique identifier for ordering.
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) id: u64,
    /// Declaration name (for dependency tracking).
    pub(crate) name: Name,
    /// Reason the command was deferred.
    pub(crate) reason: DeferralReason,
}

/// Reason a command was deferred.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum DeferralReason {
    /// Forward reference to a declaration not yet elaborated.
    ForwardReference(String),
    /// Waiting for type class instance resolution.
    InstanceResolution,
    /// Explicit user request (e.g., `#later`).
    Explicit,
}

/// Queue of deferred commands.
#[derive(Debug, Clone, Default)]
pub(crate) struct DeferralQueue {
    commands: Vec<DeferredCommand>,
    next_id: u64,
}

impl DeferralQueue {
    /// Create an empty deferral queue.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Enqueue a command for deferred elaboration.
    pub(crate) fn defer(&mut self, name: Name, reason: DeferralReason) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.commands.push(DeferredCommand { id, name, reason });
        id
    }

    /// Drain all deferred commands, returning them in FIFO order.
    pub(crate) fn drain(&mut self) -> Vec<DeferredCommand> {
        std::mem::take(&mut self.commands)
    }

    /// Number of commands currently deferred.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.commands.len()
    }

    /// Whether the queue is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }

    /// Check if a name has a pending deferral.
    #[must_use]
    pub(crate) fn is_deferred(&self, name: &Name) -> bool {
        self.commands.iter().any(|c| &c.name == name)
    }
}

// =============================================================================
// Error recovery
// =============================================================================

/// Result of elaborating a command with error recovery enabled.
#[derive(Debug, Clone)]
pub(crate) struct RecoveredResult {
    /// Commands that elaborated successfully (by index).
    pub(crate) succeeded: Vec<usize>,
    /// Commands that failed with their errors (by index).
    pub(crate) failures: Vec<(usize, ElabError)>,
}

impl RecoveredResult {
    /// Create an empty result.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            succeeded: Vec::new(),
            failures: Vec::new(),
        }
    }

    /// Record a successful elaboration.
    pub(crate) fn record_success(&mut self, index: usize) {
        self.succeeded.push(index);
    }

    /// Record a failed elaboration.
    pub(crate) fn record_failure(&mut self, index: usize, err: ElabError) {
        self.failures.push((index, err));
    }

    /// Total number of commands processed.
    #[must_use]
    pub(crate) fn total(&self) -> usize {
        self.succeeded.len() + self.failures.len()
    }

    /// Whether all commands succeeded.
    #[must_use]
    pub(crate) fn all_succeeded(&self) -> bool {
        self.failures.is_empty()
    }

    /// Number of failures.
    #[must_use]
    pub(crate) fn failure_count(&self) -> usize {
        self.failures.len()
    }
}

/// Elaborate a sequence of fallible operations with error recovery.
///
/// Calls `f` for each index in `0..count`. If `f` returns an error,
/// records it and continues to the next command.
pub(crate) fn elaborate_with_recovery<F>(count: usize, mut f: F) -> RecoveredResult
where
    F: FnMut(usize) -> Result<(), ElabError>,
{
    let mut result = RecoveredResult::new();
    for i in 0..count {
        match f(i) {
            Ok(()) => result.record_success(i),
            Err(e) => result.record_failure(i, e),
        }
    }
    result
}

// =============================================================================
// Doc-comment attachment
// =============================================================================

/// A doc comment associated with a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DocComment {
    /// The declaration name this doc is attached to.
    pub(crate) decl_name: Name,
    /// The documentation text (without leading `---` or `/--`).
    pub(crate) text: String,
}

/// Registry of doc comments, keyed by declaration name.
#[derive(Debug, Clone, Default)]
pub(crate) struct DocCommentRegistry {
    entries: Vec<DocComment>,
}

impl DocCommentRegistry {
    /// Create an empty registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Attach a doc comment to a declaration.
    pub(crate) fn attach(&mut self, decl_name: Name, text: String) {
        self.entries.push(DocComment { decl_name, text });
    }

    /// Look up the doc comment for a declaration.
    #[must_use]
    pub(crate) fn get(&self, name: &Name) -> Option<&str> {
        self.entries
            .iter()
            .rev()
            .find(|e| &e.decl_name == name)
            .map(|e| e.text.as_str())
    }

    /// Total number of doc comments.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// =============================================================================
// Command trace / logging
// =============================================================================

/// A single trace entry for command elaboration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TraceEntry {
    /// Declaration name (or anonymous for non-declaration commands).
    pub(crate) name: Name,
    /// Human-readable description of what happened.
    pub(crate) message: String,
}

/// Accumulator for command elaboration trace messages.
#[derive(Debug, Clone, Default)]
pub(crate) struct CommandTrace {
    entries: Vec<TraceEntry>,
}

impl CommandTrace {
    /// Create an empty trace.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Log a trace entry.
    pub(crate) fn log(&mut self, name: Name, message: impl Into<String>) {
        self.entries.push(TraceEntry {
            name,
            message: message.into(),
        });
    }

    /// Retrieve all trace entries.
    #[must_use]
    pub(crate) fn entries(&self) -> &[TraceEntry] {
        &self.entries
    }

    /// Number of entries.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the trace is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all entries.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

// =============================================================================
// Visibility processing
// =============================================================================
/// Visibility modifier for a declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum Visibility {
    /// No modifier -- visible within and outside the namespace.
    #[default]
    Public,
    /// `protected` -- accessible only with fully qualified name outside
    /// the defining namespace.
    Protected,
    /// `private` -- accessible only within the defining section/namespace.
    Private,
}

/// Validate visibility/declaration-kind compatibility.
pub(crate) fn validate_visibility(vis: Visibility, _decl_kind: &str) -> Result<(), ElabError> {
    // Currently all combinations are valid. This hook exists for future
    // restrictions.
    let _ = vis;
    Ok(())
}

/// Check if a declaration is explicitly marked noncomputable.
#[must_use]
pub(crate) fn is_noncomputable_explicit(modifiers_noncomputable: bool) -> bool {
    modifiers_noncomputable
}

/// Check that all dependency names have already been elaborated.
pub(crate) fn validate_ordering(
    decl_name: &Name,
    dependencies: &[Name],
    elaborated_names: &[Name],
) -> Result<(), ElabError> {
    for dep in dependencies {
        if !elaborated_names.contains(dep) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "declaration '{}' depends on '{}' which has not been elaborated yet",
                    decl_name, dep
                ),
            });
        }
    }
    Ok(())
}

// =============================================================================
// Extended elaboration config
// =============================================================================
/// Configuration for extended command elaboration.
#[derive(Debug, Clone)]
pub(crate) struct CommandElabExtConfig {
    /// Enable error recovery (continue on individual failures).
    pub(crate) error_recovery: bool,
    /// Enable command tracing.
    pub(crate) tracing: bool,
    /// Enable ordering validation.
    pub(crate) validate_ordering: bool,
    /// Maximum number of deferred commands before forcing elaboration.
    pub(crate) max_deferred: usize,
}

impl Default for CommandElabExtConfig {
    fn default() -> Self {
        Self {
            error_recovery: true,
            tracing: false,
            validate_ordering: true,
            max_deferred: 256,
        }
    }
}
