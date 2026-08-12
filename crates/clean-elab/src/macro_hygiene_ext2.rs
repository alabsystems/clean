// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended macro hygiene: scope stamping, name resolution in macro context,
//! syntax quotation hygiene, anti-quotation handling, macro-generated binding
//! detection, nested scope merging, unhygienic escape, and violation reporting.
//!
//! Builds on [`crate::macro_hygiene`] (basic hygiene tracking) and
//! [`crate::macro_hygiene_ext`] (scope coloring / alpha-rename / violation
//! checking on kernel `Expr`).  This module adds the higher-level policy layer
//! that a macro expander needs at elaboration time.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::Name;

static GLOBAL_SCOPE_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Unique identifier for a macro expansion boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ScopeStamp(u64);

impl ScopeStamp {
    #[must_use]
    pub(crate) fn root() -> Self {
        Self(0)
    }
    #[must_use]
    pub(crate) fn fresh() -> Self {
        Self(GLOBAL_SCOPE_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
    #[must_use]
    pub(crate) fn id(self) -> u64 {
        self.0
    }
    #[must_use]
    pub(crate) fn is_root(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for ScopeStamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "scope#{}", self.0)
    }
}

/// Hygiene violation kinds (extended).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Ext2ViolationKind {
    /// Name leaked across a hygiene boundary.
    ScopeLeak,
    /// Macro-generated binding shadows a user binding.
    MacroBindingShadow,
    /// Anti-quotation splice crosses incompatible scopes.
    AntiQuoteScopeMismatch,
    /// Unresolved name in macro context.
    UnresolvedInMacro,
    /// Unhygienic escape used (tracked, not an error).
    UnhygienicEscape,
}

impl fmt::Display for Ext2ViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ScopeLeak => f.write_str("ScopeLeak"),
            Self::MacroBindingShadow => f.write_str("MacroBindingShadow"),
            Self::AntiQuoteScopeMismatch => f.write_str("AntiQuoteScopeMismatch"),
            Self::UnresolvedInMacro => f.write_str("UnresolvedInMacro"),
            Self::UnhygienicEscape => f.write_str("UnhygienicEscape"),
        }
    }
}

/// A recorded hygiene violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Ext2Violation {
    pub(crate) name: Name,
    pub(crate) scope: ScopeStamp,
    pub(crate) kind: Ext2ViolationKind,
    pub(crate) message: String,
}

/// Errors returned by the ext2 hygiene API.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum HygieneExt2Error {
    #[error("unresolved name `{name}` in macro scope {scope}")]
    Unresolved { name: String, scope: ScopeStamp },
    #[error("ambiguous name `{name}`: visible in scopes {scopes:?}")]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    Ambiguous {
        name: String,
        scopes: Vec<ScopeStamp>,
    },
    #[error("anti-quotation scope mismatch for `{name}`: expected {expected}, got {actual}")]
    AntiQuoteMismatch {
        name: String,
        expected: ScopeStamp,
        actual: ScopeStamp,
    },
    #[error("scope stack underflow")]
    ScopeUnderflow,
}

/// A single name binding with its introducing scope and origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NameBinding {
    pub(crate) name: Name,
    pub(crate) scope: ScopeStamp,
    pub(crate) macro_generated: bool,
    pub(crate) unhygienic: bool,
}

/// A piece of quoted syntax that carries scope information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct QuotedSyntax {
    pub(crate) text: String,
    pub(crate) scope: ScopeStamp,
    pub(crate) anti_quotes: Vec<AntiQuote>,
}

/// An anti-quotation splice inside quoted syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AntiQuote {
    pub(crate) placeholder: String,
    pub(crate) origin_scope: ScopeStamp,
}

/// Counters for hygiene activity.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct HygieneStats {
    pub(crate) scopes_created: u64,
    pub(crate) resolutions: u64,
    pub(crate) violations_detected: u64,
    pub(crate) anti_quotes_processed: u64,
    pub(crate) unhygienic_escapes: u64,
    pub(crate) scope_merges: u64,
}

/// Extended macro hygiene context with full scope stamping, name resolution,
/// quotation hygiene, anti-quotation handling, macro-generated binding
/// detection, scope merging, unhygienic escape, and violation detection.
pub(crate) struct HygieneExt2Ctx {
    /// Stack of active scopes (innermost last). Never empty.
    scope_stack: Vec<ScopeStamp>,
    /// Per-name bindings (keyed by string representation).
    bindings: HashMap<String, Vec<NameBinding>>,
    /// Recorded violations.
    violations: Vec<Ext2Violation>,
    /// Merged scope pairs — (child, parent) meaning `child` inherits from `parent`.
    merged_scopes: HashMap<ScopeStamp, ScopeStamp>,
    /// Statistics.
    stats: HygieneStats,
}

impl Default for HygieneExt2Ctx {
    fn default() -> Self {
        Self::new()
    }
}

impl HygieneExt2Ctx {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            scope_stack: vec![ScopeStamp::root()],
            bindings: HashMap::new(),
            violations: Vec::new(),
            merged_scopes: HashMap::new(),
            stats: HygieneStats::default(),
        }
    }

    /// Enter a new macro expansion boundary; returns the fresh scope stamp.
    pub(crate) fn enter_scope(&mut self) -> ScopeStamp {
        let stamp = ScopeStamp::fresh();
        self.scope_stack.push(stamp);
        self.stats.scopes_created += 1;
        stamp
    }

    /// Leave the current macro scope.
    pub(crate) fn leave_scope(&mut self) -> Result<ScopeStamp, HygieneExt2Error> {
        if self.scope_stack.len() <= 1 {
            return Err(HygieneExt2Error::ScopeUnderflow);
        }
        Ok(self.scope_stack.pop().expect("invariant: checked above"))
    }

    #[must_use]
    pub(crate) fn current_scope(&self) -> ScopeStamp {
        self.scope_stack
            .last()
            .copied()
            .unwrap_or_else(ScopeStamp::root)
    }

    #[must_use]
    pub(crate) fn scope_depth(&self) -> usize {
        self.scope_stack.len()
    }

    /// Resolve `name` from the perspective of the current scope stack.
    ///
    /// Returns the innermost visible binding, or an error if none / ambiguous.
    pub(crate) fn resolve_name(&mut self, name: &Name) -> Result<NameBinding, HygieneExt2Error> {
        self.stats.resolutions += 1;
        let key = name.to_string();
        let Some(entries) = self.bindings.get(&key) else {
            return Err(HygieneExt2Error::Unresolved {
                name: key,
                scope: self.current_scope(),
            });
        };
        let visible: Vec<&NameBinding> = entries
            .iter()
            .filter(|b| self.is_scope_visible(b.scope))
            .collect();
        match visible.len() {
            0 => Err(HygieneExt2Error::Unresolved {
                name: key,
                scope: self.current_scope(),
            }),
            1 => Ok(visible[0].clone()),
            _ => {
                // Take the innermost (last on scope stack order).
                let innermost = visible
                    .iter()
                    .max_by_key(|b| self.scope_depth_of(b.scope))
                    .expect("invariant: visible is non-empty");
                Ok((*innermost).clone())
            }
        }
    }

    /// Introduce a name binding in the current scope.
    pub(crate) fn introduce_binding(&mut self, name: &Name, macro_generated: bool) {
        let scope = self.current_scope();
        let binding = NameBinding {
            name: name.clone(),
            scope,
            macro_generated,
            unhygienic: false,
        };
        let entries = self.bindings.entry(name.to_string()).or_default();
        if !entries.iter().any(|b| b.scope == scope && b.name == *name) {
            entries.push(binding);
        }
    }

    /// Create a quoted syntax fragment stamped with the current scope.
    #[must_use]
    pub(crate) fn quote_syntax(&self, text: &str) -> QuotedSyntax {
        QuotedSyntax {
            text: text.to_owned(),
            scope: self.current_scope(),
            anti_quotes: Vec::new(),
        }
    }

    /// Create a quoted syntax fragment with anti-quotation splices.
    #[must_use]
    pub(crate) fn quote_syntax_with_anti_quotes(
        &self,
        text: &str,
        anti_quotes: Vec<AntiQuote>,
    ) -> QuotedSyntax {
        QuotedSyntax {
            text: text.to_owned(),
            scope: self.current_scope(),
            anti_quotes,
        }
    }

    /// Validate and process an anti-quotation splice.
    ///
    /// The anti-quote's `origin_scope` must be visible from the current scope.
    pub(crate) fn process_anti_quote(&mut self, aq: &AntiQuote) -> Result<(), HygieneExt2Error> {
        self.stats.anti_quotes_processed += 1;
        if !self.is_scope_visible(aq.origin_scope) {
            let violation = Ext2Violation {
                name: Name::from_string(&aq.placeholder),
                scope: aq.origin_scope,
                kind: Ext2ViolationKind::AntiQuoteScopeMismatch,
                message: format!(
                    "anti-quote `{}` from {} not visible in {}",
                    aq.placeholder,
                    aq.origin_scope,
                    self.current_scope()
                ),
            };
            self.violations.push(violation);
            self.stats.violations_detected += 1;
            return Err(HygieneExt2Error::AntiQuoteMismatch {
                name: aq.placeholder.clone(),
                expected: self.current_scope(),
                actual: aq.origin_scope,
            });
        }
        Ok(())
    }

    /// Check whether `name` is bound by a macro-generated binding in the
    /// current context. If it shadows a user-level binding, record a violation.
    pub(crate) fn detect_macro_binding_shadow(&mut self, name: &Name) {
        let key = name.to_string();
        let Some(entries) = self.bindings.get(&key) else {
            return;
        };
        let visible: Vec<&NameBinding> = entries
            .iter()
            .filter(|b| self.is_scope_visible(b.scope))
            .collect();
        let has_user = visible.iter().any(|b| !b.macro_generated);
        let has_macro = visible.iter().any(|b| b.macro_generated);
        if has_user && has_macro {
            let violation = Ext2Violation {
                name: name.clone(),
                scope: self.current_scope(),
                kind: Ext2ViolationKind::MacroBindingShadow,
                message: format!("macro-generated binding `{name}` shadows user binding"),
            };
            self.violations.push(violation);
            self.stats.violations_detected += 1;
        }
    }

    /// Merge `child` scope into `parent`, so names visible in `parent`
    /// become visible in `child` as well.
    pub(crate) fn merge_scopes(&mut self, child: ScopeStamp, parent: ScopeStamp) {
        self.merged_scopes.insert(child, parent);
        self.stats.scope_merges += 1;
    }

    /// Introduce a binding in the *parent* scope (one level up), simulating
    /// an `unhygienic!` escape. Records a tracking violation (not an error).
    pub(crate) fn introduce_unhygienic(&mut self, name: &Name) {
        let parent = if self.scope_stack.len() >= 2 {
            self.scope_stack[self.scope_stack.len() - 2]
        } else {
            ScopeStamp::root()
        };
        let binding = NameBinding {
            name: name.clone(),
            scope: parent,
            macro_generated: true,
            unhygienic: true,
        };
        let entries = self.bindings.entry(name.to_string()).or_default();
        if !entries.iter().any(|b| b.scope == parent && b.name == *name) {
            entries.push(binding);
        }
        self.violations.push(Ext2Violation {
            name: name.clone(),
            scope: parent,
            kind: Ext2ViolationKind::UnhygienicEscape,
            message: format!("`unhygienic!` binding `{name}` in {parent}"),
        });
        self.stats.unhygienic_escapes += 1;
        self.stats.violations_detected += 1;
    }

    /// Run a full hygiene audit on the current binding set, detecting leaks.
    pub(crate) fn audit_all_bindings(&mut self) {
        let current = self.current_scope();
        let keys: Vec<String> = self.bindings.keys().cloned().collect();
        for key in &keys {
            let entries = self.bindings.get(key).cloned().unwrap_or_default();
            for entry in &entries {
                if !entry.unhygienic && !self.is_scope_visible(entry.scope) {
                    let violation = Ext2Violation {
                        name: entry.name.clone(),
                        scope: entry.scope,
                        kind: Ext2ViolationKind::ScopeLeak,
                        message: format!(
                            "`{}` from {} not visible from {}",
                            entry.name, entry.scope, current
                        ),
                    };
                    if !self.violations.contains(&violation) {
                        self.violations.push(violation);
                        self.stats.violations_detected += 1;
                    }
                }
            }
        }
    }

    /// Check a specific name for hygiene violations.
    pub(crate) fn check_name(&mut self, name: &Name) -> Vec<Ext2Violation> {
        let mut found = Vec::new();
        let key = name.to_string();
        let entries = self.bindings.get(&key).cloned().unwrap_or_default();
        let current = self.current_scope();
        for entry in &entries {
            if !entry.unhygienic && !self.is_scope_visible(entry.scope) {
                found.push(Ext2Violation {
                    name: entry.name.clone(),
                    scope: entry.scope,
                    kind: Ext2ViolationKind::ScopeLeak,
                    message: format!(
                        "`{}` from {} not visible from {}",
                        entry.name, entry.scope, current
                    ),
                });
            }
        }
        self.violations.extend(found.clone());
        self.stats.violations_detected += found.len() as u64;
        found
    }

    /// Return all recorded violations.
    #[must_use]
    pub(crate) fn violations(&self) -> &[Ext2Violation] {
        &self.violations
    }

    /// Drain and return all recorded violations.
    pub(crate) fn take_violations(&mut self) -> Vec<Ext2Violation> {
        std::mem::take(&mut self.violations)
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &HygieneStats {
        &self.stats
    }

    /// Is `scope` visible from the current scope stack (including merges)?
    fn is_scope_visible(&self, scope: ScopeStamp) -> bool {
        if scope.is_root() {
            return true;
        }
        if self.scope_stack.contains(&scope) {
            return true;
        }
        // Walk merged-scope chain: if `scope` merges into something on the
        // stack, it is also visible.
        let mut visited = HashSet::new();
        let mut current = scope;
        while let Some(&parent) = self.merged_scopes.get(&current) {
            if !visited.insert(current) {
                break; // cycle guard
            }
            if self.scope_stack.contains(&parent) {
                return true;
            }
            current = parent;
        }
        false
    }

    /// Depth of `scope` on the stack (0 = not found).
    fn scope_depth_of(&self, scope: ScopeStamp) -> usize {
        self.scope_stack
            .iter()
            .position(|s| *s == scope)
            .unwrap_or(0)
    }

    /// Return names introduced in the given scope.
    #[must_use]
    pub(crate) fn names_in_scope(&self, scope: ScopeStamp) -> Vec<Name> {
        let mut names: Vec<Name> = self
            .bindings
            .values()
            .flatten()
            .filter(|b| b.scope == scope)
            .map(|b| b.name.clone())
            .collect();
        names.sort_by_key(|a| a.to_string());
        names.dedup();
        names
    }

    /// Return all scope stamps currently on the stack.
    #[must_use]
    pub(crate) fn scope_stack(&self) -> &[ScopeStamp] {
        &self.scope_stack
    }
}
