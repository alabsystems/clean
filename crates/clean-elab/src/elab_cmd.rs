// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Syntax elaborator and `macro_rules` registries for Lean 5.
//!
//! Provides two extension points:
//! - [`ElabRuleRegistry`] dispatches elaborator handlers by syntax rule name.
//! - [`MacroRulesRegistry`] stores user-defined `macro_rules` entries by name.

use std::collections::HashMap;
use std::sync::Arc;

use crate::infer::ElabCtx;
use crate::syntax_cmd::SyntaxMatch;
use crate::ElabError;
use clean_kernel::Expr;
use clean_parser::SurfaceExpr;

/// Handler type for user-defined syntax elaborators.
pub type ElabHandler =
    dyn Fn(&[SyntaxMatch], &mut ElabCtx<'_>) -> Result<Expr, ElabError> + Send + Sync;

/// A registered elaboration rule for a named syntax rule.
pub struct ElabRule {
    /// Name of the syntax rule this handler elaborates.
    pub syntax_name: String,
    /// Handler invoked with the syntax matches and elaboration context.
    pub handler: Arc<ElabHandler>,
}

impl Clone for ElabRule {
    fn clone(&self) -> Self {
        Self {
            syntax_name: self.syntax_name.clone(),
            handler: Arc::clone(&self.handler),
        }
    }
}

impl std::fmt::Debug for ElabRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ElabRule")
            .field("syntax_name", &self.syntax_name)
            .field("handler", &"<fn>")
            .finish()
    }
}

/// Registry of elaboration rules keyed by syntax rule name.
pub struct ElabRuleRegistry {
    entries: HashMap<String, Vec<ElabRule>>,
}

impl std::fmt::Debug for ElabRuleRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ElabRuleRegistry")
            .field("rule_names", &self.entries.keys().collect::<Vec<_>>())
            .field("rule_count", &self.rule_count())
            .finish()
    }
}

impl ElabRuleRegistry {
    /// Create a new empty elaboration rule registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Register an elaboration rule.
    ///
    /// Rules for the same syntax name are tried in insertion order.
    pub fn register(&mut self, rule: ElabRule) {
        self.entries
            .entry(rule.syntax_name.clone())
            .or_default()
            .push(rule);
    }

    /// Look up all elaboration rules for a syntax name.
    #[must_use]
    pub fn lookup(&self, syntax_name: &str) -> Option<&[ElabRule]> {
        self.entries.get(syntax_name).map(|rules| rules.as_slice())
    }

    /// Try registered elaborators for a syntax name in order.
    ///
    /// Returns `None` if no rules are registered. If all handlers fail, returns
    /// the last error.
    #[must_use = "elaboration result should be checked"]
    pub fn elaborate(
        &self,
        syntax_name: &str,
        matches: &[SyntaxMatch],
        ctx: &mut ElabCtx<'_>,
    ) -> Option<Result<Expr, ElabError>> {
        let rules = self.entries.get(syntax_name)?;
        if rules.is_empty() {
            return None;
        }

        let mut last_err = None;
        for rule in rules {
            match (rule.handler)(matches, ctx) {
                Ok(expr) => return Some(Ok(expr)),
                Err(err) => last_err = Some(err),
            }
        }
        last_err.map(Err)
    }

    /// Total number of registered elaboration rules.
    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }
}

impl Default for ElabRuleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Errors for elaboration-command and macro-rule dispatch.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ElabCmdError {
    /// No elaborator rules were registered for the syntax name.
    #[error("unknown elaboration rule: {0}")]
    UnknownElabRule(String),
    /// All elaboration handlers failed.
    #[error("elaboration failed for '{syntax_name}': {detail}")]
    ElaborationFailed { syntax_name: String, detail: String },
    /// No `macro_rules` arm matched the input.
    #[error("no matching macro arm for '{macro_name}'")]
    NoMatchingArm { macro_name: String },
    /// Macro expansion failed after selecting an arm.
    #[error("macro expansion failed for '{macro_name}': {detail}")]
    MacroExpansionFailed { macro_name: String, detail: String },
}

/// A quotation-style pattern wrapper for a `macro_rules` arm.
#[derive(Debug, Clone)]
pub struct MacroRulePattern {
    /// The quoted surface pattern expression.
    pub pattern_expr: SurfaceExpr,
}

/// A single `macro_rules` arm.
#[derive(Debug, Clone)]
pub struct MacroRulesArm {
    /// The arm pattern.
    pub pattern: SurfaceExpr,
    /// The expansion produced for the pattern.
    pub expansion: SurfaceExpr,
}

/// A named `macro_rules` entry with multiple arms.
#[derive(Debug, Clone)]
pub struct MacroRulesEntry {
    /// Macro name.
    pub name: String,
    /// Arms tried in source order.
    pub arms: Vec<MacroRulesArm>,
}

/// Registry of named `macro_rules` entries.
pub struct MacroRulesRegistry {
    entries: HashMap<String, MacroRulesEntry>,
}

impl std::fmt::Debug for MacroRulesRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MacroRulesRegistry")
            .field("count", &self.entries.len())
            .field("names", &self.entries.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl MacroRulesRegistry {
    /// Create a new empty macro-rules registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Register a named `macro_rules` entry.
    ///
    /// Replaces any existing entry with the same name.
    pub fn register(&mut self, entry: MacroRulesEntry) {
        self.entries.insert(entry.name.clone(), entry);
    }

    /// Look up a named `macro_rules` entry.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&MacroRulesEntry> {
        self.entries.get(name)
    }

    /// Expand an input using the named `macro_rules` entry.
    ///
    /// Pattern matching is currently a stub: the first arm whose pattern
    /// structurally matches the input is selected. For now, all arms match.
    #[must_use = "expansion result should be checked"]
    pub fn expand(&self, name: &str, _input: &SurfaceExpr) -> Option<SurfaceExpr> {
        let entry = self.entries.get(name)?;
        // Stub: return the first arm's expansion (real pattern matching TBD)
        entry.arms.first().map(|arm| arm.expansion.clone())
    }
}

impl Default for MacroRulesRegistry {
    fn default() -> Self {
        Self::new()
    }
}
