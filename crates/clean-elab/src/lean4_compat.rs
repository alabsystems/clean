// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 compatibility shims for renamed commands, tactics, and syntax.
//!
//! This module provides a small, string-based compatibility table that can be
//! consulted before elaboration or while building migration diagnostics. It is
//! intentionally lightweight: the layer only records direct command and tactic
//! renames plus a curated list of deprecated surface forms that should produce
//! actionable user messages.
//!
//! The compatibility table does not attempt to parse Lean source on its own.
//! Instead, callers can use it to:
//! - rewrite well-known Lean 4 tactic and command names to Lean 5 entrypoints,
//! - attach migration hints to deprecated names,
//! - expose the full deprecation list for diagnostics or help text.

use hashbrown::HashMap;

/// A compatibility table for Lean 4 surface names that changed in Lean 5.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lean4Compat {
    /// Renamed tactic entrypoints keyed by their Lean 4 spelling.
    pub(crate) renamed_tactics: HashMap<String, String>,
    /// Renamed command entrypoints keyed by their Lean 4 spelling.
    pub(crate) renamed_commands: HashMap<String, String>,
    /// Deprecated syntax families and migration hints.
    pub(crate) deprecated_syntax: Vec<DeprecatedEntry>,
}

/// A single deprecated Lean 4 spelling with a suggested replacement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeprecatedEntry {
    /// The deprecated spelling or syntax family.
    pub(crate) old: String,
    /// The preferred replacement or compatibility target.
    pub(crate) new: String,
    /// The first compatibility version where the old form should be migrated.
    pub(crate) since_version: String,
    /// A user-facing explanation that can be surfaced in diagnostics.
    pub(crate) message: String,
}

impl DeprecatedEntry {
    /// Create a deprecated entry from borrowed string slices.
    #[must_use]
    pub(crate) fn new(old: &str, new: &str, since_version: &str, message: &str) -> Self {
        Self {
            old: old.to_owned(),
            new: new.to_owned(),
            since_version: since_version.to_owned(),
            message: message.to_owned(),
        }
    }

    /// Check whether this deprecation entry matches a surface name exactly.
    #[must_use]
    pub(crate) fn matches(&self, name: &str) -> bool {
        self.old == name
    }

    /// Return the deprecated spelling.
    #[must_use]
    pub(crate) fn old_name(&self) -> &str {
        self.old.as_str()
    }

    /// Return the preferred replacement spelling.
    #[must_use]
    pub(crate) fn replacement(&self) -> &str {
        self.new.as_str()
    }

    /// Return the compatibility version attached to this migration hint.
    #[must_use]
    pub(crate) fn version(&self) -> &str {
        self.since_version.as_str()
    }

    /// Return the user-facing migration message.
    #[must_use]
    pub(crate) fn diagnostic_message(&self) -> &str {
        self.message.as_str()
    }
}

impl Lean4Compat {
    /// Build the default Lean 4 compatibility table.
    #[must_use]
    pub(crate) fn new() -> Self {
        let mut compat = Self {
            renamed_tactics: HashMap::with_capacity(13),
            renamed_commands: HashMap::with_capacity(5),
            deprecated_syntax: Vec::with_capacity(26),
        };

        compat.populate_tactic_renames();
        compat.populate_command_renames();
        compat.populate_deprecations();
        compat
    }

    /// Resolve a Lean 4 tactic name to the Lean 5 spelling, if one is known.
    #[must_use]
    pub(crate) fn resolve_tactic(&self, name: &str) -> Option<&str> {
        self.renamed_tactics.get(name).map(String::as_str)
    }

    /// Resolve a Lean 4 command name to the Lean 5 spelling, if one is known.
    #[must_use]
    pub(crate) fn resolve_command(&self, name: &str) -> Option<&str> {
        self.renamed_commands.get(name).map(String::as_str)
    }

    /// Look up a deprecated entry by its original Lean 4 spelling.
    #[must_use]
    pub(crate) fn check_deprecated(&self, name: &str) -> Option<&DeprecatedEntry> {
        self.deprecated_syntax
            .iter()
            .find(|entry| entry.matches(name))
    }

    /// Check whether a tactic name is handled as a deprecated Lean 4 tactic.
    #[must_use]
    pub(crate) fn is_deprecated_tactic(&self, name: &str) -> bool {
        self.renamed_tactics.contains_key(name)
    }

    /// Check whether a command name is handled as a deprecated Lean 4 command.
    #[must_use]
    pub(crate) fn is_deprecated_command(&self, name: &str) -> bool {
        self.renamed_commands.contains_key(name)
    }

    /// Return the complete deprecated entry list.
    #[must_use]
    pub(crate) fn all_deprecated(&self) -> &[DeprecatedEntry] {
        self.deprecated_syntax.as_slice()
    }

    /// Return the number of known tactic renames.
    #[must_use]
    pub(crate) fn tactic_count(&self) -> usize {
        self.renamed_tactics.len()
    }

    /// Return the number of known command renames.
    #[must_use]
    pub(crate) fn command_count(&self) -> usize {
        self.renamed_commands.len()
    }

    fn populate_tactic_renames(&mut self) {
        insert_rename(
            &mut self.renamed_tactics,
            "simp only",
            "simp (config := { contextual := true }) only",
        );
        insert_rename(&mut self.renamed_tactics, "ring_nf", "ring");
        insert_rename(&mut self.renamed_tactics, "norm_num1", "norm_num");
        insert_rename(&mut self.renamed_tactics, "squeeze_simp", "simp?");
        insert_rename(&mut self.renamed_tactics, "library_search", "exact?");
        insert_rename(&mut self.renamed_tactics, "suggest", "exact?");
        insert_rename(&mut self.renamed_tactics, "tidy", "aesop");
        insert_rename(&mut self.renamed_tactics, "finish", "aesop");
        insert_rename(&mut self.renamed_tactics, "clarify", "aesop");
        insert_rename(&mut self.renamed_tactics, "safe", "aesop");
        insert_rename(&mut self.renamed_tactics, "obviously", "decide");
        insert_rename(&mut self.renamed_tactics, "dec_trivial", "decide");
        insert_rename(&mut self.renamed_tactics, "tauto", "omega");

        // `linarith` is intentionally omitted because its user-facing spelling
        // is unchanged in the compatibility layer.
    }

    fn populate_command_renames(&mut self) {
        insert_rename(&mut self.renamed_commands, "#check", "check_expression");
        insert_rename(&mut self.renamed_commands, "#eval", "eval_expression");
        insert_rename(&mut self.renamed_commands, "#print", "print_declaration");
        insert_rename(&mut self.renamed_commands, "#reduce", "eval_expression");
        insert_rename(
            &mut self.renamed_commands,
            "#check_failure",
            "check_failure",
        );
    }

    fn populate_deprecations(&mut self) {
        push_command_deprecations(&mut self.deprecated_syntax);
        push_tactic_norm_deprecations(&mut self.deprecated_syntax);
        push_tactic_automation_deprecations(&mut self.deprecated_syntax);
        push_syntax_deprecations(&mut self.deprecated_syntax);
    }
}

impl Default for Lean4Compat {
    fn default() -> Self {
        Self::new()
    }
}

fn insert_rename(map: &mut HashMap<String, String>, old: &str, new: &str) {
    map.insert(old.to_owned(), new.to_owned());
}

fn push_deprecation(
    entries: &mut Vec<DeprecatedEntry>,
    old: &str,
    new: &str,
    since_version: &str,
    message: &str,
) {
    entries.push(DeprecatedEntry::new(old, new, since_version, message));
}

fn push_command_deprecations(entries: &mut Vec<DeprecatedEntry>) {
    push_deprecation(
        entries,
        "#check",
        "check_expression",
        "5.0.0",
        "Use `check_expression` for Lean 5 command elaboration instead of the Lean 4 `#check` command.",
    );
    push_deprecation(
        entries,
        "#eval",
        "eval_expression",
        "5.0.0",
        "Use `eval_expression` when porting Lean 4 `#eval` scripts into Lean 5.",
    );
    push_deprecation(
        entries,
        "#print",
        "print_declaration",
        "5.0.0",
        "Use `print_declaration` instead of `#print` in Lean 5 command pipelines.",
    );
    push_deprecation(
        entries,
        "#reduce",
        "eval_expression",
        "5.0.0",
        "Lean 5 routes `#reduce` style evaluation through `eval_expression`.",
    );
    push_deprecation(
        entries,
        "#check_failure",
        "check_failure",
        "5.0.0",
        "Testing code should call `check_failure` directly instead of the Lean 4 `#check_failure` command.",
    );
}

/// Deprecation entries for simp/ring/norm tactic renames.
fn push_tactic_norm_deprecations(entries: &mut Vec<DeprecatedEntry>) {
    push_deprecation(
        entries,
        "simp only",
        "simp (config := { contextual := true }) only",
        "4.0.0",
        "Lean 5 expands `simp only` through the contextual compatibility form to preserve Lean 4 behavior.",
    );
    push_deprecation(
        entries,
        "ring_nf",
        "ring",
        "4.0.0",
        "Use `ring`; normalization-only entrypoints were folded into the main ring tactic.",
    );
    push_deprecation(
        entries,
        "norm_num1",
        "norm_num",
        "4.0.0",
        "Use `norm_num`; `norm_num1` was an internal helper and should not appear in user code.",
    );
    push_deprecation(
        entries,
        "squeeze_simp",
        "simp?",
        "4.1.0",
        "Use `simp?` to ask Lean for a smaller simp set; `squeeze_simp` was renamed.",
    );
    push_deprecation(
        entries,
        "library_search",
        "exact?",
        "4.3.0",
        "Use `exact?`; `library_search` was renamed to align with the newer suggestion workflow.",
    );
    push_deprecation(
        entries,
        "suggest",
        "exact?",
        "4.3.0",
        "Use `exact?`; `suggest` was merged into the same suggestion-oriented command family.",
    );
    push_deprecation(
        entries,
        "tauto",
        "omega",
        "4.2.0",
        "For this compatibility layer, port `tauto` uses to `omega` when the goal is in the supported arithmetic fragment.",
    );
}

/// Deprecation entries for automation tactic renames (aesop/decide family).
fn push_tactic_automation_deprecations(entries: &mut Vec<DeprecatedEntry>) {
    push_deprecation(
        entries,
        "tidy",
        "aesop",
        "4.0.0",
        "Use `aesop`; the older proof-search tactic `tidy` was superseded.",
    );
    push_deprecation(
        entries,
        "finish",
        "aesop",
        "4.0.0",
        "Use `aesop`; `finish` was retired in favor of a broader automation tactic.",
    );
    push_deprecation(
        entries,
        "clarify",
        "aesop",
        "4.0.0",
        "Use `aesop`; `clarify` style cleanup is handled as part of the newer automation flow.",
    );
    push_deprecation(
        entries,
        "safe",
        "aesop",
        "4.0.0",
        "Use `aesop`; the dedicated `safe` tactic no longer has a separate user-facing entrypoint.",
    );
    push_deprecation(
        entries,
        "obviously",
        "decide",
        "4.0.0",
        "Use `decide` for straightforward decidable goals instead of `obviously`.",
    );
    push_deprecation(
        entries,
        "dec_trivial",
        "decide",
        "4.0.0",
        "Use `decide`; `dec_trivial` was replaced by the standard decidability tactic.",
    );
}

fn push_syntax_deprecations(entries: &mut Vec<DeprecatedEntry>) {
    push_deprecation(
        entries,
        "match",
        "match ... with | pattern => result",
        "4.0.0",
        "Use arrow-style match arms with `=>`; Lean 5 diagnostics assume the modern branch form.",
    );
    push_deprecation(
        entries,
        "match h with",
        "match h with | pattern => result",
        "4.0.0",
        "Rewrite match branches to `| pattern => result`; older branch spellings are not preserved by the compatibility layer.",
    );
    push_deprecation(
        entries,
        "match ..., ... with",
        "match (x, y) with | (px, py) => result",
        "4.0.0",
        "Prefer tupled or explicit pattern matching forms when porting multi-scrutinee matches.",
    );
    push_deprecation(
        entries,
        "do",
        "do blocks with explicit line structure",
        "4.0.0",
        "Prefer line-oriented `do` blocks with one statement per line when porting Lean 4 code.",
    );
    push_deprecation(
        entries,
        "do let x <- m; n",
        "do\n  let x <- m\n  n",
        "4.0.0",
        "Split semicolon-heavy `do` notation into explicit lines to avoid parser ambiguities during migration.",
    );
    push_deprecation(
        entries,
        "do unless p do body",
        "do\n  if !p then\n    body",
        "4.0.0",
        "Rewrite deprecated `unless`-style `do` forms as explicit `if !cond then ...` blocks.",
    );
    push_deprecation(
        entries,
        "do return x; y",
        "do\n  return x",
        "4.0.0",
        "Remove trailing statements after `return`; Lean 5 expects structured `do` control flow rather than semicolon chaining.",
    );
    push_deprecation(
        entries,
        "do try body catch ex => handler",
        "do\n  try\n    body\n  catch ex =>\n    handler",
        "4.0.0",
        "Port compact `try` and `catch` notation into the block-oriented `do` form used by Lean 5.",
    );
}
