// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Notation declaration storage and lookup for Lean 5.
//!
//! Provides a registry for user-defined notations (infix, prefix, postfix,
//! and general mixfix). Notations are indexed by their leading token for
//! efficient lookup during parsing.
//!
//! # Architecture
//!
//! The registry stores [`NotationEntry`] values indexed by their leading token
//! in a `HashMap<String, Vec<_>>`. When the parser encounters a token that
//! could be user-defined notation, it queries the registry to find matching
//! entries. Multiple notations can share a leading token; they are
//! disambiguated by priority (higher priority tried first).
//!
//! This mirrors Lean 4's notation system from `Lean.Parser.Extension` where
//! notations are registered as parser extensions keyed by their leading token.
//!
//! # Example
//!
//! ```
//! use clean_elab::notation::{NotationEntry, NotationPattern, NotationPatternItem, NotationRegistry};
//! use clean_parser::NotationKind;
//!
//! let mut registry = NotationRegistry::new();
//! registry.register(NotationEntry {
//!     name: "HAdd.hAdd".to_owned(),
//!     pattern: NotationPattern {
//!         items: vec![
//!             NotationPatternItem::Placeholder,
//!             NotationPatternItem::Token("+".to_owned()),
//!             NotationPatternItem::Placeholder,
//!         ],
//!     },
//!     expansion: clean_parser::SurfaceExpr::Ident(
//!         clean_parser::Span::new(0, 0),
//!         "HAdd.hAdd".to_owned(),
//!     ),
//!     priority: 65,
//!     kind: NotationKind::Infixl,
//! });
//! assert_eq!(registry.lookup("+").len(), 1);
//! ```

use std::collections::HashMap;

use clean_parser::{NotationKind, SurfaceExpr};

/// A single item in a notation pattern.
///
/// Notation patterns describe the syntactic shape of a notation.
/// For example, `_ + _` has `[Placeholder, Token("+"), Placeholder]`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NotationPatternItem {
    /// A placeholder for an expression argument: `_`
    Placeholder,
    /// A literal token: `"+"`, `"⟨"`, `","`, etc.
    Token(String),
}

/// A notation pattern: a sequence of tokens and placeholders.
///
/// Describes the syntactic shape that the notation matches.
/// For example, infix `+` is `[Placeholder, Token("+"), Placeholder]`,
/// while a mixfix notation like `⟨_, _⟩` is
/// `[Token("⟨"), Placeholder, Token(","), Placeholder, Token("⟩")]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotationPattern {
    /// The sequence of pattern items.
    pub items: Vec<NotationPatternItem>,
}

impl NotationPattern {
    /// Extract the leading token from the pattern, if any.
    ///
    /// For infix notations, the leading token is typically the operator
    /// (the first `Token` after an initial `Placeholder`). For prefix
    /// notations, it is the first `Token`. Returns `None` if the pattern
    /// contains no tokens.
    #[must_use]
    pub fn leading_token(&self) -> Option<&str> {
        self.items.iter().find_map(|item| match item {
            NotationPatternItem::Token(t) => Some(t.as_str()),
            NotationPatternItem::Placeholder => None,
        })
    }

    /// Count the number of placeholders (expression arguments) in the pattern.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.items
            .iter()
            .filter(|item| matches!(item, NotationPatternItem::Placeholder))
            .count()
    }
}

/// A registered notation entry.
///
/// Each entry associates a name with a pattern, expansion, priority, and kind.
/// The expansion is a `SurfaceExpr` that the notation desugars into, with
/// arguments substituted for placeholders.
#[derive(Debug, Clone)]
pub struct NotationEntry {
    /// The name of the function/constant this notation expands to.
    pub name: String,
    /// The syntactic pattern for this notation.
    pub pattern: NotationPattern,
    /// The expansion template. Arguments are substituted for placeholders.
    pub expansion: SurfaceExpr,
    /// Priority for disambiguation. Higher priority is tried first.
    pub priority: u32,
    /// The kind of notation (infix, prefix, postfix, or general).
    pub kind: NotationKind,
}

/// Registry of all active notations, indexed by leading token.
///
/// Constructed via [`NotationRegistry::new`] which starts empty. Notations
/// are added via [`NotationRegistry::register`]. When multiple notations
/// share a leading token, they are stored in descending priority order.
///
/// # Integration
///
/// The parser queries this registry when encountering tokens that could be
/// user-defined notation. The elaborator populates it when processing
/// `notation`, `infixl`, `infixr`, `prefix`, and `postfix` declarations.
pub struct NotationRegistry {
    /// Notations indexed by leading token (e.g., `"+"`, `"⟨"`, `"!"`).
    entries: HashMap<String, Vec<NotationEntry>>,
}

impl std::fmt::Debug for NotationRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NotationRegistry")
            .field("token_count", &self.entries.len())
            .field("tokens", &self.entries.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl Default for NotationRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl NotationRegistry {
    /// Create a new empty notation registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Register a notation entry.
    ///
    /// The entry is indexed by its leading token (extracted from the pattern).
    /// If the pattern has no leading token, the entry is stored under the
    /// empty string key as a fallback.
    ///
    /// Within each token bucket, entries are maintained in descending priority
    /// order (higher priority first).
    pub fn register(&mut self, entry: NotationEntry) {
        let key = entry.pattern.leading_token().unwrap_or("").to_owned();
        let bucket = self.entries.entry(key).or_default();
        let pos = bucket
            .iter()
            .position(|e| e.priority < entry.priority)
            .unwrap_or(bucket.len());
        bucket.insert(pos, entry);
    }

    /// Look up all notations with the given leading token.
    ///
    /// Returns entries in descending priority order (highest priority first).
    /// Returns an empty slice if no notations match the token.
    #[must_use]
    pub fn lookup(&self, leading_token: &str) -> &[NotationEntry] {
        self.entries
            .get(leading_token)
            .map_or(&[], |v| v.as_slice())
    }

    /// Iterate over all registered notation entries.
    pub fn all_notations(&self) -> impl Iterator<Item = &NotationEntry> {
        self.entries.values().flat_map(|v| v.iter())
    }

    /// Number of distinct leading tokens with registered notations.
    #[must_use]
    pub fn token_count(&self) -> usize {
        self.entries.len()
    }

    /// Total number of registered notation entries across all tokens.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Check whether any notations are registered for a leading token.
    #[must_use]
    pub fn has_notation(&self, leading_token: &str) -> bool {
        self.entries
            .get(leading_token)
            .is_some_and(|v| !v.is_empty())
    }
}

#[cfg(test)]
#[path = "notation_tests.rs"]
mod tests;
