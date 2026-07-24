// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern matching exhaustiveness and redundancy checking.
//!
//! Implements Maranget's usefulness algorithm from "Warnings for Pattern
//! Matching" (JFP 2007) to determine whether a set of patterns is exhaustive
//! and which patterns are redundant.
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// Pattern types
// ---------------------------------------------------------------------------

/// A pattern for exhaustiveness checking.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum CheckPattern {
    /// Match a specific constructor with sub-patterns for fields.
    Constructor {
        name: String,
        args: Vec<CheckPattern>,
    },
    /// Match anything.
    Wildcard,
    /// Match a literal value.
    Literal(LitPattern),
    /// Match any of the given alternatives (or-pattern).
    Or(Vec<CheckPattern>),
}

/// A literal pattern value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LitPattern {
    /// Natural number literal.
    Nat(u64),
    /// String literal.
    String(String),
    /// Boolean literal.
    Bool(bool),
}

// ---------------------------------------------------------------------------
// Type information
// ---------------------------------------------------------------------------

/// Information about a type's constructors for exhaustiveness analysis.
#[derive(Debug, Clone)]
pub(crate) struct TypeInfo {
    /// The type name (e.g. "Bool", "Option", "List").
    pub name: String,
    /// The constructors of this type.
    pub constructors: Vec<ConstructorInfo>,
    /// Whether this type is recursive (e.g. List, Nat).
    pub is_recursive: bool,
}

/// Information about a single constructor.
#[derive(Debug, Clone)]
pub(crate) struct ConstructorInfo {
    /// Constructor name (e.g. "true", "Some", "nil").
    pub name: String,
    /// Number of fields.
    pub arity: usize,
    /// Names of field types (for nested exhaustiveness).
    pub field_types: Vec<String>,
}

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

/// Result of an exhaustiveness check.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum ExhaustivenessResult {
    /// All inputs are covered.
    Exhaustive,
    /// Some inputs are not covered.
    NonExhaustive { missing: Vec<CheckPattern> },
    /// Some patterns are unreachable (already covered by earlier ones).
    Redundant { redundant_indices: Vec<usize> },
}

// ---------------------------------------------------------------------------
// Checker
// ---------------------------------------------------------------------------

/// Exhaustiveness and redundancy checker for pattern match expressions.
pub(crate) struct ExhaustivenessChecker {
    type_registry: HashMap<String, TypeInfo>,
}

impl ExhaustivenessChecker {
    /// Create a new checker with an empty type registry.
    pub fn new() -> Self {
        Self {
            type_registry: HashMap::new(),
        }
    }

    /// Register a type and its constructors.
    pub fn register_type(&mut self, info: TypeInfo) {
        self.type_registry.insert(info.name.clone(), info);
    }

    /// Check a pattern matrix for exhaustiveness and redundancy.
    #[must_use]
    pub fn check(&self, patterns: &[Vec<CheckPattern>], type_name: &str) -> ExhaustivenessResult {
        let redundant = self.find_redundant(patterns);
        if !redundant.is_empty() {
            return ExhaustivenessResult::Redundant {
                redundant_indices: redundant,
            };
        }
        // Use the `useful` predicate: if a wildcard vector is useful, match
        // is non-exhaustive.
        let width = patterns.first().map_or(1, |r| r.len());
        let witness = vec![CheckPattern::Wildcard; width];
        if self.useful(patterns, &witness) {
            let missing = self.missing_patterns(patterns, type_name);
            ExhaustivenessResult::NonExhaustive { missing }
        } else {
            ExhaustivenessResult::Exhaustive
        }
    }

    /// Maranget's U predicate: is `vector` useful w.r.t. `matrix`?
    #[must_use]
    pub fn useful(&self, matrix: &[Vec<CheckPattern>], vector: &[CheckPattern]) -> bool {
        if vector.is_empty() {
            return matrix.is_empty();
        }
        match &vector[0] {
            CheckPattern::Constructor { name, args } => {
                let arity = args.len();
                let spec_m = Self::specialize(matrix, name, arity);
                let spec_v = Self::specialize_row(vector, name, arity);
                self.useful(&spec_m, &spec_v)
            }
            CheckPattern::Literal(lit) => {
                let key = literal_key(lit);
                let spec_m = Self::specialize(matrix, &key, 0);
                let spec_v = vector[1..].to_vec();
                self.useful(&spec_m, &spec_v)
            }
            CheckPattern::Or(alts) => alts.iter().any(|alt| {
                let mut v = vec![alt.clone()];
                v.extend_from_slice(&vector[1..]);
                self.useful(matrix, &v)
            }),
            CheckPattern::Wildcard => {
                let sigma = first_column_heads(matrix);
                if self.is_sigma_complete(&sigma) {
                    sigma.iter().any(|(name, arity)| {
                        let spec_m = Self::specialize(matrix, name, *arity);
                        let mut spec_v = vec![CheckPattern::Wildcard; *arity];
                        spec_v.extend_from_slice(&vector[1..]);
                        self.useful(&spec_m, &spec_v)
                    })
                } else {
                    let def = Self::default_matrix(matrix);
                    self.useful(&def, &vector[1..])
                }
            }
        }
    }

    /// Specialize matrix on a constructor (or literal key).
    pub fn specialize(
        matrix: &[Vec<CheckPattern>],
        head: &str,
        arity: usize,
    ) -> Vec<Vec<CheckPattern>> {
        let mut out = Vec::new();
        for row in matrix {
            if row.is_empty() {
                continue;
            }
            Self::specialize_pat(&row[0], &row[1..], head, arity, &mut out);
        }
        out
    }

    /// Default matrix: keep wildcard-headed rows, drop first column.
    pub fn default_matrix(matrix: &[Vec<CheckPattern>]) -> Vec<Vec<CheckPattern>> {
        let mut out = Vec::new();
        for row in matrix {
            if row.is_empty() {
                continue;
            }
            match &row[0] {
                CheckPattern::Wildcard => out.push(row[1..].to_vec()),
                CheckPattern::Or(alts)
                    if alts.iter().any(|a| matches!(a, CheckPattern::Wildcard)) =>
                {
                    out.push(row[1..].to_vec());
                }
                _ => {}
            }
        }
        out
    }

    /// Generate witness patterns for non-exhaustiveness.
    pub fn missing_patterns(
        &self,
        matrix: &[Vec<CheckPattern>],
        type_name: &str,
    ) -> Vec<CheckPattern> {
        if matrix.is_empty() {
            return vec![CheckPattern::Wildcard];
        }
        if let Some(info) = self.type_registry.get(type_name) {
            let sigma = first_column_heads(matrix);
            let present: HashSet<&str> = sigma.iter().map(|(n, _)| n.as_str()).collect();
            let mut missing = Vec::new();
            for ctor in &info.constructors {
                if !present.contains(ctor.name.as_str()) {
                    // Specialize matrix on this missing ctor to see if wildcards cover it.
                    let spec = Self::specialize(matrix, &ctor.name, ctor.arity);
                    let rest = matrix.first().map_or(0, |r| r.len().saturating_sub(1));
                    let witness = vec![CheckPattern::Wildcard; ctor.arity + rest];
                    if self.useful(&spec, &witness) {
                        missing.push(CheckPattern::Constructor {
                            name: ctor.name.clone(),
                            args: vec![CheckPattern::Wildcard; ctor.arity],
                        });
                    }
                }
            }
            // All constructors present — check nested missing patterns.
            if missing.is_empty() {
                for (ctor_name, arity) in &sigma {
                    let spec = Self::specialize(matrix, ctor_name, *arity);
                    let ft = info
                        .constructors
                        .iter()
                        .find(|c| c.name == *ctor_name)
                        .and_then(|c| c.field_types.first())
                        .map(|s| s.as_str())
                        .unwrap_or(type_name);
                    let sub = self.missing_patterns(&spec, ft);
                    for s in sub {
                        let mut args = vec![s];
                        while args.len() < *arity {
                            args.push(CheckPattern::Wildcard);
                        }
                        missing.push(CheckPattern::Constructor {
                            name: ctor_name.clone(),
                            args,
                        });
                    }
                }
            }
            missing
        } else {
            vec![CheckPattern::Wildcard]
        }
    }

    /// Find indices of redundant patterns.
    pub fn find_redundant(&self, patterns: &[Vec<CheckPattern>]) -> Vec<usize> {
        let mut redundant = Vec::new();
        for i in 0..patterns.len() {
            if !self.useful(&patterns[..i], &patterns[i]) {
                redundant.push(i);
            }
        }
        redundant
    }

    // -- internal helpers --

    fn is_sigma_complete(&self, sigma: &[(String, usize)]) -> bool {
        if sigma.is_empty() {
            return false;
        }
        let names: HashSet<&str> = sigma.iter().map(|(n, _)| n.as_str()).collect();
        // Bool literals use encoded keys.
        let true_key = literal_key(&LitPattern::Bool(true));
        let false_key = literal_key(&LitPattern::Bool(false));
        if names.len() == 2
            && names.contains(true_key.as_str())
            && names.contains(false_key.as_str())
        {
            return true;
        }
        // Registered types.
        for info in self.type_registry.values() {
            if info.constructors.len() == sigma.len()
                && info
                    .constructors
                    .iter()
                    .all(|c| names.contains(c.name.as_str()))
            {
                return true;
            }
        }
        false
    }

    fn specialize_pat(
        pat: &CheckPattern,
        tail: &[CheckPattern],
        head: &str,
        arity: usize,
        out: &mut Vec<Vec<CheckPattern>>,
    ) {
        match pat {
            CheckPattern::Constructor { name, args } if name == head => {
                let mut row = args.clone();
                row.extend_from_slice(tail);
                out.push(row);
            }
            CheckPattern::Wildcard => {
                let mut row = vec![CheckPattern::Wildcard; arity];
                row.extend_from_slice(tail);
                out.push(row);
            }
            CheckPattern::Literal(lit) if literal_key(lit) == head => {
                out.push(tail.to_vec());
            }
            CheckPattern::Or(alts) => {
                for alt in alts {
                    Self::specialize_pat(alt, tail, head, arity, out);
                }
            }
            _ => {}
        }
    }

    fn specialize_row(vector: &[CheckPattern], head: &str, arity: usize) -> Vec<CheckPattern> {
        if vector.is_empty() {
            return vec![];
        }
        match &vector[0] {
            CheckPattern::Constructor { name, args } if name == head => {
                let mut row = args.clone();
                row.extend_from_slice(&vector[1..]);
                row
            }
            CheckPattern::Wildcard => {
                let mut row = vec![CheckPattern::Wildcard; arity];
                row.extend_from_slice(&vector[1..]);
                row
            }
            _ => vector[1..].to_vec(),
        }
    }
}

// ---------------------------------------------------------------------------
// Free helpers
// ---------------------------------------------------------------------------

/// Encode a literal as a unique key for specialization.
fn literal_key(lit: &LitPattern) -> String {
    match lit {
        LitPattern::Nat(n) => format!("__lit_nat_{n}"),
        LitPattern::String(s) => format!("__lit_str_{s}"),
        LitPattern::Bool(b) => format!("__lit_bool_{b}"),
    }
}

/// Collect distinct head symbols from the first column.
fn first_column_heads(matrix: &[Vec<CheckPattern>]) -> Vec<(String, usize)> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for row in matrix {
        if let Some(pat) = row.first() {
            collect_heads(pat, &mut seen, &mut result);
        }
    }
    result
}

fn collect_heads(
    pat: &CheckPattern,
    seen: &mut HashSet<String>,
    result: &mut Vec<(String, usize)>,
) {
    match pat {
        CheckPattern::Constructor { name, args } => {
            if seen.insert(name.clone()) {
                result.push((name.clone(), args.len()));
            }
        }
        CheckPattern::Literal(lit) => {
            let key = literal_key(lit);
            if seen.insert(key.clone()) {
                result.push((key, 0));
            }
        }
        CheckPattern::Or(alts) => {
            for alt in alts {
                collect_heads(alt, seen, result);
            }
        }
        CheckPattern::Wildcard => {}
    }
}

#[cfg(test)]
#[path = "match_exhaustive_tests.rs"]
mod tests;
