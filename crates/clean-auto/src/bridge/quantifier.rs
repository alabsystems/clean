// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mixed quantifier scope analysis
//!
//! Types for representing and analyzing quantifier prefixes with mixed
//! universal and existential quantifiers.

use clean_kernel::Expr;
use std::collections::HashMap;

// ============================================================================
// Mixed Quantifier Scope Analysis
// ============================================================================

/// Quantifier kind (universal or existential)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QuantifierKind {
    /// Universal quantifier (∀)
    Forall,
    /// Existential quantifier (∃)
    Exists,
}

/// A single binder in a quantifier prefix
#[derive(Clone, Debug)]
pub(crate) struct QuantifierBinder {
    /// The kind of quantifier (∀ or ∃)
    pub(crate) kind: QuantifierKind,
    /// The type of the bound variable
    pub(crate) ty: Expr,
    /// The de Bruijn index of this binder in the flattened context
    pub(crate) index: u32,
}

/// Quantifier prefix representing a sequence of quantifiers
///
/// For example, `∀x. ∃y. ∀z. P(x,y,z)` is represented as:
/// - binders: [(∀, A, 2), (∃, B, 1), (∀, C, 0)]
/// - body: P(x,y,z) with BVars 2, 1, 0
///
/// The index is the de Bruijn index in the flattened body.
#[derive(Clone, Debug)]
pub(crate) struct QuantifierPrefix {
    /// The sequence of quantifier binders from outermost to innermost
    pub(crate) binders: Vec<QuantifierBinder>,
    /// The innermost body (with BVars for all bound variables)
    pub(crate) body: Expr,
}

impl QuantifierPrefix {
    /// Get the number of quantifiers in this prefix
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.binders.len()
    }

    /// Check if the prefix is empty (no quantifiers)
    pub fn is_empty(&self) -> bool {
        self.binders.is_empty()
    }

    /// Get the alternation depth of this quantifier prefix
    ///
    /// The alternation depth is the number of times the quantifier kind changes.
    /// - `∀x. P(x)` has depth 0 (no alternation)
    /// - `∀x. ∃y. P(x,y)` has depth 1 (one alternation: ∀→∃)
    /// - `∀x. ∃y. ∀z. P(x,y,z)` has depth 2 (two alternations: ∀→∃→∀)
    /// - `∃x. ∃y. P(x,y)` has depth 0 (no alternation, all ∃)
    ///
    /// Higher alternation depth generally indicates harder formulas to decide.
    pub fn alternation_depth(&self) -> u32 {
        if self.binders.is_empty() {
            return 0;
        }

        let mut depth = 0;
        let mut prev_kind = self.binders[0].kind;

        for binder in &self.binders[1..] {
            if binder.kind != prev_kind {
                depth += 1;
                prev_kind = binder.kind;
            }
        }

        depth
    }

    /// Check if this is a purely universal prefix (∀...∀)
    pub fn is_purely_universal(&self) -> bool {
        self.binders
            .iter()
            .all(|b| b.kind == QuantifierKind::Forall)
    }

    /// Check if this is a purely existential prefix (∃...∃)
    pub fn is_purely_existential(&self) -> bool {
        self.binders
            .iter()
            .all(|b| b.kind == QuantifierKind::Exists)
    }

    /// Get the outermost quantifier kind, if any
    #[cfg(test)]
    pub fn outermost_kind(&self) -> Option<QuantifierKind> {
        self.binders.first().map(|b| b.kind)
    }

    /// Get indices of all universal variables
    pub fn forall_indices(&self) -> Vec<u32> {
        self.binders
            .iter()
            .filter(|b| b.kind == QuantifierKind::Forall)
            .map(|b| b.index)
            .collect()
    }

    /// Get indices of all existential variables
    #[cfg(test)]
    pub fn exists_indices(&self) -> Vec<u32> {
        self.binders
            .iter()
            .filter(|b| b.kind == QuantifierKind::Exists)
            .map(|b| b.index)
            .collect()
    }

    /// Get the dependencies for Skolemization
    ///
    /// For each existential variable, returns the indices of universal variables
    /// that appear before it in the prefix (which the Skolem function should depend on).
    ///
    /// Example: `∀x. ∃y. ∀z. ∃w. P(x,y,z,w)`
    /// - y depends on \[x\]
    /// - w depends on \[x, z\]
    pub fn skolem_dependencies(&self) -> HashMap<u32, Vec<u32>> {
        let mut deps = HashMap::new();
        let mut preceding_foralls = Vec::new();

        for binder in &self.binders {
            match binder.kind {
                QuantifierKind::Forall => {
                    preceding_foralls.push(binder.index);
                }
                QuantifierKind::Exists => {
                    deps.insert(binder.index, preceding_foralls.clone());
                }
            }
        }

        deps
    }
}
