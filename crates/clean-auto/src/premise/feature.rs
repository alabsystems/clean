// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature extraction for premise selection: Feature, FeatureSet, FeatureExtractor.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};
use std::collections::HashSet;

/// A feature extracted from an expression for ML-based premise selection
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Feature {
    /// Constant symbol (function/type name)
    Const(Name),
    /// Application pattern: f applied to something
    App(Name),
    /// Binary application pattern: (f _ _)
    BinApp(Name),
    /// Theory marker (e.g., "arith", "set", "list")
    Theory(String),
}

/// Feature set for a term/goal
#[derive(Clone, Debug, Default)]
pub(crate) struct FeatureSet {
    features: HashSet<Feature>,
}

impl FeatureSet {
    /// Create a new empty feature set
    pub fn new() -> Self {
        Self {
            features: HashSet::new(),
        }
    }

    /// Add a feature
    pub fn add(&mut self, f: Feature) {
        self.features.insert(f);
    }

    /// Get all features
    pub fn features(&self) -> &HashSet<Feature> {
        &self.features
    }

    /// Check if empty
    ///
    /// Kept alive as the mandatory `len`/`is_empty` counterpart (clippy's
    /// `len_without_is_empty` requires it); no test exercises it yet —
    /// awaiting production wiring — 2026-07-31.
    #[cfg(test)]
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.features.is_empty()
    }

    /// Number of features
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.features.len()
    }

    /// Compute overlap (intersection size) with another feature set
    pub fn overlap(&self, other: &FeatureSet) -> usize {
        self.features.intersection(&other.features).count()
    }

    /// Compute Jaccard similarity with another feature set
    pub fn jaccard(&self, other: &FeatureSet) -> f64 {
        let intersection = self.overlap(other);
        let union = self.features.union(&other.features).count();
        if union == 0 {
            0.0
        } else {
            intersection as f64 / union as f64
        }
    }
}

/// Extract features from an expression
pub(crate) struct FeatureExtractor {
    /// Maximum depth for recursive feature extraction
    max_depth: usize,
    /// Whether to include type features
    include_types: bool,
    /// Whether to include application patterns
    include_patterns: bool,
}

impl Default for FeatureExtractor {
    fn default() -> Self {
        Self {
            max_depth: 3,
            include_types: true,
            include_patterns: true,
        }
    }
}

impl FeatureExtractor {
    /// Create a new feature extractor with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Set maximum extraction depth
    #[cfg(test)]
    #[must_use]
    pub fn with_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    /// Enable/disable type features
    #[cfg(test)]
    #[must_use]
    pub fn with_types(mut self, include: bool) -> Self {
        self.include_types = include;
        self
    }

    /// Enable/disable pattern features
    #[cfg(test)]
    #[must_use]
    pub fn with_patterns(mut self, include: bool) -> Self {
        self.include_patterns = include;
        self
    }

    /// Extract features from an expression
    ///
    /// REQUIRES: `expr` is a well-formed Lean expression
    /// ENSURES: Returns features from constants within max_depth
    /// ENSURES: Returns pattern features (App/BinApp) only if include_patterns is true
    /// ENSURES: Traverses type positions (in Lam/Pi) only if include_types is true
    /// ENSURES: For Let, traverses type position only if include_types is true, but val/body always
    /// ENSURES: Feature extraction is deterministic (same input → same output)
    pub fn extract(&self, expr: &Expr) -> FeatureSet {
        let mut features = FeatureSet::new();
        self.extract_recursive(expr, 0, &mut features);
        features
    }

    fn extract_recursive(&self, expr: &Expr, depth: usize, features: &mut FeatureSet) {
        if depth > self.max_depth {
            return;
        }

        match expr.kind() {
            ExprKind::Const(name, _levels) => {
                features.add(Feature::Const(name.clone()));
                // Add theory feature based on name prefix
                if let Some(theory) = self.detect_theory(name) {
                    features.add(Feature::Theory(theory));
                }
            }

            ExprKind::App(f, arg) => {
                // Extract from both parts
                self.extract_recursive(f, depth + 1, features);
                self.extract_recursive(arg, depth + 1, features);

                // Add application pattern feature
                if self.include_patterns {
                    if let ExprKind::Const(name, _) = f.kind() {
                        features.add(Feature::App(name.clone()));
                    }
                    // Check for binary application
                    if let ExprKind::App(ff, _) = f.kind() {
                        if let ExprKind::Const(name, _) = ff.kind() {
                            features.add(Feature::BinApp(name.clone()));
                        }
                    }
                }
            }

            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                if self.include_types {
                    self.extract_recursive(ty, depth + 1, features);
                }
                self.extract_recursive(body, depth + 1, features);
            }

            ExprKind::Let(_, ty, val, body, _) => {
                if self.include_types {
                    self.extract_recursive(ty, depth + 1, features);
                }
                self.extract_recursive(val, depth + 1, features);
                self.extract_recursive(body, depth + 1, features);
            }

            ExprKind::Proj(name, _idx, struct_expr) => {
                features.add(Feature::Const(name.clone()));
                self.extract_recursive(struct_expr, depth + 1, features);
            }

            ExprKind::Sort(_) | ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {
                // Terminal expressions - no features
            }

            // MData is transparent - extract from inner expression
            ExprKind::MData(_, inner) => {
                self.extract_recursive(inner, depth, features);
            }

            // Mode-specific expressions - no features for now
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. }
            | ExprKind::SProp
            | ExprKind::Squash(_) => {
                // Mode-specific expressions - no feature extraction yet
            }
        }
    }

    /// Detect theory based on constant name
    fn detect_theory(&self, name: &Name) -> Option<String> {
        let s = name.to_string();
        // Common prefixes for different theories
        if s.starts_with("Nat.") || s.starts_with("Int.") {
            Some("arith".to_string())
        } else if s.starts_with("List.") || s.starts_with("Array.") {
            Some("list".to_string())
        } else if s.starts_with("Set.") || s.starts_with("Finset.") {
            Some("set".to_string())
        } else if s.starts_with("Real.") || s.starts_with("Complex.") {
            Some("analysis".to_string())
        } else if s.starts_with("String.") || s.starts_with("Char.") {
            Some("string".to_string())
        } else {
            None
        }
    }

    /// Extract all constants from an expression (for MePo)
    pub fn extract_constants(&self, expr: &Expr) -> HashSet<Name> {
        let mut constants = HashSet::new();
        self.extract_constants_recursive(expr, &mut constants);
        constants
    }

    fn extract_constants_recursive(&self, expr: &Expr, constants: &mut HashSet<Name>) {
        match expr.kind() {
            ExprKind::Const(name, _) => {
                constants.insert(name.clone());
            }
            ExprKind::App(f, arg) => {
                self.extract_constants_recursive(f, constants);
                self.extract_constants_recursive(arg, constants);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.extract_constants_recursive(ty, constants);
                self.extract_constants_recursive(body, constants);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.extract_constants_recursive(ty, constants);
                self.extract_constants_recursive(val, constants);
                self.extract_constants_recursive(body, constants);
            }
            ExprKind::Proj(name, _, struct_expr) => {
                constants.insert(name.clone());
                self.extract_constants_recursive(struct_expr, constants);
            }
            ExprKind::Sort(_) | ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {}
            // MData is transparent - extract constants from inner
            ExprKind::MData(_, inner) => {
                self.extract_constants_recursive(inner, constants);
            }
            // Mode-specific expressions - no constants
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. }
            | ExprKind::SProp
            | ExprKind::Squash(_) => {}
        }
    }
}
