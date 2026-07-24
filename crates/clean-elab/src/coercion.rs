// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coercion insertion for the elaborator.
//!
//! When the elaborator encounters a type mismatch between an expected type and
//! an inferred type, it consults the coercion registry for a registered
//! `@[coe]` function that bridges the gap. If found, the expression is wrapped
//! in a coercion application transparently.
//!
//! # Architecture
//!
//! - [`CoercionRegistry`] stores registered coercion functions indexed by
//!   (source, target) type pairs for O(1) lookup.
//! - [`CoercionEntry`] describes a single coercion with its source type, target
//!   type, and function name.
//! - [`find_coercion_chain`] resolves transitive coercion paths (A->B->C) via
//!   BFS with cycle detection.
//! - [`apply_coercion`] wraps an expression with a coercion function application.
//! - [`CoercionKind`] distinguishes direct `@[coe]` coercions from type class
//!   coercions (CoeTC, CoeHTCoe) and built-in up-casts (Nat->Int).
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Elab/Coercion.lean`, `src/Lean/Meta/Coe.lean`

use std::collections::{HashMap, HashSet, VecDeque};

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use crate::error::ElabError;

/// Maximum chain length for transitive coercion resolution.
/// Prevents runaway search in large coercion graphs.
const MAX_COERCION_CHAIN_LENGTH: usize = 8;

/// Kind of coercion, distinguishing how the coercion was registered.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum CoercionKind {
    /// Direct `@[coe]` attribute coercion.
    Direct,
    /// Type class coercion via `Coe` instance.
    CoeTC,
    /// Heterogeneous type class coercion via `CoeHTCoe` instance.
    CoeHTCoe,
    /// Built-in numeric up-cast (e.g., Nat -> Int, Int -> Rat).
    BuiltinUpcast,
}

/// A single registered coercion entry.
#[derive(Debug, Clone)]
pub(crate) struct CoercionEntry {
    /// Fully qualified name of the coercion function.
    pub(crate) fn_name: Name,
    /// Source type name (head constant of the source type).
    pub(crate) source: Name,
    /// Target type name (head constant of the target type).
    pub(crate) target: Name,
    /// How this coercion was registered.
    pub(crate) kind: CoercionKind,
}

/// Result of a coercion lookup: either a single step or a chain.
#[derive(Debug, Clone)]
pub(crate) struct CoercionPath {
    /// Ordered sequence of coercion entries from source to target.
    pub(crate) steps: Vec<CoercionEntry>,
}

impl CoercionPath {
    /// Number of coercion steps in this path.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether this path is empty (no coercions needed).
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// Registry of coercion functions indexed by (source, target) type pairs.
///
/// Supports O(1) direct lookup and BFS chain resolution for transitive
/// coercions. Thread-safe for read-only access after construction.
#[derive(Debug, Clone, Default)]
pub(crate) struct CoercionRegistry {
    /// Direct coercions indexed by (source_type, target_type).
    direct: HashMap<(Name, Name), CoercionEntry>,
    /// All coercions originating from a given source type.
    /// Used for BFS chain resolution.
    by_source: HashMap<Name, Vec<CoercionEntry>>,
    /// Set of all registered coercion function names for quick membership check.
    registered_names: HashSet<Name>,
}

impl CoercionRegistry {
    /// Create a new, empty coercion registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a coercion function.
    ///
    /// # Errors
    ///
    /// Returns `Err` if a coercion from `source` to `target` is already
    /// registered (prevents ambiguous coercion paths).
    pub(crate) fn register(&mut self, entry: CoercionEntry) -> Result<(), ElabError> {
        let key = (entry.source.clone(), entry.target.clone());
        if self.direct.contains_key(&key) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "coercion from '{}' to '{}' is already registered",
                    entry.source, entry.target,
                ),
            });
        }
        self.registered_names.insert(entry.fn_name.clone());
        self.by_source
            .entry(entry.source.clone())
            .or_default()
            .push(entry.clone());
        self.direct.insert(key, entry);
        Ok(())
    }

    /// Register a built-in numeric up-cast coercion.
    pub(crate) fn register_builtin_upcast(
        &mut self,
        fn_name: &str,
        source: &str,
        target: &str,
    ) -> Result<(), ElabError> {
        self.register(CoercionEntry {
            fn_name: Name::from_string(fn_name),
            source: Name::from_string(source),
            target: Name::from_string(target),
            kind: CoercionKind::BuiltinUpcast,
        })
    }

    /// Create a registry pre-populated with standard built-in up-casts.
    #[must_use]
    pub(crate) fn with_builtins() -> Self {
        let mut reg = Self::new();
        // Nat -> Int is the most common built-in coercion in Lean 4.
        // Ignoring errors here since we control the inputs.
        let _ = reg.register_builtin_upcast("Int.ofNat", "Nat", "Int");
        reg
    }

    /// Look up a direct (single-step) coercion from `source` to `target`.
    #[must_use]
    pub(crate) fn find_direct(&self, source: &Name, target: &Name) -> Option<&CoercionEntry> {
        self.direct.get(&(source.clone(), target.clone()))
    }

    /// Check whether a function name is registered as a coercion.
    #[must_use]
    pub(crate) fn is_coercion(&self, name: &Name) -> bool {
        self.registered_names.contains(name)
    }

    /// Number of registered coercions.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.direct.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.direct.is_empty()
    }

    /// Find a coercion path from `source` to `target`, possibly via
    /// intermediate types (BFS with cycle detection).
    ///
    /// Returns `None` if no path exists within `MAX_COERCION_CHAIN_LENGTH`.
    #[must_use]
    pub(crate) fn find_chain(&self, source: &Name, target: &Name) -> Option<CoercionPath> {
        // Fast path: direct lookup.
        if let Some(entry) = self.find_direct(source, target) {
            return Some(CoercionPath {
                steps: vec![entry.clone()],
            });
        }

        // BFS for transitive coercion chains.
        let mut visited: HashSet<Name> = HashSet::new();
        visited.insert(source.clone());

        // Queue entries: (current_type, path_so_far)
        let mut queue: VecDeque<(Name, Vec<CoercionEntry>)> = VecDeque::new();
        queue.push_back((source.clone(), Vec::new()));

        while let Some((current, path)) = queue.pop_front() {
            if path.len() >= MAX_COERCION_CHAIN_LENGTH {
                continue;
            }
            let Some(neighbors) = self.by_source.get(&current) else {
                continue;
            };
            for entry in neighbors {
                if entry.target == *target {
                    let mut full_path = path.clone();
                    full_path.push(entry.clone());
                    return Some(CoercionPath { steps: full_path });
                }
                if visited.insert(entry.target.clone()) {
                    let mut new_path = path.clone();
                    new_path.push(entry.clone());
                    queue.push_back((entry.target.clone(), new_path));
                }
            }
        }

        None
    }

    /// Iterate over all registered coercion entries.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &CoercionEntry> {
        self.direct.values()
    }
}

// ============================================================================
// Coercion application
// ============================================================================

/// Apply a single coercion to an expression.
///
/// Constructs `coercion_fn expr`, wrapping the expression with the coercion
/// function application.
///
/// # REQUIRES
/// - `coercion_fn_name` refers to a valid coercion function
/// - `expr` is well-typed with the coercion's source type
///
/// # ENSURES
/// - Returns `Expr::app(Expr::const_(coercion_fn_name, []), expr)`
pub(crate) fn apply_coercion(coercion_fn_name: &Name, expr: Expr) -> Expr {
    Expr::app(Expr::const_(coercion_fn_name.clone(), Vec::new()), expr)
}

/// Apply a coercion path (possibly multi-step) to an expression.
///
/// For a path [A->B, B->C], transforms `expr` into `coe_BC (coe_AB expr)`.
///
/// # REQUIRES
/// - `path` is a valid coercion chain
/// - `expr` is well-typed with the first coercion's source type
///
/// # ENSURES
/// - Each coercion in the path is applied left-to-right
/// - Empty path returns `expr` unchanged
pub(crate) fn apply_coercion_path(path: &CoercionPath, expr: Expr) -> Expr {
    path.steps
        .iter()
        .fold(expr, |acc, entry| apply_coercion(&entry.fn_name, acc))
}

// ============================================================================
// Head type extraction
// ============================================================================

/// Extract the head constant name from a type expression.
///
/// For `Nat`, returns `Nat`.
/// For `List Nat`, returns `List`.
/// For `@Array Nat 5`, returns `Array`.
/// For non-constant heads (bvar, fvar, etc.), returns `None`.
#[must_use]
pub(crate) fn head_type_name(ty: &Expr) -> Option<Name> {
    let head = ty.get_app_fn();
    match head.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Attempt to find and apply a coercion for a type mismatch.
///
/// Given an expression with `actual_type` where `expected_type` is needed,
/// looks up a coercion (direct or chain) and wraps the expression if found.
///
/// # REQUIRES
/// - `registry` is a valid coercion registry
/// - `expr` is well-typed with `actual_type`
///
/// # ENSURES
/// - On `Ok(expr)`, the returned expression has been wrapped with coercions
/// - On `Err`, no applicable coercion was found
pub(crate) fn try_coerce(
    registry: &CoercionRegistry,
    expr: Expr,
    actual_type: &Expr,
    expected_type: &Expr,
) -> Result<Expr, ElabError> {
    let source = head_type_name(actual_type).ok_or_else(|| ElabError::TypeMismatch {
        expected: format!("{expected_type:?}"),
        actual: format!("{actual_type:?}"),
    })?;
    let target = head_type_name(expected_type).ok_or_else(|| ElabError::TypeMismatch {
        expected: format!("{expected_type:?}"),
        actual: format!("{actual_type:?}"),
    })?;

    let path = registry
        .find_chain(&source, &target)
        .ok_or_else(|| ElabError::TypeMismatch {
            expected: format!("{expected_type:?}"),
            actual: format!("{actual_type:?}"),
        })?;

    Ok(apply_coercion_path(&path, expr))
}

#[cfg(test)]
#[path = "coercion_tests.rs"]
mod tests;
