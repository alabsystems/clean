// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simplification procedures (simprocs) for the `simp` tactic.
//!
//! A simproc is a custom simplification procedure invoked during simp's main
//! loop. Unlike simp lemmas (which are rewrite rules), simprocs are arbitrary
//! functions that can evaluate expressions. For example, `Nat.reduceAdd`
//! evaluates `2 + 3` to `5` by computing the result.
//!
//! In Lean 4, simprocs are declared via the `@[simproc]` attribute and
//! registered in `Lean.Meta.Simp.Simprocs`. This module implements the
//! equivalent infrastructure for clean.
//!
//! ## Architecture
//!
//! - [`Simproc`] wraps a function pointer with metadata (name, discriminant)
//! - [`SimprocSet`] is the registry of all available simprocs
//! - [`SimprocResult`] describes the outcome: `Continue`, `Done`, or `Visit`
//! - Built-in simprocs for Nat arithmetic are in [`super::simproc_builtins`]
//!
//! ## Integration
//!
//! The main simp loop in `simp/mod.rs` calls `try_simprocs` after attempting
//! lemma rewrites. If a simproc fires, its result (with proof) is used just
//! like a lemma rewrite.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::tactic::core::{Goal, ProofState};

use super::types::SimpResult;
use super::{simproc_builtins, simproc_builtins_bool};

/// The result of running a simproc on an expression.
///
/// Mirrors Lean 4's `Simp.Step` with three outcomes.
#[derive(Debug, Clone)]
pub(crate) enum SimprocResult {
    /// The simproc did not apply to this expression.
    Continue,
    /// The simproc fully reduced the expression.
    /// Contains the simplified expression and an optional proof.
    Done(SimpResult),
    /// The simproc made partial progress; simp should continue simplifying
    /// the result. Contains the partially simplified expression and proof.
    Visit(SimpResult),
}

/// Type alias for simproc functions.
///
/// A simproc takes the proof state, current goal, and the expression to
/// simplify, and returns a `SimprocResult`.
pub(crate) type SimprocFn = fn(&ProofState, &Goal, &Expr) -> SimprocResult;

/// A registered simplification procedure.
#[derive(Clone)]
pub(crate) struct Simproc {
    /// Name of the simproc (e.g., `Nat.reduceAdd`)
    pub(crate) name: Name,
    /// The head constant this simproc matches on.
    /// Used for fast dispatch — the simproc is only invoked when the
    /// expression's head matches this discriminant.
    pub(crate) discriminant: Name,
    /// The actual simplification function.
    pub(crate) proc: SimprocFn,
    /// Priority (higher = tried first, like simp lemmas).
    pub(crate) priority: u32,
}

impl std::fmt::Debug for Simproc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Simproc")
            .field("name", &self.name)
            .field("discriminant", &self.discriminant)
            .field("priority", &self.priority)
            .finish()
    }
}

/// Registry of simplification procedures, indexed by head discriminant
/// for O(1) dispatch.
#[derive(Debug, Clone, Default)]
pub(crate) struct SimprocSet {
    /// All registered simprocs, sorted by priority (highest first).
    all: Vec<Simproc>,
    /// Index from head constant name to indices into `all`.
    index: hashbrown::HashMap<Name, Vec<usize>>,
}

impl SimprocSet {
    /// Create a new empty registry.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a simproc.
    ///
    /// ENSURES: The simproc is added to the registry and indexed by its discriminant.
    pub(crate) fn register(&mut self, sp: Simproc) {
        let idx = self.all.len();
        self.index
            .entry(sp.discriminant.clone())
            .or_default()
            .push(idx);
        self.all.push(sp);
    }

    /// Get simprocs matching the given expression head.
    ///
    /// Returns simprocs whose discriminant matches the expression's head constant,
    /// sorted by priority (highest first).
    pub(crate) fn get_matching(&self, expr: &Expr) -> Vec<&Simproc> {
        let head = expr.get_app_fn();
        let head_name = match head.kind() {
            ExprKind::Const(name, _) => name,
            _ => return Vec::new(),
        };

        let Some(indices) = self.index.get(head_name) else {
            return Vec::new();
        };

        let mut result: Vec<&Simproc> = indices.iter().map(|&idx| &self.all[idx]).collect();
        result.sort_by_key(|b| std::cmp::Reverse(b.priority));
        result
    }

    /// Check if the registry is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.all.is_empty()
    }

    /// Number of registered simprocs.
    pub(crate) fn len(&self) -> usize {
        self.all.len()
    }
}

/// Try applying simprocs to an expression.
///
/// Iterates through simprocs matching the expression's head and returns
/// the first successful result.
///
/// REQUIRES: `simprocs` is a valid simproc registry
/// ENSURES: Returns `Some(SimpResult)` if a simproc fired, `None` otherwise
/// ENSURES: The returned SimpResult has a valid proof term if non-definitional
pub(crate) fn try_simprocs(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    simprocs: &SimprocSet,
) -> Option<SimpResult> {
    if simprocs.is_empty() {
        return None;
    }

    for sp in simprocs.get_matching(expr) {
        match (sp.proc)(state, goal, expr) {
            SimprocResult::Done(result) | SimprocResult::Visit(result) => {
                if result.expr != *expr {
                    return Some(result);
                }
            }
            SimprocResult::Continue => {}
        }
    }

    None
}

/// Create the default set of built-in simprocs.
///
/// These correspond to the simprocs registered by Lean 4's Init library:
/// - `Nat.reduceAdd`, `Nat.reduceMul`, `Nat.reducePow` (arithmetic)
/// - `Nat.reduceSub` (saturating subtraction)
/// - `Nat.reduceSucc`, `Nat.reduceGcd` (unary/binary)
/// - `Nat.reduceMod`, `Nat.reduceDiv` (division)
/// - `Nat.reduceBEq`, `Nat.reduceLt`, `Nat.reduceLe` (comparisons)
///
/// ENSURES: Returns a `SimprocSet` with all built-in simprocs registered
pub(crate) fn builtin_simprocs() -> SimprocSet {
    let mut set = SimprocSet::new();
    simproc_builtins::register_nat_arith(&mut set);
    simproc_builtins::register_nat_comparisons(&mut set);
    simproc_builtins_bool::register_bool_simprocs(&mut set);
    simproc_builtins_bool::register_prop_simprocs(&mut set);
    set
}
