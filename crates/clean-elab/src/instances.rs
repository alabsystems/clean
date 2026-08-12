// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type class instance resolution
//!
//! This module implements type class instance resolution for clean.
//!
//! # Overview
//!
//! Type classes in Lean are structures marked with `class`. Instances are
//! definitions that provide implementations of a type class for specific types.
//!
//! For example:
//! ```lean
//! class Add (α : Type) where
//!   add : α → α → α
//!
//! instance : Add Nat where
//!   add := Nat.add
//! ```
//!
//! When elaborating `[inst : Add α]`, the instance resolver searches for
//! a registered instance that can provide `Add α`.
//!
//! # Algorithm
//!
//! The resolution algorithm uses a simple depth-first search:
//! 1. Normalize the target type to get the class name and arguments
//! 2. Look up all instances for that class
//! 3. Try each instance in priority order
//! 4. For each instance, unify its result type with the target
//! 5. Recursively resolve any instance arguments the instance requires
//!
//! # Priority
//!
//! Instances have numeric priorities (higher = tried first).
//! Default priority is 1000 (Lean's `default`; `low` = 100, `high` = 10000).
//! Instances can override with e.g. `(priority := low)` or `@[instance 50]`.
//! Within one priority tier, candidates are tried most-recent-first (the
//! kernel registry prepends within a tier and [`InstanceTable`] preserves
//! that feed order — see `test_equal_priority_preserves_feed_order`).

use clean_kernel::expr::Expr;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use std::collections::HashMap;

/// Information about a type class
#[derive(Clone, Debug)]
pub struct ClassInfo {
    /// Name of the type class (e.g., `Add`)
    pub name: Name,
    /// Number of parameters (e.g., 1 for `Add α`)
    pub num_params: usize,
    /// Indices of "output parameters" that can be inferred from other params
    /// For example, in `Functor F`, F is an out-param if the functor can be inferred from context
    pub out_params: Vec<usize>,
    /// Indices of "semi-output parameters" that are filled by instances but can also
    /// be constrained by context. Unlike outParams, semiOutParams participate in
    /// normal unification but instances are expected to provide concrete values.
    pub semi_out_params: Vec<usize>,
}

/// Information about a type class instance
#[derive(Clone, Debug)]
pub struct InstanceInfo {
    /// Name of the instance definition
    pub name: Name,
    /// Name of the class this instance implements
    pub class_name: Name,
    /// The instance expression (may have universe parameters)
    pub expr: Expr,
    /// The instance type (e.g., `Add Nat`)
    pub type_: Expr,
    /// Priority (higher = tried first)
    pub priority: u32,
    /// Synthesization order for the instance's Pi-telescope binders (Lean's
    /// `InstanceEntry.synthOrder`, `Lean/Meta/Instances.lean:46-60`): binder
    /// indices in the order their `[inst]` sub-goals must be synthesized so
    /// each sub-goal's solution determines the metavariables later ones
    /// consume. `None` = not persisted (hand-registered lane); the resolver
    /// computes a Lean-style default (see `infer::synth_order`).
    pub synth_order: Option<Vec<usize>>,
}

/// Default instance priority — Lean's `default` prio (1000).
///
/// Lean's priority keywords: `low` = 100, `default`/`mid` = 1000,
/// `high` = 10000 (`Init/Prelude` `prio` macros; clean-parser's
/// `instance_priority_value` maps the keywords identically). This constant
/// was previously 100, which made an UNANNOTATED instance TIE with a
/// `(priority := low)` one — and the most-recent-first tie-break then let a
/// newer low-priority instance silently beat an older default-priority one
/// (r82 `instprio_low_loses_recency`: 5 provable where Lean proves 4). B99.
///
/// NOTE: every hand-registered prelude instance that Lean also declares now
/// records the priority the shipped `.olean` serializes — 1000 for all but
/// `instBEqOfDecidableEq` (500) — so a user instance no longer OUT-prioritizes
/// it but TIES with it, and the most-recent-first tie-break decides. The winner
/// is unchanged (a user instance is always newer than the prelude) and it is
/// now the winner for Lean's reason rather than by accident. Prelude instances
/// with no Lean twin still carry the fabricated
/// `clean_kernel::DEFAULT_INSTANCE_PRIORITY` (100). Census + ratchet:
/// `data/prelude_instance_priority_census.json`.
pub const DEFAULT_PRIORITY: u32 = 1000;

/// Instance table for efficient lookup
#[derive(Clone, Debug, Default)]
pub struct InstanceTable {
    /// Registered type classes
    classes: HashMap<Name, ClassInfo>,
    /// Instances by class name, sorted by priority (highest first)
    instances: HashMap<Name, Vec<InstanceInfo>>,
}

impl InstanceTable {
    /// Create a new empty instance table
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a type class
    ///
    /// # Arguments
    /// * `name` - The name of the type class
    /// * `num_params` - Number of parameters the class takes
    /// * `out_params` - Indices of output parameters (can be empty)
    pub fn register_class(&mut self, name: Name, num_params: usize, out_params: Vec<usize>) {
        self.classes.insert(
            name.clone(),
            ClassInfo {
                name,
                num_params,
                out_params,
                semi_out_params: Vec::new(),
            },
        );
    }

    /// Register a type class with both out-params and semi-out-params
    ///
    /// # Arguments
    /// * `name` - The name of the type class
    /// * `num_params` - Number of parameters the class takes
    /// * `out_params` - Indices of output parameters
    /// * `semi_out_params` - Indices of semi-output parameters
    pub fn register_class_full(
        &mut self,
        name: Name,
        num_params: usize,
        out_params: Vec<usize>,
        semi_out_params: Vec<usize>,
    ) {
        self.classes.insert(
            name.clone(),
            ClassInfo {
                name,
                num_params,
                out_params,
                semi_out_params,
            },
        );
    }

    /// Check if a name is a registered type class
    pub fn is_class(&self, name: &Name) -> bool {
        self.classes.contains_key(name)
    }

    /// Get information about a type class
    pub fn get_class(&self, name: &Name) -> Option<&ClassInfo> {
        self.classes.get(name)
    }

    /// Add an instance for a type class
    ///
    /// # Arguments
    /// * `instance_name` - Name of the instance definition
    /// * `class_name` - Name of the type class
    /// * `expr` - The instance expression
    /// * `type_` - The instance type (fully elaborated)
    /// * `priority` - Instance priority (higher = tried first)
    pub fn add_instance(
        &mut self,
        instance_name: Name,
        class_name: Name,
        expr: Expr,
        type_: Expr,
        priority: u32,
    ) {
        self.add_instance_with_synth_order(instance_name, class_name, expr, type_, priority, None);
    }

    /// Add an instance carrying a persisted synthesization order
    /// (`InstanceEntry.synthOrder`; see [`InstanceInfo::synth_order`]).
    ///
    /// [`Self::add_instance`] delegates here with `synth_order = None`,
    /// which makes the resolver compute a Lean-style default.
    pub fn add_instance_with_synth_order(
        &mut self,
        instance_name: Name,
        class_name: Name,
        expr: Expr,
        type_: Expr,
        priority: u32,
        synth_order: Option<Vec<usize>>,
    ) {
        let info = InstanceInfo {
            name: instance_name,
            class_name: class_name.clone(),
            expr,
            type_,
            priority,
            synth_order,
        };

        let instances = self.instances.entry(class_name).or_default();

        // Insert maintaining sorted order by priority (highest first)
        let pos = instances
            .iter()
            .position(|i| i.priority < priority)
            .unwrap_or(instances.len());
        instances.insert(pos, info);
    }

    /// Get all instances for a class, sorted by priority (highest first)
    pub fn get_instances(&self, class_name: &Name) -> &[InstanceInfo] {
        self.instances.get(class_name).map_or(&[], Vec::as_slice)
    }

    /// Get all registered classes
    pub fn classes(&self) -> impl Iterator<Item = &ClassInfo> {
        self.classes.values()
    }

    /// Get number of registered classes
    pub fn num_classes(&self) -> usize {
        self.classes.len()
    }

    /// Get total number of instances
    pub fn num_instances(&self) -> usize {
        self.instances.values().map(Vec::len).sum()
    }
}

/// Result of instance resolution
#[derive(Clone, Debug)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) enum ResolveResult {
    /// Successfully resolved to an instance expression
    Success(Expr),
    /// No matching instance found
    NotFound,
    /// Resolution failed with an error
    Error(String),
}

/// Extract the class name and arguments from a type expression
///
/// For `Add Nat`, returns `Some((Add, [Nat]))`
/// For non-class types, returns `None`
/// Like [`extract_class_app`], but also returns the class constant's
/// UNIVERSE LEVELS.
///
/// Instance search matches a candidate against a goal by class name and
/// argument list; the levels on the class constant itself were dropped on
/// the floor. That is fine while every class is universe-monomorphic at the
/// use site, but a class with a level the ARGUMENTS do not mention — Lean's
/// `class HasEquiv.{u,v} (α : Sort u) where Equiv : α → α → Sort v`, whose
/// `v` appears only in a FIELD — leaves that level an unsolved metavariable
/// in the goal (`HasEquiv {1, ?v} Nat`), and no amount of argument
/// unification can pin it. Unifying the level lists at the match site
/// solves it from the candidate (`instHasEquivOfSetoid : HasEquiv.{u,0} α`
/// gives `?v := 0`), which is what makes the `≈` notation resolve.
pub(crate) fn extract_class_app_with_levels(ty: &Expr) -> Option<(Name, Vec<Level>, Vec<Expr>)> {
    let mut args = Vec::new();
    let mut current = ty;
    while let ExprKind::App(func, arg) = current.kind() {
        args.push(arg.as_ref().clone());
        current = func.as_ref();
    }
    if let ExprKind::Const(name, levels) = current.kind() {
        args.reverse();
        Some((name.clone(), levels.to_vec(), args))
    } else {
        None
    }
}

pub(crate) fn extract_class_app(ty: &Expr) -> Option<(Name, Vec<Expr>)> {
    let mut args = Vec::new();
    let mut current = ty;

    // Unwrap applications to get the head and arguments
    while let ExprKind::App(func, arg) = current.kind() {
        args.push(arg.as_ref().clone());
        current = func.as_ref();
    }

    // The head should be a constant (the class name)
    if let ExprKind::Const(name, _) = current.kind() {
        args.reverse(); // Args were collected in reverse order
        Some((name.clone(), args))
    } else {
        None
    }
}

#[cfg(test)]
#[path = "instances_tests.rs"]
mod tests;
