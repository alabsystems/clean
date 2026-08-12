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
pub enum ResolveResult {
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
pub fn extract_class_app_with_levels(ty: &Expr) -> Option<(Name, Vec<Level>, Vec<Expr>)> {
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

pub fn extract_class_app(ty: &Expr) -> Option<(Name, Vec<Expr>)> {
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
mod tests {
    use super::*;
    use clean_kernel::expr::Expr;
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;

    #[test]
    fn test_instance_table_basic() {
        let mut table = InstanceTable::new();

        // Register a class
        let add_class = Name::from_string("Add");
        table.register_class(add_class.clone(), 1, vec![]);
        assert!(table.is_class(&add_class));
        assert_eq!(table.num_classes(), 1);

        // Add an instance
        let nat = Name::from_string("Nat");
        let inst_name = Name::from_string("instAddNat");
        let inst_expr = Expr::const_(inst_name.clone(), vec![]);
        let inst_type = Expr::app(
            Expr::const_(add_class.clone(), vec![]),
            Expr::const_(nat.clone(), vec![]),
        );

        table.add_instance(
            inst_name.clone(),
            add_class.clone(),
            inst_expr,
            inst_type,
            DEFAULT_PRIORITY,
        );

        let instances = table.get_instances(&add_class);
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].name, inst_name);
    }

    #[test]
    fn test_instance_priority_ordering() {
        let mut table = InstanceTable::new();

        let class_name = Name::from_string("Show");
        table.register_class(class_name.clone(), 1, vec![]);

        // Add instances with different priorities
        table.add_instance(
            Name::from_string("low"),
            class_name.clone(),
            Expr::const_(Name::from_string("low"), vec![]),
            Expr::const_(class_name.clone(), vec![]),
            50,
        );
        table.add_instance(
            Name::from_string("high"),
            class_name.clone(),
            Expr::const_(Name::from_string("high"), vec![]),
            Expr::const_(class_name.clone(), vec![]),
            150,
        );
        table.add_instance(
            Name::from_string("default"),
            class_name.clone(),
            Expr::const_(Name::from_string("default"), vec![]),
            Expr::const_(class_name.clone(), vec![]),
            100,
        );

        let instances = table.get_instances(&class_name);
        assert_eq!(instances.len(), 3);
        assert_eq!(instances[0].name, Name::from_string("high"));
        assert_eq!(instances[1].name, Name::from_string("default"));
        assert_eq!(instances[2].name, Name::from_string("low"));
    }

    #[test]
    fn test_equal_priority_preserves_feed_order() {
        // Tie-break contract (B99): `add_instance` inserts a new instance
        // AFTER existing entries of the SAME priority (`position(<)`), i.e.
        // the table preserves the feed order within a tier. The kernel env
        // registry feeds `init_instances_from_env` most-recent-FIRST within a
        // tier (`register_instance` inserts before `<=`), so the elaborated
        // table order is: priority desc, then most-recent-first — the
        // Lean-faithful order `candidate_order`'s ascending-index tiebreak
        // then consumes.
        let mut table = InstanceTable::new();
        let class_name = Name::from_string("Tie");
        table.register_class(class_name.clone(), 1, vec![]);

        // Simulate the kernel-env feed for: `older` declared first, `newer`
        // declared second, both at DEFAULT_PRIORITY. The env registry yields
        // them newest-first, so the table receives `newer` then `older`.
        for name in ["newer", "older"] {
            table.add_instance(
                Name::from_string(name),
                class_name.clone(),
                Expr::const_(Name::from_string(name), vec![]),
                Expr::const_(class_name.clone(), vec![]),
                DEFAULT_PRIORITY,
            );
        }
        // A higher-priority instance still dominates both, regardless of feed
        // position.
        table.add_instance(
            Name::from_string("high"),
            class_name.clone(),
            Expr::const_(Name::from_string("high"), vec![]),
            Expr::const_(class_name.clone(), vec![]),
            DEFAULT_PRIORITY + 1,
        );

        let names: Vec<String> = table
            .get_instances(&class_name)
            .iter()
            .map(|i| i.name.to_string())
            .collect();
        assert_eq!(
            names,
            vec!["high", "newer", "older"],
            "table order must be priority desc, then feed order (newest first) within a tier"
        );
    }

    #[test]
    fn test_default_priority_is_lean_default() {
        // Lean fidelity pin: default 1000 sits strictly between `low` (100)
        // and `high` (10000), so `(priority := low)` LOSES to an unannotated
        // instance and `(priority := high)` beats one (B99).
        assert_eq!(DEFAULT_PRIORITY, 1000);
    }

    #[test]
    fn test_extract_class_app() {
        // Test Add Nat
        let add = Name::from_string("Add");
        let nat = Name::from_string("Nat");
        let ty = Expr::app(
            Expr::const_(add.clone(), vec![]),
            Expr::const_(nat.clone(), vec![]),
        );

        let result = extract_class_app(&ty);
        let (class_name, args) = result.expect("extract_class_app should find Add Nat");
        assert_eq!(class_name, add);
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].kind(), ExprKind::Const(n, _) if *n == nat));
    }

    #[test]
    fn test_extract_class_app_multiple_args() {
        // Test Functor F A
        let functor = Name::from_string("Functor");
        let f = Name::from_string("F");
        let a = Name::from_string("A");

        let ty = Expr::app(
            Expr::app(
                Expr::const_(functor.clone(), vec![]),
                Expr::const_(f.clone(), vec![]),
            ),
            Expr::const_(a.clone(), vec![]),
        );

        let result = extract_class_app(&ty);
        let (class_name, args) = result.expect("extract_class_app should find Functor F A");
        assert_eq!(class_name, functor);
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn test_extract_class_app_no_args() {
        // Test bare class name
        let inhabited = Name::from_string("Inhabited");
        let ty = Expr::const_(inhabited.clone(), vec![]);

        let result = extract_class_app(&ty);
        let (class_name, args) = result.expect("extract_class_app should find bare Inhabited");
        assert_eq!(class_name, inhabited);
        assert_eq!(args.len(), 0);
    }

    #[test]
    fn test_extract_class_app_non_class() {
        // Test non-constant head (e.g., a BVar)
        let ty = Expr::bvar(0);
        assert!(
            extract_class_app(&ty).is_none(),
            "BVar should not be a class app"
        );

        // Test Sort
        let ty = Expr::sort(Level::zero());
        assert!(
            extract_class_app(&ty).is_none(),
            "Sort should not be a class app"
        );
    }

    #[test]
    fn test_class_with_out_params() {
        let mut table = InstanceTable::new();

        // Register OutParam-style class like `Functor`
        let functor = Name::from_string("Functor");
        table.register_class(functor.clone(), 1, vec![0]); // F is an out-param

        let info = table.get_class(&functor).unwrap();
        assert_eq!(info.num_params, 1);
        assert_eq!(info.out_params, vec![0]);
    }
}
