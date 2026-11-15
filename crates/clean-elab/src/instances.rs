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
//! Default priority is 1000 (Lean's `default`; `low` = 100, `mid` = 500,
//! `high` = 10000).
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
/// Lean's priority keywords: `low` = 100, `mid` = 500, `default` = 1000,
/// `high` = 10000 (`Init/Notation.lean` `prio` macros; clean-parser's
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
    /// Registered classes that are reducible ALIASES of another class
    /// (`DecidableLT α` ⟶ `∀ a b, Decidable (a < b)`), keyed by the class they
    /// conclude in — see [`crate::instance_alias`]. Empty unless the table was
    /// built from an environment (`init_instances_from_env`).
    aliases: HashMap<Name, Vec<crate::instance_alias::ClassAlias>>,
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
    pub(crate) fn register_class_full(
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
    pub(crate) fn add_instance_with_synth_order(
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

    /// Append an instance WITHOUT maintaining the priority order; the caller
    /// must finish with [`Self::sort_instances_by_priority`] before the table
    /// is read. Bulk-load path for [`crate::infer::ElabCtx::new`].
    ///
    /// MEASURED (Mathlib `Logic/Basic` through `clean check`, 166k-constant
    /// environment): with the local-context cache in place, 76-93% of all
    /// elaboration time was `ElabCtx::new` → `init_instances_from_env` →
    /// [`Self::add_instance_with_synth_order`] — the sorted insert's position
    /// scan plus `Vec::insert` shift make loading a class's instances
    /// QUADRATIC in their count, paid again for EVERY declaration because the
    /// table is rebuilt per `ElabCtx`. Appending and sorting once is
    /// O(n log n) and yields the identical order (see the sort's contract).
    pub(crate) fn push_instance_unsorted(
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
        self.instances.entry(class_name).or_default().push(info);
    }

    /// Restore the per-class order [`Self::add_instance_with_synth_order`]
    /// maintains: priority descending, and among equal priorities the
    /// insertion order. The sorted insert places each newcomer after every
    /// existing entry of priority `>=` its own, which is exactly what a STABLE
    /// descending sort of the append order produces — so a table bulk-loaded
    /// through [`Self::push_instance_unsorted`] and sorted here is
    /// element-for-element equal to one built by repeated sorted inserts.
    pub(crate) fn sort_instances_by_priority(&mut self) {
        for instances in self.instances.values_mut() {
            // `sort_by_key` is stable.
            instances.sort_by_key(|info| std::cmp::Reverse(info.priority));
        }
    }

    /// Put the entries of `changed` where Lean's state has them: each named
    /// in `entries` takes that priority, and every class holding one of them
    /// is re-sorted into Lean's order — priority descending, then position in
    /// the index descending (`SynthInstance.getInstances` stable-sorts the
    /// leaf by priority and tries the last entry first). A position not in
    /// `entries` is the environment's (`Environment::instance_seq`).
    pub(crate) fn apply_instance_entries(
        &mut self,
        changed: &[Name],
        entries: &HashMap<Name, crate::instance_store::FrameEntry>,
        env: &clean_kernel::Environment,
    ) {
        if changed.is_empty() {
            return;
        }
        let changed: std::collections::HashSet<&Name> = changed.iter().collect();
        for instances in self.instances.values_mut() {
            if !instances.iter().any(|info| changed.contains(&info.name)) {
                continue;
            }
            for info in instances.iter_mut() {
                if let Some(entry) = entries.get(&info.name) {
                    info.priority = entry.priority;
                }
            }
            let seq_of = |name: &Name| {
                entries
                    .get(name)
                    .map(|entry| entry.seq)
                    .or_else(|| env.instance_seq(name))
                    .unwrap_or(0)
            };
            instances.sort_by_cached_key(|info| {
                (
                    std::cmp::Reverse(info.priority),
                    std::cmp::Reverse(seq_of(&info.name)),
                )
            });
        }
    }

    /// The buckets holding any of `names`, as they are now (for
    /// [`Self::restore_buckets`]).
    pub(crate) fn snapshot_buckets(&self, names: &[Name]) -> Vec<(Name, Vec<InstanceInfo>)> {
        let names: std::collections::HashSet<&Name> = names.iter().collect();
        self.instances
            .iter()
            .filter(|(_, instances)| instances.iter().any(|info| names.contains(&info.name)))
            .map(|(class, instances)| (class.clone(), instances.clone()))
            .collect()
    }

    /// Put back buckets [`Self::snapshot_buckets`] took.
    pub(crate) fn restore_buckets(&mut self, buckets: Vec<(Name, Vec<InstanceInfo>)>) {
        for (class, instances) in buckets {
            self.instances.insert(class, instances);
        }
    }

    /// Get all instances for a class, sorted by priority (highest first)
    pub(crate) fn get_instances(&self, class_name: &Name) -> &[InstanceInfo] {
        self.instances.get(class_name).map_or(&[], Vec::as_slice)
    }

    /// Record the reducible class aliases of the table's classes, grouped by
    /// the class each concludes in ([`crate::instance_alias::class_aliases_by_final`]).
    pub(crate) fn set_class_aliases(
        &mut self,
        aliases: HashMap<Name, Vec<crate::instance_alias::ClassAlias>>,
    ) {
        self.aliases = aliases;
    }

    /// The registered alias classes whose reducible telescope concludes in
    /// `final_class` (`Decidable` ⟶ `DecidableEq`, `DecidableLT`, …).
    pub(crate) fn aliases_of(&self, final_class: &Name) -> &[crate::instance_alias::ClassAlias] {
        self.aliases.get(final_class).map_or(&[], Vec::as_slice)
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

/// The class a `@[instance]` target registers under: the constant head of its
/// type's conclusion.
///
/// Lean's `instance` attribute (`src/Lean/Meta/Instances.lean`, `addInstance`
/// → `getClassName`) reads the class off the declaration's type after peeling
/// the telescope, and rejects a declaration whose conclusion is not a class
/// application. This is the single implementation of that rule — every caller
/// that registers a `KernelInstanceInfo` from a declaration name must use it,
/// so no path can drift into inventing a class name of its own.
///
/// # Errors
///
/// - [`ElabError::UnknownIdent`] if `decl_name` is not in `env`.
/// - [`ElabError::Unsupported`] if the conclusion is not an application of a
///   registered class (Lean's "invalid 'instance' attribute").
pub(crate) fn instance_class_of(
    env: &clean_kernel::Environment,
    decl_name: &Name,
) -> Result<Name, crate::ElabError> {
    let target_ty = env
        .get_const(decl_name)
        .map(|info| info.type_.clone())
        .ok_or_else(|| {
            crate::ElabError::UnknownIdent(format!("attribute [instance] target {decl_name}"))
        })?;
    let mut conclusion = &target_ty;
    while let ExprKind::Pi(_, _, body) = conclusion.kind() {
        conclusion = body;
    }
    // A reducible ALIAS of a class (`DecidableLT α` ⟶ `∀ a b, Decidable (a <
    // b)`) is accepted too: Lean's `getClassName` reads the class through a
    // reducible telescope, so `attribute [instance] LinearOrder.toDecidableLT`
    // is an instance of `Decidable`. Clean files it under the alias, as
    // `clean-olean` files the imported ones, and the caller registers the
    // alias as a class ([`crate::instance_alias::register_alias_class`]).
    extract_class_app(conclusion)
        .map(|(class_name, _)| class_name)
        .filter(|class_name| {
            env.get_class_info(class_name).is_some()
                || crate::instance_alias::alias_class_arity(env, class_name).is_some()
        })
        .ok_or_else(|| crate::ElabError::Unsupported {
            feature: format!(
                "attribute [instance]: type of `{decl_name}` does not conclude in a \
                 registered class (got `{conclusion}`)"
            ),
        })
}

#[cfg(test)]
#[path = "instances_tests.rs"]
mod tests;
