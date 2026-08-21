// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! File-level context for tracking accumulated `variable` declarations and
//! opened namespaces across declarations within a single file.

use crate::infer::user_term::UserTermElab;
use crate::macro_integration::MacroCtx;
use crate::namespace::NamespaceState;
use crate::tactic::TacticRegistry;
use clean_kernel::name::Name;
use clean_parser::SurfaceBinder;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

/// File-level context for tracking accumulated `variable` declarations and
/// namespace state across declarations within a single file.
///
/// In Lean 4, `variable` commands accumulate within file scope and are
/// automatically prepended to subsequent declarations (theorem, def, axiom).
/// Similarly, `open Nat` makes names from `Nat` available for all subsequent
/// declarations in the file.
///
/// This context tracks those accumulated variables, universe parameters, and
/// namespace aliases, and handles section scoping for all of them.
///
/// # Example
///
/// ```lean
/// variable {P : Type*}
/// variable [NormedAddCommGroup P]
/// open Nat
/// theorem foo (x : P) : P := add x x
/// -- `add` resolves to `Nat.add` via the open command
/// ```
#[derive(Default, Clone)]
pub struct FileContext {
    /// Accumulated variables from `variable` commands
    variables: Vec<SurfaceBinder>,
    /// Stable lexical identity for each entry in `variables`.
    ///
    /// Nullary notation may capture a section variable.  Tracking identity
    /// separately from spelling prevents that captured `x` from silently
    /// rebinding to an unrelated outer/global `x` after the section ends.
    variable_scope_ids: Vec<u64>,
    /// Monotone source of lexical variable identities (zero is never used).
    next_variable_scope_id: u64,
    /// Accumulated universe parameter names from `universe` commands
    universe_params: Vec<String>,
    /// Section scope stack - each entry is the index into `variables` at section start
    section_stack: Vec<usize>,
    /// Universe scope stack - each entry is the index into `universe_params` at section start
    universe_section_stack: Vec<usize>,
    /// Namespace state: tracks `open` aliases that persist across declarations
    namespace_state: NamespaceState,
    /// Macro and notation registrations that persist across file declarations.
    macro_ctx: MacroCtx,
    /// Tactic registrations from file-scope `elab ... : tactic` commands.
    tactic_registry: Option<TacticRegistry>,
    /// Term-elaborator registrations from file-scope `elab ... : term` commands.
    ///
    /// `ElabCtx` is rebuilt per declaration, so without persisting these here a
    /// `elab "myone" : term => ...` was registered and then dropped before the
    /// next declaration could use it (`UnknownIdent("myone")`). Threaded exactly
    /// like `tactic_registry`.
    user_term_elabs: HashMap<String, UserTermElab>,
    /// File-level option overrides from `set_option` commands.
    /// Maps option name -> raw string value (None for boolean toggle).
    /// Section-scoped: `section ... end` restores prior option state.
    options: HashMap<String, Option<String>>,
    /// Section scope stack for options — stores snapshot of overridden keys
    /// at each section boundary for rollback.
    option_section_stack: Vec<Vec<(String, Option<Option<String>>)>>,
    /// Current namespace prefix for qualifying declaration names.
    /// Set when entering a namespace block, cleared when exiting.
    /// This allows `elaborate_decl_and_register_inner` to flatten namespace
    /// blocks and register each inner declaration individually, so that later
    /// declarations within the same namespace can reference earlier ones.
    namespace_prefix: String,
    /// Extra .olean search paths associated with this file, such as Lake
    /// project and package build outputs discovered by `clean check`.
    import_search_paths: Vec<PathBuf>,
    /// Disable external `.olean` import search for Clean-native authority
    /// checks that must not depend on Lean/Lake/Mathlib artifacts.
    disable_external_import_search: bool,
    /// Modules already loaded into the environment by an earlier `import` in
    /// this file, threaded across every `import` declaration so a Mathlib
    /// file's large overlapping `.olean` closures (Lean.Elab.*, Lean.Server.*,
    /// Mathlib.*) are read and walked once, not re-read once per top-level
    /// import.
    ///
    /// This is the caller-owned `visited` set for
    /// [`clean_olean::load_module_with_deps_bounded_shared`]. `hashbrown`'s
    /// `Default` yields an empty set, so the struct-level `#[derive(Default)]`
    /// stays correct.
    import_visited: hashbrown::HashSet<String>,
    /// Depth of the current `local`-attribute scope: incremented per
    /// `section` ([`Self::enter_section`]) and per `namespace` block
    /// ([`Self::enter_local_scope`]). `local instance`s record the depth they
    /// were declared at and are retired when that depth is exited (B99).
    local_scope_depth: usize,
    /// `local instance`s currently in force, with the `local_scope_depth`
    /// they were declared at. Depth-0 entries (file-level `local instance`)
    /// stay for the rest of the file — Lean's `local` file scope.
    live_local_instances: Vec<(Name, usize)>,
    /// `local instance`s whose declaring scope has ENDED. Injected into each
    /// declaration's `ElabCtx` as hidden instances so resolution never picks
    /// them again — the env-side registration is append-only, so visibility
    /// is filtered here rather than deregistered (B99; the r82
    /// `instprio_local_section_shadow` leak proved 9 outside the section
    /// where Lean proves 5).
    dead_local_instances: HashSet<Name>,
    /// `scoped instance`s: instance name → declaring namespace. Visible only
    /// while the declaring namespace is the current namespace (or an
    /// ancestor of it) or is `open`ed — checked dynamically at resolution
    /// time so `open Foo in def …` sees them (B99; the r82
    /// `instprio_scoped_open_in` leak proved 2 without any `open`).
    scoped_instances: HashMap<Name, Name>,
    /// `@[default_instance]` registrations: (instance, class, priority) in
    /// declaration order. Consulted when a type-class goal still has an open
    /// (metavariable) input — Lean's default-instance mechanism (B99; the
    /// r82 `instprio_default_instance_mvar` gap proved 3 where Lean's
    /// defaulting proves 4).
    default_instances: Vec<(Name, Name, u32)>,
}

impl FileContext {
    /// Create a new empty file context
    ///
    /// # ENSURES
    /// - `has_variables() == false`
    /// - `has_universe_params() == false`
    /// - Section stack is empty
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The LEXICAL state of this context, frozen at the current source
    /// position, with the import caches left behind.
    ///
    /// Header-first batch elaboration ([`crate::module_batch`]) takes one of
    /// these per declaration. That is what makes lexical scoping structural
    /// rather than a convention: a declaration elaborated out of authored order
    /// holds `open`, `notation`, `set_option`, `variable`, the namespace state
    /// and the local/scoped/default instance tables exactly as they stood WHERE
    /// IT WAS WRITTEN, so an `open` or an `end` appearing later in the file
    /// cannot reach backward into it.
    ///
    /// `import_search_paths` and `import_visited` are deliberately NOT carried.
    /// They are a memo of which `.olean` closures have already been walked —
    /// for a Mathlib file, thousands of `String`s added precisely to make
    /// imports O(union) — and they are not lexical: a snapshot is never used to
    /// process an `import`, which the plan phase applies in authored order
    /// against the caller's own context. `disable_external_import_search` IS
    /// carried: it is import POLICY, not a cache.
    ///
    /// COST, stated honestly: this clones the whole context and then drops the
    /// caches, so the transient allocation is the same as `clone()`. What
    /// changes is what is RETAINED — a batch holds one snapshot per
    /// declaration, and the difference between `O(declarations × lexical
    /// state)` and `O(declarations × import closure)` is the one that decides
    /// whether the approach scales to a Mathlib-sized file. The transient is
    /// freed before the next snapshot is taken.
    #[must_use]
    pub fn lexical_snapshot(&self) -> Self {
        let mut snapshot = self.clone();
        snapshot.import_search_paths = Vec::new();
        snapshot.import_visited = hashbrown::HashSet::new();
        snapshot
    }

    /// Add variables from a `variable` declaration
    ///
    /// # ENSURES
    /// - `current_variables().len()` increases by `binders.len()`
    /// - Variables are appended (order preserved)
    pub fn add_variables(&mut self, binders: &[SurfaceBinder]) {
        for _ in binders {
            self.next_variable_scope_id = self.next_variable_scope_id.saturating_add(1);
            self.variable_scope_ids.push(self.next_variable_scope_id);
        }
        self.variables.extend(binders.iter().cloned());
    }

    /// Add universe parameter names from a `universe` declaration
    ///
    /// # ENSURES
    /// - `current_universe_params().len()` increases by `names.len()`
    pub fn add_universe_params(&mut self, names: &[String]) {
        self.universe_params.extend(names.iter().cloned());
    }

    /// Enter a section (push scope marker)
    ///
    /// # ENSURES
    /// - Saves current variable count for later restoration
    /// - Saves option scope boundary for rollback
    /// - Nested sections are supported (stack-based)
    pub fn enter_section(&mut self) {
        self.section_stack.push(self.variables.len());
        self.universe_section_stack.push(self.universe_params.len());
        self.option_section_stack.push(Vec::new());
        self.local_scope_depth += 1;
    }

    /// Exit a section (pop scope and truncate variables)
    ///
    /// # ENSURES
    /// - Variables added since last `enter_section()` are removed
    /// - Universe params added since last `enter_section()` are removed
    /// - Options set since last `enter_section()` are restored
    /// - `local instance`s declared in the section are retired (B99)
    /// - No-op if section stack is empty
    pub fn exit_section(&mut self) {
        if let Some(marker) = self.section_stack.pop() {
            self.variables.truncate(marker);
            self.variable_scope_ids.truncate(marker);
        }
        if let Some(marker) = self.universe_section_stack.pop() {
            self.universe_params.truncate(marker);
        }
        if let Some(rollback) = self.option_section_stack.pop() {
            for (key, prev_value) in rollback.into_iter().rev() {
                match prev_value {
                    Some(old) => {
                        self.options.insert(key, old);
                    }
                    None => {
                        self.options.remove(&key);
                    }
                }
            }
        }
        self.exit_local_scope();
    }

    /// Enter a `local`-attribute scope WITHOUT section variable/option
    /// bookkeeping — used by the `namespace` block driver, where `local`
    /// declarations are scoped to the block exactly as in a `section` (Lean:
    /// `local` = current section OR namespace scope) but `variable`/option
    /// scoping is handled by the namespace machinery (B99).
    pub(crate) fn enter_local_scope(&mut self) {
        self.local_scope_depth += 1;
    }

    /// Exit a `local`-attribute scope: retire every `local instance` declared
    /// at a depth deeper than the remaining scope. Retired instances move to
    /// [`Self::dead_local_instances`] and stay hidden for the rest of the
    /// file (the env registration is append-only). Counterpart of
    /// [`Self::enter_local_scope`]; also invoked by [`Self::exit_section`].
    pub(crate) fn exit_local_scope(&mut self) {
        self.local_scope_depth = self.local_scope_depth.saturating_sub(1);
        let depth = self.local_scope_depth;
        let mut idx = 0;
        while idx < self.live_local_instances.len() {
            if self.live_local_instances[idx].1 > depth {
                let (name, _) = self.live_local_instances.swap_remove(idx);
                self.dead_local_instances.insert(name);
            } else {
                idx += 1;
            }
        }
    }

    /// Record a `local instance` at the current local-scope depth (B99).
    pub(crate) fn record_local_instance(&mut self, name: Name) {
        self.live_local_instances
            .push((name, self.local_scope_depth));
    }

    /// Record a `scoped instance` with its declaring namespace (B99).
    pub(crate) fn record_scoped_instance(&mut self, name: Name, namespace: Name) {
        self.scoped_instances.insert(name, namespace);
    }

    /// Record a `@[default_instance]` registration (declaration order) (B99).
    pub(crate) fn record_default_instance(&mut self, name: Name, class: Name, priority: u32) {
        self.default_instances.push((name, class, priority));
    }

    /// `local instance`s whose declaring scope has ended — hidden from
    /// resolution for the rest of the file (B99).
    #[must_use]
    pub(crate) fn dead_local_instances(&self) -> &HashSet<Name> {
        &self.dead_local_instances
    }

    /// `scoped instance` → declaring namespace map (B99).
    #[must_use]
    pub(crate) fn scoped_instance_map(&self) -> &HashMap<Name, Name> {
        &self.scoped_instances
    }

    /// `@[default_instance]` registrations, in declaration order (B99).
    #[must_use]
    pub(crate) fn default_instance_entries(&self) -> &[(Name, Name, u32)] {
        &self.default_instances
    }

    /// Exit a section, rolling the section's `set_option` overrides back out of
    /// BOTH this `FileContext` and the kernel environment.
    ///
    /// [`exit_section`](Self::exit_section) alone restores only `self.options`.
    /// But a file-scope `set_option` inside a section is also written straight to
    /// the kernel env (via `Environment::set_option`), and
    /// [`apply_options_to_env`](Self::apply_options_to_env) only ever *adds*,
    /// never removes — so without this a section-scoped `set_option` (e.g.
    /// `set_option autoImplicit false`) would persist in the env past the
    /// section, silently mis-elaborating every following declaration. The env
    /// starts with no options populated (all option state originates from
    /// `set_option`), so the section frame's recorded previous values are exactly
    /// the env's previous values; applying the same rollback to the env restores
    /// it precisely.
    pub fn exit_section_restoring_env_options(&mut self, env: &mut clean_kernel::Environment) {
        if let Some(rollback) = self.option_section_stack.last() {
            for (key, prev_value) in rollback.iter().rev() {
                match prev_value {
                    Some(old) => env.set_option(key.clone(), old.clone()),
                    None => env.remove_option(key),
                }
            }
        }
        self.exit_section();
    }

    /// Get currently accumulated variables
    ///
    /// # ENSURES
    /// - Returns all variables in scope (may be empty)
    #[must_use]
    pub fn current_variables(&self) -> &[SurfaceBinder] {
        &self.variables
    }

    /// Get currently accumulated universe parameters
    ///
    /// # ENSURES
    /// - Returns all universe params in scope (may be empty)
    #[must_use]
    pub fn current_universe_params(&self) -> &[String] {
        &self.universe_params
    }

    /// Check if there are any accumulated variables
    ///
    /// # ENSURES
    /// - Returns `current_variables().len() > 0`
    #[must_use]
    pub fn has_variables(&self) -> bool {
        !self.variables.is_empty()
    }

    /// Check if there are any accumulated universe parameters
    ///
    /// # ENSURES
    /// - Returns `current_universe_params().len() > 0`
    #[must_use]
    pub fn has_universe_params(&self) -> bool {
        !self.universe_params.is_empty()
    }

    /// Get a reference to the namespace state.
    ///
    /// Used to initialize `ElabCtx` with persisted open/export aliases.
    #[must_use]
    pub fn namespace_state(&self) -> &NamespaceState {
        &self.namespace_state
    }

    /// Get a mutable reference to the namespace state.
    ///
    /// Used to update the persisted state after elaboration of `open`/`export`
    /// commands.
    pub fn namespace_state_mut(&mut self) -> &mut NamespaceState {
        &mut self.namespace_state
    }

    /// Read the persisted macro context WITHOUT moving it out.
    ///
    /// The take/replace pair below is the driver's idiom, and it is correct
    /// there because a declaration is elaborated exactly once. Header-first
    /// batch elaboration re-elaborates a deferred declaration in a later round
    /// against the same lexical snapshot, so it must borrow instead: taking
    /// would leave the snapshot holding EMPTY macro state for every round after
    /// the first, silently un-registering the file's notation mid-batch.
    pub(crate) fn macro_ctx(&self) -> &MacroCtx {
        &self.macro_ctx
    }

    /// Active section-variable spellings paired with stable lexical identities.
    /// Kept parallel to `variables` by `add_variables`/`exit_section`.
    pub(crate) fn active_variable_bindings(&self) -> impl Iterator<Item = (&str, u64)> {
        debug_assert_eq!(self.variables.len(), self.variable_scope_ids.len());
        self.variables
            .iter()
            .zip(self.variable_scope_ids.iter().copied())
            .map(|(binder, id)| (binder.name.as_str(), id))
    }

    /// Mutable access to the persisted macro context, for the driver's
    /// namespace/section arms to push/pop scoped-notation activation frames
    /// around a block's inner declarations (an `open scoped` inside the block
    /// must not stay active past its `end`).
    pub(crate) fn macro_ctx_mut(&mut self) -> &mut MacroCtx {
        &mut self.macro_ctx
    }

    /// Read the persisted tactic registry without moving it out. See
    /// [`FileContext::macro_ctx`].
    pub(crate) fn tactic_registry(&self) -> Option<&TacticRegistry> {
        self.tactic_registry.as_ref()
    }

    /// Read the persisted user term elaborators without moving them out. See
    /// [`FileContext::macro_ctx`].
    pub(crate) fn user_term_elabs(&self) -> &HashMap<String, UserTermElab> {
        &self.user_term_elabs
    }

    /// Move the persisted macro context out for a declaration elaboration.
    ///
    /// The caller must return it with `replace_macro_ctx` after elaboration.
    pub(crate) fn take_macro_ctx(&mut self) -> MacroCtx {
        std::mem::take(&mut self.macro_ctx)
    }

    /// Replace the persisted macro context after a declaration elaboration.
    pub(crate) fn replace_macro_ctx(&mut self, macro_ctx: MacroCtx) {
        self.macro_ctx = macro_ctx;
    }

    /// Move the persisted tactic registry out for declaration elaboration.
    pub(crate) fn take_tactic_registry(&mut self) -> Option<TacticRegistry> {
        self.tactic_registry.take()
    }

    /// Replace the persisted tactic registry after declaration elaboration.
    pub(crate) fn replace_tactic_registry(&mut self, tactic_registry: TacticRegistry) {
        self.tactic_registry = Some(tactic_registry);
    }

    /// Take the persisted user term elaborators for the next declaration.
    pub(crate) fn take_user_term_elabs(&mut self) -> HashMap<String, UserTermElab> {
        std::mem::take(&mut self.user_term_elabs)
    }

    /// Replace the persisted user term elaborators after declaration elaboration.
    pub(crate) fn replace_user_term_elabs(&mut self, elabs: HashMap<String, UserTermElab>) {
        self.user_term_elabs = elabs;
    }

    /// Set a file-level option override.
    ///
    /// If inside a section, the previous value is recorded for rollback
    /// when the section ends. At file scope, the option persists until
    /// overwritten or the file ends.
    pub fn set_option(&mut self, name: String, value: Option<String>) {
        // Record rollback info if inside a section
        if let Some(frame) = self.option_section_stack.last_mut() {
            let prev = self.options.get(&name).cloned();
            frame.push((name.clone(), prev));
        }
        self.options.insert(name, value);
    }

    /// Get a file-level option value.
    ///
    /// Returns `Some(&value)` if the option has been set (value may be `None`
    /// for boolean toggles like `set_option pp.all`), or `None` if the option
    /// has not been set at file level.
    #[must_use]
    pub fn get_option(&self, name: &str) -> Option<&Option<String>> {
        self.options.get(name)
    }

    /// Get all file-level option overrides.
    #[must_use]
    pub fn options(&self) -> &HashMap<String, Option<String>> {
        &self.options
    }

    /// Apply all file-level option overrides to an environment.
    ///
    /// Called before elaborating each declaration so the environment
    /// reflects the current file-level option state.
    pub fn apply_options_to_env(&self, env: &mut clean_kernel::Environment) {
        for (name, value) in &self.options {
            env.set_option(name.clone(), value.clone());
        }
    }

    /// Enter a namespace, extending the current namespace prefix.
    ///
    /// The prefix is used by `elaborate_decl_and_register_inner` to qualify
    /// declaration names when flattening namespace blocks.
    pub fn enter_namespace(&mut self, name: &str) {
        if self.namespace_prefix.is_empty() {
            self.namespace_prefix = name.to_owned();
        } else {
            self.namespace_prefix = format!("{}.{}", self.namespace_prefix, name);
        }
    }

    /// Exit the current namespace, restoring the parent prefix.
    pub fn exit_namespace(&mut self) {
        if let Some(dot_pos) = self.namespace_prefix.rfind('.') {
            self.namespace_prefix.truncate(dot_pos);
        } else {
            self.namespace_prefix.clear();
        }
    }

    /// Get the current namespace prefix.
    ///
    /// Returns an empty string when at the root (no namespace active).
    #[must_use]
    pub fn namespace_prefix(&self) -> &str {
        &self.namespace_prefix
    }

    /// Replace the file-level import search paths used for `.olean` loading.
    pub fn set_import_search_paths(&mut self, paths: Vec<PathBuf>) {
        self.import_search_paths = paths;
    }

    /// Get the file-level import search paths used for `.olean` loading.
    #[must_use]
    pub fn import_search_paths(&self) -> &[PathBuf] {
        &self.import_search_paths
    }

    /// Get a mutable reference to the persistent set of modules already loaded
    /// by this file's earlier `import` declarations.
    ///
    /// Threaded into [`clean_olean::load_module_with_deps_bounded_shared`] so a
    /// file's overlapping `.olean` closures are read once across all its
    /// imports rather than re-read per top-level import.
    pub fn import_visited_mut(&mut self) -> &mut hashbrown::HashSet<String> {
        &mut self.import_visited
    }

    /// Disable external `.olean` import search for this file context.
    ///
    /// When set, `Import` declarations only initialize Clean's built-in
    /// module preludes; they do not consult Lean / Lake / Mathlib `.olean`
    /// artifacts as semantic authority.
    pub fn disable_external_import_search(&mut self) {
        self.disable_external_import_search = true;
    }

    /// Whether imports may search external `.olean` paths.
    #[must_use]
    pub fn external_import_search_enabled(&self) -> bool {
        !self.disable_external_import_search
    }
}
