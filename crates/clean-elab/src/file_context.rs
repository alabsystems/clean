// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! File-level context for tracking accumulated `variable` declarations and
//! opened namespaces across declarations within a single file.

use crate::imports::ImportPolicy;
use crate::infer::section_prune::SectionPruneRequest;
use crate::infer::user_term::UserTermElab;
use crate::macro_integration::MacroCtx;
use crate::namespace::NamespaceState;
use crate::tactic::TacticRegistry;
use clean_kernel::name::Name;
use clean_parser::{Span, SurfaceBinder, SurfaceName};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

/// Is this `variable` binder Lean's binder-annotation-UPDATE form?
///
/// True exactly for a bare name inside a bracketed binder with no type
/// ascription and no default value — `(P)`, `{P}`, `⦃P⦄`. An instance binder
/// never qualifies: the parser turns `[Decidable P]` into a binder whose `ty`
/// is the class application, so `[…]` always carries a type here.
fn is_binder_annotation_update(binder: &SurfaceBinder) -> bool {
    binder.ty.is_none() && binder.default.is_none() && !binder.name.is_unescaped_component("_")
}

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
    /// New module-system header, distinct from the legacy main module name.
    module_system: bool,
    /// Opt-in IDE observations; absent for ordinary compiler/checker callers.
    tactic_goal_capture: Option<crate::tactic::TacticGoalCapture>,
    term_info_capture: Option<crate::term_info::TermInfoCapture>,
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
    universe_params: Vec<SurfaceName>,
    /// Section scope stack - each entry is the index into `variables` at section start
    section_stack: Vec<usize>,
    /// Section variables forced into every following declaration by `include`.
    ///
    /// Lean includes a section `variable` only in declarations that MENTION it;
    /// `include x` overrides that for the rest of the scope and `omit x`
    /// cancels it. Names, not binders: `include` names a variable that
    /// `variables` already holds.
    included_variables: Vec<SurfaceName>,
    /// Section scope stack for `included_variables` — one snapshot per
    /// `enter_section`, restored on `exit_section`, so an `include` dies with
    /// its section exactly as the `variable` it names does.
    included_section_stack: Vec<Vec<SurfaceName>>,
    /// Binder annotations of the ALREADY-ACCUMULATED variables at section start,
    /// one snapshot per open section, parallel to `section_stack`.
    ///
    /// A `variable (P)` inside a section may re-annotate a variable declared
    /// OUTSIDE it (`FileContext::apply_variable_command`). That edit is scoped to
    /// the section, exactly like a declaration is: measured with lean 4.33.1 on
    /// 2026-08-23, `section Outer / variable {P : Prop} / section Inner /
    /// variable (P) / … / end Inner` proves `inner_t : ∀ (P : Prop), P → P` and
    /// `outer_t : ∀ {P : Prop}, P → P`. Truncation alone cannot undo it — the
    /// mutated entry lives BELOW the marker — so the annotations are restored
    /// from here on `end`.
    section_binder_infos: Vec<Vec<clean_parser::SurfaceBinderInfo>>,
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
    namespace_prefix: SurfaceName,
    /// One exact prefix per entered block; a block may contain multiple components.
    namespace_prefix_stack: Vec<SurfaceName>,
    /// Extra .olean search paths associated with this file, such as Lake
    /// project and package build outputs discovered by `clean check`.
    import_search_paths: Vec<PathBuf>,
    /// The Lean world this file's imports resolve in, or why they cannot
    /// resolve in any (gap G72), set by [`Self::set_import_context_for_file`].
    /// `None` resolves them in the checkout's pin, as for a file outside any
    /// project.
    import_world: Option<Result<clean_olean::ImportWorld, clean_olean::ImportWorldRefusal>>,
    /// Disable external `.olean` import search for Clean-native authority
    /// checks that must not depend on Lean/Lake/Mathlib artifacts.
    disable_external_import_search: bool,
    /// What to do with an `import` that resolves to nothing real. Defaults to
    /// [`ImportPolicy::FailClosed`] — see that type for the two silent-pass
    /// reproductions this field exists to refuse.
    import_policy: ImportPolicy,
    /// Modules this run already satisfied by elaborating their intra-project
    /// `.lean` SOURCE (recorded by `clean check`'s first pass). Such an import
    /// is resolved — the declarations are in the environment — even though the
    /// project has no compiled `.olean` for it, so the fail-closed policy must
    /// not refuse it.
    imports_satisfied_from_source: HashSet<Name>,
    /// Source modules this run tried but did not finish successfully. A failed
    /// source import must never fall back to an artifact or a builtin provider.
    imports_refused_from_source: HashMap<Name, String>,
    /// Direct imports whose compiler metadata is available to this source file.
    compiler_imports: HashSet<Name>,
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
    /// Lean's INSTANCE STATE for this module: one state per open scope
    /// (section / namespace block), each a copy of the enclosing one when
    /// pushed and discarded at `end`, over the environment's global instance
    /// table (see [`crate::instance_store`]). Pushed and popped with
    /// [`Self::local_scope_depth`].
    instance_store: crate::instance_store::InstanceStore,
    /// `local simp` lemmas currently in force, with the `local_scope_depth`
    /// they were declared at (depth 0 stays for the rest of the file).
    live_local_simp_lemmas: Vec<(Name, usize)>,
    /// `local simp` lemmas whose scope has ended and which
    /// [`Self::retire_local_attributes`] has yet to unregister.
    ended_local_simp_lemmas: Vec<Name>,
    live_local_csimp: Vec<(clean_kernel::env::csimp::LocalRule, usize)>,
    ended_local_csimp: Vec<clean_kernel::env::csimp::LocalRule>,
    active_csimp_namespaces: Vec<(Name, usize)>,
    /// `scoped instance`s: instance name → declaring namespace. Visible only
    /// while the declaring namespace is the current namespace (or an
    /// ancestor of it) or is `open`ed — checked dynamically at resolution
    /// time so `open Foo in def …` sees them (B99; the r82
    /// `instprio_scoped_open_in` leak proved 2 without any `open`).
    scoped_instances: HashMap<Name, Name>,
    /// The `private` declarations of OTHER modules: every name the
    /// environment marked `private` before this file's first own declaration
    /// (taken again after each `import`, so a source import elaborated into
    /// the same environment counts as another module). Lean mangles a private
    /// name with its module (`_private.P.0.c`) and resolves only the current
    /// module's, so none of these is reachable from this file; Clean keeps the
    /// plain name, so they are filtered by this set instead. `None` until the
    /// first declaration is elaborated.
    foreign_private_decls: Option<std::sync::Arc<HashSet<Name>>>,
    /// `@[default_instance]` registrations: (instance, class, priority) in
    /// declaration order. Consulted when a type-class goal still has an open
    /// (metavariable) input — Lean's default-instance mechanism (B99; the
    /// r82 `instprio_default_instance_mvar` gap proved 3 where Lean's
    /// defaulting proves 4).
    default_instances: Vec<(Name, Name, u32)>,
    /// The section-variable pruning [`crate::preprocess_decl_with_context`]
    /// asked for the declaration it just rewrote, keyed by that declaration's
    /// span: its scan was incomplete, so it prepended every section variable
    /// and the elaboration of that same declaration drops the unused ones
    /// (`crate::infer::section_prune`). Overwritten by every preprocess and
    /// consumed by the next elaboration, so it never outlives the declaration.
    pending_section_prune: Option<(Span, SectionPruneRequest)>,
    /// The elaboration run this context belongs to: a new context is a new
    /// run, its clones and lexical snapshots stay in it, and
    /// [`Self::fork_run`] starts another. Registration
    /// records each declaration with it, and the `attribute [..]` command may
    /// bind `implemented_by` or `extern` only to a declaration of its own run
    /// (`crate::declared_here`).
    elab_unit: crate::declared_here::ElabUnit,
}

// A prepared `FileContext` can be shared across threads: a driver may
// elaborate a prelude once into a `static` and hand each check (on its own
// large-stack worker) an owned copy. A non-`Send`/`Sync` field -- an `Rc` in
// `foreign_private_decls` did it once -- would force that cache per thread,
// re-elaborating the prelude on every worker; Trust's temporal lanes still
// keep theirs per thread for that old reason. Such a copy MUST be made with
// `FileContext::fork_run`, not `clone`: a clone stays in the prelude's
// elaboration run, so the check's `attribute [implemented_by]` or
// `attribute [extern]` command could bind a prelude declaration, which Lean
// refuses as imported (`crate::declared_here`). Trust's lanes still clone
// (`docs/DECISIONS.md` R80 item 2).
const _: fn() = || {
    fn shared_across_threads<T: Send + Sync>() {}
    shared_across_threads::<FileContext>();
};

impl FileContext {
    /// Observe actual term elaboration without changing checking policy.
    pub fn set_term_info_capture(&mut self, capture: Option<crate::term_info::TermInfoCapture>) {
        self.term_info_capture = capture;
    }

    pub(crate) fn term_info_capture(&self) -> Option<crate::term_info::TermInfoCapture> {
        self.term_info_capture.clone()
    }

    /// Observe actual normal tactic states without changing checking policy.
    pub fn set_tactic_goal_capture(&mut self, capture: Option<crate::tactic::TacticGoalCapture>) {
        self.tactic_goal_capture = capture;
    }

    pub(crate) fn tactic_goal_capture(&self) -> Option<crate::tactic::TacticGoalCapture> {
        self.tactic_goal_capture.clone()
    }
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
    /// against the caller's own context. `disable_external_import_search`,
    /// `import_policy`, `imports_satisfied_from_source` and source refusals ARE
    /// carried: they are
    /// import POLICY and per-file resolution FACT, not caches — dropping the
    /// last one would make a snapshot refuse an import the run demonstrably
    /// resolved from source.
    ///
    /// COST, stated honestly: this clones the whole context and then drops the
    /// caches, so the transient allocation is the same as `clone()`. What
    /// changes is what is RETAINED — a batch holds one snapshot per
    /// declaration, and the difference between `O(declarations × lexical
    /// state)` and `O(declarations × import closure)` is the one that decides
    /// whether the approach scales to a Mathlib-sized file. The transient is
    /// freed before the next snapshot is taken.
    #[must_use]
    pub(crate) fn lexical_snapshot(&self) -> Self {
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
    pub(crate) fn add_variables(&mut self, binders: &[SurfaceBinder]) {
        for _ in binders {
            self.next_variable_scope_id = self.next_variable_scope_id.saturating_add(1);
            self.variable_scope_ids.push(self.next_variable_scope_id);
        }
        self.variables.extend(
            binders
                .iter()
                .map(crate::section_scope::section_variable_binder),
        );
    }

    /// Apply one source-level `variable` command, Lean-4 style.
    ///
    /// A bracketed binder written with NO type ascription — `variable (P Q a b)`,
    /// `variable {P Q}` — is **not** a declaration. It is Lean 4's *binder
    /// annotation update*: it re-binds ALREADY-DECLARED section variables at a
    /// new annotation, keeping their declared type and their position in the
    /// telescope (lean4 `src/Lean/Elab/Command.lean`, `replaceBinderAnnotation`).
    /// Measured against lean 4.33.1 on 2026-08-23:
    ///
    /// ```text
    /// variable {P Q R : Prop} {a b : Nat}
    /// variable (P Q a b)
    /// theorem t (h : P) : P ∧ a = a := ⟨h, rfl⟩
    /// -- t : ∀ (P : Prop) (a : Nat), P → P ∧ a = a
    /// ```
    ///
    /// Appending them as fresh variables instead put the SAME name in the
    /// telescope twice and typed the survivor with a metavariable
    /// (`infer/elab_variable.rs` mints one for a binder with no annotation), so
    /// every declaration in the governed block met an unresolved `?m` where a
    /// type was required. That is what the `ite`/`dite` block of
    /// `Mathlib/Logic/Basic.lean` — governed by its lines 874 (`variable
    /// (P Q a b)`) and 929 (`variable {P Q}`) — died on, as
    /// `Type mismatch: expected conditional guard of type Bool or Prop, got
    /// FVar(FVarId(9223372036854775808))` and as
    /// `elaboration left unresolved variables`. Pinned by
    /// `crates/clean-elab/tests/section_variable_binder_annotation_e2e.rs`.
    ///
    /// A name that is NOT already declared keeps the pre-existing behaviour: it
    /// becomes a new variable whose type the elaborator infers. That matches
    /// Lean, which accepts `variable (Zed)` for an undeclared `Zed` and gives it
    /// `(Zed : Sort u_1)` rather than rejecting it (measured, lean 4.33.1).
    ///
    /// # ENSURES
    /// - Returns the full accumulated telescope AFTER this command
    /// - An annotation update changes only `info`: it never moves, re-types or
    ///   duplicates the variable it targets
    /// - Every binder that is not an annotation update is appended, exactly as
    ///   [`Self::add_variables`] would
    pub(crate) fn apply_variable_command(
        &mut self,
        binders: &[SurfaceBinder],
    ) -> Vec<SurfaceBinder> {
        for binder in binders {
            if is_binder_annotation_update(binder) {
                if let Some(declared) = self
                    .variables
                    .iter_mut()
                    .rev()
                    .find(|declared| declared.name == binder.name)
                {
                    declared.info = binder.info;
                    continue;
                }
            }
            self.add_variables(std::slice::from_ref(binder));
        }
        self.variables.clone()
    }

    /// Add universe parameter names from a `universe` declaration
    ///
    /// # ENSURES
    /// - `current_universe_params().len()` increases by `names.len()`
    pub(crate) fn add_universe_params(&mut self, names: &[SurfaceName]) {
        self.universe_params.extend(names.iter().cloned());
    }

    /// Apply an `include x y …` command: force these section variables into
    /// every following declaration of the current scope.
    ///
    /// # ENSURES
    /// - Each name is in `included_variables` (idempotent, order preserved)
    pub(crate) fn include_variables(&mut self, names: &[SurfaceName]) {
        for name in names {
            if !self.included_variables.iter().any(|n| n == name) {
                self.included_variables.push(name.clone());
            }
        }
    }

    /// Apply an `omit x y …` command: cancel a preceding `include`.
    ///
    /// # ENSURES
    /// - None of `names` is in `included_variables`
    pub(crate) fn omit_variables(&mut self, names: &[SurfaceName]) {
        self.included_variables.retain(|n| !names.contains(n));
    }

    /// Section variables currently forced in by `include`.
    pub(crate) fn included_variables(&self) -> &[SurfaceName] {
        &self.included_variables
    }

    /// Record (or, with `None`, clear) the section-variable pruning the
    /// declaration at `span` needs — see `pending_section_prune`.
    pub(crate) fn set_pending_section_prune(
        &mut self,
        span: Span,
        request: Option<SectionPruneRequest>,
    ) {
        self.pending_section_prune = request.map(|request| (span, request));
    }

    /// The pruning recorded for the declaration at `span`, if any. Anything
    /// recorded for a different declaration is discarded.
    pub(crate) fn take_pending_section_prune(&mut self, span: Span) -> Option<SectionPruneRequest> {
        match self.pending_section_prune.take() {
            Some((recorded, request)) if recorded == span => Some(request),
            _ => None,
        }
    }

    /// Enter a section (push scope marker)
    ///
    /// # ENSURES
    /// - Saves current variable count for later restoration
    /// - Saves the outer variables' binder annotations for later restoration
    /// - Saves option scope boundary for rollback
    /// - Nested sections are supported (stack-based)
    pub(crate) fn enter_section(&mut self) {
        self.included_section_stack
            .push(self.included_variables.clone());
        self.section_binder_infos
            .push(self.variables.iter().map(|v| v.info).collect());
        self.section_stack.push(self.variables.len());
        self.universe_section_stack.push(self.universe_params.len());
        self.option_section_stack.push(Vec::new());
        self.enter_local_scope();
    }

    /// Exit a section (pop scope and truncate variables)
    ///
    /// # ENSURES
    /// - Variables added since last `enter_section()` are removed
    /// - Binder annotations re-bound since last `enter_section()` are restored
    /// - Universe params added since last `enter_section()` are removed
    /// - Options set since last `enter_section()` are restored
    /// - `local instance`s declared in the section are retired (B99)
    /// - No-op if section stack is empty
    pub(crate) fn exit_section(&mut self) {
        if let Some(saved) = self.included_section_stack.pop() {
            self.included_variables = saved;
        }
        if let Some(marker) = self.section_stack.pop() {
            self.variables.truncate(marker);
            self.variable_scope_ids.truncate(marker);
        }
        if let Some(infos) = self.section_binder_infos.pop() {
            for (declared, info) in self.variables.iter_mut().zip(infos) {
                declared.info = info;
            }
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
        self.instance_store.push_scope();
    }

    /// Exit a `local`-attribute scope: its instance state is discarded (Lean's
    /// `popScope`) — a `local instance` declared there is out of the state
    /// again, an instance erased there is back. Counterpart of
    /// [`Self::enter_local_scope`]; also invoked by [`Self::exit_section`].
    pub(crate) fn exit_local_scope(&mut self) {
        self.local_scope_depth = self.local_scope_depth.saturating_sub(1);
        let depth = self.local_scope_depth;
        let (ended, live): (Vec<_>, Vec<_>) = std::mem::take(&mut self.live_local_simp_lemmas)
            .into_iter()
            .partition(|(_, declared_at)| *declared_at > depth);
        self.live_local_simp_lemmas = live;
        self.ended_local_simp_lemmas
            .extend(ended.into_iter().map(|(name, _)| name));
        let (ended, live): (Vec<_>, Vec<_>) = std::mem::take(&mut self.live_local_csimp)
            .into_iter()
            .partition(|(_, at)| *at > depth);
        self.live_local_csimp = live;
        self.active_csimp_namespaces.retain(|(_, at)| *at <= depth);
        self.ended_local_csimp
            .extend(ended.into_iter().map(|(token, _)| token));
        self.instance_store.pop_scope();
    }

    /// Record a `local simp` lemma at the current local-scope depth. It is
    /// unregistered once that scope has ended; see
    /// [`Self::retire_local_attributes`].
    pub(crate) fn record_local_simp_lemma(&mut self, name: Name) {
        self.live_local_simp_lemmas
            .push((name, self.local_scope_depth));
    }

    /// Keep a local compiler-rule identity until its declaring scope ends.
    pub(crate) fn record_local_csimp(&mut self, token: clean_kernel::env::csimp::LocalRule) {
        self.live_local_csimp.push((token, self.local_scope_depth));
    }

    /// Retire local simp and compiler-simplification attributes at scope end.
    ///
    /// Ending a scope ([`Self::exit_local_scope`]) has no environment at
    /// hand, so it only queues the lemmas; this drains the queue. It runs when
    /// a section or namespace closes and again before the next declaration
    /// elaborates, so no later `simp` sees a lemma past its scope — Lean's
    /// `attribute [local simp] foo in <cmd>` is `section … end` around the one
    /// command (`Lean/Elab/BuiltinCommand.lean:516-519`).
    pub(crate) fn retire_local_attributes(&mut self, env: &mut clean_kernel::Environment) {
        for token in std::mem::take(&mut self.ended_local_csimp) {
            clean_kernel::env::csimp::retire_local(env, token);
        }
        for name in std::mem::take(&mut self.ended_local_simp_lemmas) {
            env.unregister_simp_lemma(&name);
        }
    }

    /// Lean's instance state for this module (see [`Self::instance_store`]).
    pub(crate) fn instance_store_mut(&mut self) -> &mut crate::instance_store::InstanceStore {
        &mut self.instance_store
    }

    /// The instances this module gave a global entry while they already had
    /// one, in order (see `InstanceStore::global_readds`): part of what the
    /// module exports to an importer.
    #[must_use]
    pub fn instance_global_readds(&self) -> Vec<Name> {
        self.instance_store.global_readds().to_vec()
    }

    /// The current scope's instance state, for an elaboration context.
    #[must_use]
    pub(crate) fn instance_view(
        &self,
        env: &clean_kernel::Environment,
    ) -> crate::instance_store::InstanceView {
        self.instance_store.view(env)
    }

    /// Record a `local instance` declaration (B99): a local entry in the
    /// current scope's state, until that scope ends. The environment
    /// registers it and marks it local first.
    pub(crate) fn record_local_instance(
        &mut self,
        env: &mut clean_kernel::Environment,
        name: Name,
    ) {
        let Some(priority) = env.instance_priority(&name) else {
            return;
        };
        self.instance_store.add_local(env, &name, priority);
    }

    /// Activate the `scoped` entries of namespaces that just became active
    /// (`namespaces`, each newly activated by `open` / `namespace`): Lean's
    /// `activateScoped` on the current scope's state, which adds them in
    /// order unless the namespace is already active there.
    pub(crate) fn activate_scoped_instances(
        &mut self,
        env: &mut clean_kernel::Environment,
        namespaces: &[Name],
    ) {
        for ns in namespaces {
            self.instance_store.activate(env, ns);
        }
    }

    /// Activate namespace compiler rules once in this scope's inherited view.
    pub(crate) fn activate_scoped_csimp(
        &mut self,
        env: &mut clean_kernel::Environment,
        namespaces: &[Name],
    ) -> Result<(), crate::ElabError> {
        for ns in namespaces {
            if self
                .active_csimp_namespaces
                .iter()
                .any(|(name, _)| name == ns)
            {
                continue;
            }
            let tokens =
                clean_kernel::env::csimp::activate_namespace(env, ns).ok_or_else(|| {
                    crate::ElabError::Unsupported {
                        feature: "compiler attribute activation identity exhausted".into(),
                    }
                })?;
            self.active_csimp_namespaces
                .push((ns.clone(), self.local_scope_depth));
            for token in tokens {
                self.record_local_csimp(token);
            }
        }
        Ok(())
    }

    /// A scoped definition added while its namespace is already active.
    pub(crate) fn activate_new_scoped_csimp(
        &mut self,
        env: &mut clean_kernel::Environment,
        namespace: &Name,
        theorem: &Name,
    ) -> Result<(), crate::ElabError> {
        if self.namespace_state.is_scope_active(namespace) {
            let token = crate::csimp_attribute::register_local(env, theorem)?;
            self.record_local_csimp(token);
        }
        Ok(())
    }

    /// Record a `scoped instance` with its declaring namespace (B99).
    pub(crate) fn record_scoped_instance(&mut self, name: Name, namespace: Name) {
        self.scoped_instances.insert(name, namespace);
    }

    /// Drop `name`'s `scoped` declaration from this file's map (a global
    /// `attribute [instance]` made it an instance everywhere).
    pub(crate) fn forget_scoped_instance(&mut self, name: &Name) {
        self.scoped_instances.remove(name);
    }

    /// Record a `@[default_instance]` registration (declaration order) (B99).
    pub(crate) fn record_default_instance(&mut self, name: Name, class: Name, priority: u32) {
        self.default_instances.push((name, class, priority));
    }

    /// Take the snapshot of other modules' `private` declarations (see
    /// [`Self::foreign_private_decls`]). `refresh` retakes it (after an
    /// `import`); otherwise it is taken only once, before the file's first
    /// own declaration.
    pub(crate) fn note_foreign_private_decls(
        &mut self,
        env: &clean_kernel::Environment,
        refresh: bool,
    ) {
        if refresh || self.foreign_private_decls.is_none() {
            self.foreign_private_decls = Some(std::sync::Arc::new(
                env.private_decl_names().cloned().collect(),
            ));
        }
    }

    /// The `private` declarations of other modules, which this file cannot
    /// name (empty before the first declaration).
    #[must_use]
    pub(crate) fn foreign_private_decls(&self) -> std::sync::Arc<HashSet<Name>> {
        self.foreign_private_decls.clone().unwrap_or_default()
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
    pub(crate) fn exit_section_restoring_env_options(
        &mut self,
        env: &mut clean_kernel::Environment,
    ) {
        if let Some(rollback) = self.option_section_stack.last() {
            for (key, prev_value) in rollback.iter().rev() {
                match prev_value {
                    Some(old) => env.set_option(key.clone(), old.clone()),
                    None => env.remove_option(key),
                }
            }
        }
        self.exit_section();
        self.retire_local_attributes(env);
    }

    /// Get currently accumulated variables
    ///
    /// # ENSURES
    /// - Returns all variables in scope (may be empty)
    #[must_use]
    pub(crate) fn current_variables(&self) -> &[SurfaceBinder] {
        &self.variables
    }

    /// Get currently accumulated universe parameters
    ///
    /// # ENSURES
    /// - Returns all universe params in scope (may be empty)
    #[must_use]
    pub(crate) fn current_universe_params(&self) -> &[SurfaceName] {
        &self.universe_params
    }

    /// Check if there are any accumulated variables
    ///
    /// # ENSURES
    /// - Returns `current_variables().len() > 0`
    #[must_use]
    pub(crate) fn has_variables(&self) -> bool {
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
    pub(crate) fn namespace_state(&self) -> &NamespaceState {
        &self.namespace_state
    }

    /// Get a mutable reference to the namespace state.
    ///
    /// Used to update the persisted state after elaboration of `open`/`export`
    /// commands.
    pub(crate) fn namespace_state_mut(&mut self) -> &mut NamespaceState {
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
    pub(crate) fn active_variable_bindings(&self) -> impl Iterator<Item = (&SurfaceName, u64)> {
        debug_assert_eq!(self.variables.len(), self.variable_scope_ids.len());
        self.variables
            .iter()
            .zip(self.variable_scope_ids.iter().copied())
            .map(|(binder, id)| (&binder.name, id))
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

    /// Set (`Some`) or clear (`None`) one file-level option entry WITHOUT
    /// recording it for section rollback, returning the previous entry. For
    /// `set_option … in <decl>`, which scopes the value to one declaration and
    /// restores the previous entry itself.
    pub(crate) fn replace_option_unscoped(
        &mut self,
        name: &str,
        value: Option<Option<String>>,
    ) -> Option<Option<String>> {
        match value {
            Some(value) => self.options.insert(name.to_string(), value),
            None => self.options.remove(name),
        }
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
    pub(crate) fn apply_options_to_env(&self, env: &mut clean_kernel::Environment) {
        for (name, value) in &self.options {
            env.set_option(name.clone(), value.clone());
        }
    }

    /// Enter a namespace, extending the current namespace prefix.
    ///
    /// The prefix is used by `elaborate_decl_and_register_inner` to qualify
    /// declaration names when flattening namespace blocks.
    pub fn enter_namespace(&mut self, name: &SurfaceName) {
        self.namespace_prefix_stack
            .push(self.namespace_prefix.clone());
        self.namespace_prefix = name.qualify_under(&self.namespace_prefix);
    }

    /// Restore the prefix at the start of the namespace block.
    pub fn exit_namespace(&mut self) {
        self.namespace_prefix = self.namespace_prefix_stack.pop().unwrap_or_default();
    }

    /// Exact current namespace, anonymous at the root.
    #[must_use]
    pub fn namespace_prefix(&self) -> &SurfaceName {
        &self.namespace_prefix
    }

    /// Name the module this file is — Lean's `env.mainModule`, the name its
    /// importers write (`import Pkg.A`). Its `private` theorems and axioms are
    /// then registered as `_private.<module>.0.<name>` and their plain names
    /// resolve in this file only (G21,
    /// `designs/2026-10-08-private-name-mangling.md`). A context never named
    /// keeps the plain-name regime (`docs/DECISIONS.md`, 2026-10-08).
    pub fn set_main_module(&mut self, module: Name) {
        if !module.is_anon() {
            self.namespace_state_mut().set_main_module(module);
        }
    }

    /// The module this file is, when [`Self::set_main_module`] named it.
    #[must_use]
    pub fn main_module(&self) -> Option<&Name> {
        self.namespace_state().main_module()
    }

    /// The elaboration run this context belongs to (`crate::declared_here`).
    pub(crate) fn elab_unit(&self) -> crate::declared_here::ElabUnit {
        self.elab_unit
    }

    /// A copy of this context in a NEW elaboration run: what a driver that
    /// elaborated a prelude once hands each consumer (Trust's temporal lanes
    /// cache the prelude's `(Environment, FileContext)` and give every check a
    /// copy). The prelude's declarations are then imported to the consumer, as
    /// a module's are in Lean, so its `attribute [implemented_by]` and
    /// `attribute [extern]` commands may not name one ("... because it is in
    /// an imported module", `crate::declared_here`), and two consumers' runs
    /// are distinct. A plain `clone` keeps the run, which a lexical snapshot of
    /// the same file needs (`crate::module_batch`); it is the wrong copy for a
    /// consumer.
    #[must_use]
    pub fn fork_run(&self) -> Self {
        Self {
            elab_unit: crate::declared_here::ElabUnit::fresh(),
            tactic_goal_capture: None,
            term_info_capture: None,
            ..self.clone()
        }
    }

    /// A temporary context for a block elaborated without one (a `namespace`
    /// or `section` reached with no `FileContext`): it belongs to the run of
    /// every caller without one, so what was declared before the block is
    /// its own.
    #[must_use]
    pub(crate) fn scratch() -> Self {
        Self {
            elab_unit: crate::declared_here::ElabUnit::UNSCOPED,
            ..Self::default()
        }
    }
}

#[path = "file_context_imports.rs"]
mod import_context;
