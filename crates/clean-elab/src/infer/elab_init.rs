// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ElabCtx initialization and public accessor helpers.

use super::*;

/// Build an InstanceTable from the kernel environment's registered classes and instances.
///
/// Extracted from `ElabCtx::new` to keep constructor size manageable.
/// Uses proper universe levels from `const_info.level_params` when building
/// fallback instance expressions (Part of #1828).
/// The declaring namespace of every IMPORTED `scoped instance` in `env`, as
/// the olean loader recorded it (`clean_olean::ScopedInstanceState`). Feeds
/// `ElabCtx::instance_visible`, which already gates source-declared scoped
/// instances on `open` / namespace entry (Lean's `activateScoped`); until
/// 2026-09-10 an imported `scoped instance` was simply global, so
/// `example (α : Type) [LE α] : LT α := inferInstance` passed through
/// Mathlib's `Classical.Order.instOrd` where Lean fails.
fn imported_scoped_instances(env: &Environment) -> HashMap<Name, Name> {
    env.get_ext_state::<clean_olean::ScopedInstanceState>(clean_olean::scoped_instance_idx())
        .map(|state| state.scope_of.clone())
        .unwrap_or_default()
}

/// Every `local instance` the environment records. A context built without a
/// `FileContext` has no instance in force as `local` (it declares none), so all
/// of them are hidden, as Lean hides another module's `local instance`; a
/// context built for a file replaces this with the file's instance state
/// (`FileContext::instance_view`).
fn other_modules_local_instances(env: &Environment) -> std::collections::HashSet<Name> {
    env.local_instance_names().cloned().collect()
}

fn init_instances_from_env(env: &Environment) -> InstanceTable {
    let mut instances = InstanceTable::new();

    // Collect classes once instead of walking `env.classes()` twice — this runs
    // on every `ElabCtx::new` (every command). Order-preserving: same two phases,
    // one underlying iteration of the class map.
    let classes: Vec<_> = env.classes().collect();

    for class_info in &classes {
        instances.register_class_full(
            class_info.name.clone(),
            class_info.num_params,
            class_info.out_params.clone(),
            class_info.semi_out_params.clone(),
        );
    }

    // The kernel prelude ships the `OfNat` CONSTANT (and `instOfNatNat`)
    // without registering it in the env class table, so the sweep above
    // misses it: `is_class("OfNat")` was false, the literal elaborator's
    // Step-1 instance search never ran, and a user-defined `OfNat` instance
    // could never fire (every non-hardcoded typed literal fell back to a raw
    // Nat lit). Seed the class (α, n — no out-params) so its instances load
    // in the loop below. Engagement gate: with the class absent every
    // dependent path already failed; nothing that previously resolved
    // changes. (B95)
    //
    // B101 extends the same seed to the homogeneous arithmetic classes
    // `Add`/`Mul`/`Sub` (1 param, no out-params), which the kernel prelude
    // likewise ships as constants without class registration. Without it,
    // (a) the `[Add α]` premise of the seeded `instHAdd` bridge could never
    // resolve (`resolve_instance_candidates` bails on `!is_class`), and
    // (b) a USER `instance : Add X` — persisted under class `Add` by
    // `register.rs` — was never re-imported into later commands' tables
    // (the loop below only walks registered class names). Same engagement
    // gate as B95: with the class absent, every dependent path already
    // failed. (`Div` has no prelude constant — kernel co-tenant — and the
    // guard skips it naturally; `Neg` is already env-registered.)
    let mut class_names: Vec<Name> = classes.iter().map(|c| c.name.clone()).collect();
    for (seed_name, num_params) in [("OfNat", 2), ("Add", 1), ("Mul", 1), ("Sub", 1)] {
        let seed = Name::from_string(seed_name);
        if !instances.is_class(&seed) && env.get_const(&seed).is_some() {
            instances.register_class_full(seed.clone(), num_params, vec![], vec![]);
            class_names.push(seed);
        }
    }

    for class_name in &class_names {
        for inst_info in env.get_class_instances(class_name) {
            // Prefer inst_info.type_/value (with correct binder info) over const_info
            // when available. This handles the case where a toParent projection has
            // Default binders but the instance needs Implicit/InstImplicit binders.
            // See #443 for details.
            let (inst_type, inst_expr) = if let (Some(ty), Some(val)) =
                (inst_info.type_.as_ref(), inst_info.value.as_ref())
            {
                (ty.clone(), val.clone())
            } else if let Some(const_info) = env.get_const(&inst_info.name) {
                let inst_type = const_info.type_.clone();
                // Lean-faithful synthesized-instance TERM: the instance CONSTANT
                // (with its own declared universe params, matching `inst_type`'s),
                // never the constant's unfolded value. Lean's `synthInstance`
                // returns `instFoo α subInst`; substituting the definition body
                // instead inlined `BEq.mk (fun a b => Decidable.decide …)` /
                // `OfNat.mk …` structure literals into every use site, so
                // clean-elaborated terms diverged structurally from real-Lean
                // encodings of the same source and cross-encoding unification
                // failed (trust-ir Lean↔Clean bridge blocker B2: the
                // `if rhs == 0` division guards of `semIntBinOp`). The two forms
                // are definitionally equal — whnf unfolds the constant wherever a
                // field is actually projected — so accepts are unchanged; only
                // the emitted term shape changes.
                let levels: Vec<Level> = const_info
                    .level_params
                    .iter()
                    .map(|p| Level::param(p.clone()))
                    .collect();
                let inst_expr = Expr::const_(inst_info.name.clone(), levels);
                (inst_type, inst_expr)
            } else {
                continue;
            };

            // Bulk path: append now, sort once below. The per-insert sorted
            // variant was measured QUADRATIC per class and dominated every
            // declaration's elaboration once instance resolution was fixed
            // (see `InstanceTable::push_instance_unsorted`).
            instances.push_instance_unsorted(
                inst_info.name.clone(),
                inst_info.class_name.clone(),
                inst_expr,
                inst_type,
                inst_info.priority,
                env.get_instance_synth_order(&inst_info.name)
                    .map(<[usize]>::to_vec),
            );
        }
    }
    instances.sort_instances_by_priority();

    // Lean indexes an instance by its type after a REDUCIBLE telescope
    // (`Lean/Meta/Instances.lean` `mkInstanceKey`), so an instance filed here
    // under an alias class (`DecidableLT`, from `clean-olean`'s syntactic
    // filing) also answers goals of the class the alias unfolds to. Record
    // which registered classes are such aliases; the resolver reads their
    // buckets for final-class goals (`resolve_instance_candidates`).
    let aliases =
        crate::instance_alias::class_aliases_by_final(env, &class_names, |n| instances.is_class(n));
    instances.set_class_aliases(aliases);

    instances
}

impl<'a> ElabCtx<'a> {
    pub(crate) fn set_source_world(&mut self, world: clean_kernel::LeanWorld) {
        self.source_world = Some(world);
    }

    pub(crate) fn set_tactic_goal_capture(
        &mut self,
        capture: Option<crate::tactic::TacticGoalCapture>,
    ) {
        self.tactic_goal_capture = capture;
    }
    /// Create a new elaboration context for the given environment.
    ///
    /// # ENSURES
    /// - Context is initialized with classes and instances from `env`
    /// - Local bindings are empty
    /// - Metavariable state is fresh
    /// - Macro context has built-in macros
    pub fn new(env: &'a Environment) -> Self {
        let instances = init_instances_from_env(env);

        Self {
            env,
            source_world: None,
            locals: local_bindings::LocalBindings::new(),
            local_name_aliases: Vec::new(),
            single_theorem_capture: None,
            shared_if_let_scrutinees: Vec::new(),
            structural_rec_sites: Vec::new(),
            recursive_changed_params: std::collections::HashSet::new(),
            recursive_call_miss: None,
            where_termination: Vec::new(),
            aux_decl_locals: std::collections::HashSet::new(),
            let_rec_lift: let_rec_lift::LetRecLiftState::default(),
            public_param_infos: Vec::new(),
            mutual_lift_entries: Vec::new(),
            mutual_eq_lemmas: Vec::new(),
            logged_deriving_failures: Vec::new(),
            universe_params: Vec::new(),
            file_universe_params: Vec::new(),
            file_universe_scope_known: false,
            decl_explicit_universes: None,
            metas: MetaState::new(),
            next_fvar: 0,
            level_mint: crate::level_mint::LevelMint::new(),
            instances,
            local_instances: Vec::new(),
            hidden_instances: other_modules_local_instances(env),
            scoped_instances: imported_scoped_instances(env),
            foreign_private_decls: std::sync::Arc::default(),
            private_module_known: false,
            instance_view: None,
            classical_tactic_scope: 0,
            instance_search_steps: 0,
            failed_local_subgoals: std::collections::HashSet::new(),
            instance_search_stuck: false,
            user_default_instance_answers: 0,
            open_numeral_let_types: Vec::new(),
            let_rec_settled_open_numerals: 0,
            numeral_postpone_depth: 0,
            postponing_let_depth: 0,
            postponing_scope_start: 0,
            defer_user_defaults: 0,
            deferred_user_default_goals: 0,
            user_default_priority_floor: None,
            lean_order_ground_refusal: None,
            lean_default_points: 0,
            binop_tree_plans: Vec::new(),
            redex_binder_domains: None,
            redex_binder_escaped: false,
            pinned_redex_binder_types: None,
            pinned_lambda_binder_types: Vec::new(),
            settle_floor: None,
            bne_beq_head: None,
            alias_instance_heads: HashMap::new(),
            struct_lit_trees: Vec::new(),
            struct_lit_join_parent: false,
            default_instances: HashMap::new(),
            instance_cache: HashMap::new(),
            tc_caches: RefCell::new(TcCaches::default()),
            tc_cache_state: RefCell::new(None),
            local_ctx_cache: RefCell::new(None),
            decl_memo: RefCell::new(demand_local_ctx::DeclMemo::default()),
            recursor_auth_cache: RefCell::new(HashMap::new()),
            cases_on_auth_cache: RefCell::new(HashMap::new()),
            macro_ctx: MacroCtx::new(),
            tactic_registry: {
                let mut reg = TacticRegistry::new();
                crate::tactic::builtins::register_builtin_tactics(&mut reg);
                reg
            },
            term_elab_registry: TermElabRegistry::new(),
            user_term_elabs: HashMap::new(),
            imported_term_syntax: None,
            imported_runtime: None,
            meta_value_bindings: HashMap::new(),
            collected_aesop_attrs: Vec::new(),
            collected_simp_attrs: Vec::new(),
            collected_local_simp: Vec::new(),
            collected_local_csimp: Vec::new(),
            collected_scoped_csimp: Vec::new(),
            collected_reducibility: Vec::new(),
            collected_matchers: Vec::new(),
            collected_extern: Vec::new(),
            collected_export: Vec::new(),
            collected_deprecated: Vec::new(),
            collected_inline_attributes: Vec::new(),
            collected_specialize: Vec::new(),
            collected_csimp: Vec::new(),
            collected_definition_attrs: Vec::new(),
            simple_equation_sources: Vec::new(),
            collected_congr: Vec::new(),
            collected_ext: Vec::new(),
            collected_grind: Vec::new(),
            collected_refl: Vec::new(),
            collected_symm: Vec::new(),
            collected_nospecialize: Vec::new(),
            collected_implemented_by: Vec::new(),
            collected_coe: Vec::new(),
            collected_match_pattern: Vec::new(),
            collected_init: Vec::new(),
            collected_default_instance: Vec::new(),
            collected_instance_attrs: Vec::new(),
            collected_scoped_instance_attrs: Vec::new(),
            collected_class_attrs: Vec::new(),
            collected_derive_handler: Vec::new(),
            collected_attribute_removals: Vec::new(),
            auto_implicits: Vec::new(),
            auto_implicit_lookup: HashMap::new(),
            in_decl_context: false, // Default to false for standalone expression elaboration
            in_term_body: false,
            section_binder_stack: Vec::new(),
            included_var_stack: Vec::new(),
            current_expected_type: None,
            dot_elim: Default::default(),
            recursive_def_ctx: None,
            explicit_mode: false,
            value_is_explicit_app: false,
            suppress_binop_homogenize: false,
            lambda_postpone: Default::default(),
            postponed_open_carrier_instances: Vec::new(),
            do_pure_obligations: Vec::new(),
            do_monad_info: None,
            do_control_info: None,
            do_control_stack: None,
            do_wrapped_monad: None,
            do_loop_ctx: None,
            do_mut_vars: Vec::new(),
            do_active_mut_vars: Vec::new(),
            do_pure_state: false,
            pending_level_assigns: RefCell::new(Vec::new()),
            namespace_state: crate::namespace::NamespaceState::new(),
            namespace_prefix: SurfaceName::default(),
            decl_site_namespace: None,
            local_options: HashMap::new(),
            match_dependent_motive: None,
            match_dependent_motive_indices: 0,
            match_index_discriminating_punit: None,
            nested_mutual_aux_arms: None,
            hole_names: HashMap::new(),
            local_forall_binder_names: HashMap::new(),
            surface_forall_binder_names: Vec::new(),
            self_reference: None,
            unstaged_siblings: Vec::new(),
            tactic_trace: tactic_trace::TacticTrace::default(),
            tactic_goal_capture: None,
            term_info_capture: None,
            term_contexts: Vec::new(),
            term_info_stack: Vec::new(),
            term_local_display_names: HashMap::new(),
            tactic_goal_block: None,
            section_prune: None,
            section_prune_outcome: None,
        }
    }

    /// Take collected aesop attributes for registration
    ///
    /// After elaboration, callers should retrieve these and register them:
    /// ```text
    /// for (name, attr) in ctx.take_aesop_attrs() {
    ///     register_aesop_rule(&mut env, name, &attr);
    /// }
    /// ```
    ///
    /// # ENSURES
    /// - Returns all collected aesop attributes (moves ownership)
    /// - After call, internal collection is empty
    pub(crate) fn take_aesop_attrs(&mut self) -> Vec<(Name, AesopAttr)> {
        std::mem::take(&mut self.collected_aesop_attrs)
    }

    /// Take collected simp lemma attributes for registration
    pub(crate) fn take_simp_attrs(&mut self) -> Vec<(Name, KernelSimpPriority)> {
        std::mem::take(&mut self.collected_simp_attrs)
    }

    /// Take the simp lemmas a `local simp` registered (a subset of
    /// [`Self::take_simp_attrs`]), for scoped retirement.
    pub(crate) fn take_scoped_csimp(&mut self) -> Vec<(Name, Name)> {
        std::mem::take(&mut self.collected_scoped_csimp)
    }

    pub(crate) fn take_local_csimp(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_local_csimp)
    }

    pub(crate) fn take_local_simp(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_local_simp)
    }

    /// Take collected reducibility attributes for registration
    pub(crate) fn take_reducibility(&mut self) -> Vec<(Name, Reducibility)> {
        std::mem::take(&mut self.collected_reducibility)
    }

    /// Take collected extern bindings for registration
    pub(crate) fn take_extern(
        &mut self,
    ) -> Vec<(
        Name,
        clean_kernel::env::CompilerExternMetadata,
        crate::declared_here::AttributeSite,
    )> {
        std::mem::take(&mut self.collected_extern)
    }

    /// Take collected export bindings for registration
    pub(crate) fn take_export(&mut self) -> Vec<(Name, String)> {
        std::mem::take(&mut self.collected_export)
    }

    /// Take collected deprecations for registration
    pub(crate) fn take_deprecated(&mut self) -> Vec<(Name, Option<String>)> {
        std::mem::take(&mut self.collected_deprecated)
    }

    /// Drain the one ordered compiler-attribute queue.
    pub(crate) fn take_inline_attributes(
        &mut self,
    ) -> Vec<crate::decl_attributes::InlineAttributeUse> {
        std::mem::take(&mut self.collected_inline_attributes)
    }

    #[cfg(test)]
    fn take_inline_mode(&mut self, mode: clean_kernel::env::csimp::InlineMode) -> Vec<Name> {
        let mut names = Vec::new();
        self.collected_inline_attributes.retain(|use_| {
            if use_.mode == mode {
                names.push(use_.name.clone());
                false
            } else {
                true
            }
        });
        names
    }

    /// Take collected inline hints for registration
    #[cfg(test)]
    pub(crate) fn take_inline(&mut self) -> Vec<Name> {
        self.take_inline_mode(clean_kernel::env::csimp::InlineMode::Inline)
    }

    /// Take collected noinline hints for registration
    #[cfg(test)]
    pub(crate) fn take_noinline(&mut self) -> Vec<Name> {
        self.take_inline_mode(clean_kernel::env::csimp::InlineMode::NoInline)
    }

    /// Take collected always_inline hints for registration
    #[cfg(test)]
    pub(crate) fn take_always_inline(&mut self) -> Vec<Name> {
        self.take_inline_mode(clean_kernel::env::csimp::InlineMode::AlwaysInline)
    }

    /// Take collected specialize hints for registration
    pub(crate) fn take_specialize(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_specialize)
    }

    /// Take collected csimp lemmas for registration
    pub(crate) fn take_csimp(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_csimp)
    }

    pub(crate) fn take_definition_attrs(&mut self) -> Vec<crate::definition_attrs::NamedAttribute> {
        std::mem::take(&mut self.collected_definition_attrs)
    }

    /// Take collected congr lemmas for registration
    pub(crate) fn take_congr(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_congr)
    }

    /// Take collected ext lemmas for registration
    pub(crate) fn take_ext(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_ext)
    }

    /// Take collected `@[grind]` registrations for registration.
    pub(crate) fn take_grind(&mut self) -> Vec<(Name, clean_kernel::env::GrindAttrKind)> {
        std::mem::take(&mut self.collected_grind)
    }

    /// Take collected refl lemmas for registration
    pub(crate) fn take_refl(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_refl)
    }

    /// Take collected symm lemmas for registration
    pub(crate) fn take_symm(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_symm)
    }

    /// Take collected macro_inline hints for registration
    #[cfg(test)]
    pub(crate) fn take_macro_inline(&mut self) -> Vec<Name> {
        self.take_inline_mode(clean_kernel::env::csimp::InlineMode::MacroInline)
    }

    /// Take collected inline_if_reduce hints for registration
    #[cfg(test)]
    pub(crate) fn take_inline_if_reduce(&mut self) -> Vec<Name> {
        self.take_inline_mode(clean_kernel::env::csimp::InlineMode::InlineIfReduce)
    }

    /// Take collected nospecialize hints for registration
    pub(crate) fn take_nospecialize(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_nospecialize)
    }

    /// Take collected @[implemented_by] bindings for registration
    pub(crate) fn take_implemented_by(&mut self) -> Vec<crate::implemented_by::ImplementedByUse> {
        std::mem::take(&mut self.collected_implemented_by)
    }

    /// Take collected @[coe] coercion registrations
    pub(crate) fn take_coe(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_coe)
    }

    /// Take collected @[match_pattern] registrations
    pub(crate) fn take_match_pattern(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_match_pattern)
    }

    /// Take collected @[init] registrations
    pub(crate) fn take_init(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_init)
    }

    /// Take collected @[default_instance] registrations (name, priority)
    pub(crate) fn take_default_instance(&mut self) -> Vec<(Name, u32)> {
        std::mem::take(&mut self.collected_default_instance)
    }

    /// Take collected `attribute [instance]` / `@[instance N]` registrations
    /// (name, priority) for kernel-side instance registration (B06).
    pub(crate) fn take_instance_attrs(&mut self) -> Vec<(Name, u32)> {
        std::mem::take(&mut self.collected_instance_attrs)
    }

    /// Take the `local instance` / `scoped instance` attributes collected
    /// this declaration.
    pub(crate) fn take_scoped_instance_attrs(&mut self) -> Vec<(Name, u32, ScopedInstanceAttr)> {
        std::mem::take(&mut self.collected_scoped_instance_attrs)
    }

    /// Take the `attribute [class] X` targets collected this declaration.
    pub(crate) fn take_class_attrs(&mut self) -> Vec<crate::class_attribute::ClassAttribute> {
        std::mem::take(&mut self.collected_class_attrs)
    }

    /// Take collected @[derive_handler] registrations.
    pub(crate) fn take_derive_handler(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_derive_handler)
    }

    /// Take collected file-scope attribute removals.
    pub(crate) fn take_attribute_removals(&mut self) -> Vec<(Name, String)> {
        std::mem::take(&mut self.collected_attribute_removals)
    }

    /// Set the namespace state for this elaboration context.
    ///
    /// Used to inject file-level open/export aliases from [`FileContext`]
    /// so that names opened in a previous declaration are visible during
    /// elaboration of subsequent declarations.
    ///
    /// Also syncs `namespace_prefix` from `NamespaceState.current_namespace()`
    /// so that `qualify_name()` correctly prefixes declaration names (#3410).
    pub(crate) fn set_namespace_state(&mut self, state: crate::namespace::NamespaceState) {
        // Sync namespace_prefix from the NamespaceState's current namespace
        // so that qualify_name() correctly prefixes declaration names (#3410).
        let current_ns = state.current_namespace();
        self.namespace_prefix = SurfaceName::from_name(current_ns.clone());
        self.namespace_state = state;
    }

    /// Declare which same-batch declarations contributed no forward-resolvable
    /// header, so an identifier naming one gets a refusal that points at the
    /// SIBLING rather than a name-distance guess.
    ///
    /// Diagnostic-only, and read only where resolution has already failed
    /// ([`ElabCtx::unknown_ident_error`]): it cannot make a name resolve, and
    /// it cannot make one stop resolving. Empty for every caller that is not
    /// [`crate::module_batch`]'s body phase, which leaves those callers'
    /// messages byte-identical.
    pub(crate) fn set_unstaged_siblings(&mut self, siblings: Vec<UnstagedSibling>) {
        self.unstaged_siblings = siblings;
    }

    /// Take the namespace state out of this context, replacing it with empty.
    ///
    /// Called after elaboration to persist open/export aliases back to
    /// [`FileContext`] for use by subsequent declarations.
    pub(crate) fn take_namespace_state(&mut self) -> crate::namespace::NamespaceState {
        std::mem::take(&mut self.namespace_state)
    }

    /// Create with a pre-populated instance table
    pub fn with_instances(env: &'a Environment, instances: InstanceTable) -> Self {
        Self {
            env,
            source_world: None,
            locals: local_bindings::LocalBindings::new(),
            local_name_aliases: Vec::new(),
            single_theorem_capture: None,
            shared_if_let_scrutinees: Vec::new(),
            structural_rec_sites: Vec::new(),
            recursive_changed_params: std::collections::HashSet::new(),
            recursive_call_miss: None,
            where_termination: Vec::new(),
            aux_decl_locals: std::collections::HashSet::new(),
            let_rec_lift: let_rec_lift::LetRecLiftState::default(),
            public_param_infos: Vec::new(),
            mutual_lift_entries: Vec::new(),
            mutual_eq_lemmas: Vec::new(),
            logged_deriving_failures: Vec::new(),
            universe_params: Vec::new(),
            file_universe_params: Vec::new(),
            file_universe_scope_known: false,
            decl_explicit_universes: None,
            metas: MetaState::new(),
            next_fvar: 0,
            level_mint: crate::level_mint::LevelMint::new(),
            instances,
            local_instances: Vec::new(),
            hidden_instances: other_modules_local_instances(env),
            scoped_instances: imported_scoped_instances(env),
            foreign_private_decls: std::sync::Arc::default(),
            private_module_known: false,
            instance_view: None,
            classical_tactic_scope: 0,
            instance_search_steps: 0,
            failed_local_subgoals: std::collections::HashSet::new(),
            instance_search_stuck: false,
            user_default_instance_answers: 0,
            open_numeral_let_types: Vec::new(),
            let_rec_settled_open_numerals: 0,
            numeral_postpone_depth: 0,
            postponing_let_depth: 0,
            postponing_scope_start: 0,
            defer_user_defaults: 0,
            deferred_user_default_goals: 0,
            user_default_priority_floor: None,
            lean_order_ground_refusal: None,
            lean_default_points: 0,
            binop_tree_plans: Vec::new(),
            redex_binder_domains: None,
            redex_binder_escaped: false,
            pinned_redex_binder_types: None,
            pinned_lambda_binder_types: Vec::new(),
            settle_floor: None,
            bne_beq_head: None,
            alias_instance_heads: HashMap::new(),
            struct_lit_trees: Vec::new(),
            struct_lit_join_parent: false,
            default_instances: HashMap::new(),
            instance_cache: HashMap::new(),
            tc_caches: RefCell::new(TcCaches::default()),
            tc_cache_state: RefCell::new(None),
            local_ctx_cache: RefCell::new(None),
            decl_memo: RefCell::new(demand_local_ctx::DeclMemo::default()),
            recursor_auth_cache: RefCell::new(HashMap::new()),
            cases_on_auth_cache: RefCell::new(HashMap::new()),
            macro_ctx: MacroCtx::new(),
            tactic_registry: {
                let mut reg = TacticRegistry::new();
                crate::tactic::builtins::register_builtin_tactics(&mut reg);
                reg
            },
            term_elab_registry: TermElabRegistry::new(),
            user_term_elabs: HashMap::new(),
            imported_term_syntax: None,
            imported_runtime: None,
            meta_value_bindings: HashMap::new(),
            collected_aesop_attrs: Vec::new(),
            collected_simp_attrs: Vec::new(),
            collected_local_simp: Vec::new(),
            collected_local_csimp: Vec::new(),
            collected_scoped_csimp: Vec::new(),
            collected_reducibility: Vec::new(),
            collected_matchers: Vec::new(),
            collected_extern: Vec::new(),
            collected_export: Vec::new(),
            collected_deprecated: Vec::new(),
            collected_inline_attributes: Vec::new(),
            collected_specialize: Vec::new(),
            collected_csimp: Vec::new(),
            collected_definition_attrs: Vec::new(),
            simple_equation_sources: Vec::new(),
            collected_congr: Vec::new(),
            collected_ext: Vec::new(),
            collected_grind: Vec::new(),
            collected_refl: Vec::new(),
            collected_symm: Vec::new(),
            collected_nospecialize: Vec::new(),
            collected_implemented_by: Vec::new(),
            collected_coe: Vec::new(),
            collected_match_pattern: Vec::new(),
            collected_init: Vec::new(),
            collected_default_instance: Vec::new(),
            collected_instance_attrs: Vec::new(),
            collected_scoped_instance_attrs: Vec::new(),
            collected_class_attrs: Vec::new(),
            collected_derive_handler: Vec::new(),
            collected_attribute_removals: Vec::new(),
            auto_implicits: Vec::new(),
            auto_implicit_lookup: HashMap::new(),
            in_decl_context: false,
            in_term_body: false,
            section_binder_stack: Vec::new(),
            included_var_stack: Vec::new(),
            current_expected_type: None,
            dot_elim: Default::default(),
            recursive_def_ctx: None,
            explicit_mode: false,
            value_is_explicit_app: false,
            suppress_binop_homogenize: false,
            lambda_postpone: Default::default(),
            postponed_open_carrier_instances: Vec::new(),
            do_pure_obligations: Vec::new(),
            do_monad_info: None,
            do_control_info: None,
            do_control_stack: None,
            do_wrapped_monad: None,
            do_loop_ctx: None,
            do_mut_vars: Vec::new(),
            do_active_mut_vars: Vec::new(),
            do_pure_state: false,
            pending_level_assigns: RefCell::new(Vec::new()),
            namespace_state: crate::namespace::NamespaceState::new(),
            namespace_prefix: SurfaceName::default(),
            decl_site_namespace: None,
            local_options: HashMap::new(),
            match_dependent_motive: None,
            match_dependent_motive_indices: 0,
            match_index_discriminating_punit: None,
            nested_mutual_aux_arms: None,
            hole_names: HashMap::new(),
            local_forall_binder_names: HashMap::new(),
            surface_forall_binder_names: Vec::new(),
            self_reference: None,
            unstaged_siblings: Vec::new(),
            tactic_trace: tactic_trace::TacticTrace::default(),
            tactic_goal_capture: None,
            term_info_capture: None,
            term_contexts: Vec::new(),
            term_info_stack: Vec::new(),
            term_local_display_names: HashMap::new(),
            tactic_goal_block: None,
            section_prune: None,
            section_prune_outcome: None,
        }
    }

    /// Inject per-declaration instance-scope state from the `FileContext`
    /// (B99): `local instance`s whose scope has ended (hidden), `scoped
    /// instance` → declaring-namespace visibility, and the
    /// `@[default_instance]` table (class → entries in declaration order).
    /// All three default to empty, leaving resolution unchanged for callers
    /// that construct an `ElabCtx` without file-scope state.
    pub(crate) fn set_instance_scope_state(
        &mut self,
        hidden: std::collections::HashSet<Name>,
        scoped: HashMap<Name, Name>,
        defaults: &[(Name, Name, u32)],
    ) {
        self.hidden_instances = hidden;
        // The file's own `scoped instance`s on top of the IMPORTED ones (the
        // olean's `scoped` entries, seeded at construction): both must keep
        // gating on `open`, so this merges rather than replaces.
        self.scoped_instances = imported_scoped_instances(self.env);
        self.scoped_instances.extend(scoped);
        self.default_instances.clear();
        for (inst, class, priority) in defaults {
            self.default_instances
                .entry(class.clone())
                .or_default()
                .push((inst.clone(), *priority));
        }
    }

    /// Inject the module's CURRENT instance state
    /// ([`crate::FileContext::instance_view`]): from here on it alone decides
    /// which instances resolution may pick (`instance_visible`), and the
    /// entries whose priority or position differ from the environment's
    /// global table are re-sorted into Lean's order in this context's table.
    pub(crate) fn set_instance_view(&mut self, view: crate::instance_store::InstanceView) {
        self.hidden_instances = view.hidden();
        let changed: Vec<Name> = view.overrides.keys().cloned().collect();
        self.instances
            .apply_instance_entries(&changed, &view.overrides, self.env);
        self.instance_view = Some(view);
    }

    /// Inject the `private` declarations of other modules, which no name in
    /// this declaration may resolve to (see `FileContext::
    /// foreign_private_decls`).
    pub(crate) fn set_foreign_private_decls(
        &mut self,
        names: std::sync::Arc<std::collections::HashSet<Name>>,
    ) {
        self.foreign_private_decls = names;
        self.private_module_known = true;
    }

    /// Get mutable access to the instance table
    pub fn instances_mut(&mut self) -> &mut InstanceTable {
        &mut self.instances
    }

    /// Get read access to the instance table
    pub fn instances(&self) -> &InstanceTable {
        &self.instances
    }

    /// Get read access to the local instance entries.
    ///
    /// Returns a slice of `(FVarId, Expr)` pairs representing instance-implicit
    /// binders that are in scope. These are searched before global instances
    /// during instance resolution.
    pub(crate) fn local_instance_entries(&self) -> &[(FVarId, Expr)] {
        &self.local_instances
    }

    /// Set the expected type for bidirectional type checking (#172)
    ///
    /// Used by anonymous constructor syntax `⟨...⟩` to determine which structure
    /// to construct. Should be set before elaborating definition bodies with type annotations.
    pub(crate) fn set_expected_type(&mut self, ty: Option<Expr>) {
        self.current_expected_type = ty;
    }

    /// Install the auxiliary-arm source for a fused nested-mutual fold (Track AA).
    ///
    /// When elaborating the fused primary def (`T.f : T -> R`) of a
    /// `{ T.f : T -> R, T.g : C T -> R }` block, this carries `T.g`'s arms so
    /// the nested-recursor minor builder fills the `T._<container>` minors with
    /// the genuine fold body (instead of a degenerate default), and the sibling
    /// function names so a sibling self-call inside a minor body rewrites to its
    /// induction hypothesis. Pass `None` to clear it. See
    /// [`super::NestedMutualAuxArms`].
    pub(crate) fn set_nested_mutual_aux_arms(
        &mut self,
        source: Option<(
            SurfaceName,
            Vec<clean_parser::SurfaceMatchArm>,
            Vec<(SurfaceName, SurfaceExpr)>,
        )>,
    ) {
        self.nested_mutual_aux_arms =
            source.map(
                |(container_name, arms, sibling_signatures)| NestedMutualAuxArms {
                    container_name,
                    arms,
                    sibling_signatures,
                },
            );
    }

    /// Get the current expected type, if any (#172)
    pub fn expected_type(&self) -> Option<&Expr> {
        self.current_expected_type.as_ref()
    }

    /// Get read access to the macro context
    pub fn macro_ctx(&self) -> &MacroCtx {
        &self.macro_ctx
    }

    /// Replace the macro context for file-scoped notation/macro state.
    ///
    /// Syncs the scoped-notation gate to this context's namespace prefix: a
    /// persisted `MacroCtx` arrives from `FileContext` with the PREVIOUS
    /// declaration's namespace recorded, and callers set the namespace state
    /// (`set_namespace_state`) before installing the macro context.
    pub(crate) fn set_macro_ctx(&mut self, macro_ctx: MacroCtx) {
        self.macro_ctx = macro_ctx;
        self.macro_ctx.set_current_namespace(&self.namespace_prefix);
    }

    /// Replace the tactic registry for file-scoped tactic elaborator state.
    pub(crate) fn set_tactic_registry(&mut self, tactic_registry: TacticRegistry) {
        self.tactic_registry = tactic_registry;
    }

    /// Move out the macro context after declaration elaboration.
    pub(crate) fn take_macro_ctx(&mut self) -> MacroCtx {
        std::mem::take(&mut self.macro_ctx)
    }

    /// Move out the tactic registry after declaration elaboration.
    pub(crate) fn take_tactic_registry(&mut self) -> TacticRegistry {
        std::mem::take(&mut self.tactic_registry)
    }

    /// Replace the user term elaborators for file-scoped `elab ... : term` state.
    pub(crate) fn set_user_term_elabs(&mut self, elabs: HashMap<String, user_term::UserTermElab>) {
        self.user_term_elabs = elabs;
    }

    /// Move out the user term elaborators after declaration elaboration.
    pub(crate) fn take_user_term_elabs(&mut self) -> HashMap<String, user_term::UserTermElab> {
        std::mem::take(&mut self.user_term_elabs)
    }

    /// Set universe parameters for the current declaration
    #[must_use]
    pub fn with_universe_params(mut self, params: Vec<SurfaceName>) -> Self {
        self.universe_params = params;
        self
    }

    /// Get an option value, checking local overrides first, then environment.
    ///
    /// Local overrides are set by `set_option` commands inside sections or
    /// namespaces and are scoped to the enclosing block. Environment options
    /// are set at file scope.
    #[must_use]
    pub(crate) fn get_option(&self, name: &str) -> Option<&Option<String>> {
        self.local_options
            .get(name)
            .or_else(|| self.env.get_option(name))
    }

    /// Set a local option override (for section-scoped `set_option`).
    pub(crate) fn set_local_option(&mut self, name: String, value: Option<String>) {
        self.local_options.insert(name, value);
    }
}
