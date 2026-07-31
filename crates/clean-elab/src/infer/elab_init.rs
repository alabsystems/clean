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

            instances.add_instance_with_synth_order(
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

    instances
}

impl<'a> ElabCtx<'a> {
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
            locals: Vec::new(),
            local_let_values: HashMap::new(),
            shared_if_let_scrutinees: Vec::new(),
            universe_params: Vec::new(),
            metas: MetaState::new(),
            next_fvar: 0,
            next_universe: 0,
            instances,
            local_instances: Vec::new(),
            hidden_instances: std::collections::HashSet::new(),
            scoped_instances: HashMap::new(),
            default_instances: HashMap::new(),
            instance_cache: HashMap::new(),
            tc_caches: RefCell::new(TcCaches::default()),
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
            meta_value_bindings: HashMap::new(),
            collected_aesop_attrs: Vec::new(),
            collected_simp_attrs: Vec::new(),
            collected_reducibility: Vec::new(),
            collected_extern: Vec::new(),
            collected_export: Vec::new(),
            collected_deprecated: Vec::new(),
            collected_inline: Vec::new(),
            collected_noinline: Vec::new(),
            collected_always_inline: Vec::new(),
            collected_specialize: Vec::new(),
            collected_csimp: Vec::new(),
            collected_congr: Vec::new(),
            collected_ext: Vec::new(),
            collected_refl: Vec::new(),
            collected_symm: Vec::new(),
            collected_macro_inline: Vec::new(),
            collected_inline_if_reduce: Vec::new(),
            collected_nospecialize: Vec::new(),
            collected_implemented_by: Vec::new(),
            collected_coe: Vec::new(),
            collected_match_pattern: Vec::new(),
            collected_init: Vec::new(),
            collected_default_instance: Vec::new(),
            collected_instance_attrs: Vec::new(),
            collected_derive_handler: Vec::new(),
            collected_attribute_removals: Vec::new(),
            auto_implicits: Vec::new(),
            auto_implicit_lookup: HashMap::new(),
            in_decl_context: false, // Default to false for standalone expression elaboration
            in_term_body: false,
            section_binder_stack: Vec::new(),
            current_expected_type: None,
            recursive_def_ctx: None,
            explicit_mode: false,
            suppress_binop_homogenize: false,
            do_monad_info: None,
            do_control_info: None,
            do_control_stack: None,
            do_wrapped_monad: None,
            do_loop_ctx: None,
            do_mut_vars: Vec::new(),
            do_pure_state: false,
            pending_level_assigns: RefCell::new(Vec::new()),
            namespace_state: crate::namespace::NamespaceState::new(),
            namespace_prefix: String::new(),
            local_options: HashMap::new(),
            match_dependent_motive: None,
            match_dependent_motive_indices: 0,
            match_index_discriminating_punit: None,
            nested_mutual_aux_arms: None,
            hole_names: HashMap::new(),
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
    pub fn take_aesop_attrs(&mut self) -> Vec<(Name, AesopAttr)> {
        std::mem::take(&mut self.collected_aesop_attrs)
    }

    /// Take collected simp lemma attributes for registration
    pub fn take_simp_attrs(&mut self) -> Vec<(Name, KernelSimpPriority)> {
        std::mem::take(&mut self.collected_simp_attrs)
    }

    /// Take collected reducibility attributes for registration
    pub fn take_reducibility(&mut self) -> Vec<(Name, Reducibility)> {
        std::mem::take(&mut self.collected_reducibility)
    }

    /// Take collected extern bindings for registration
    pub fn take_extern(&mut self) -> Vec<(Name, String)> {
        std::mem::take(&mut self.collected_extern)
    }

    /// Take collected export bindings for registration
    pub fn take_export(&mut self) -> Vec<(Name, String)> {
        std::mem::take(&mut self.collected_export)
    }

    /// Take collected deprecations for registration
    pub fn take_deprecated(&mut self) -> Vec<(Name, Option<String>)> {
        std::mem::take(&mut self.collected_deprecated)
    }

    /// Take collected inline hints for registration
    pub fn take_inline(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_inline)
    }

    /// Take collected noinline hints for registration
    pub fn take_noinline(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_noinline)
    }

    /// Take collected always_inline hints for registration
    pub fn take_always_inline(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_always_inline)
    }

    /// Take collected specialize hints for registration
    pub fn take_specialize(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_specialize)
    }

    /// Take collected csimp lemmas for registration
    pub fn take_csimp(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_csimp)
    }

    /// Take collected congr lemmas for registration
    pub fn take_congr(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_congr)
    }

    /// Take collected ext lemmas for registration
    pub fn take_ext(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_ext)
    }

    /// Take collected refl lemmas for registration
    pub fn take_refl(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_refl)
    }

    /// Take collected symm lemmas for registration
    pub fn take_symm(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_symm)
    }

    /// Take collected macro_inline hints for registration
    pub fn take_macro_inline(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_macro_inline)
    }

    /// Take collected inline_if_reduce hints for registration
    pub fn take_inline_if_reduce(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_inline_if_reduce)
    }

    /// Take collected nospecialize hints for registration
    pub fn take_nospecialize(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_nospecialize)
    }

    /// Take collected @[implemented_by] bindings for registration
    pub fn take_implemented_by(&mut self) -> Vec<(Name, String)> {
        std::mem::take(&mut self.collected_implemented_by)
    }

    /// Take collected @[coe] coercion registrations
    pub fn take_coe(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_coe)
    }

    /// Take collected @[match_pattern] registrations
    pub fn take_match_pattern(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_match_pattern)
    }

    /// Take collected @[init] registrations
    pub fn take_init(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_init)
    }

    /// Take collected @[default_instance] registrations (name, priority)
    pub fn take_default_instance(&mut self) -> Vec<(Name, u32)> {
        std::mem::take(&mut self.collected_default_instance)
    }

    /// Take collected `attribute [instance]` / `@[instance N]` registrations
    /// (name, priority) for kernel-side instance registration (B06).
    pub fn take_instance_attrs(&mut self) -> Vec<(Name, u32)> {
        std::mem::take(&mut self.collected_instance_attrs)
    }

    /// Take collected @[derive_handler] registrations.
    pub fn take_derive_handler(&mut self) -> Vec<Name> {
        std::mem::take(&mut self.collected_derive_handler)
    }

    /// Take collected file-scope attribute removals.
    pub fn take_attribute_removals(&mut self) -> Vec<(Name, String)> {
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
    pub fn set_namespace_state(&mut self, state: crate::namespace::NamespaceState) {
        // Sync namespace_prefix from the NamespaceState's current namespace
        // so that qualify_name() correctly prefixes declaration names (#3410).
        let current_ns = state.current_namespace();
        if !current_ns.is_anon() {
            self.namespace_prefix = current_ns.to_string();
        }
        self.namespace_state = state;
    }

    /// Take the namespace state out of this context, replacing it with empty.
    ///
    /// Called after elaboration to persist open/export aliases back to
    /// [`FileContext`] for use by subsequent declarations.
    pub fn take_namespace_state(&mut self) -> crate::namespace::NamespaceState {
        std::mem::take(&mut self.namespace_state)
    }

    /// Create with a pre-populated instance table
    pub fn with_instances(env: &'a Environment, instances: InstanceTable) -> Self {
        Self {
            env,
            locals: Vec::new(),
            local_let_values: HashMap::new(),
            shared_if_let_scrutinees: Vec::new(),
            universe_params: Vec::new(),
            metas: MetaState::new(),
            next_fvar: 0,
            next_universe: 0,
            instances,
            local_instances: Vec::new(),
            hidden_instances: std::collections::HashSet::new(),
            scoped_instances: HashMap::new(),
            default_instances: HashMap::new(),
            instance_cache: HashMap::new(),
            tc_caches: RefCell::new(TcCaches::default()),
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
            meta_value_bindings: HashMap::new(),
            collected_aesop_attrs: Vec::new(),
            collected_simp_attrs: Vec::new(),
            collected_reducibility: Vec::new(),
            collected_extern: Vec::new(),
            collected_export: Vec::new(),
            collected_deprecated: Vec::new(),
            collected_inline: Vec::new(),
            collected_noinline: Vec::new(),
            collected_always_inline: Vec::new(),
            collected_specialize: Vec::new(),
            collected_csimp: Vec::new(),
            collected_congr: Vec::new(),
            collected_ext: Vec::new(),
            collected_refl: Vec::new(),
            collected_symm: Vec::new(),
            collected_macro_inline: Vec::new(),
            collected_inline_if_reduce: Vec::new(),
            collected_nospecialize: Vec::new(),
            collected_implemented_by: Vec::new(),
            collected_coe: Vec::new(),
            collected_match_pattern: Vec::new(),
            collected_init: Vec::new(),
            collected_default_instance: Vec::new(),
            collected_instance_attrs: Vec::new(),
            collected_derive_handler: Vec::new(),
            collected_attribute_removals: Vec::new(),
            auto_implicits: Vec::new(),
            auto_implicit_lookup: HashMap::new(),
            in_decl_context: false,
            in_term_body: false,
            section_binder_stack: Vec::new(),
            current_expected_type: None,
            recursive_def_ctx: None,
            explicit_mode: false,
            suppress_binop_homogenize: false,
            do_monad_info: None,
            do_control_info: None,
            do_control_stack: None,
            do_wrapped_monad: None,
            do_loop_ctx: None,
            do_mut_vars: Vec::new(),
            do_pure_state: false,
            pending_level_assigns: RefCell::new(Vec::new()),
            namespace_state: crate::namespace::NamespaceState::new(),
            namespace_prefix: String::new(),
            local_options: HashMap::new(),
            match_dependent_motive: None,
            match_dependent_motive_indices: 0,
            match_index_discriminating_punit: None,
            nested_mutual_aux_arms: None,
            hole_names: HashMap::new(),
        }
    }

    /// Inject per-declaration instance-scope state from the `FileContext`
    /// (B99): `local instance`s whose scope has ended (hidden), `scoped
    /// instance` → declaring-namespace visibility, and the
    /// `@[default_instance]` table (class → entries in declaration order).
    /// All three default to empty, leaving resolution unchanged for callers
    /// that construct an `ElabCtx` without file-scope state.
    pub fn set_instance_scope_state(
        &mut self,
        hidden: std::collections::HashSet<Name>,
        scoped: HashMap<Name, Name>,
        defaults: &[(Name, Name, u32)],
    ) {
        self.hidden_instances = hidden;
        self.scoped_instances = scoped;
        self.default_instances.clear();
        for (inst, class, priority) in defaults {
            self.default_instances
                .entry(class.clone())
                .or_default()
                .push((inst.clone(), *priority));
        }
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
    pub fn local_instance_entries(&self) -> &[(FVarId, Expr)] {
        &self.local_instances
    }

    /// Set the expected type for bidirectional type checking (#172)
    ///
    /// Used by anonymous constructor syntax `⟨...⟩` to determine which structure
    /// to construct. Should be set before elaborating definition bodies with type annotations.
    pub fn set_expected_type(&mut self, ty: Option<Expr>) {
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
    pub fn set_nested_mutual_aux_arms(
        &mut self,
        source: Option<(String, Vec<clean_parser::SurfaceMatchArm>, Vec<String>)>,
    ) {
        self.nested_mutual_aux_arms =
            source.map(
                |(container_short, arms, sibling_func_names)| super::NestedMutualAuxArms {
                    container_short,
                    arms,
                    sibling_func_names,
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
    pub(crate) fn set_macro_ctx(&mut self, macro_ctx: MacroCtx) {
        self.macro_ctx = macro_ctx;
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
    pub(crate) fn set_user_term_elabs(
        &mut self,
        elabs: std::collections::HashMap<String, super::user_term::UserTermElab>,
    ) {
        self.user_term_elabs = elabs;
    }

    /// Move out the user term elaborators after declaration elaboration.
    pub(crate) fn take_user_term_elabs(
        &mut self,
    ) -> std::collections::HashMap<String, super::user_term::UserTermElab> {
        std::mem::take(&mut self.user_term_elabs)
    }

    /// Set universe parameters for the current declaration
    #[must_use]
    pub fn with_universe_params(mut self, params: Vec<String>) -> Self {
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
