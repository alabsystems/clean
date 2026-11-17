// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attributes collected during elaboration, carried from the `ElabCtx` that
//! produced them to the `Environment` they are registered into.
//!
//! This is a two-step type on purpose. An `ElabCtx` holds an IMMUTABLE borrow
//! of the environment it elaborates against, so the attribute registrations —
//! which need `&mut Environment` — cannot run while it is alive. Splitting
//! [`CtxAttributes::collect`] from [`CtxAttributes::apply`] makes that ordering
//! a property of the types rather than a comment about where to put `drop(ctx)`.
//!
//! It also decouples the two environments. The one-declaration-at-a-time driver
//! elaborates and registers into the same environment, so the split is
//! invisible there. Header-first batch elaboration ([`crate::module_batch`])
//! elaborates against a NON-AUTHORITATIVE staging environment and registers
//! into a separate authoritative one, and needs exactly this handoff to reuse
//! the attribute pipeline without reuniting the two.

use clean_kernel::Name;

use crate::declared_here::{declared_by, AttributeSite, ElabUnit};
use crate::{
    instances, register_aesop_rule, register_user_derive_handler, ElabCtx, ElabError, FileContext,
};
use clean_kernel::env::{
    GrindAttrKind, Reducibility, SimpPriority as KernelSimpPriority, TrustedEnvExt,
};
use clean_parser::AesopAttr;

/// Every attribute an elaboration collected, drained out of its `ElabCtx`.
#[derive(Debug, Default)]
pub(crate) struct CtxAttributes {
    aesop_attrs: Vec<(Name, AesopAttr)>,
    simp_attrs: Vec<(Name, KernelSimpPriority)>,
    /// The subset of `simp_attrs` registered by `local simp`.
    local_simp_attrs: Vec<Name>,
    reducibility_attrs: Vec<(Name, Reducibility)>,
    /// `@[extern]` bindings, with where each was written.
    extern_attrs: Vec<(Name, String, AttributeSite)>,
    export_attrs: Vec<(Name, String)>,
    deprecated_attrs: Vec<(Name, Option<String>)>,
    inline_attrs: Vec<Name>,
    noinline_attrs: Vec<Name>,
    always_inline_attrs: Vec<Name>,
    specialize_attrs: Vec<Name>,
    csimp_attrs: Vec<Name>,
    definition_attrs: Vec<crate::definition_attrs::NamedAttribute>,
    local_csimp_attrs: Vec<Name>,
    scoped_csimp_attrs: Vec<(Name, Name)>,
    congr_attrs: Vec<Name>,
    ext_attrs: Vec<Name>,
    /// `@[grind]` registrations. Feeds the grind registry ONLY — never the
    /// ambient `@[simp]` set.
    grind_attrs: Vec<(Name, GrindAttrKind)>,
    refl_attrs: Vec<Name>,
    symm_attrs: Vec<Name>,
    macro_inline_attrs: Vec<Name>,
    inline_if_reduce_attrs: Vec<Name>,
    nospecialize_attrs: Vec<Name>,
    implemented_by_attrs: Vec<crate::implemented_by::ImplementedByUse>,
    coe_attrs: Vec<Name>,
    match_pattern_attrs: Vec<Name>,
    init_attrs: Vec<Name>,
    default_instance_attrs: Vec<(Name, u32)>,
    instance_attrs: Vec<(Name, u32)>,
    /// `attribute [local instance]` / `attribute [scoped instance]`.
    scoped_instance_attrs: Vec<(Name, u32, crate::infer::ScopedInstanceAttr)>,
    /// Declaration/standalone class attributes, retaining global/local/scoped origin.
    class_attrs: Vec<crate::class_attribute::ClassAttribute>,
    derive_handler_attrs: Vec<Name>,
    attribute_removals: Vec<(Name, String)>,
    /// Parameter names of the `where` / `let rec` auxiliaries the declaration
    /// lifted (`parent.go`), for named arguments on them.
    let_rec_param_infos: Vec<(Name, Vec<(Name, clean_kernel::BinderInfo)>)>,
    /// Members a recursive `mutual` block was lifted into (gap G23).
    mutual_lift_entries: Vec<crate::infer::mutual_lift::MutualLiftEntry>,
    mutual_eq_lemmas: Vec<crate::infer::mutual_lift::PendingEqLemma>,
}

impl CtxAttributes {
    /// Drain every attribute out of `ctx`. Must run BEFORE `ctx` is dropped;
    /// after this the context holds none.
    pub(crate) fn collect(ctx: &mut ElabCtx<'_>) -> Self {
        Self {
            aesop_attrs: ctx.take_aesop_attrs(),
            simp_attrs: ctx.take_simp_attrs(),
            local_simp_attrs: ctx.take_local_simp(),
            reducibility_attrs: ctx.take_reducibility(),
            extern_attrs: ctx.take_extern(),
            export_attrs: ctx.take_export(),
            deprecated_attrs: ctx.take_deprecated(),
            inline_attrs: ctx.take_inline(),
            noinline_attrs: ctx.take_noinline(),
            always_inline_attrs: ctx.take_always_inline(),
            specialize_attrs: ctx.take_specialize(),
            csimp_attrs: ctx.take_csimp(),
            definition_attrs: ctx.take_definition_attrs(),
            local_csimp_attrs: ctx.take_local_csimp(),
            scoped_csimp_attrs: ctx.take_scoped_csimp(),
            congr_attrs: ctx.take_congr(),
            ext_attrs: ctx.take_ext(),
            grind_attrs: ctx.take_grind(),
            refl_attrs: ctx.take_refl(),
            symm_attrs: ctx.take_symm(),
            macro_inline_attrs: ctx.take_macro_inline(),
            inline_if_reduce_attrs: ctx.take_inline_if_reduce(),
            nospecialize_attrs: ctx.take_nospecialize(),
            implemented_by_attrs: ctx.take_implemented_by(),
            coe_attrs: ctx.take_coe(),
            match_pattern_attrs: ctx.take_match_pattern(),
            init_attrs: ctx.take_init(),
            default_instance_attrs: ctx.take_default_instance(),
            instance_attrs: ctx.take_instance_attrs(),
            scoped_instance_attrs: ctx.take_scoped_instance_attrs(),
            class_attrs: ctx.take_class_attrs(),
            derive_handler_attrs: ctx.take_derive_handler(),
            attribute_removals: ctx.take_attribute_removals(),
            let_rec_param_infos: ctx.take_let_rec_param_infos(),
            mutual_lift_entries: ctx.take_mutual_lift_entries(),
            mutual_eq_lemmas: ctx.take_mutual_eq_lemmas(),
        }
    }

    /// Register every collected attribute into `env`.
    ///
    /// Must run AFTER the declaration itself is registered, so an attribute can
    /// reference it. `env` is the AUTHORITATIVE environment — attributes are
    /// registered where the declaration is, never where it was elaborated.
    ///
    /// # Errors
    /// Returns [`ElabError`] when an attribute names a declaration that does
    /// not exist, targets a type that does not conclude in a registered class,
    /// or requests an unsupported removal.
    pub(crate) fn apply(
        self,
        env: &mut clean_kernel::Environment,
        mut file_ctx: Option<&mut FileContext>,
    ) -> Result<(), ElabError> {
        let Self {
            aesop_attrs,
            simp_attrs,
            local_simp_attrs,
            reducibility_attrs,
            extern_attrs,
            export_attrs,
            deprecated_attrs,
            inline_attrs,
            noinline_attrs,
            always_inline_attrs,
            specialize_attrs,
            csimp_attrs,
            definition_attrs,
            local_csimp_attrs,
            scoped_csimp_attrs,
            congr_attrs,
            ext_attrs,
            grind_attrs,
            refl_attrs,
            symm_attrs,
            macro_inline_attrs,
            inline_if_reduce_attrs,
            nospecialize_attrs,
            implemented_by_attrs,
            coe_attrs,
            match_pattern_attrs,
            init_attrs,
            default_instance_attrs,
            instance_attrs,
            scoped_instance_attrs,
            class_attrs,
            derive_handler_attrs,
            attribute_removals,
            let_rec_param_infos,
            mutual_lift_entries,
            mutual_eq_lemmas,
        } = self;

        // Class refusal must not leave an earlier attribute or an earlier
        // target of the same command partially registered. Registration of the
        // declaration itself has already happened, but every attribute effect
        // below remains untouched if any class target/scope is invalid.
        let class_infos = crate::class_attribute::prepare_attributes(env, &class_attrs)?;

        crate::definition_attrs::apply(env, file_ctx.as_deref(), definition_attrs)?;

        // The lifted-member registry, for members that registered.
        for entry in mutual_lift_entries {
            if env.get_const(&entry.member).is_some() {
                env.add_ext_entry::<crate::infer::mutual_lift::MutualLiftState>(
                    crate::infer::mutual_lift::mutual_lift_idx(),
                    &entry,
                );
            }
        }

        // Named equation lemmas `f.eq_N` of lifted members, through the
        // kernel's checked `add_decl`. One the kernel refuses is not minted
        // (its name stays unknown); it is never registered unchecked.
        for lemma in mutual_eq_lemmas {
            if env.get_const(&lemma.name).is_some() {
                continue;
            }
            let name = lemma.name.clone();
            if let Err(err) = env.add_decl(clean_kernel::Declaration::Theorem {
                name: lemma.name,
                level_params: lemma.universe_params,
                type_: lemma.ty,
                value: lemma.proof,
            }) {
                tracing::debug!("mutual lift: equation lemma `{name}` not minted: {err}");
            }
        }

        // Parameter names of lifted helpers, for named arguments on them.
        // Only for an auxiliary that registered.
        for (name, infos) in let_rec_param_infos {
            if env.get_const(&name).is_some() {
                env.add_checked_param_infos(&name, infos, false)
                    .map_err(|error| ElabError::KernelRegistrationFailed {
                        operation: "lifted helper parameter metadata".into(),
                        detail: error.to_string(),
                    })?;
            }
        }

        // Now register attributes that reference the declaration

        // Register aesop rules
        for (name, attr) in aesop_attrs {
            register_aesop_rule(env, name, &attr);
        }

        // Register simp lemmas
        for (name, priority) in simp_attrs {
            env.register_simp_lemma(name, priority);
        }
        // A `local simp` lemma is retired when the scope it was declared in
        // ends (`FileContext::retire_local_attributes`). With no file context
        // there is no scope to end, and it stays for the rest of the run —
        // what Lean does for a `local` attribute outside any section.
        if let Some(fc) = file_ctx.as_deref_mut() {
            for name in local_simp_attrs {
                fc.record_local_simp_lemma(name);
            }
        }

        // Apply reducibility attributes
        // These override the default reducibility set at declaration time
        for (name, reducibility) in reducibility_attrs {
            env.set_reducibility(&name, reducibility);
        }

        // Register extern bindings. Lean's `externAttr` is a
        // `ParametricAttribute`, whose `add` refuses the command form on a
        // declaration of an imported module: one this run did not add
        // (`crate::declared_here`).
        let unit = ElabUnit::of(file_ctx.as_deref());
        for (decl_name, extern_name, site) in extern_attrs {
            if site == AttributeSite::AttributeCommand && !declared_by(env, unit, &decl_name) {
                return Err(ElabError::AttributeOnImportedDeclaration {
                    attribute: "extern",
                    decl: decl_name,
                });
            }
            env.register_extern(decl_name, extern_name);
        }

        // Register export bindings
        for (decl_name, export_name) in export_attrs {
            env.register_export(decl_name, export_name);
        }

        // Register deprecations
        for (name, msg) in deprecated_attrs {
            env.register_deprecated(name, msg);
        }

        // Register inline hints
        for name in inline_attrs {
            env.register_inline(name);
        }

        // Register noinline hints
        for name in noinline_attrs {
            env.register_noinline(name);
        }

        // Register always_inline hints
        for name in always_inline_attrs {
            env.register_always_inline(name);
        }

        // Register specialize hints
        for name in specialize_attrs {
            env.register_specialize(name);
        }

        for (name, namespace) in scoped_csimp_attrs {
            require_public_csimp(env, file_ctx.as_deref(), &name)?;
            if namespace.is_anon() {
                return Err(ElabError::Unsupported {
                    feature: "scoped attributes must be used inside namespaces".into(),
                });
            }
            if !clean_kernel::env::csimp::define_scoped(env, &namespace, &name) {
                return Err(ElabError::InvalidCsimpTheorem { name });
            }
            if let Some(fc) = file_ctx.as_deref_mut() {
                fc.activate_new_scoped_csimp(env, &namespace, &name)?;
            }
        }

        for name in local_csimp_attrs {
            let token = crate::csimp_attribute::register_local(env, &name)?;
            if let Some(fc) = file_ctx.as_deref_mut() {
                fc.record_local_csimp(token);
            }
        }

        // Register csimp lemmas
        for name in csimp_attrs {
            require_public_csimp(env, file_ctx.as_deref(), &name)?;
            crate::csimp_attribute::register(env, &name)?;
        }

        // Register congr lemmas
        for name in congr_attrs {
            env.register_congr(name);
        }

        // Register ext lemmas
        for name in ext_attrs {
            env.register_ext(name);
        }

        // Register `@[grind]` lemmas. Separate registry, consumed only by the
        // `grind` tactic.
        for (name, kind) in grind_attrs {
            env.register_grind_lemma(name, kind);
        }

        // Register refl lemmas
        for name in refl_attrs {
            env.register_refl(name);
        }

        // Register symm lemmas
        for name in symm_attrs {
            env.register_symm(name);
        }

        // Register macro_inline hints
        for name in macro_inline_attrs {
            env.register_macro_inline(name);
        }

        // Register inline_if_reduce hints
        for name in inline_if_reduce_attrs {
            env.register_inline_if_reduce(name);
        }

        // Register nospecialize hints
        for name in nospecialize_attrs {
            env.register_nospecialize(name);
        }

        // Register @[implemented_by] bindings, each resolved and validated as
        // pinned Lean does (`crate::implemented_by`): the compiler runs the
        // implementation in the declaration's place, so a binding Lean rejects
        // must never register.
        let mut bindings = Vec::with_capacity(implemented_by_attrs.len());
        for use_ in &implemented_by_attrs {
            let target =
                crate::implemented_by::resolve_implemented_by(env, file_ctx.as_deref(), use_)?;
            bindings.push((use_.decl.clone(), target));
        }
        // The command form comes after code that may already reach what it
        // binds: record that code in the environment before the binding
        // changes any chain (`crate::implemented_by::compiled_before_binding`),
        // with or without a file context, so every lane compiling from `env`
        // sees it (`Environment::compiled_before_record`).
        // A binding that is not registered (`binding_applies`) rebinds nothing.
        let rebound: std::collections::HashSet<Name> = implemented_by_attrs
            .iter()
            .filter(|use_| {
                use_.site == AttributeSite::AttributeCommand
                    && crate::implemented_by::binding_applies(env, &use_.decl)
            })
            .map(|use_| use_.decl.clone())
            .collect();
        if !rebound.is_empty() {
            let found = crate::implemented_by::compiled_before_binding(env, &rebound);
            env.record_compiled_before(found);
            // The rebound declaration's OWN code came first too, and pinned
            // Lean's inliner copies it into callers compiled after the
            // command (`crate::implemented_by::own_code_before_binding`).
            let own = crate::implemented_by::own_code_before_binding(env, &rebound);
            env.record_compiled_before(own);
        }
        for (decl_name, impl_name) in bindings {
            // A `@[macro_inline]` declaration's body is expanded at every
            // call site, and pinned Lean never runs its implementation
            // (`crate::implemented_by::binding_applies`).
            if crate::implemented_by::binding_applies(env, &decl_name) {
                env.register_implemented_by(decl_name, impl_name);
            }
        }

        // Register @[coe] coercions
        for name in coe_attrs {
            env.register_coercion(name);
        }

        // Register @[match_pattern] declarations
        for name in match_pattern_attrs {
            env.register_match_pattern(name);
        }

        // Register @[init] functions
        // Note: actual initialization execution requires IO runtime; we record the
        // registration so downstream consumers can query and execute init functions.
        for name in init_attrs {
            env.register_init_fn(name);
        }

        // Register @[default_instance] declarations (B99): record membership in
        // the kernel-side registry (pre-existing) AND the FileContext
        // default-instance table (class → entries with priority, declaration
        // order) that drives open-metavariable defaulting in instance
        // resolution. The class is read off the declaration type's conclusion
        // (like the `attribute [instance]` handler below); a conclusion without
        // a constant head cannot participate in class-goal defaulting, so only
        // the membership registry is updated for it (unchanged behavior).
        for (name, priority) in default_instance_attrs {
            if let Some(fc) = file_ctx.as_deref_mut() {
                let conclusion_class = env.get_const(&name).and_then(|info| {
                    let mut conclusion = &info.type_;
                    while let clean_kernel::ExprKind::Pi(_, _, body) = conclusion.kind() {
                        conclusion = body;
                    }
                    instances::extract_class_app(conclusion).map(|(class_name, _)| class_name)
                });
                if let Some(class_name) = conclusion_class {
                    fc.record_default_instance(name.clone(), class_name, priority);
                }
            }
            env.register_default_instance(name);
        }

        // Register `attribute [instance] foo` / `@[instance N] def foo` targets as
        // type class instances (B06; sweep row classes_instances/p14). Lean ground
        // truth: the `instance` attribute calls `addInstance`
        // (lean4 `src/Lean/Meta/Instances.lean`) after validating that the
        // declaration's type concludes in a class application. The class name is
        // read off the target type's conclusion; a non-class conclusion is a LOUD
        // error, exactly like Lean's "invalid 'instance' attribute". Duplicate
        // registration (e.g. re-running the attribute command) is a no-op.
        // All targets were validated before any attribute effects. Classes
        // must be visible before the instance attributes below are applied.
        for info in class_infos {
            env.register_class(info);
        }

        // The instance attributes change Lean's INSTANCE STATE, which is
        // scoped (see `crate::instance_store`); `instance_state` applies
        // them against the file's scope state. Without a `FileContext` the
        // file is a single top-level scope.
        let mut temp_fc;
        let fc_for_instances: &mut FileContext = match file_ctx.as_deref_mut() {
            Some(fc) => fc,
            None => {
                temp_fc = FileContext::new();
                &mut temp_fc
            }
        };
        for (name, priority) in instance_attrs {
            instance_state::add_global(env, fc_for_instances, &name, priority)?;
        }
        for (name, priority, kind) in scoped_instance_attrs {
            instance_state::add_scoped(env, fc_for_instances, &name, priority, &kind)?;
        }

        // Register @[derive_handler] declarations.
        for name in derive_handler_attrs {
            register_user_derive_handler(env, &name)?;
        }

        for (name, attr_name) in attribute_removals {
            match attr_name.as_str() {
                "instance" => {
                    let fc: &mut FileContext = match file_ctx.as_deref_mut() {
                        Some(fc) => fc,
                        None => {
                            temp_fc = FileContext::new();
                            &mut temp_fc
                        }
                    };
                    instance_state::erase(env, fc, &name)?;
                }
                "simp" => {
                    if !env.unregister_simp_lemma(&name) {
                        return Err(ElabError::Unsupported {
                            feature: format!(
                                "cannot remove @[{attr_name}]: not applied to '{}'",
                                name
                            ),
                        });
                    }
                }
                _ => {
                    return Err(ElabError::Unsupported {
                        feature: format!("attribute removal for '[-{attr_name}]' is not supported"),
                    });
                }
            }
        }
        Ok(())
    }
}

/// Lean 4.8.0's `instance` attribute (`Lean/Meta/Instances.lean`:
/// `addInstance` with its `AttributeKind`, and `erase`) against the module's
/// instance-state stack ([`crate::instance_store`], which states Lean's model
/// and cites its sources). Every form is applied exactly as Lean applies it:
///
/// * a global entry (`attribute [instance p] x`) is inserted into every open
///   scope's state and into the environment's global table — IN PLACE with
///   the new priority where the state's tree already holds `x` (erased or
///   not: `eraseCore` leaves the tree entry), pushed as the newest where it
///   does not;
/// * a `local` entry into the innermost state only;
/// * a `scoped` entry into `scopedEntries[ns]` and every state where `ns` is
///   active;
/// * `-instance` erases from the innermost state only, and fails when the
///   instance is not in force there ("'x' does not have [instance]
///   attribute").
mod instance_state {
    use super::{instances, ElabError, FileContext, Name};

    /// Register `name`, not yet an instance, as a fresh entry of its class.
    fn register_new(
        env: &mut clean_kernel::Environment,
        name: &Name,
        priority: u32,
    ) -> Result<(), ElabError> {
        // One shared implementation of Lean's `getClassName` rule, also used
        // by the `@[instance]` command-elab handler, so the two paths cannot
        // drift into inventing different class names.
        let class_name = instances::instance_class_of(env, name)?;
        crate::instance_alias::register_alias_class(env, &class_name);
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name: name.clone(),
            class_name,
            priority,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// `attribute [instance p] name` / `@[instance p]`.
    pub(super) fn add_global(
        env: &mut clean_kernel::Environment,
        fc: &mut FileContext,
        name: &Name,
        priority: u32,
    ) -> Result<(), ElabError> {
        if !env.is_instance(name) {
            // A fresh global entry: pushed in every state and in the table.
            return register_new(env, name, priority);
        }
        fc.instance_store_mut().add_global(env, name, priority);
        // It has a global entry now, so it is no longer only `scoped`.
        fc.forget_scoped_instance(name);
        Ok(())
    }

    /// `attribute [local instance p] name` / `attribute [scoped instance p]
    /// name`.
    pub(super) fn add_scoped(
        env: &mut clean_kernel::Environment,
        fc: &mut FileContext,
        name: &Name,
        priority: u32,
        kind: &crate::infer::ScopedInstanceAttr,
    ) -> Result<(), ElabError> {
        match kind {
            crate::infer::ScopedInstanceAttr::Scoped(ns) => {
                if ns.is_anon() {
                    return Err(ElabError::Unsupported {
                        feature: "scoped attributes must be used inside namespaces".to_string(),
                    });
                }
                if !env.is_instance(name) {
                    // Its only entry is this scoped one: in no state until
                    // `ns` is active there.
                    register_new(env, name, priority)?;
                    env.get_ext_state_mut::<clean_olean::ScopedInstanceState>(
                        clean_olean::scoped_instance_idx(),
                    )
                    .scope_of
                    .insert(name.clone(), ns.clone());
                    fc.record_scoped_instance(name.clone(), ns.clone());
                }
                fc.instance_store_mut().add_scoped(env, ns, name, priority);
                Ok(())
            }
            crate::infer::ScopedInstanceAttr::Local => {
                if !env.is_instance(name) {
                    // Its only entry is this local one: never exported.
                    register_new(env, name, priority)?;
                    env.mark_local_instance(name.clone());
                }
                fc.instance_store_mut().add_local(env, name, priority);
                Ok(())
            }
        }
    }

    /// `attribute [-instance] name`.
    pub(super) fn erase(
        env: &mut clean_kernel::Environment,
        fc: &mut FileContext,
        name: &Name,
    ) -> Result<(), ElabError> {
        fc.instance_store_mut()
            .erase(env, name)
            .map_err(ElabError::UnknownIdent)
    }
}

// Lean requires exported/scoped compiler attributes to name public declarations
// in module-system files. Local attributes and legacy private rules are valid.
fn require_public_csimp(
    env: &clean_kernel::Environment,
    file: Option<&FileContext>,
    name: &Name,
) -> Result<(), ElabError> {
    if file.is_some_and(FileContext::is_module_system) && env.is_private(name) {
        return Err(ElabError::Unsupported {
            feature: format!("Cannot add attribute [csimp]: Declaration `{name}` must be public"),
        });
    }
    Ok(())
}
