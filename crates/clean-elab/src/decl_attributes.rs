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

use crate::{
    instances, register_aesop_rule, register_user_derive_handler, ElabCtx, ElabError, FileContext,
};
use clean_kernel::env::{Reducibility, SimpPriority as KernelSimpPriority, TrustedEnvExt};
use clean_parser::AesopAttr;

/// Every attribute an elaboration collected, drained out of its `ElabCtx`.
#[derive(Debug, Default)]
pub(crate) struct CtxAttributes {
    aesop_attrs: Vec<(Name, AesopAttr)>,
    simp_attrs: Vec<(Name, KernelSimpPriority)>,
    reducibility_attrs: Vec<(Name, Reducibility)>,
    extern_attrs: Vec<(Name, String)>,
    export_attrs: Vec<(Name, String)>,
    deprecated_attrs: Vec<(Name, Option<String>)>,
    inline_attrs: Vec<Name>,
    noinline_attrs: Vec<Name>,
    always_inline_attrs: Vec<Name>,
    specialize_attrs: Vec<Name>,
    csimp_attrs: Vec<Name>,
    congr_attrs: Vec<Name>,
    ext_attrs: Vec<Name>,
    refl_attrs: Vec<Name>,
    symm_attrs: Vec<Name>,
    macro_inline_attrs: Vec<Name>,
    inline_if_reduce_attrs: Vec<Name>,
    nospecialize_attrs: Vec<Name>,
    implemented_by_attrs: Vec<(Name, String)>,
    coe_attrs: Vec<Name>,
    match_pattern_attrs: Vec<Name>,
    init_attrs: Vec<Name>,
    default_instance_attrs: Vec<(Name, u32)>,
    instance_attrs: Vec<(Name, u32)>,
    derive_handler_attrs: Vec<Name>,
    attribute_removals: Vec<(Name, String)>,
}

impl CtxAttributes {
    /// Drain every attribute out of `ctx`. Must run BEFORE `ctx` is dropped;
    /// after this the context holds none.
    pub(crate) fn collect(ctx: &mut ElabCtx<'_>) -> Self {
        Self {
            aesop_attrs: ctx.take_aesop_attrs(),
            simp_attrs: ctx.take_simp_attrs(),
            reducibility_attrs: ctx.take_reducibility(),
            extern_attrs: ctx.take_extern(),
            export_attrs: ctx.take_export(),
            deprecated_attrs: ctx.take_deprecated(),
            inline_attrs: ctx.take_inline(),
            noinline_attrs: ctx.take_noinline(),
            always_inline_attrs: ctx.take_always_inline(),
            specialize_attrs: ctx.take_specialize(),
            csimp_attrs: ctx.take_csimp(),
            congr_attrs: ctx.take_congr(),
            ext_attrs: ctx.take_ext(),
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
            derive_handler_attrs: ctx.take_derive_handler(),
            attribute_removals: ctx.take_attribute_removals(),
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
            reducibility_attrs,
            extern_attrs,
            export_attrs,
            deprecated_attrs,
            inline_attrs,
            noinline_attrs,
            always_inline_attrs,
            specialize_attrs,
            csimp_attrs,
            congr_attrs,
            ext_attrs,
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
            derive_handler_attrs,
            attribute_removals,
        } = self;

        // Now register attributes that reference the declaration

        // Register aesop rules
        for (name, attr) in aesop_attrs {
            register_aesop_rule(env, name, &attr);
        }

        // Register simp lemmas
        for (name, priority) in simp_attrs {
            env.register_simp_lemma(name, priority);
        }

        // Apply reducibility attributes
        // These override the default reducibility set at declaration time
        for (name, reducibility) in reducibility_attrs {
            env.set_reducibility(&name, reducibility);
        }

        // Register extern bindings
        for (decl_name, extern_name) in extern_attrs {
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

        // Register csimp lemmas
        for name in csimp_attrs {
            env.register_csimp(name);
        }

        // Register congr lemmas
        for name in congr_attrs {
            env.register_congr(name);
        }

        // Register ext lemmas
        for name in ext_attrs {
            env.register_ext(name);
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

        // Register @[implemented_by] bindings
        for (decl_name, impl_name) in implemented_by_attrs {
            let impl_n = Name::from_string(&impl_name);
            env.register_implemented_by(decl_name, impl_n);
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
        for (name, priority) in instance_attrs {
            if env.is_instance(&name) {
                continue;
            }
            let target_ty = env
                .get_const(&name)
                .map(|info| info.type_.clone())
                .ok_or_else(|| {
                    ElabError::UnknownIdent(format!("attribute [instance] target {name}"))
                })?;
            let mut conclusion = &target_ty;
            while let clean_kernel::ExprKind::Pi(_, _, body) = conclusion.kind() {
                conclusion = body;
            }
            let class_name = instances::extract_class_app(conclusion)
                .map(|(class_name, _)| class_name)
                .filter(|class_name| env.get_class_info(class_name).is_some())
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "attribute [instance]: type of `{name}` does not conclude in a \
                         registered class (got `{conclusion}`)"
                    ),
                })?;
            env.register_instance(clean_kernel::KernelInstanceInfo {
                name,
                class_name,
                priority,
                type_: None,
                value: None,
            });
        }

        // Register @[derive_handler] declarations.
        for name in derive_handler_attrs {
            register_user_derive_handler(env, &name)?;
        }

        for (name, attr_name) in attribute_removals {
            match attr_name.as_str() {
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
