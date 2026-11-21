// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute collection for declaration elaboration.
//!
//! Wires parsed `@[attr]` annotations to Environment registration methods.
//! Collected attributes are retrieved via `take_*` methods after elaboration.

use crate::attribute_ext2::supports_file_scope_attribute_removal;
use crate::declared_here::AttributeSite;
use crate::implemented_by::ImplementedByUse;
use crate::namespace::NamespaceState;
use crate::ElabError;
use clean_kernel::env::{
    GrindAttrKind as KernelGrindAttrKind, Reducibility, SimpPriority as KernelSimpPriority,
};
use clean_kernel::name::Name;
use clean_parser::{Attribute, AttributeCommandAttr, SimpPriority as ParserSimpPriority};

use super::{ElabCtx, ElabResult};

/// Attribute names that the parser surfaces as [`Attribute::Unknown`] but which
/// are legitimate Lean 4 / Mathlib attributes (or attribute-scope modifiers)
/// that Clean recognizes but does not yet model. Modeled attributes use dedicated
/// variants or named handlers in `definition_attrs`. A name that is neither
/// modeled nor in this set is
/// a hard error, matching Lean's `unknown attribute` diagnostic
/// (`src/Lean/Attributes.lean`, gap sweep B21 / p14).
pub(crate) const KNOWN_UNMODELED_ATTRS: &[&str] = &[
    // Inline attribute-scope modifiers: `@[local simp]`, `@[scoped instance]`.
    "local",
    "scoped",
    // Inline attribute removal `@[-simp]` (parser stores the bare name as "-").
    "-",
    // Builtin/compiler attribute without a dedicated parser variant.
    "unbox",
    // Documentation.
    "inherit_doc",
    "builtin_doc",
    // Lake / build.
    "default_target",
    // Metaprogramming & elaboration extensibility.
    "derive_handler",
    "widget_module",
    "elab",
    "term_elab",
    "command_elab",
    "builtin_term_elab",
    "builtin_command_elab",
    "macro",
    "builtin_macro",
    "macro_rules",
    "app_unexpander",
    "app_delab",
    "delab",
    "term_parser",
    "command_parser",
    "tactic_parser",
    "builtin_term_parser",
    "builtin_command_parser",
    "builtin_init",
    // Tactic / simp-proc extensibility.
    "tactic",
    "builtin_tactic",
    "simproc",
    "builtin_simproc",
    "simproc_decl",
    "sevalproc",
    "builtin_sevalproc",
    "unification_hint",
    "elab_as_elim",
    // Common Mathlib norm/mono/cast/lemma-tag attributes.
    "norm_cast",
    "push_cast",
    "coe_decl",
    "mono",
    "gcongr",
    "positivity",
    "fun_prop",
    "measurability",
    "continuity",
    "aesop_unfold",
    // DECLARATION-GENERATING, and tolerated as a no-op only because Clean
    // cannot act on them: each mints a SECOND declaration that the rest of the
    // file then names. Skipping the generation makes those names unknown
    // identifiers hundreds of lines from their cause — `Mathlib/Order/Basic.lean`
    // carries `@[to_dual]` on 116 of its 204 declarations and uses `Eq.ge`,
    // `LE.le.trans'` and `LE.le.trans_lt'`, which nothing else in Mathlib
    // produces. Pinned by `crates/clean-elab/tests/to_dual_attribute_pin_e2e.rs`;
    // read its module doc before moving either name to a fail-closed list,
    // because the refusal is a ratchet re-arm and not a cleanup.
    "to_additive",
    "to_dual",
    "ext_iff",
    "pp_nodot",
    "pp_using_anonymous_constructor",
];

/// Whether `name` is a recognized attribute even though the parser could not
/// map it to a modeled [`Attribute`] variant.
#[must_use]
pub(crate) fn is_known_unmodeled_attr(name: &str) -> bool {
    KNOWN_UNMODELED_ATTRS.contains(&name)
}

/// Map the parser's `@[grind …]` modifier onto the kernel registry's kind.
///
/// One-to-one on the modeled kinds; the unmodeled spellings stay verbatim so a
/// later increment can read what the annotation actually said rather than
/// guessing from the fact that Clean ignored it.
fn grind_kind_to_kernel(kind: &clean_parser::GrindAttrKind) -> KernelGrindAttrKind {
    match kind {
        clean_parser::GrindAttrKind::Infer => KernelGrindAttrKind::Infer,
        clean_parser::GrindAttrKind::EqLhs => KernelGrindAttrKind::EqLhs,
        clean_parser::GrindAttrKind::Forward => KernelGrindAttrKind::Forward,
        clean_parser::GrindAttrKind::Backward => KernelGrindAttrKind::Backward,
        clean_parser::GrindAttrKind::Cases => KernelGrindAttrKind::Cases,
        clean_parser::GrindAttrKind::Ext => KernelGrindAttrKind::Ext,
        clean_parser::GrindAttrKind::Intro => KernelGrindAttrKind::Intro,
        clean_parser::GrindAttrKind::Unmodeled(text) => {
            KernelGrindAttrKind::Unmodeled(text.clone())
        }
    }
}

impl<'a> ElabCtx<'a> {
    /// Refuse an attribute name Clean neither models nor explicitly recognizes.
    ///
    /// Unknown names must not gain semantics by resembling a modeled attribute,
    /// or silently succeed as no-ops. Recognized but unmodeled names retain their
    /// existing policy; this check does not implement their handlers or establish
    /// that an upstream module registered them. Dynamic attribute registration
    /// remains a separate metaprogramming gap.
    pub(crate) fn ensure_known_attributes(&self, attrs: &[Attribute]) -> Result<(), ElabError> {
        for attr in attrs {
            match attr {
                Attribute::Unknown(name) => {
                    if !is_known_unmodeled_attr(name)
                        && !crate::definition_attrs::modeled_name(name)
                    {
                        return Err(ElabError::UnknownAttribute { name: name.clone() });
                    }
                }
                // `local` / `scoped` custom eliminators: Lean's
                // `customEliminatorExt` is a scoped extension, so a local
                // registration applies until the section ends and a scoped
                // one wherever its namespace is open. Clean models only the
                // global kind; dropping the modifier (or the attribute) would
                // run `induction` with a different eliminator than Lean's.
                Attribute::Local(inner) | Attribute::Scoped(inner) => {
                    if let Some(mode) = crate::decl_attributes::inline_mode(inner) {
                        let scope = if matches!(attr, Attribute::Local(_)) {
                            "local"
                        } else {
                            "scoped"
                        };
                        return Err(ElabError::Unsupported {
                            feature: format!(
                                "attribute '{}' must be global, not {scope}",
                                crate::decl_attributes::inline_attribute_name(mode)
                            ),
                        });
                    }
                    if let Some(written) =
                        crate::tactic::custom_eliminator::scoped_eliminator_attr(attr)
                    {
                        return Err(ElabError::Unsupported {
                            feature: format!(
                                "`{written}`: only the global kind of this attribute is modeled"
                            ),
                        });
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub(crate) fn collect_syntactic_defeq(
        &mut self,
        name: &Name,
        value: &clean_parser::SurfaceExpr,
    ) {
        if crate::definition_attrs::bare_rfl(value) {
            self.collected_definition_attrs
                .push(crate::definition_attrs::NamedAttribute {
                    name: name.clone(),
                    attribute: "defeq".into(),
                    site: AttributeSite::Declaration,
                });
        }
    }

    /// Collect all attributes for a declaration and store in context for later registration.
    ///
    /// This wires parsed @[attr] annotations to Environment::register_* methods.
    /// The collected attributes are retrieved via take_* methods after elaboration.
    pub(crate) fn collect_attributes(&mut self, name: &Name, attrs: &[Attribute]) {
        self.collect_attributes_at(name, attrs, AttributeSite::Declaration, &[]);
    }

    /// [`Self::collect_attributes`], saying where the attributes were written
    /// (on the declaration, or by an `attribute [..] name` command) and which
    /// constants registered with the declaration Lean has not added yet when
    /// it applies them (the later members of a `mutual` block).
    pub(crate) fn collect_attributes_at(
        &mut self,
        name: &Name,
        attrs: &[Attribute],
        site: AttributeSite,
        not_yet_declared: &[Name],
    ) {
        for attr in attrs {
            if let Some(class_attr) = crate::class_attribute::ClassAttribute::collect(name, attr) {
                self.collected_class_attrs.push(class_attr);
            }
            match attr {
                Attribute::Aesop(aesop_attr) => {
                    self.collected_aesop_attrs
                        .push((name.clone(), aesop_attr.clone()));
                }
                Attribute::Simp { .. }
                | Attribute::Congr
                | Attribute::Ext
                | Attribute::Refl
                | Attribute::Symm
                | Attribute::Csimp => self.collect_simp_lemma_attr(name, attr),

                // `@[grind]` feeds the GRIND registry and nothing else. It is
                // deliberately not routed through `collect_simp_lemma_attr`:
                // Mathlib tags lemmas `@[grind]` that are deliberately not
                // `@[simp]`, so leaking them into the ambient simp set would
                // change every `simp` in the file (Lean confines `@[grind]`
                // equations to grind's own E-graph).
                Attribute::Grind(kind) => {
                    self.collected_grind
                        .push((name.clone(), grind_kind_to_kernel(kind)));
                }

                Attribute::Reducible | Attribute::Semireducible | Attribute::Irreducible => {
                    self.collect_reducibility_attr(name, attr);
                }

                Attribute::Inline
                | Attribute::Noinline
                | Attribute::AlwaysInline
                | Attribute::MacroInline
                | Attribute::InlineIfReduce
                | Attribute::Specialize
                | Attribute::Nospecialize => self.collect_compiler_attr(name, attr, site, None),

                Attribute::Extern(extern_name) => {
                    self.collected_extern
                        .push((name.clone(), extern_name.clone().into(), site));
                }
                Attribute::ExternMetadata(metadata) => {
                    self.collected_extern
                        .push((name.clone(), metadata.clone(), site));
                }
                Attribute::Export(export_name) => {
                    self.collected_export
                        .push((name.clone(), export_name.clone()));
                }
                Attribute::Deprecated(msg) => {
                    self.collected_deprecated.push((name.clone(), msg.clone()));
                }
                // Captured with the scope Lean resolves it in, and resolved
                // when applied, against the environment the declaration was
                // registered into (`crate::implemented_by`).
                Attribute::ImplementedBy(written) => {
                    let scope = self.implemented_by_scope(site);
                    self.collected_implemented_by.push(ImplementedByUse {
                        decl: name.clone(),
                        written: written.clone(),
                        site,
                        scope,
                        foreign_private: self.foreign_private_decls.clone(),
                        not_yet_declared: not_yet_declared.into(),
                    });
                }
                Attribute::Coe => {
                    self.collected_coe.push(name.clone());
                }
                Attribute::MatchPattern => {
                    self.collected_match_pattern.push(name.clone());
                }
                Attribute::Init => {
                    self.collected_init.push(name.clone());
                }
                Attribute::DefaultInstance { priority } => {
                    // Lean's `@[default_instance]` default priority is 1000
                    // (`default`); an explicit `@[default_instance N]`
                    // overrides it. This priority orders entries in the
                    // DEFAULT-INSTANCE table (open-metavariable defaulting);
                    // it does not change ordinary instance resolution (B99).
                    self.collected_default_instance
                        .push((name.clone(), priority.unwrap_or(1000)));
                }
                // `attribute [instance] foo` / `@[instance N] def foo …`:
                // register the named definition as a type class instance
                // (B06; Lean `src/Lean/Meta/Instances.lean`, `addInstance`).
                // An `instance` DECLARATION carries its priority directly in
                // `SurfaceDecl::Instance { priority }` and never routes here.
                Attribute::InstancePriority(priority) => {
                    self.collected_instance_attrs
                        .push((name.clone(), *priority));
                }
                // Collected above, including scope wrappers, for authoritative
                // target validation before any attribute effects are applied.
                Attribute::Class => {}
                Attribute::Unknown(attr_name)
                    if crate::definition_attrs::modeled_name(attr_name) =>
                {
                    self.collected_definition_attrs
                        .push(crate::definition_attrs::NamedAttribute {
                            name: name.clone(),
                            attribute: attr_name.clone(),
                            site,
                        });
                }
                Attribute::Unknown(attr_name) if attr_name == "derive_handler" => {
                    self.collected_derive_handler.push(name.clone());
                }
                Attribute::Unknown(_) => {}
                // `local simp`: register the lemma and mark it for retirement
                // when the enclosing section/namespace ends (the registrar
                // hands the mark to the `FileContext`). A lemma that is
                // ALREADY a simp lemma is left alone: the local attribute
                // adds nothing, and retiring it at the scope's end would take
                // away the global attribute it had before.
                // Refused by `ensure_known_attributes`; recorded here as well
                // so a declaration path that never ran that check still fails
                // at application (`definition_attrs::apply`) instead of
                // dropping the attribute.
                Attribute::Local(_) | Attribute::Scoped(_)
                    if crate::tactic::custom_eliminator::scoped_eliminator_attr(attr).is_some() =>
                {
                    if let Some(written) =
                        crate::tactic::custom_eliminator::scoped_eliminator_attr(attr)
                    {
                        let named = crate::definition_attrs::NamedAttribute {
                            name: name.clone(),
                            attribute: written,
                            site,
                        };
                        self.collected_definition_attrs.push(named);
                    }
                }
                Attribute::Local(inner) if crate::decl_attributes::inline_mode(inner).is_some() => {
                    self.collect_compiler_attr(name, inner, site, Some("local"));
                }
                Attribute::Scoped(inner)
                    if crate::decl_attributes::inline_mode(inner).is_some() =>
                {
                    self.collect_compiler_attr(name, inner, site, Some("scoped"));
                }
                Attribute::Local(inner) => {
                    if matches!(inner.as_ref(), Attribute::Csimp) {
                        self.collected_local_csimp.push(name.clone());
                    }
                    if matches!(inner.as_ref(), Attribute::Simp { .. })
                        && !self.env.is_simp_lemma(name)
                    {
                        self.collect_simp_lemma_attr(name, inner);
                        self.collected_local_simp.push(name.clone());
                    }
                    // `local instance`: in the current scope's instance state
                    // only (applied at register time, where the scope is).
                    if let Attribute::InstancePriority(priority) = inner.as_ref() {
                        self.collected_scoped_instance_attrs.push((
                            name.clone(),
                            *priority,
                            super::ScopedInstanceAttr::Local,
                        ));
                    }
                }
                // `scoped instance`: an instance wherever the CURRENT
                // namespace is active. Lean refuses it at the root
                // ("scoped attributes must be used inside namespaces"), and
                // so does registration when the namespace is anonymous.
                Attribute::Scoped(inner) => {
                    if matches!(inner.as_ref(), Attribute::Csimp) {
                        self.collected_scoped_csimp.push((
                            name.clone(),
                            self.namespace_state.current_namespace().clone(),
                        ));
                    }
                    if let Attribute::InstancePriority(priority) = inner.as_ref() {
                        self.collected_scoped_instance_attrs.push((
                            name.clone(),
                            *priority,
                            super::ScopedInstanceAttr::Scoped(
                                self.namespace_state.current_namespace().clone(),
                            ),
                        ));
                    }
                }
            }
        }
    }

    /// Collect simp/lemma-family attributes (simp, congr, ext, refl, symm, csimp).
    fn collect_simp_lemma_attr(&mut self, name: &Name, attr: &Attribute) {
        match attr {
            Attribute::Simp { priority } => {
                let kernel_priority = match priority {
                    Some(ParserSimpPriority::Low) => KernelSimpPriority::Custom(500),
                    Some(ParserSimpPriority::Normal) | None => KernelSimpPriority::Default,
                    Some(ParserSimpPriority::High) => KernelSimpPriority::Custom(1500),
                };
                self.collected_simp_attrs
                    .push((name.clone(), kernel_priority));
            }
            Attribute::Congr => self.collected_congr.push(name.clone()),
            Attribute::Ext => self.collected_ext.push(name.clone()),
            Attribute::Refl => self.collected_refl.push(name.clone()),
            Attribute::Symm => self.collected_symm.push(name.clone()),
            Attribute::Csimp => self.collected_csimp.push(name.clone()),
            _ => {}
        }
    }

    /// The scope an `@[implemented_by]` target resolves in: the use's own,
    /// with the namespace pinned Lean opens around the declaration entered
    /// (`Self::decl_site_namespace`: `N` for `def N.d` and `private def N.d`,
    /// nothing for `def _root_.N.d`, a `mutual` block's common prefix). The
    /// command form resolves where it is written.
    fn implemented_by_scope(&self, site: AttributeSite) -> NamespaceState {
        let mut scope = self.namespace_state.clone();
        if site == AttributeSite::Declaration {
            if let Some(opened) = &self.decl_site_namespace {
                if opened != scope.current_namespace() {
                    scope.enter_resolved_namespace(opened.clone());
                }
            }
        }
        scope
    }

    /// Collect reducibility attributes (reducible, semireducible, irreducible).
    fn collect_reducibility_attr(&mut self, name: &Name, attr: &Attribute) {
        let level = match attr {
            Attribute::Reducible => Reducibility::Reducible,
            Attribute::Semireducible => Reducibility::Regular(0),
            Attribute::Irreducible => Reducibility::Irreducible,
            _ => return,
        };
        self.collected_reducibility.push((name.clone(), level));
    }

    /// Collect compiler/inlining attributes (inline, noinline, always_inline, etc.).
    fn collect_compiler_attr(
        &mut self,
        name: &Name,
        attr: &Attribute,
        site: AttributeSite,
        scope: Option<&'static str>,
    ) {
        if let Some(mode) = crate::decl_attributes::inline_mode(attr) {
            self.collected_inline_attributes
                .push(crate::decl_attributes::InlineAttributeUse {
                    name: name.clone(),
                    mode,
                    site,
                    scope,
                });
            return;
        }
        match attr {
            Attribute::Specialize => self.collected_specialize.push(name.clone()),
            Attribute::Nospecialize => self.collected_nospecialize.push(name.clone()),
            _ => {}
        }
    }

    /// Elaborate the `attribute [attrs] name1 name2 ...` command.
    pub(super) fn elab_attribute_command(
        &mut self,
        attrs: &[AttributeCommandAttr],
        names: &[clean_parser::SurfaceName],
    ) -> Result<ElabResult, ElabError> {
        for name_str in names {
            // Resolved in THIS module's scope, Lean's way (namespace first,
            // then root/`open`/alias together, ambiguity refused): see
            // `resolve_global_const_no_overload`.
            let resolved_name = match crate::name_resolution::resolve_global_const_no_overload(
                name_str,
                &self.namespace_state,
                self.env,
                &self.foreign_private_decls,
            ) {
                Ok(resolved) => resolved,
                Err(crate::name_resolution::GlobalConstResolution::Unknown) => {
                    return Err(ElabError::UnknownIdent(format!(
                        "attribute target '{}' not found in environment",
                        name_str
                    )));
                }
                Err(crate::name_resolution::GlobalConstResolution::Ambiguous(candidates)) => {
                    return Err(ElabError::UnknownIdent(format!(
                        "ambiguous attribute target '{}', possible interpretations: [{}]",
                        name_str,
                        candidates
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )));
                }
            };
            for attr in attrs {
                match attr {
                    AttributeCommandAttr::Add(attr) => {
                        // B21: `attribute [unknownAttr] foo` is a loud error too.
                        self.ensure_known_attributes(std::slice::from_ref(attr))?;
                        // Class attributes follow the same register-time
                        // validation as declaration-form attributes.

                        self.collect_attributes_at(
                            &resolved_name,
                            std::slice::from_ref(attr),
                            AttributeSite::AttributeCommand,
                            &[],
                        );
                    }
                    AttributeCommandAttr::Remove(attr_name) => {
                        if !supports_file_scope_attribute_removal(attr_name) {
                            return Err(ElabError::Unsupported {
                                feature: format!(
                                    "attribute removal for '[-{attr_name}]' is not supported"
                                ),
                            });
                        }
                        self.collected_attribute_removals
                            .push((resolved_name.clone(), attr_name.clone()));
                    }
                }
            }
        }
        Ok(ElabResult::Skipped)
    }
}
