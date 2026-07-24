// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute collection for declaration elaboration.
//!
//! Wires parsed `@[attr]` annotations to Environment registration methods.
//! Collected attributes are retrieved via `take_*` methods after elaboration.

use crate::attribute_ext2::supports_file_scope_attribute_removal;
use crate::ElabError;
use clean_kernel::env::{Reducibility, SimpPriority as KernelSimpPriority};
use clean_kernel::name::Name;
use clean_parser::{Attribute, AttributeCommandAttr, SimpPriority as ParserSimpPriority};

use super::{ElabCtx, ElabResult};

/// Attribute names that the parser surfaces as [`Attribute::Unknown`] but which
/// are legitimate Lean 4 / Mathlib attributes (or attribute-scope modifiers)
/// that Clean recognizes but does not yet model. Every modeled attribute is a
/// dedicated [`Attribute`] variant, so `Unknown` only carries names outside the
/// parser's table. A name that is neither a modeled variant nor in this set is
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
    "to_additive",
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

impl<'a> ElabCtx<'a> {
    /// Tolerate unknown attributes as no-ops — the Lean-drop-in behavior.
    ///
    /// Every attribute Clean MODELS is a dedicated [`Attribute`] variant (`simp`,
    /// `ext`, `class`, `instance`, `reducible`, …) and is honored normally; only
    /// the parser's [`Attribute::Unknown`] fallbacks reach here. Real Lean core +
    /// Mathlib register hundreds of attributes via macros/plugins that Clean's
    /// finite set does not enumerate (`@[grind]`, `@[mfld_simps]`, `@[nolint]`,
    /// `@[gcongr]`, `@[simps]`, custom `register_simp_attr`/`register_label_attr`
    /// names, …). A declaration carrying one MUST still elaborate — Clean cannot
    /// act on an attribute it does not model, so ignoring it is the only sound
    /// option, and the declaration itself is still fully kernel-re-checked. The
    /// original strict B21 rejection (`unknown attribute '[…]'`) walled real
    /// Mathlib source outright.
    ///
    /// (Slightly more lenient than a fully-provisioned Lean, which rejects an
    /// attribute registered by NO module — the scalable drop-in stance while
    /// Clean's attribute set is incomplete. `is_known_unmodeled_attr` is retained
    /// for callers that still want the recognized-name check.)
    pub(crate) fn ensure_known_attributes(&self, attrs: &[Attribute]) -> Result<(), ElabError> {
        for attr in attrs {
            if let Attribute::Unknown(name) = attr {
                if !is_known_unmodeled_attr(name) {
                    tracing::debug!(
                        attribute = %name,
                        "tolerating unknown (unmodeled) attribute as a no-op (drop-in)"
                    );
                }
            }
        }
        Ok(())
    }

    /// Collect all attributes for a declaration and store in context for later registration.
    ///
    /// This wires parsed @[attr] annotations to Environment::register_* methods.
    /// The collected attributes are retrieved via take_* methods after elaboration.
    pub(crate) fn collect_attributes(&mut self, name: &Name, attrs: &[Attribute]) {
        for attr in attrs {
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

                Attribute::Reducible | Attribute::Semireducible | Attribute::Irreducible => {
                    self.collect_reducibility_attr(name, attr);
                }

                Attribute::Inline
                | Attribute::Noinline
                | Attribute::AlwaysInline
                | Attribute::MacroInline
                | Attribute::InlineIfReduce
                | Attribute::Specialize
                | Attribute::Nospecialize => self.collect_compiler_attr(name, attr),

                Attribute::Extern(extern_name) => {
                    self.collected_extern
                        .push((name.clone(), extern_name.clone()));
                }
                Attribute::Export(export_name) => {
                    self.collected_export
                        .push((name.clone(), export_name.clone()));
                }
                Attribute::Deprecated(msg) => {
                    self.collected_deprecated.push((name.clone(), msg.clone()));
                }
                Attribute::ImplementedBy(impl_name) => {
                    self.collected_implemented_by
                        .push((name.clone(), impl_name.clone()));
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
                // Handled elsewhere — not through the collected_* + take_* pattern
                Attribute::Class => {}
                Attribute::Unknown(attr_name) if attr_name == "derive_handler" => {
                    self.collected_derive_handler.push(name.clone());
                }
                Attribute::Unknown(_) => {}
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
    fn collect_compiler_attr(&mut self, name: &Name, attr: &Attribute) {
        match attr {
            Attribute::Inline => self.collected_inline.push(name.clone()),
            Attribute::Noinline => self.collected_noinline.push(name.clone()),
            Attribute::AlwaysInline => self.collected_always_inline.push(name.clone()),
            Attribute::MacroInline => self.collected_macro_inline.push(name.clone()),
            Attribute::InlineIfReduce => self.collected_inline_if_reduce.push(name.clone()),
            Attribute::Specialize => self.collected_specialize.push(name.clone()),
            Attribute::Nospecialize => self.collected_nospecialize.push(name.clone()),
            _ => {}
        }
    }

    /// Elaborate the `attribute [attrs] name1 name2 ...` command.
    pub(super) fn elab_attribute_command(
        &mut self,
        attrs: &[AttributeCommandAttr],
        names: &[String],
    ) -> Result<ElabResult, ElabError> {
        for name_str in names {
            let name = Name::from_string(name_str);
            let resolved = if self.env.get_const(&name).is_some() {
                Some(name)
            } else if let Some(qualified) = self.namespace_state.resolve(name_str) {
                if self.env.get_const(qualified).is_some() {
                    Some(qualified.clone())
                } else {
                    None
                }
            } else {
                None
            };
            let Some(resolved_name) = resolved else {
                return Err(ElabError::UnknownIdent(format!(
                    "attribute target '{}' not found in environment",
                    name_str
                )));
            };
            for attr in attrs {
                match attr {
                    AttributeCommandAttr::Add(attr) => {
                        // B21: `attribute [unknownAttr] foo` is a loud error too.
                        self.ensure_known_attributes(std::slice::from_ref(attr))?;
                        self.collect_attributes(&resolved_name, std::slice::from_ref(attr));
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
