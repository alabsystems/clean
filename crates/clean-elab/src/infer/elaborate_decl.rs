// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration elaboration dispatch for the type inference context
//!
//! This module contains the top-level dispatch (`elab_decl_inner`) that routes
//! each `SurfaceDecl` variant to its elaboration logic:
//! - `def`/`theorem`/`axiom`/`opaque` value declarations -> `elab_decl_value.rs`
//! - `inductive`/`structure`/`class`/`instance` type declarations
//! - macro registrations, commands, and other declarations
//!
//! Attribute collection is in `elab_attributes.rs`.
//! Level canonicalization is in `elab_canonicalize.rs`.
//!
//! Extracted from mod.rs to reduce file size (#760).

use crate::macro_integration::quotation_category_head;
use crate::tactic::{TacticArgPattern, TacticEntry, TacticError};
use crate::term_info::TermInfoCapture;
use crate::ElabError;
use clean_parser::{
    DoElem, MacroArm, SurfaceArg, SurfaceDecl, SurfaceExpr, SurfaceLit, SurfaceName, SurfaceTactic,
    SurfaceTacticLocation, SyntaxPatternItem,
};
use std::sync::Arc;

use super::{ElabCtx, ElabResult};

impl<'a> ElabCtx<'a> {
    pub(super) fn qualify_name(&self, name: &SurfaceName) -> SurfaceName {
        name.qualify_under(&self.namespace_prefix)
    }

    /// The kernel name a declaration with these modifiers registers under:
    /// its namespace-qualified name, or — for a `private` declaration of a
    /// kind that is mangled ([`mangles_private_names`]) in a module the driver
    /// named — Lean's `_private.<module>.0.<name>` (`applyVisibility`,
    /// `Lean/Elab/DeclModifiers.lean:150-166`; G21).
    pub(crate) fn kernel_decl_name(
        &self,
        name: &SurfaceName,
        modifiers: &clean_parser::DeclModifiers,
        kind: PrivateNameKind,
    ) -> clean_kernel::Name {
        self.kernel_decl_name_for(name, private_kind_of(modifiers, kind))
    }

    /// [`Self::kernel_decl_name`] for a declaration whose privacy is already
    /// read off its modifiers: `Some(kind)` for a `private` one.
    pub(crate) fn kernel_decl_name_for(
        &self,
        name: &SurfaceName,
        private_kind: Option<PrivateNameKind>,
    ) -> clean_kernel::Name {
        self.kernel_name_of_qualified(self.qualify_name(name).into_name(), private_kind)
    }

    /// [`Self::kernel_decl_name_for`] over a name that is already
    /// namespace-qualified (a named instance's, or an anonymous instance's
    /// freshened `inst…`).
    pub(crate) fn kernel_name_of_qualified(
        &self,
        qualified: clean_kernel::Name,
        private_kind: Option<PrivateNameKind>,
    ) -> clean_kernel::Name {
        if private_kind.is_some_and(mangles_private_names) {
            if let Some(mangled) = self.namespace_state.private_name(&qualified) {
                return mangled;
            }
        }
        qualified
    }

    /// The name an inductive family (`inductive` / `structure` / `class`, a
    /// `mutual` inductive member) is elaborated under: the namespace-qualified
    /// surface name, or — for a `private` one in a module the driver named —
    /// Lean's `_private.<module>.0.<name>` (G21 B3). Every name the family
    /// derives from it (constructors, recursors, `casesOn`, projections,
    /// `mk.injEq`) then carries the prefix, as Lean's do
    /// (`_private.Pkg.A.0.Foo.S.mk`, measured on Lean 4.8.0).
    pub(crate) fn family_decl_name(
        &self,
        name: &SurfaceName,
        modifiers: &clean_parser::DeclModifiers,
    ) -> SurfaceName {
        let qualified = self.qualify_name(name);
        let kernel = self.kernel_name_of_qualified(
            qualified.name().clone(),
            private_kind_of(modifiers, PrivateNameKind::Family),
        );
        if kernel == *qualified.name() {
            qualified
        } else {
            SurfaceName::from_name(kernel)
        }
    }

    /// Lean's `isPrivateNameFromImportedModule env name` in a module the
    /// driver named: `name` is private and another module minted it. Always
    /// `false` without a named module, whose private names are plain.
    pub(crate) fn is_imported_private_name(&self, name: &clean_kernel::Name) -> bool {
        self.namespace_state.main_module().is_some_and(|module| {
            crate::private_names::is_private_name_from_imported_module(Some(module), name)
        })
    }

    /// Whether the environment declares `name` in any form Lean's
    /// `env.contains` sees (a constant, inductive, constructor or recursor).
    fn declares(&self, name: &clean_kernel::Name) -> bool {
        self.env.get_const(name).is_some()
            || self.env.get_inductive(name).is_some()
            || self.env.get_constructor(name).is_some()
            || self.env.get_recursor(name).is_some()
    }

    /// Lean 4.8.0's `checkNotAlreadyDeclared` (`Lean/Elab/DeclModifiers.lean:
    /// 17-40`) for the cases a `private` name is in, in a module the driver
    /// named. Mangling separates a private declaration from a public one of
    /// the same user-facing name in the kernel, so without this rule `private
    /// theorem x` then `theorem x`, `theorem y` then `private theorem y`, and
    /// a namespaced `private theorem N.w` then `theorem N.w` would all be
    /// accepted where Lean refuses them (measured 2026-10-08, ThE–ThH). A
    /// public name that exists is left to the kernel's duplicate check, as
    /// before.
    fn check_private_not_already_declared(&self, decl: &SurfaceDecl) -> Result<(), ElabError> {
        if self.namespace_state.main_module().is_none() {
            return Ok(());
        }
        let (name, modifiers, kind) = match decl {
            SurfaceDecl::Mutual { decls, .. } => {
                for inner in decls {
                    self.check_private_not_already_declared(inner)?;
                }
                return Ok(());
            }
            SurfaceDecl::Theorem {
                name, modifiers, ..
            } => (name, modifiers, PrivateNameKind::Theorem),
            SurfaceDecl::Axiom {
                name, modifiers, ..
            } => (name, modifiers, PrivateNameKind::Axiom),
            SurfaceDecl::Def {
                name, modifiers, ..
            }
            | SurfaceDecl::Opaque {
                name, modifiers, ..
            }
            | SurfaceDecl::Instance {
                name: Some(name),
                modifiers,
                ..
            } => (name, modifiers, PrivateNameKind::Definition),
            SurfaceDecl::Inductive {
                name, modifiers, ..
            }
            | SurfaceDecl::Structure {
                name, modifiers, ..
            }
            | SurfaceDecl::Class {
                name, modifiers, ..
            } => (name, modifiers, PrivateNameKind::Family),
            SurfaceDecl::Coinductive {
                name, modifiers, ..
            } => (name, modifiers, PrivateNameKind::NotYetMangled),
            _ => return Ok(()),
        };
        let user = self.qualify_name(name).into_name();
        let decl_name = self.kernel_decl_name(name, modifiers, kind);
        self.check_private_name_free(&user, &decl_name)
    }

    /// The rules of [`Self::check_private_not_already_declared`] for one
    /// declaration whose namespace-qualified user-facing name is `user` and
    /// whose kernel name is `decl_name` (equal to `user` unless mangled). An
    /// anonymous instance, whose name is minted only once its class is
    /// elaborated, calls this directly. A no-op without a named module.
    pub(crate) fn check_private_name_free(
        &self,
        user: &clean_kernel::Name,
        decl_name: &clean_kernel::Name,
    ) -> Result<(), ElabError> {
        if self.namespace_state.main_module().is_none() {
            return Ok(());
        }
        let shown = |n: &clean_kernel::Name| crate::private_names::user_facing_name(n).to_string();
        let refuse = |message: String| Err(ElabError::PrivateNameAlreadyDeclared { message });
        let is_mangled = crate::private_names::is_private_name(decl_name);
        if is_mangled && self.declares(decl_name) {
            return refuse(format!(
                "private declaration '{}' has already been declared",
                shown(decl_name)
            ));
        }
        if !is_mangled {
            if let Some(private) = self.namespace_state.private_name(decl_name) {
                if self.declares(&private) {
                    return refuse(format!(
                        "a private declaration '{}' has already been declared",
                        shown(decl_name)
                    ));
                }
            }
        }
        // `private theorem y` over an existing `y`. A plain-named `private`
        // declaration of ANOTHER module (a kind not mangled yet) is not this
        // module's and does not collide (Lean mangles it too); one of this
        // module is a private declaration of the same name.
        if is_mangled && self.declares(user) {
            if !self.env.is_private(user) {
                return refuse(format!(
                    "a non-private declaration '{}' has already been declared",
                    shown(user)
                ));
            }
            if !self.foreign_private_decls.contains(user) {
                return refuse(format!(
                    "private declaration '{}' has already been declared",
                    shown(user)
                ));
            }
        }
        Ok(())
    }

    /// Activate the scoped notations of the namespaces named by an `open` /
    /// `open scoped` command (Lean `elabOpen`: only the SIMPLE forms activate
    /// scoped declarations — `open Foo (x)` / `hiding` / `renaming` import
    /// names only). Candidate resolutions are the path as written plus each
    /// current-namespace prefix qualification (mirroring Lean's
    /// `resolveNamespace` candidates); activating a namespace that declared
    /// no scoped notation is a no-op.
    fn activate_open_scoped_notation(&mut self, paths: &[clean_parser::OpenPath]) {
        for path in paths {
            if !(path.names.is_empty() && path.hiding.is_empty() && path.renaming.is_empty()) {
                continue;
            }
            let ns = path.path.clone();
            if ns.is_anonymous() {
                continue;
            }
            let mut candidates = vec![ns.qualify_under(&SurfaceName::default())];
            let mut prefix = self.namespace_prefix.clone();
            while !prefix.is_anonymous() {
                candidates.push(ns.qualify_under(&prefix));
                prefix = prefix.parent();
            }
            for candidate in candidates {
                self.macro_ctx.activate_scoped_namespace(&candidate);
            }
        }
    }

    fn elab_namespace(
        &mut self,
        name: &SurfaceName,
        decls: &[SurfaceDecl],
    ) -> Result<ElabResult, ElabError> {
        let prev_prefix = std::mem::take(&mut self.namespace_prefix);
        self.namespace_prefix = name.qualify_under(&prev_prefix);
        // Update NamespaceState so that name resolution inside the block
        // can qualify bare identifiers with the current namespace prefix.
        // Without this, elab_ident cannot resolve `Ty` as `TMir.Ty` inside
        // `namespace TMir { ... }`. Fixes #3410 (UnknownFVar in namespace).
        self.namespace_state
            .enter_resolved_namespace(self.namespace_prefix.name().clone());
        // A namespace block is an alias-scope boundary (Lean pushes a Scope per
        // `namespace`; `end` pops it, discarding its `open` decls —
        // `Lean/Elab/BuiltinCommand.lean` `elabNamespace`/`elabEnd`). Without
        // this, an `open` inside the block leaked file-wide (gap sweep B13).
        // `export` aliases intentionally SURVIVE the pop: they are inserted
        // scope-immune (`insert_alias_unscoped`), mirroring Lean's permanent
        // env alias table.
        self.namespace_state.push_scope();
        // Scoped-notation gate: the block's namespace (and its ancestors)
        // implicitly activate their `scoped notation`s while current; `open`
        // activations made inside the block die at `end` with the frame.
        self.macro_ctx.push_scoped_activation_frame();
        self.macro_ctx.set_current_namespace(&self.namespace_prefix);
        // Namespace-scoped `variable` binders: Lean scopes `variable` to the
        // enclosing namespace exactly as to a section (`Mathlib/Data/Subtype`:
        // `namespace Subtype` + `variable {p q : α → Prop}` + decls USING p).
        // Mirror `elab_section`'s discipline — accumulate Variable binders,
        // prepend the USED closure to each subsequent declaration, truncate
        // on every exit path so the variables die with the namespace.
        let saved_section_binders = self.section_binder_stack.len();
        let saved_included = self.included_var_stack.clone();
        let mut results = Vec::new();
        for inner in decls {
            let processed = if matches!(inner, SurfaceDecl::Variable { .. }) {
                // Chained `variable` lines: hand validation the accumulated
                // telescope (the preprocess Variable arm prepends the
                // context's current variables; the throwaway FileContext's
                // accumulation is discarded).
                if self.section_binder_stack.is_empty() {
                    None
                } else {
                    let mut fc = crate::FileContext::new();
                    fc.add_variables(&self.section_binder_stack.clone());
                    Some(crate::preprocess::preprocess_decl_with_context(
                        inner, &mut fc,
                    ))
                }
            } else {
                self.prepend_section_binders(inner)
            };
            let result = self.elab_decl(processed.as_ref().unwrap_or(inner));
            // A pruning armed for `inner` must not reach the next declaration.
            let _ = self.take_section_prune_outcome();
            let result = match result {
                Ok(r) => r,
                Err(e) => {
                    self.section_binder_stack.truncate(saved_section_binders);
                    self.included_var_stack = saved_included;
                    self.namespace_state.pop_scope();
                    self.namespace_state.exit_namespace();
                    self.namespace_prefix = prev_prefix;
                    self.macro_ctx.pop_scoped_activation_frame();
                    self.macro_ctx.set_current_namespace(&self.namespace_prefix);
                    return Err(e);
                }
            };
            if let SurfaceDecl::Variable { binders, .. } = inner {
                self.section_binder_stack.extend(
                    binders
                        .iter()
                        .map(crate::section_scope::section_variable_binder),
                );
            }
            apply_include_omit(&mut self.included_var_stack, inner);
            if !matches!(result, ElabResult::Skipped) {
                results.push(result);
            }
        }
        self.section_binder_stack.truncate(saved_section_binders);
        self.included_var_stack = saved_included;
        self.namespace_state.pop_scope();
        self.namespace_state.exit_namespace();
        self.namespace_prefix = prev_prefix;
        self.macro_ctx.pop_scoped_activation_frame();
        self.macro_ctx.set_current_namespace(&self.namespace_prefix);
        Ok(ElabResult::Multiple(results))
    }

    /// `decl` with the section variables of this `ElabCtx`-level block
    /// prepended — the same rewrite `preprocess_decl_with_context` performs on
    /// the file-level path — or `None` when it receives none. When the
    /// selection could not scan `decl`, the pruning of the unused ones is
    /// armed for its elaboration (`section_prune`).
    fn prepend_section_binders(&mut self, decl: &SurfaceDecl) -> Option<SurfaceDecl> {
        let selection = crate::section_var_selection::select_section_binders(
            &self.section_binder_stack,
            decl,
            Some(&self.macro_ctx),
            &self.included_var_stack,
        );
        if selection.binders.is_empty() {
            return None;
        }
        if let Some(request) = selection.prune {
            self.set_section_prune_request(request);
        }
        // The rewrite re-selects over `selection.binders`, so it must see the
        // same `include`s or a theorem would drop the variables they force.
        let mut fc = crate::FileContext::new();
        fc.add_variables(&selection.binders);
        fc.include_variables(&self.included_var_stack);
        Some(crate::preprocess::preprocess_decl_with_context(
            decl, &mut fc,
        ))
    }

    fn elab_section(&mut self, decls: &[SurfaceDecl]) -> Result<ElabResult, ElabError> {
        self.namespace_state.push_scope();
        let saved_options = self.local_options.clone();
        let saved_macro_ctx = self.macro_ctx.clone();
        // Section-scoped `variable` binders (B03). Lean brings section
        // variables into scope as REAL binders on the declarations that USE
        // them (`Lean/Elab/Command.lean` `elabVariable`; usage-based
        // inclusion in `Lean/Elab/MutualDef.lean`). Before B03 these
        // references only elaborated by falling through to body
        // auto-implicits, which B03 removes (auto-bound implicits are
        // header-only), so the binders must be made real here: accumulate
        // binders from `variable` decls in this block and prepend the USED
        // subset to each subsequent value declaration via the same
        // `preprocess` rewrite the top-level marker form uses. The stack is
        // truncated on exit so the variables go out of scope with the
        // section; nested sections inherit the outer stack through recursion.
        let saved_section_binders = self.section_binder_stack.len();
        let saved_included = self.included_var_stack.clone();
        // SOUNDNESS (#section-drops-all-but-last): this used to keep only `last_result`, so in a
        // section with several declarations ONLY THE LAST was returned — and since registration
        // happens on the returned `ElabResult`, every non-final declaration silently vanished
        // (elaborated but never registered; no error). Collect EVERY non-skipped result into
        // `ElabResult::Multiple`, which `register_elab_result` registers element-by-element —
        // exactly how `elab_namespace` (above) already reports its inner declarations.
        let mut results: Vec<ElabResult> = Vec::new();
        for decl in decls {
            let processed = self.prepend_section_binders(decl);
            let result = self.elab_decl_inner(processed.as_ref().unwrap_or(decl));
            // A pruning armed for `decl` must not reach the next declaration.
            let _ = self.take_section_prune_outcome();
            match result {
                Ok(ElabResult::Skipped) => {}
                Ok(r) => results.push(r),
                Err(e) => {
                    // SOUNDNESS (#section-drops-all-but-last / namespace-ABORT
                    // lineage): this used to `return Err(e)`, aborting the section
                    // on the FIRST failing sibling and dropping every good one.
                    // Record the failure as an explicit `Failed` leaf and CONTINUE
                    // — the leaf is counted and reported (namespace-qualified name
                    // + original `decl` for span accuracy) but NOT registered (it
                    // already failed). Nested-section paths reaching `elab_section`
                    // directly are now resilient too; the top-level file section is
                    // intercepted earlier by the lib.rs Section arm. State is
                    // restored once after the loop, so no per-failure cleanup here.
                    let short = crate::preprocess_ext::decl_name(decl)
                        .cloned()
                        .unwrap_or_default();
                    results.push(ElabResult::Failed {
                        name: self.qualify_name(&short).to_string(),
                        decl: Box::new(decl.clone()),
                        error: Box::new(e),
                    });
                }
            }
            if let SurfaceDecl::Variable { binders, .. } = decl {
                self.section_binder_stack.extend(
                    binders
                        .iter()
                        .map(crate::section_scope::section_variable_binder),
                );
            }
            apply_include_omit(&mut self.included_var_stack, decl);
        }
        self.local_options = saved_options;
        self.macro_ctx = saved_macro_ctx;
        self.section_binder_stack.truncate(saved_section_binders);
        self.included_var_stack = saved_included;
        self.namespace_state.pop_scope();
        // Preserve the historical shape for degenerate sections (empty / commands-only → Skipped;
        // exactly one declaration → that declaration) so downstream matchers keep working; the
        // fix is that MULTIPLE declarations now ALL surface (and thus all register).
        Ok(if results.len() > 1 {
            ElabResult::Multiple(results)
        } else {
            results.pop().unwrap_or(ElabResult::Skipped)
        })
    }

    fn elab_tactic_elab_decl(
        &mut self,
        pattern: &[SyntaxPatternItem],
        category: &str,
        body: &SurfaceExpr,
    ) -> Result<ElabResult, ElabError> {
        self.elab_tactic_decl(pattern, category, body, None)
    }

    /// [`Self::elab_tactic_elab_decl`], or — with `template` — the body of a
    /// tactic MACRO: a quotation over the operand variables `template.vars`,
    /// which every use INSTANTIATES (`clean_parser::instantiate_tactic_template`)
    /// with the call's arguments, as Lean expands the macro, hygienically
    /// unless `template.hygienic` is false.
    fn elab_tactic_decl(
        &mut self,
        pattern: &[SyntaxPatternItem],
        category: &str,
        body: &SurfaceExpr,
        template: Option<super::user_tactic::TacticTemplate>,
    ) -> Result<ElabResult, ElabError> {
        // Phase 5: term-category elaborators. A `elab "kw" e:term : term => body`
        // declaration makes `kw e` in term position elaborate to the body with
        // the call-site argument substituted in. Registration mirrors the tactic
        // path's tractable core (leading keyword + flat bound variables); the
        // recognition+routing happens in `ElabCtx::elaborate`.
        if category == "term" {
            return self.elab_term_elab_decl(pattern, body);
        }
        if category != "tactic" {
            return Ok(ElabResult::Skipped);
        }
        // Match the surface pattern: a leading string literal (the tactic
        // keyword) optionally followed by bound term/ident antiquotations.
        // Patterns using repetition, optional groups, bare category refs, or
        // interspersed literals are deferred (return Skipped) — they need an
        // ElabRuleRegistry that can re-run the parser with the custom grammar.
        let Some(parsed) = parse_tactic_elab_pattern(pattern) else {
            return Ok(ElabResult::Skipped);
        };
        let TacticElabPattern {
            name,
            bound_vars,
            repetition,
        } = parsed;
        let arg_pattern = arg_pattern_for_bound_vars(&bound_vars, repetition.as_ref());
        let bound_names: Vec<SurfaceName> = bound_vars.into_iter().map(|v| v.name).collect();
        let repetition_name = repetition.map(|r| r.name);

        // A simple registry entry is always recorded so the parser learns the
        // tactic keyword and its argument pattern (`tactic_patterns()`). For an
        // executable body (a `by` tactic block) the simple handler is never the
        // one that fires — the compound handler registered below takes priority
        // in `eval_tactic` — but we still give it an honest error in case it is
        // reached directly.
        self.tactic_registry.register(TacticEntry {
            name: name.clone(),
            pattern: arg_pattern,
            handler: simple_unsupported_handler(name.clone(), bound_names.clone(), body),
        });

        // Phase 1: if the body parsed as a `by` tactic block of supported tactic
        // shapes, register a compound handler that binds the call-site arguments
        // to the pattern variables, substitutes them into the body tactic AST,
        // and delegates to the existing tactic evaluator. Soundness: delegation
        // only — no new way to close a goal. Deferred body shapes (do-notation
        // monadic bodies, bodies that elaborate brand-new expressions at tactic
        // runtime, ...) keep the honest-error simple handler registered above.
        //
        // Phase 6: when the pattern has a trailing repetition variable
        // (`xs:ident*` / `xs:term*`), register the VARIADIC handler instead. It
        // binds the fixed prefix args 1:1, collects the remaining call-site args
        // into a list for the repetition var, and expands each body tactic that
        // mentions the repetition var once per list element. Soundness is
        // unchanged: the expanded sequence is still delegated to the existing
        // tactic evaluator (no new way to close a goal).
        if let SurfaceExpr::ByTactic(_, tactics) = body {
            if super::user_tactic::is_executable_tactic_body(tactics) {
                // A macro's operands are its template's operand variables.
                let (template, bound_names, repetition_name) = match template {
                    Some(template) => {
                        let rep = repetition_name
                            .as_ref()
                            .and_then(|_| template.vars.last().cloned());
                        let fixed = match rep {
                            Some(_) => template.vars[..template.vars.len() - 1].to_vec(),
                            None => template.vars.clone(),
                        };
                        (Some(template.hygienic), fixed, rep)
                    }
                    None => (None, bound_names, repetition_name),
                };
                let handler = match (template, repetition_name) {
                    (Some(hygienic), Some(rep_name)) => {
                        super::user_tactic::build_variadic_tactic_macro_handler(
                            name,
                            bound_names,
                            rep_name,
                            tactics.clone(),
                            hygienic,
                        )
                    }
                    (Some(hygienic), None) => super::user_tactic::build_tactic_macro_handler(
                        name,
                        bound_names,
                        tactics.clone(),
                        hygienic,
                    ),
                    (None, Some(rep_name)) => super::user_tactic::build_variadic_tactic_handler(
                        name,
                        bound_names,
                        rep_name,
                        tactics.clone(),
                    ),
                    (None, None) => super::user_tactic::build_user_tactic_handler(
                        name,
                        bound_names,
                        tactics.clone(),
                    ),
                };
                self.tactic_registry.register_compound(handler);
            }
        }
        Ok(ElabResult::Skipped)
    }

    /// Tactic-position `macro` command: `macro "kw" … : tactic => `(tactic| …)`.
    ///
    /// The Syntax-level macro expander cannot fire at tactic position (`by`
    /// blocks cross the surface↔Syntax bridge as opaque nodes — see
    /// `macro_integration::to_syntax`), so a tactic-category macro whose RHS
    /// is a `(tactic| …)` quotation registers through the SAME
    /// substitute-and-delegate bridge as `elab … : tactic` (`user_tactic`):
    /// the quotation body is parsed ONCE here into a `by` tactic sequence
    /// (pattern antiquotation references `$x` rewritten to their bound names)
    /// and handed to [`Self::elab_tactic_elab_decl`], whose compound handler
    /// binds call-site args and delegates to the existing tactic evaluator.
    /// Soundness: delegation only — no new way to close a goal; every produced
    /// proof still passes `verify_tactic_proof`/`add_decl`.
    ///
    /// Returns `Ok(None)` for shapes this route does not own (a non-tactic /
    /// non-conv category, or a tactic-category RHS that is not a
    /// category-headed quotation): the caller falls through to the
    /// Syntax-level path unchanged. A conv-category macro is routed to
    /// [`Self::try_register_conv_macro`], which owns it end-to-end. Shapes
    /// this route DOES own reject loudly when unsupported (a `conv` head on a
    /// TACTIC-category macro, an antiquotation the pattern does not bind, a
    /// body the tactic grammar cannot parse) — never a silent registration
    /// whose use site could mis-expand.
    fn try_register_tactic_macro(
        &mut self,
        pattern: &[SyntaxPatternItem],
        category: &str,
        expansion: &SurfaceExpr,
        site: clean_parser::TemplateSiteId,
    ) -> Result<Option<ElabResult>, ElabError> {
        if category == "conv" {
            // Conv-position macros register through the conv bridge — the same
            // substitute-and-delegate architecture as the tactic route below,
            // delegating into the conv body sequencer (`run_conv_body`). The
            // route OWNS the whole category: unsupported shapes reject loudly
            // (the Syntax-level expander can never fire at conv position, so
            // falling through would register a silently-dead macro).
            return self
                .try_register_conv_macro(pattern, expansion, site)
                .map(Some);
        }
        if category != "tactic" {
            return Ok(None);
        }
        let SurfaceExpr::SyntaxQuote(_, content) = expansion else {
            return Ok(None);
        };
        let Some((head, body)) = quotation_category_head(content) else {
            return Ok(None);
        };
        match head {
            "tactic" => {}
            "conv" => {
                return Err(ElabError::MacroError(
                    "a tactic macro's expansion must be a `(tactic| …)` quotation, got \
                     `(conv| …)` — declare the macro `: conv` to expand at conv position"
                        .to_string(),
                ));
            }
            other => {
                return Err(ElabError::MacroError(format!(
                    "a tactic macro's expansion must be a `(tactic| …)` quotation, got \
                     `({other}| …)`"
                )));
            }
        }
        let bound: Vec<&SurfaceName> = pattern
            .iter()
            .filter_map(|item| match item {
                SyntaxPatternItem::Variable { name, .. } => Some(name),
                _ => None,
            })
            .collect();
        // `$x` is the operand; a bare `x` of the template is the template's
        // own identifier (hygienic, resolved where the macro is declared).
        // So `$x` is spelled `«$x»`, an identifier distinct from every other
        // name the quotation writes, and the template is walked over those.
        let Some(body) = rewrite_tactic_antiquots(body, &bound) else {
            return Err(ElabError::MacroError(format!(
                "tactic macro expansion `(tactic| {body})` uses an antiquotation the \
                 pattern does not bind"
            )));
        };
        let vars: Vec<SurfaceName> = bound
            .iter()
            .map(|name| tactic_operand_variable(name))
            .collect();
        let patterns = self.tactic_registry.tactic_patterns();
        let by_expr = clean_parser::parse_expr_with_tactics(&format!("by {body}"), &patterns)
            .map_err(|e| {
                ElabError::MacroError(format!(
                    "tactic macro expansion `(tactic| {body})` does not parse as a tactic \
                     sequence: {e}"
                ))
            })?;
        if !matches!(by_expr, SurfaceExpr::ByTactic(..)) {
            return Err(ElabError::MacroError(format!(
                "tactic macro expansion `(tactic| {body})` did not produce a tactic block"
            )));
        }
        // The template's free names resolve HERE, as for a term macro: a
        // tactic macro declared under `open A` reads `A`'s names at every use
        // (Lean pre-resolves the quotation's identifiers), and no binder of
        // the template captures an operand's identifier. Under `set_option
        // hygiene false` the template is the bare substitution.
        let hygienic = self.templates_hygienic();
        let by_expr = if hygienic {
            self.record_template_site_resolutions(site, &vars, &by_expr)?;
            self.macro_ctx
                .mark_template(&by_expr, &vars, site)
                .map_err(|refusal| {
                    ElabError::MacroError(format!("template refused: {}", refusal.reason()))
                })?
        } else {
            by_expr
        };
        self.elab_tactic_decl(
            pattern,
            "tactic",
            &by_expr,
            Some(super::user_tactic::TacticTemplate { vars, hygienic }),
        )
        .map(Some)
    }

    /// One tactic- or conv-position `macro_rules` arm:
    /// `` macro_rules | `(tactic| kw $a …) => `(tactic| …) `` or
    /// `` macro_rules | `(conv| kw $a …) => `(conv| …) ``.
    ///
    /// Returns `Ok(false)` for arms this route does not own (no recognized
    /// category head, or a term/command head): those stay on the Syntax-level
    /// path byte-for-byte. A tactic- or conv-headed arm IS owned: it either
    /// registers through the matching bridge or rejects loudly (fail closed),
    /// because the Syntax-level registration can never fire at tactic/conv
    /// position and would leave a silently-dead arm.
    fn try_register_tactic_macro_rules_arm(
        &mut self,
        arm: &MacroArm,
        site: clean_parser::TemplateSiteId,
    ) -> Result<bool, ElabError> {
        let SurfaceExpr::SyntaxQuote(_, content) = arm.pattern.as_ref() else {
            return Ok(false);
        };
        let Some((head, pat_body)) = quotation_category_head(content) else {
            return Ok(false);
        };
        let items = match head {
            "tactic" | "conv" => macro_rules_arm_pattern_items(pat_body, head)?,
            _ => return Ok(false),
        };
        if head == "conv" {
            // Conv-headed arm: the conv bridge owns it end-to-end (registers
            // or rejects loudly — see `try_register_conv_macro`).
            self.try_register_conv_macro(&items, arm.expansion.as_ref(), site)?;
            return Ok(true);
        }
        // The expansion side reuses the macro-command route (tactic-head
        // check, antiquotation rewrite, body parse, bridge registration).
        match self.try_register_tactic_macro(&items, "tactic", arm.expansion.as_ref(), site)? {
            Some(_) => Ok(true),
            None => Err(ElabError::MacroError(
                "tactic macro_rules expansion must be a `(tactic| …)` quotation (fail closed)"
                    .to_string(),
            )),
        }
    }

    /// Conv-position `macro` command: `macro "kw" … : conv => `(conv| …)`
    /// (also reached by conv-headed `macro_rules` arms via
    /// [`Self::try_register_tactic_macro_rules_arm`]).
    ///
    /// Registers through the conv substitute-and-delegate bridge
    /// (`infer::user_conv`): the quotation body is parsed ONCE here into a
    /// conv tactic script (pattern antiquotation references `$x` rewritten to
    /// their bound names) and a compound handler is registered that binds the
    /// call-site args, substitutes them into the script, and delegates to the
    /// conv body sequencer (`run_conv_body`). The handler refuses to run
    /// outside a conv body (`ProofState::in_conv_body`). Soundness: delegation
    /// only — the conv boundary (`eval_conv_goal`/`eval_conv_hyps`) still
    /// rebuilds and kernel-checks the whole-target equality exactly as for an
    /// inline conv script; the macro adds no way to change a focus or close a
    /// goal.
    ///
    /// This route OWNS the entire conv category: every unsupported shape is a
    /// loud rejection (fail closed), never a fall-through to the Syntax-level
    /// registration (which can never fire at conv position — the macro would
    /// be silently dead). Rejected shapes: a non-`(conv| …)` expansion, an
    /// intractable pattern, repetition/optional binders, an antiquotation the
    /// pattern does not bind, an unparseable script, a keyword colliding with
    /// a registered tactic (the registry is category-flat), and an
    /// argument-taking macro whose script contains tactics substitution
    /// cannot be shown to reach (`user_conv::substitution_reaches`).
    fn try_register_conv_macro(
        &mut self,
        pattern: &[SyntaxPatternItem],
        expansion: &SurfaceExpr,
        site: clean_parser::TemplateSiteId,
    ) -> Result<ElabResult, ElabError> {
        let SurfaceExpr::SyntaxQuote(_, content) = expansion else {
            return Err(ElabError::MacroError(
                "a conv macro's expansion must be a `(conv| …)` quotation; other body \
                 shapes are rejected (fail closed) rather than registered as a macro \
                 that can never fire at conv position"
                    .to_string(),
            ));
        };
        let Some((head, body)) = quotation_category_head(content) else {
            return Err(ElabError::MacroError(
                "a conv macro's expansion must be a `(conv| …)`-headed quotation (fail closed)"
                    .to_string(),
            ));
        };
        if head != "conv" {
            return Err(ElabError::MacroError(format!(
                "a conv macro's expansion must be a `(conv| …)` quotation, got `({head}| …)`"
            )));
        }
        let Some(parsed) = parse_tactic_elab_pattern(pattern) else {
            return Err(ElabError::MacroError(
                "unsupported conv macro pattern shape (supported: a leading keyword \
                 literal followed by plain antiquotation variables) (fail closed)"
                    .to_string(),
            ));
        };
        let TacticElabPattern {
            name,
            bound_vars,
            repetition,
        } = parsed;
        if repetition.is_some() {
            return Err(ElabError::MacroError(format!(
                "conv macro `{name}`: repetition variables are not supported yet (fail closed)"
            )));
        }
        if bound_vars
            .iter()
            .any(|v| category_is_optional(v.category.as_ref()))
        {
            return Err(ElabError::MacroError(format!(
                "conv macro `{name}`: optional binders are not supported yet (fail closed)"
            )));
        }
        // The registry is category-flat: the conv keyword dispatches through
        // the same `Named` route as ordinary tactics, so an existing name
        // (simple OR compound entry) would be silently replaced — reject.
        if self.tactic_registry.is_registered(&name)
            || self.tactic_registry.get_compound(&name).is_some()
        {
            return Err(ElabError::MacroError(format!(
                "conv macro `{name}` collides with an already-registered tactic name; \
                 Clean's tactic registry is category-flat, so the declaration is \
                 rejected (fail closed) rather than shadowing the tactic"
            )));
        }
        let bound: Vec<&SurfaceName> = bound_vars.iter().map(|v| &v.name).collect();
        // As for a tactic macro: `$x` is the operand, spelled `«$x»`, and a
        // bare `x` is the template's own identifier.
        let Some(script_src) = rewrite_tactic_antiquots(body, &bound) else {
            return Err(ElabError::MacroError(format!(
                "conv macro expansion `(conv| {body})` uses an antiquotation the \
                 pattern does not bind"
            )));
        };
        let patterns = self.tactic_registry.tactic_patterns();
        let by_expr =
            clean_parser::parse_expr_with_tactics(&format!("by conv => {script_src}"), &patterns)
                .map_err(|e| {
                ElabError::MacroError(format!(
                    "conv macro expansion `(conv| {script_src})` does not parse as a \
                         conv script: {e}"
                ))
            })?;
        let SurfaceExpr::ByTactic(_, tactics) = by_expr else {
            return Err(ElabError::MacroError(format!(
                "conv macro expansion `(conv| {script_src})` did not produce a tactic block"
            )));
        };
        let script = match tactics.as_slice() {
            [SurfaceTactic::Conv(_, SurfaceTacticLocation::Goal, script)] if !script.is_empty() => {
                script.clone()
            }
            _ => {
                return Err(ElabError::MacroError(format!(
                    "conv macro expansion `(conv| {script_src})` did not parse as a single \
                     non-empty conv script (fail closed)"
                )));
            }
        };
        let bound_names: Vec<SurfaceName> = bound
            .iter()
            .map(|name| tactic_operand_variable(name))
            .collect();
        if !bound_names.is_empty() {
            if let Some(offender) = script
                .iter()
                .find(|t| !super::user_conv::substitution_reaches(t, &bound_names))
            {
                return Err(ElabError::MacroError(format!(
                    "conv macro `{name}` binds arguments, but its expansion contains {} — \
                     argument substitution cannot be shown to reach it, so the declaration \
                     is rejected (fail closed) rather than registered as a macro that \
                     could silently mis-expand",
                    super::user_conv::conv_tactic_shape(offender)
                )));
            }
        }
        // The simple entry teaches the parser the keyword + argument pattern
        // (`tactic_patterns()`); dispatch always prefers the compound entry
        // registered next, so the simple handler is an honest-error backstop.
        let arg_pattern = arg_pattern_for_bound_vars(&bound_vars, None);
        self.tactic_registry.register(TacticEntry {
            name: name.clone(),
            pattern: arg_pattern,
            handler: super::user_conv::conv_macro_simple_handler(name.clone()),
        });
        // The script is a template, expanded hygienically at each use (see
        // `try_register_tactic_macro`).
        let hygienic = self.templates_hygienic();
        let script = if hygienic {
            let block = SurfaceExpr::ByTactic(clean_parser::Span::dummy(), script);
            self.record_template_site_resolutions(site, &bound_names, &block)?;
            match self.macro_ctx.mark_template(&block, &bound_names, site) {
                Ok(SurfaceExpr::ByTactic(_, marked)) => marked,
                Ok(_) => unreachable!("the template walk keeps a tactic block a tactic block"),
                Err(refusal) => {
                    return Err(ElabError::MacroError(format!(
                        "template refused: {}",
                        refusal.reason()
                    )))
                }
            }
        } else {
            script
        };
        self.tactic_registry
            .register_compound(super::user_conv::build_user_conv_handler(
                name,
                bound_names,
                script,
                hygienic,
            ));
        Ok(ElabResult::Skipped)
    }

    /// Register a user-defined term-category elaborator
    /// (`elab "kw" e:term ... : term => <body>`).
    ///
    /// Accepts the tractable core: a leading string-literal keyword followed by
    /// zero or more flat bound term/ident antiquotations (the same shape the
    /// tactic path accepts). Repetition, optional groups, bare category refs, or
    /// interspersed literals are deferred (`Skipped`) — they need a custom
    /// grammar re-parse that is not yet available.
    ///
    /// Phase 6 note: a TRAILING repetition variable (`xs:term,*`) IS recognized
    /// by the shared pattern parser, but a *term*-category variadic elaborator
    /// requires an expansion semantics (a comma/operator fold of the element
    /// list, or per-element code generation) that the substitute-and-reelaborate
    /// bridge does not yet provide. So a recognized term repetition is DEFERRED
    /// here (`Skipped`) rather than registered with the wrong arity — the
    /// variadic path is currently tactic-only.
    ///
    /// On success the keyword and its bound variable names are recorded in
    /// `user_term_elabs`; `ElabCtx::elaborate` then recognizes a call to the
    /// keyword (`App(Ident(kw), args)` / bare `Ident(kw)`), substitutes the
    /// call-site arguments into the body, and re-elaborates the substituted body
    /// through the normal kernel-checked pipeline.
    fn elab_term_elab_decl(
        &mut self,
        pattern: &[SyntaxPatternItem],
        body: &SurfaceExpr,
    ) -> Result<ElabResult, ElabError> {
        let Some(parsed) = parse_tactic_elab_pattern(pattern) else {
            return Ok(ElabResult::Skipped);
        };
        let TacticElabPattern {
            name,
            bound_vars,
            repetition,
        } = parsed;
        // Term-category variadic elaborators are deferred (see doc comment): the
        // fold/codegen expansion is not yet implemented, and registering a
        // fixed-arity term elaborator for a variadic pattern would silently
        // mis-bind, so we defer honestly instead.
        if repetition.is_some() {
            return Ok(ElabResult::Skipped);
        }
        // Optional patterns (`x:term?`): the parser carries the `?` as a suffix on
        // the bound variable's category (`"term?"`). A SINGLE trailing optional
        // binder is tractable for the substitute-and-reelaborate bridge — the
        // keyword accepts the optional argument present or absent. A `?` on any
        // NON-trailing binder is NOT tractable (the positional substitution model
        // cannot skip a hole in the middle), so we defer those honestly.
        let optional_trailing = classify_optional_trailing(&bound_vars);
        let OptionalClassification::Tractable(optional_trailing) = optional_trailing else {
            return Ok(ElabResult::Skipped);
        };
        let bound_names: Vec<SurfaceName> = bound_vars.into_iter().map(|v| v.name).collect();
        self.user_term_elabs.insert(
            name,
            super::user_term::UserTermElab {
                bound_vars: bound_names,
                body: body.clone(),
                optional_trailing,
            },
        );
        Ok(ElabResult::Skipped)
    }

    /// Elaborate a surface declaration to a kernel declaration
    ///
    /// # REQUIRES
    /// - `decl` is a valid surface declaration from the parser
    ///
    /// # ENSURES
    /// - On success, returns `ElabResult` matching declaration type
    /// - Auto-implicit discovery is enabled during elaboration
    /// - Universe levels are canonicalized in the result
    pub fn elab_decl(&mut self, decl: &SurfaceDecl) -> Result<ElabResult, ElabError> {
        // Nested/generated declarations own only their own do obligations.
        // Failed work must not poison the next declaration on a reused context.
        let previous_do_obligations = std::mem::take(&mut self.do_pure_obligations);
        let previous_postponed = self.postponed_open_carrier_instances.clone();
        // Expected-sort names belong to this declaration's elaboration;
        // source-info identities remain shared across the document.
        let previous_term_capture = self.term_info_capture.take();
        self.term_info_capture = previous_term_capture
            .as_ref()
            .map(TermInfoCapture::declaration_scope);
        // Enable auto-implicits for declaration elaboration (#164)
        // Save previous state to restore after (for nested calls)
        let prev_in_decl_context = self.in_decl_context;
        self.in_decl_context = true;

        // Name the declaration whose body is about to be elaborated, so an
        // identifier that turns out to be its OWN name is refused as a
        // recursive definition rather than guessed at by name distance
        // (`ElabError::RecursionOutsideFragment`).
        //
        // Written here, at the single per-declaration entry point, and
        // UNCONDITIONALLY — `None` is assigned for every shape that has no
        // self-reference question — so a subject can never survive into the
        // next declaration and mislabel a genuine typo there. `elab_decl` is
        // re-entered for generated/nested declarations, which correctly
        // rebinds the subject for their extent; the previous value is put back
        // on the way out, alongside `in_decl_context`.
        let previous_self_reference =
            std::mem::replace(&mut self.self_reference, Self::self_reference_subject(decl));

        let result = self
            .elab_decl_inner(decl)
            .map(|result| self.canonicalize_levels_in_elab_result(result));
        // Every `deriving` failure is attached by the dispatcher arm that
        // recorded it; one still pending here fails the declaration rather
        // than vanish with the context.
        let result = match self.unattached_deriving_failure() {
            Some(error) => Err(error),
            None => result,
        };
        // (A B07 post-pass rewrote instance-less `Pure.pure`/`Bind.bind` axiom
        // applications into `Proj` form here. Those axioms proved `False` and
        // were replaced on 2026-09-28 by Lean's class projections, which carry
        // their synthesized instance, so there is nothing left to rewrite.)

        let result = result.and_then(|result| {
            self.ensure_do_pure_obligations()?;
            Ok(result)
        });
        self.do_pure_obligations = previous_do_obligations;
        if result.is_err() {
            self.postponed_open_carrier_instances = previous_postponed;
        }

        // Restore context state after elaboration
        self.in_decl_context = prev_in_decl_context;
        self.self_reference = previous_self_reference;
        self.term_info_capture = previous_term_capture;
        result
    }

    /// The declaration `decl` defines, when a reference to its own name inside
    /// it would be a recursive definition rather than a missing name.
    ///
    /// `None` for every other shape — a `axiom`/`opaque`/`inductive` has no
    /// body that could self-refer, and a `mutual` block, `example` or command
    /// has no single subject — which is what keeps the refusal from firing
    /// where it does not apply. The parameter count is the SURFACE binder
    /// count here; `elab_definition_inner` refines it once equation-form
    /// normalization has lifted binders out of an arrow type.
    fn self_reference_subject(decl: &SurfaceDecl) -> Option<super::SelfReferenceSubject> {
        let (name, binders) = match decl {
            SurfaceDecl::Def { name, binders, .. } | SurfaceDecl::Theorem { name, binders, .. } => {
                (name, binders)
            }
            _ => return None,
        };
        Some(super::SelfReferenceSubject {
            written: name.clone(),
            params: binders.len(),
        })
    }

    /// The name a source declaration introduces, as written: one name, a
    /// `mutual` block's members, or nothing (`example`, commands).
    pub(super) fn declared_surface_name(decl: &SurfaceDecl) -> DeclaredSurfaceName<'_> {
        match decl {
            SurfaceDecl::Def { name, .. }
            | SurfaceDecl::Theorem { name, .. }
            | SurfaceDecl::Axiom { name, .. }
            | SurfaceDecl::Opaque { name, .. }
            | SurfaceDecl::Inductive { name, .. }
            | SurfaceDecl::Coinductive { name, .. }
            | SurfaceDecl::Codata { name, .. }
            | SurfaceDecl::Codef { name, .. }
            | SurfaceDecl::Structure { name, .. }
            | SurfaceDecl::Class { name, .. }
            | SurfaceDecl::Instance {
                name: Some(name), ..
            } => DeclaredSurfaceName::One(name),
            SurfaceDecl::Mutual { decls, .. } => DeclaredSurfaceName::Block(decls),
            _ => DeclaredSurfaceName::None,
        }
    }

    /// Refuse a source declaration — of ANY kind, `private`, `protected`,
    /// `_root_`-qualified or inside a namespace — whose full name is reserved
    /// for a kernel-owned axiom: a foundational axiom (`propext`,
    /// `Quot.sound`, `Classical.choice`, the `Quot` primitives) or a trust
    /// marker (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`), matched
    /// STRUCTURALLY or by PRINTED FORM
    /// ([`clean_kernel::is_reserved_ambient_axiom_name`]).
    ///
    /// Structurally equal names already collide in the kernel wherever the
    /// kernel's own declaration is present; this refusal also holds in an
    /// environment without it, with a clear error instead of a duplicate-name
    /// failure. The printed-form half is the one Lean itself would accept:
    /// `axiom «Quot.sound» : False` declares a ONE-component name that is not
    /// Lean's `Quot.sound` but prints exactly like it, so every report that
    /// lists it (`assumptions`, `#print axioms`, a bundle's axiom list) would
    /// show the foundation. Until 2026-09-28 the axiom classifier also compared
    /// printed names, and a proof of `False` through such an axiom passed
    /// `clean check` with nothing disclosed. Clean refuses the name
    /// deliberately, as a hardening beyond Lean; nothing sound needs it.
    ///
    /// Runs in every environment, whether or not it models Lean's `Init`
    /// (`check_not_declared_in_lean_core` does not always), and ahead of it.
    fn check_not_reserved_kernel_name(&self, decl: &SurfaceDecl) -> Result<(), ElabError> {
        let name = match Self::declared_surface_name(decl) {
            DeclaredSurfaceName::One(name) => name,
            DeclaredSurfaceName::Block(decls) => {
                for inner in decls {
                    self.check_not_reserved_kernel_name(inner)?;
                }
                return Ok(());
            }
            DeclaredSurfaceName::None => return Ok(()),
        };
        let full = self.qualify_name(name).into_name();
        if clean_kernel::is_reserved_ambient_axiom_name(&full) {
            return Err(ElabError::ReservedKernelName {
                name: full.to_unambiguous_string(),
                printed: full.to_string(),
            });
        }
        Ok(())
    }

    /// Refuse a declaration whose full name is a constant of Lean 4.8.0 core
    /// (`crate::lean_core_names`): the environment of a Lean file with no
    /// `import` line already holds it, so Lean reports it as already declared
    /// (`Lean.Elab.checkNotAlreadyDeclared`) and keeps its core meaning.
    ///
    /// This holds whether or not Clean models the constant. Clean's prelude
    /// models only part of `Init`, and the kernel's duplicate check sees only
    /// what the prelude holds; for the rest Clean used to accept the user's
    /// declaration and compute with the user's body: `def Nat.lcm := fun x y
    /// => x + y + 7` proved `Nat.lcm 4 6 = 17` (Lean 4.8.0: 12), `def bne`,
    /// `def List.getLast!`, `def EmptyCollection.emptyCollection` (read back
    /// through `∅`) and 19 more core names likewise (measured 2026-09-26).
    ///
    /// Only SOURCE declarations come through here. Clean's own model of
    /// `Init` is built into the environment by the prelude providers
    /// (`clean_kernel::Environment::init_*`), never by elaborating a
    /// declaration, so it is exempt by construction and nothing a user writes
    /// can claim that exemption. `private` does not change the full name here,
    /// and Lean refuses a private redeclaration of a core name as well ("a
    /// non-private declaration … has already been declared").
    ///
    /// The rule applies in full in an environment that holds Clean's model of
    /// `Init` (`Environment::models_lean_init`: built by the prelude, as
    /// every `clean check`, project and lake lane is). Lean's check consults
    /// the environment, and one built without the prelude holds no core
    /// constant — a Lean `prelude` file, or a kernel-model harness such as
    /// `clean-verify`'s foundation units (`inductive Nat`, `inductive Eq`,
    /// `def Nat.add`), may declare those names. There the core name is still
    /// refused where the environment already RESOLVES it as the core
    /// constant without declaring it — a redirect (`xor` is `Bool.xor`), the
    /// `cond` fallback, a recognizer's `T.elim` — as it was before
    /// (`Self::models_lean_core_global`).
    fn check_not_declared_in_lean_core(&self, decl: &SurfaceDecl) -> Result<(), ElabError> {
        let name = match Self::declared_surface_name(decl) {
            DeclaredSurfaceName::One(name) => name,
            DeclaredSurfaceName::Block(decls) => {
                for inner in decls {
                    self.check_not_declared_in_lean_core(inner)?;
                }
                return Ok(());
            }
            DeclaredSurfaceName::None => return Ok(()),
        };
        let full = self.qualify_name(name).into_name();
        if !crate::lean_core_names::is_lean_init_constant(&full) {
            return Ok(());
        }
        let declared_in_core = self.env.models_lean_init() || {
            let present = self.env.get_const(&full).is_some()
                || self.env.get_inductive(&full).is_some()
                || self.env.get_constructor(&full).is_some()
                || self.env.get_recursor(&full).is_some();
            !present && self.models_lean_core_global(&full)
        };
        if declared_in_core {
            return Err(ElabError::DeclaredInLeanCore {
                name: full.to_string(),
            });
        }
        Ok(())
    }

    /// The `SurfaceDecl::Notation` arm of [`Self::elab_decl`], run in whatever
    /// namespace the caller has made current.
    fn elab_notation_decl(
        &mut self,
        span: clean_parser::Span,
        kind: clean_parser::NotationKind,
        precedence: Option<u32>,
        pattern: &[clean_parser::NotationItem],
        expansion: &SurfaceExpr,
        scope: clean_parser::DeclScope,
    ) -> Result<ElabResult, ElabError> {
        // The template's free references resolve HERE, as Lean
        // pre-resolves a quotation's identifiers at the declaration
        // (`crate::namespace::TemplateResolution`). The parser marked
        // them with this site; the registration below marks the macro
        // form's the same way.
        // Under `set_option hygiene false` nothing is pre-resolved.
        let site = clean_parser::TemplateSiteId::of_span(span);
        let hygienic = self.templates_hygienic();
        if hygienic {
            self.record_template_resolutions(site, pattern, expansion)?;
        }
        self.macro_ctx.set_template_site(Some(site));
        self.macro_ctx.set_template_hygiene(hygienic);
        let registered = self.register_notation_decl(kind, precedence, pattern, expansion, scope);
        self.macro_ctx.set_template_site(None);
        self.macro_ctx.set_template_hygiene(true);
        registered
    }

    /// Register a `notation` command's template (the body of the
    /// `SurfaceDecl::Notation` arm of [`Self::elab_decl`]).
    fn register_notation_decl(
        &mut self,
        kind: clean_parser::NotationKind,
        precedence: Option<u32>,
        pattern: &[clean_parser::NotationItem],
        expansion: &SurfaceExpr,
        scope: clean_parser::DeclScope,
    ) -> Result<ElabResult, ElabError> {
        // `scoped notation` (Lean: active only when the declaring
        // namespace is opened / current — `Lean/Elab/Notation.lean`
        // attrKind `scoped`) registers against the CURRENT namespace
        // and stays out of the live registry until that namespace is
        // active (current, an ancestor of the current namespace, or
        // activated by `open Ns` / `open scoped Ns`). At root Lean
        // rejects the `scoped` modifier ("scoped attributes must be
        // used inside namespaces"), so we fail closed there rather
        // than registering a notation that could never be gated
        // honestly (gap sweep B13, namespaces_scoping/p10).
        if scope == clean_parser::DeclScope::Scoped {
            if self.namespace_prefix.is_anonymous() {
                return Err(ElabError::MacroError(
                    "scoped notation must be declared inside a namespace".to_string(),
                ));
            }
            let namespace = self.namespace_prefix.clone();
            self.macro_ctx
                .register_scoped_notation(&namespace, kind, precedence, pattern, expansion)
                .map_err(|e| ElabError::MacroError(e.to_string()))?;
            return Ok(ElabResult::Skipped);
        }
        // `local notation` and plain `notation` both register in the
        // macro context; section/namespace blocks snapshot-restore the
        // macro context, which bounds `local` to its block.
        self.macro_ctx
            .register_notation(kind, precedence, pattern, expansion)
            .map_err(|e| ElabError::MacroError(e.to_string()))?;
        Ok(ElabResult::Skipped)
    }

    /// Inner implementation of declaration elaboration, inside the namespace
    /// pinned Lean opens around `decl` (`Self::decl_site_namespace`), which
    /// a nested command (`namespace`, `section`, `open … in`) replaces for
    /// its own declarations and which is restored on the way out.
    pub(super) fn elab_decl_inner(&mut self, decl: &SurfaceDecl) -> Result<ElabResult, ElabError> {
        let opened = self.lean_decl_namespace(decl);
        let entered = opened.as_ref().map_or_else(Vec::new, |ns| {
            crate::newly_entered_namespaces(&self.namespace_state, ns)
        });
        // Lean expands a qualified declaration to a namespace block. Each
        // component activates its scoped instances for the signature and body.
        let instance_scope = (!entered.is_empty()).then(|| {
            self.namespace_state.push_scope();
            for ns in &entered {
                self.namespace_state.activate_scoped(ns.clone());
            }
            self.clear_instance_cache();
            self.activate_scoped_instances_here(&entered)
        });
        let enclosing = std::mem::replace(&mut self.decl_site_namespace, opened);
        let section_family = matches!(decl, SurfaceDecl::Structure { binders, .. } | SurfaceDecl::Inductive { binders, .. }
            if super::family_section_parameters::section_prefix(binders) > 0);
        let result = if section_family {
            self.with_local_scope_rollback(|ctx| ctx.elab_decl_inner_at_site(decl))
        } else {
            self.elab_decl_inner_at_site(decl)
        };
        self.decl_site_namespace = enclosing;
        if let Some(saved) = instance_scope {
            self.restore_instance_state(saved);
            self.namespace_state.pop_scope();
            self.clear_instance_cache();
        }
        result
    }

    fn elab_decl_inner_at_site(&mut self, decl: &SurfaceDecl) -> Result<ElabResult, ElabError> {
        self.check_not_reserved_kernel_name(decl)?;
        self.check_not_declared_in_lean_core(decl)?;
        self.check_private_not_already_declared(decl)?;
        match decl {
            SurfaceDecl::Def {
                name,
                universe_params,
                binders,
                ty,
                val,
                attrs,
                termination,
                modifiers,
                where_decls,
                ..
            } => self.elab_definition_inner(
                name,
                universe_params,
                binders,
                ty.as_deref(),
                val,
                attrs,
                termination,
                modifiers,
                where_decls,
            ),

            SurfaceDecl::Theorem {
                name,
                universe_params,
                binders,
                ty,
                proof,
                attrs,
                termination,
                modifiers,
                where_decls,
                ..
            } => self.elab_theorem_inner(
                name,
                universe_params,
                binders,
                ty,
                proof,
                attrs,
                termination,
                modifiers,
                where_decls,
            ),

            SurfaceDecl::Axiom {
                name,
                universe_params,
                binders,
                ty,
                attrs,
                modifiers,
                ..
            } => self.elab_axiom_inner(name, universe_params, binders, ty, attrs, modifiers),

            SurfaceDecl::Opaque {
                name,
                universe_params,
                binders,
                ty,
                val,
                attrs,
                modifiers,
                ..
            } => self.elab_opaque_inner(
                name,
                universe_params,
                binders,
                ty,
                val.as_deref(),
                attrs,
                modifiers,
            ),

            SurfaceDecl::Inductive {
                name,
                universe_params,
                binders,
                ty,
                ctors,
                deriving,
                modifiers,
                ..
            } => {
                self.set_decl_universe_params(universe_params);
                let qname = self.family_decl_name(name, modifiers);
                let result = self.elab_inductive(
                    &qname,
                    universe_params,
                    binders,
                    ty,
                    ctors,
                    deriving,
                    modifiers,
                );
                // A failed `deriving` class is an error beside the type, never
                // instead of it (`deriving_log`).
                self.attach_logged_deriving_failures(decl, result)
            }

            // Coinductive (#191): the v1 greatest-fixpoint lowering.
            //
            // A `coinductive` declaration must NEVER be routed through
            // `elab_inductive` — that would silently mint the LEAST fixpoint
            // (with an induction principle the gfp must not have), so proofs
            // would check while meaning something other than what the user
            // wrote. Instead the declaration is lowered to the impredicative
            // gfp encoding (`crate::coinductive_surface`), and every shape the
            // lowering does not fully understand still rejects LOUDLY.
            SurfaceDecl::Coinductive {
                name,
                universe_params,
                binders,
                ty,
                ctors,
                deriving,
                modifiers,
                ..
            } => {
                let qname = self.qualify_name(name);
                let generated = crate::coinductive_surface::lower(
                    &qname,
                    name,
                    self.env,
                    universe_params,
                    binders,
                    ty,
                    ctors,
                    deriving,
                    modifiers,
                )?;
                // Elaborate the generated declarations against a CLONE of the
                // environment: each one depends on its predecessors (`P.coind`
                // needs `P` to unfold), and `ElabCtx` holds only an immutable
                // borrow. The results are handed back as an
                // `ElabResult::Multiple`, which the registration path installs
                // — and the kernel re-checks — one by one into the real
                // environment, exactly as for hand-written source. Nothing is
                // added unchecked and no axiom is minted.
                let mut candidate: clean_kernel::Environment = self.env.clone();
                let mut results = Vec::with_capacity(generated.len());
                for gen_decl in &generated {
                    let r = crate::elaborate_decl_and_register(&mut candidate, gen_decl).map_err(
                        |e| ElabError::Unsupported {
                            feature: format!(
                                "coinductive declaration `{qname}`: the generated \
                                 greatest-fixpoint declaration `{}` failed to \
                                 elaborate/kernel-check ({}); the declaration is \
                                 REJECTED rather than partially registered",
                                crate::preprocess_ext::decl_name(gen_decl).map(ToString::to_string).unwrap_or_else(|| "?".into()),
                                e
                            ),
                        },
                    )?;
                    results.push(r);
                }
                Ok(ElabResult::Multiple(results))
            }

            SurfaceDecl::Codef { .. } => Err(ElabError::Unsupported {
                feature: "codef is a top-level command (handled before per-decl \
                          elaboration); it cannot appear nested inside namespaces, \
                          sections, or mutual blocks yet"
                    .to_string(),
            }),
            SurfaceDecl::Codata { .. } => Err(ElabError::Unsupported {
                feature: "codata is a top-level command (handled before per-decl \
                          elaboration); it cannot appear nested inside namespaces, \
                          sections, or mutual blocks yet"
                    .to_string(),
            }),
            SurfaceDecl::Structure {
                name,
                universe_params,
                binders,
                extends,
                ty,
                ctor_name,
                fields,
                deriving,
                modifiers,
                ..
            } => {
                // Install declared universe params as BOTH active and RIGID, so
                // fresh params minted while elaborating universe-polymorphic
                // field/parent constants (e.g. `Inh.{u_0} α`) collapse ONTO the
                // declaration's `u` rather than silently renaming `u` to `u_0`.
                self.set_decl_universe_params(universe_params);
                let qname = self.family_decl_name(name, modifiers);
                let result = self.elab_structure(
                    &qname,
                    universe_params,
                    binders,
                    extends,
                    ty.as_deref(),
                    ctor_name.as_ref(),
                    fields,
                    deriving,
                    modifiers,
                    super::elab_structure::StructureKind::Structure,
                ).map(|(result, _)| result);
                // A failed `deriving` class is an error beside the structure,
                // never instead of it (`deriving_log`).
                self.attach_logged_deriving_failures(decl, result)
            }

            SurfaceDecl::Class {
                name,
                universe_params,
                binders,
                extends,
                ty,
                fields,
                modifiers,
                ..
            } => {
                self.set_decl_universe_params(universe_params);
                let qname = self.family_decl_name(name, modifiers);
                self.elab_class(
                    &qname,
                    universe_params,
                    binders,
                    extends,
                    ty.as_deref(),
                    fields,
                    modifiers,
                )
            }

            SurfaceDecl::Instance {
                name,
                universe_params,
                binders,
                class_type,
                fields,
                priority,
                modifiers,
                compiler_attrs,
                ..
            } => {
                self.set_decl_universe_params(universe_params);
                let qname = name.as_ref().map(|n| self.qualify_name(n));
                let result = self.elab_instance(
                    qname.as_ref(),
                    universe_params,
                    binders,
                    class_type,
                    fields,
                    *priority,
                    modifiers,
                )?;
                // `@[implemented_by]` / `@[extern]` on the instance bind the
                // instance constant, applied after it is registered like a
                // `def`'s (`decl_attributes`).
                match &result {
                    ElabResult::Instance { name, .. } => {
                        self.collect_attributes(name, compiler_attrs);
                    }
                    _ if !compiler_attrs.is_empty() => {
                        return Err(ElabError::Unsupported {
                            feature: "`@[implemented_by]` / `@[extern]` on an instance that \
                                      did not elaborate to one instance constant"
                                .to_string(),
                        });
                    }
                    _ => {}
                }
                Ok(result)
            }

            // Macro-related declarations: register with macro context
            SurfaceDecl::Syntax {
                name,
                priority,
                pattern,
                category,
                ..
            } => {
                let name = name.as_ref().map(|n| self.qualify_name(n));
                self.macro_ctx
                    .register_syntax(name.as_ref(), priority.as_ref(), pattern, category)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::DeclareSyntaxCat { name, .. } => {
                self.macro_ctx.register_typed_syntax_category(name)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Macro {
                span,
                pattern,
                category,
                expansion,
                ..
            } => {
                // Tactic-position macros (`macro "kw" … : tactic =>
                // `(tactic| …)`) register through the tactic bridge — the
                // Syntax-level expander cannot fire at tactic position (`by`
                // blocks cross the surface↔Syntax bridge as opaque nodes).
                // `Some` means the route owned the declaration (registered, or
                // rejected loudly); `None` falls through to the Syntax-level
                // registration unchanged.
                let routed = self.try_register_tactic_macro(
                    pattern,
                    category,
                    expansion,
                    clean_parser::TemplateSiteId::of_span(*span),
                )?;
                if let Some(result) = routed {
                    return Ok(result);
                }
                // Unknown-category gate (fail closed): the Syntax-level
                // registration below ignores the category entirely, so a
                // macro declared with a category Clean does not know — a
                // typo (`: tatic`) or an unimplemented Lean category
                // (`: calc`) — used to register silently and never fire at
                // any position: the declaration vanished without a trace.
                // Reject it loudly at the declaration, naming the category.
                // Scope, precisely:
                //   - `tactic` / `conv` were routed by the bridges above
                //     (`conv` never reaches this gate; a tactic-category
                //     macro whose RHS is not a category-headed quotation
                //     does, and `tactic` is a registered built-in category,
                //     so its Syntax-level fall-through is unchanged);
                //   - `term` / `command` are registered built-in categories
                //     and keep the Syntax-level registration;
                //   - `attr` / `doElem` are registered built-in categories
                //     Mathlib declares load-bearing macros in (`simps?` /
                //     `continuity` / `to_additive?` at attr; `haveI'` /
                //     `letI'` at doElem) — NEEDS-SUPPORT, kept on the
                //     current skip path rather than rejected (survey
                //     2026-08-22 over the mathlib4 checkout);
                //   - a category declared with `declare_syntax_cat` is
                //     legitimate and keeps the current path.
                if !self.macro_ctx.has_syntax_category(category) {
                    return Err(ElabError::MacroError(format!(
                        "macro category `{category}` is not a known syntax category, \
                         so this macro could never fire; it is rejected (fail \
                         closed) rather than silently skipped — supported \
                         categories are `term`, `tactic`, `conv`, and `command` \
                         (`attr` and `doElem` register but do not expand yet); \
                         declare a custom category first with \
                         `declare_syntax_cat {category}`"
                    )));
                }
                // The template's free names resolve HERE (Lean pre-resolves a
                // quotation's identifiers at the declaration), as for a
                // `notation`: a `macro` declared under `open A` reads `A`'s
                // names at every use, whatever is open there.
                // A template the walk refuses is still registered (as a
                // refusing expansion), so a use is refused rather than read
                // as other syntax; the declaration reports the refusal.
                // Under `set_option hygiene false` nothing is pre-resolved:
                // the template's names resolve at each use.
                let site = clean_parser::TemplateSiteId::of_span(*span);
                let hygienic = self.templates_hygienic();
                let recorded = if hygienic {
                    self.record_macro_template(site, expansion)
                } else {
                    Ok(())
                };
                self.macro_ctx.set_template_site(Some(site));
                self.macro_ctx.set_template_hygiene(hygienic);
                let registered = self
                    .macro_ctx
                    .register_macro(pattern, category, expansion)
                    .map_err(|e| ElabError::MacroError(e.to_string()));
                self.macro_ctx.set_template_site(None);
                self.macro_ctx.set_template_hygiene(true);
                registered?;
                recorded?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::MacroRules {
                span, name, arms, ..
            } => {
                // Tactic-position arms (`` `(tactic| kw …) => `(tactic| …) ``)
                // register through the tactic bridge — the Syntax-level
                // expander cannot fire at tactic position. Remaining arms keep
                // the Syntax-level registration unchanged.
                let syntax_level_arms = arms
                    .iter()
                    .filter_map(|arm| match self
                        .try_register_tactic_macro_rules_arm(arm, clean_parser::TemplateSiteId::of_span(*span))
                    {
                        Ok(true) => None,
                        Ok(false) => Some(Ok(arm.clone())),
                        Err(e) => Some(Err(e)),
                    })
                    .collect::<Result<Vec<MacroArm>, ElabError>>()?;
                if !syntax_level_arms.is_empty() {
                    // Pre-resolve the arms' templates at this declaration (see
                    // the `Macro` arm).
                    let site = clean_parser::TemplateSiteId::of_span(*span);
                    let hygienic = self.templates_hygienic();
                    let mut recorded = Ok(());
                    for arm in syntax_level_arms.iter().filter(|_| hygienic) {
                        let arm_recorded = self.record_macro_template(site, &arm.expansion);
                        if recorded.is_ok() {
                            recorded = arm_recorded;
                        }
                    }
                    self.macro_ctx.set_template_site(Some(site));
                    self.macro_ctx.set_template_hygiene(hygienic);
                    let registered = self
                        .macro_ctx
                        .register_macro_rules(name.as_ref(), &syntax_level_arms)
                        .map_err(|e| ElabError::MacroError(e.to_string()));
                    self.macro_ctx.set_template_site(None);
                    self.macro_ctx.set_template_hygiene(true);
                    registered?;
                    recorded?;
                }
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Notation {
                span,
                kind,
                precedence,
                pattern,
                expansion,
                scope,
                scope_ns,
            } => {
                // Mathlib's `scoped[NS]` is `with_weak_namespace _root_.NS`:
                // the declaration is registered in, and its template resolved
                // against, `NS` -- not the namespace it is written in.
                let enclosing = scope_ns
                    .as_ref()
                    .map(|ns| std::mem::replace(&mut self.namespace_prefix, ns.clone()));
                let registered = self.elab_notation_decl(*span, *kind, *precedence, pattern, expansion, *scope);
                // Restored on every path, the error one included.
                if let Some(enclosing) = enclosing {
                    self.namespace_prefix = enclosing;
                }
                registered
            }

            SurfaceDecl::Check { expr, .. } => {
                let kernel_expr = self.elaborate(expr)?;
                let result = crate::commands::elab_check_rendered(
                    self.env,
                    &kernel_expr,
                    self.private_names_rendering(),
                )?;
                Ok(ElabResult::Command(super::CommandOutput::Check(result)))
            }
            SurfaceDecl::Eval { expr, .. } => {
                let kernel_expr = self.elaborate(expr)?;
                // What pinned Lean will not run (review r6, X11 and X1;
                // docs/DECISIONS.md R134): a term that depends on `sorry`, uses
                // a constant with no code, or has no way to be displayed.
                let ty = clean_kernel::TypeChecker::new(self.env)
                    .infer_type(&kernel_expr)
                    .map_err(|e| ElabError::KernelCheckFailed {
                        name: clean_kernel::name::Name::anon(),
                        detail: e.to_string(),
                    })?;
                if let Some(message) =
                    crate::lean_compile_checks::eval_refusal(self.env, &kernel_expr, &ty)
                {
                    return Err(ElabError::CommandFailed { message });
                }
                if let Some(runtime) = &self.imported_runtime {
                    if let Some(result) = runtime.eval(self.env, &kernel_expr)? {
                        return Ok(ElabResult::Command(super::CommandOutput::Eval(result)));
                    }
                }
                let result = crate::commands::elab_eval(self.env, &kernel_expr)?;
                Ok(ElabResult::Command(super::CommandOutput::Eval(result)))
            }
            SurfaceDecl::Reduce {
                expr,
                reduce_proofs,
                reduce_types,
                ..
            } => {
                // Not `#eval`: nothing is compiled or run, and no `Repr` is
                // needed (`crate::reduce_command`).
                let bound_option_set = crate::reduce_command::BOUND_OPTIONS
                    .into_iter()
                    .chain(crate::reduce_command::WARNING_OPTIONS)
                    .find(|option| self.get_option(option).is_some());
                let kernel_expr = self.elaborate(expr)?;
                let flags = crate::reduce_command::ReduceFlags {
                    reduce_types: *reduce_types,
                    reduce_proofs: *reduce_proofs,
                };
                let result = crate::reduce_command::elab_reduce(
                    self.env,
                    &kernel_expr,
                    flags,
                    bound_option_set,
                )?;
                Ok(ElabResult::Command(super::CommandOutput::Reduce(result)))
            }
            SurfaceDecl::Print { name, .. } => {
                // A name that is no constant as written resolves the way
                // Lean's `#print` resolves it (`realizeGlobalConstWithInfos`):
                // through the namespace, the `open`s and the private step, so
                // `#print p` reaches this module's private `p`, which exists
                // nowhere under its plain name once mangled (G21).
                let resolved = if name.is_relative_constructor()
                    || self.env.get_const(name.name()).is_some()
                    || self.env.get_inductive(name.name()).is_some()
                    || self.env.get_constructor(name.name()).is_some()
                    || self.env.get_recursor(name.name()).is_some()
                {
                    None
                } else {
                    match self.resolve_global_ident_target(name) {
                        super::elab_core::IdentTarget::Global(global) => Some(global),
                        _ => None,
                    }
                };
                let rendering = self.private_names_rendering();
                let result = match resolved {
                    Some(global) => crate::commands::elab_print_resolved(
                        self.env,
                        &name.to_string(),
                        &global,
                        rendering,
                    )?,
                    None if name.is_relative_constructor() => {
                        crate::commands::elab_print_typed(self.env, name)?
                    }
                    None => crate::commands::elab_print_resolved(
                        self.env,
                        &name.to_string(),
                        name.name(),
                        rendering,
                    )?,
                };
                Ok(ElabResult::Command(super::CommandOutput::Print(result)))
            }
            SurfaceDecl::PrintAxioms { name, .. } => self.elab_print_axioms_cmd(name),
            SurfaceDecl::PrintEquations { name, .. } => crate::print_equations::read_existing(
                self.env,
                &self.namespace_state,
                &self.foreign_private_decls,
                name,
            ),
            SurfaceDecl::Guard { expr, .. } => self.elab_guard_cmd(expr),
            SurfaceDecl::GuardMsgs { doc, spec, cmd, .. } => {
                self.elab_guard_msgs_cmd(doc.as_deref(), spec, cmd)
            }
            SurfaceDecl::Variable { binders, visibility, .. } => {
                if visibility.is_some() {
                    let world = match clean_olean::environment_world(self.env) {
                        Some(tag) => tag.parse::<clean_kernel::LeanWorld>()
                            .map_err(|error| ElabError::SourceWorld(error.to_string()))?,
                        None => clean_kernel::LeanWorld::ORACLE,
                    };
                    if !world.variable_visibility() {
                        return Err(ElabError::SourceWorld(format!("{world} does not admit public/private variable")));
                    }
                }
                self.elab_variable_binders(binders)?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Open {
                paths,
                scoped,
                body,
                ..
            } => {
                // SOUNDNESS (#open-in-body-drop): the `scoped` early-return used to fire BEFORE
                // the `body` check, so `open scoped X in theorem t : T := prf` returned `Skipped`
                // WITHOUT elaborating `t` at all — the theorem silently vanished (no error, no
                // `Failed` leaf, never kernel-checked, never registered). The body must be
                // elaborated regardless of scoped-ness: `open scoped` activates the namespace's
                // scoped notations (namespace-gated in the macro registry), so for a scoped
                // open the body is elaborated with those notations active but WITHOUT bringing
                // names into scope; a plain `open … in` additionally opens the names for the
                // body, and activates scoped notations too (Lean `elabOpen`: the simple form
                // calls `activateScoped`).
                if let Some(inner) = body {
                    self.namespace_state.push_scope();
                    self.macro_ctx.push_scoped_activation_frame();
                    self.activate_open_scoped_notation(paths);
                    let before = self.namespace_state.activated_scopes().to_vec();
                    let open_result = if *scoped {
                        crate::namespace::process_open_scoped(
                            self.env,
                            paths,
                            &mut self.namespace_state,
                        );
                        Ok(())
                    } else {
                        crate::namespace::process_open(self.env, paths, &mut self.namespace_state)
                            .map_err(|e| ElabError::Unsupported {
                                feature: e.to_string(),
                            })
                    };
                    let activated = self.namespace_state.newly_activated(&before);
                    let saved = self.activate_scoped_instances_here(&activated);
                    let result = open_result.and_then(|()| self.elab_decl_inner(inner));
                    self.restore_instance_state(saved);
                    self.macro_ctx.pop_scoped_activation_frame();
                    self.namespace_state.pop_scope();
                    return result;
                }
                self.activate_open_scoped_notation(paths);
                // The file-level driver activates the namespaces' scoped
                // instances in the environment once this declaration's
                // namespace state is persisted (`FileContext::
                // activate_scoped_instances`).
                if *scoped {
                    crate::namespace::process_open_scoped(
                        self.env,
                        paths,
                        &mut self.namespace_state,
                    );
                    return Ok(ElabResult::Skipped);
                }
                crate::namespace::process_open(self.env, paths, &mut self.namespace_state)
                    .map_err(|e| ElabError::Unsupported {
                        feature: e.to_string(),
                    })?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Namespace { name, decls, .. } => self.elab_namespace(name, decls),
            SurfaceDecl::Section { decls, .. } => self.elab_section(decls),
            SurfaceDecl::Export {
                namespace, names, ..
            } => {
                // `export Foo (x)` registers an alias for `Foo.x` in the
                // CURRENT namespace (Lean `Lean/Elab/BuiltinCommand.lean`
                // `elabExport`: `addAlias (currNamespace ++ id)`): at root the
                // alias is bare `x`; inside `namespace Bar` it is `Bar.x`,
                // visible as `x` from within `Bar` (via the outward walk) and
                // as `Bar.x` elsewhere in the file. The current namespace was
                // previously hardwired to `None`, exporting everything at root.
                let current_ns = if self.namespace_prefix.is_anonymous() {
                    None
                } else {
                    Some(&self.namespace_prefix)
                };
                crate::namespace::process_export(
                    self.env,
                    namespace,
                    names,
                    current_ns,
                    &mut self.namespace_state,
                )
                .map_err(|e| ElabError::Unsupported {
                    feature: e.to_string(),
                })?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Alias { names, target, attrs, modifiers, .. } => {
                if names.is_empty() {
                    let target = self.with_term_body_scope(|ctx| ctx.elab_ident(target))?;
                    if !matches!(target.kind(), clean_kernel::ExprKind::Const(..)) {
                        return Err(ElabError::Unsupported { feature: "alias target must be a global constant".into() });
                    }
                    return Ok(ElabResult::Skipped);
                }
                let mut results = Vec::with_capacity(names.len());
                for (name, direction) in names {
                    results.push(self.elab_alias_inner(name, target, *direction, attrs, modifiers)?);
                }
                Ok(ElabResult::Multiple(results))
            }
            SurfaceDecl::Example {
                binders, ty, val, ..
            } => {
                if matches!(val.as_ref(), SurfaceExpr::Hole(_)) {
                    return Err(ElabError::CannotInfer);
                }
                // B18: the shared `elab_def_body` boundary relocates a body/type
                // mismatch to a loud `TypeMismatch` at elaboration. For an
                // `example` the dedicated kernel check below produces the same
                // verdict attributed to `example`, so re-wrap the relocated
                // mismatch to keep that attribution (Lean `elabExample`).
                // A mismatch raised INSIDE the example's `by` body arrives as
                // `ElabError::InTactic { source: TypeMismatch, .. }` and is
                // deliberately not re-wrapped: naming the tactic that raised
                // it is the more precise attribution, and the verdict is the
                // same either way.
                let (ty_expr, val_expr) = match self.elab_decl_body(binders, ty.as_deref(), val) {
                    Ok((ty, val, _)) => (ty, val),
                    Err(ElabError::TypeMismatch { expected, actual }) => {
                        return Err(ElabError::KernelCheckFailed {
                            name: clean_kernel::name::Name::from_string("example"),
                            detail: format!(
                                "example proof has type `{actual}` which is not \
                                     definitionally equal to the stated type `{expected}`"
                            ),
                        });
                    }
                    Err(e) => return Err(e),
                };

                // Substitute metavariables and level constraints, then wrap with
                // auto-implicit binders — mirroring the `theorem`/`def` paths so
                // the kernel check below sees the same fully-closed term that a
                // named declaration would.
                let ty_expr = self.metas.instantiate(&ty_expr);
                let val_expr = self.metas.instantiate(&val_expr);
                let ty_expr = self.metas.instantiate_levels(&ty_expr);
                let val_expr = self.metas.instantiate_levels(&val_expr);
                let auto_implicits = self.take_auto_implicits();
                let (ty_expr, val_expr) =
                    Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

                // SOUNDNESS (#example-kernel-check): `example` declarations were
                // previously discarded (`ElabResult::Skipped`) WITHOUT any kernel
                // verification of the proof term. That made `example : <false> :=
                // rfl` a silent false-green: the elaborator accepted `rfl` against
                // any `Eq` goal because the kernel never checked that the proof's
                // inferred type was def-eq to the stated type. Named `theorem`/`def`
                // declarations are sound because they flow through `add_decl`'s
                // kernel check; `example` skipped it entirely.
                //
                // We now run the same kernel check that `add_decl` performs for a
                // Theorem: infer the type of the proof term (which fully kernel-
                // checks it) and, when an explicit type was given, require the
                // inferred type to be definitionally equal to the stated type.
                // The result is still discarded (no environment registration), so
                // `example` remains anonymous and namespace-neutral — but it is now
                // genuinely verified.
                let inferred_ty = {
                    use clean_kernel::tc::TypeChecker;
                    let tc = TypeChecker::new(self.env);
                    let inferred =
                        tc.infer_type(&val_expr)
                            .map_err(|e| ElabError::KernelCheckFailed {
                                name: clean_kernel::name::Name::from_string("example"),
                                detail: e.to_string(),
                            })?;
                    if ty.is_some() && !tc.is_def_eq(&inferred, &ty_expr) {
                        return Err(ElabError::KernelCheckFailed {
                            name: clean_kernel::name::Name::from_string("example"),
                            detail: format!(
                                "example proof has type `{inferred}` which is not \
                                 definitionally equal to the stated type `{ty_expr}`"
                            ),
                        });
                    }
                    inferred
                };

                // B02 (GAP_SWEEP_2026-07-09): surface the checked example as a
                // countable declaration leaf instead of `Skipped`. Lean checks
                // `example` through the full def-elab pipeline and then discards
                // it (lean4 `src/Lean/Elab/Declaration.lean`, `elabExample`);
                // `ElabResult::Example` mirrors that — registration is a no-op,
                // but `clean check` now counts it in "Checked N declarations".
                // With no explicit type the inferred type stands in (as for a
                // `def` without an ascription).
                Ok(ElabResult::Example {
                    ty: if ty.is_some() { ty_expr } else { inferred_ty },
                    val: val_expr,
                })
            }
            SurfaceDecl::Attribute { attrs, names, .. } => {
                self.elab_attribute_command(attrs, names)
            }
            SurfaceDecl::Mutual { decls, .. } => self.elab_mutual(decls),
            SurfaceDecl::SetOption {
                name, value, body, ..
            } => {
                // Drop-in: an UNKNOWN option NAME is tolerated as a no-op (Lean
                // core/plugins/linters register options Clean's registry does not
                // enumerate — `genInjectivity`, `linter.*`); the wrapped decl must
                // still elaborate. A KNOWN option with a wrongly-typed value stays
                // a loud error. See `validate_command_option_lenient`.
                let _known =
                    crate::options_registry::validate_command_option_lenient(&crate::options_registry::surface_option_key(name)?, value.as_deref())?;
                if let Some(inner_decl) = body {
                    // Per-declaration scoping: `set_option ... in <decl>` sets
                    // the option for that one command only (Lean's `in`), so
                    // the previous local value is restored after it — a
                    // `set_option hygiene false in notation …` inside a section
                    // must not leave the section's later templates unhygienic.
                    let key = crate::options_registry::surface_option_key(name)?;
                    let previous = self.local_options.get(&key).cloned();
                    self.set_local_option(key.clone(), value.clone());
                    let result = self.elab_decl_inner(inner_decl);
                    match previous {
                        Some(previous) => {
                            self.local_options.insert(key, previous);
                        }
                        None => {
                            self.local_options.remove(&key);
                        }
                    }
                    result
                } else {
                    // Store option locally so it is visible within the current
                    // elaboration context (sections, namespaces). The file-scope
                    // handler in lib.rs persists options to Environment and
                    // FileContext for cross-declaration visibility.
                    self.set_local_option(crate::options_registry::surface_option_key(name)?, value.clone());
                    Ok(ElabResult::Skipped)
                }
            }
            SurfaceDecl::Elab {
                pattern,
                category,
                body,
                ..
            } => self.elab_tactic_elab_decl(pattern, category, body),
            // `include` / `omit` register nothing themselves — they steer which
            // section variables the FOLLOWING declarations receive, which the
            // section/namespace drivers and `preprocess_decl_with_context`
            // apply from the file context.
            SurfaceDecl::IncludeVars { .. } | SurfaceDecl::OmitVars { .. } => {
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::DerivingInstance { classes, types, .. } => {
                self.elab_standalone_deriving(classes, types)
            }
            SurfaceDecl::Import { .. }
            | SurfaceDecl::UniverseDecl { .. }
            | SurfaceDecl::DeclareAesopRuleSets { .. }
            // `library_note «title»` carries no checkable content — a no-op.
            | SurfaceDecl::LibraryNote { .. } => Ok(ElabResult::Skipped),
            SurfaceDecl::Prelude { .. } => {
                if crate::source_prelude::is_bare_module(self.env) && self.env.num_constants() == 0 {
                    Ok(ElabResult::Skipped)
                } else {
                    Err(ElabError::ParseError("prelude requires a fresh module environment without implicit Init".to_owned()))
                }
            }
            SurfaceDecl::RawDecl { content, .. } => Err(ElabError::ParseError(format!(
                "parser recovery produced raw declaration: {content}"
            ))),
        }
    }
}

/// Apply an `include` / `omit` command to a block's forced-in variable names.
///
/// Neither command can name a variable into existence — the name must already
/// be a section `variable` for
/// [`crate::section_var_selection::select_section_binders`] to have anything to
/// include.
fn apply_include_omit(included: &mut Vec<SurfaceName>, decl: &SurfaceDecl) {
    match decl {
        SurfaceDecl::IncludeVars { names, .. } => {
            for name in names {
                if !included.iter().any(|n| n == name) {
                    included.push(name.clone());
                }
            }
        }
        SurfaceDecl::OmitVars { names, .. } => {
            included.retain(|n| !names.contains(n));
        }
        _ => {}
    }
}

/// The operand variable a tactic macro's template writes for the pattern
/// variable `name`: the identifier `«$name»` (see [`rewrite_tactic_antiquots`]).
fn tactic_operand_variable(name: &SurfaceName) -> SurfaceName {
    SurfaceName::component(
        format!("${}", name.component_text().unwrap_or_default()),
        true,
    )
}

/// Rewrite the pattern-bound antiquotation references of a tactic- or
/// conv-quotation body so the body parses with the plain tactic grammar:
/// each `$x` becomes the identifier `«$x»` ([`tactic_operand_variable`]),
/// which no other identifier of the quotation spells — a bare `x` in the
/// quotation is the TEMPLATE's `x`, never the operand (Lean: `$x + x` is the
/// operand plus the template's own `x✝`). The body is then a template over
/// those variables, which every use instantiates with the call's arguments.
/// An antiquotation that is NOT pattern-bound — including `$(…)` splices —
/// and a quotation that already writes `«$` return `None`, so the caller
/// rejects loudly rather than registering a macro that would mis-expand.
fn rewrite_tactic_antiquots(body: &str, bound: &[&SurfaceName]) -> Option<String> {
    if body.contains("«$") {
        return None;
    }
    let mut out = String::with_capacity(body.len());
    let mut rest = body;
    while let Some(pos) = rest.find('$') {
        out.push_str(&rest[..pos]);
        let after = &rest[pos + 1..];
        let ident_len = after
            .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .unwrap_or(after.len());
        let name = &after[..ident_len];
        let parsed = clean_parser::parse_name(name).ok()?;
        if name.is_empty() || !bound.contains(&&parsed) {
            return None;
        }
        out.push_str("«$");
        out.push_str(name);
        out.push('»');
        rest = &after[ident_len..];
    }
    out.push_str(rest);
    Some(out)
}

/// Decompose a category-headed `macro_rules` arm pattern body (`kw $a …`)
/// into `SyntaxPatternItem`s: a leading keyword literal, then only plain
/// antiquotations. Anything richer (interspersed literals, `$(…)` splices,
/// nested syntax) needs a custom-grammar re-parse that is not yet available —
/// reject loudly rather than registering a dead arm. Shared by the tactic and
/// conv arm routes; `category` ("tactic" / "conv") appears only in
/// diagnostics.
fn macro_rules_arm_pattern_items(
    pat_body: &str,
    category: &str,
) -> Result<Vec<SyntaxPatternItem>, ElabError> {
    let mut tokens = pat_body.split_whitespace();
    let Some(keyword) = tokens.next() else {
        return Err(ElabError::MacroError(format!(
            "{category} macro_rules pattern `({category}| …)` has no keyword"
        )));
    };
    let keyword_starts_ident = keyword
        .chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_');
    let keyword_is_ident = keyword_starts_ident
        && keyword
            .chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?'));
    if !keyword_is_ident {
        return Err(ElabError::MacroError(format!(
            "{category} macro_rules pattern must start with a keyword identifier, got \
             `{keyword}` (supported shape: `({category}| kw $a …)`)"
        )));
    }
    let mut items = vec![SyntaxPatternItem::Literal(keyword.to_string())];
    for token in tokens {
        let antiquot = token.strip_prefix('$').filter(|name| {
            !name.is_empty()
                && name
                    .chars()
                    .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\''))
        });
        let Some(name) = antiquot else {
            return Err(ElabError::MacroError(format!(
                "{category} macro_rules pattern argument `{token}` is not a plain \
                 antiquotation (supported shape: `({category}| kw $a …)`)"
            )));
        };
        items.push(SyntaxPatternItem::Variable {
            name: clean_parser::parse_name(name)
                .map_err(|err| ElabError::MacroError(err.to_string()))?,
            category: None,
        });
    }
    Ok(items)
}

/// Build the simple-entry handler for a tactic elaborator.
///
/// The simple handler is the fallback that fires only if no executable compound
/// handler is registered (i.e. the body is a deferred shape such as a `do`-block
/// monadic body). It reports an honest error — a static `throwError` message
/// when present, otherwise an "unsupported body" diagnostic listing the bound
/// variables — and never fabricates success.
fn simple_unsupported_handler(
    name: String,
    bound_names: Vec<SurfaceName>,
    body: &SurfaceExpr,
) -> crate::tactic::TacticHandler {
    let static_message = find_throw_error_message(body);
    Arc::new(move |_ps, args| {
        let detail = match &static_message {
            Some(message) => message.clone(),
            None if bound_names.is_empty() => {
                format!("unsupported tactic elaborator body for `{name}`")
            }
            None => format!(
                "unsupported tactic elaborator body for `{name}` (bound: {}; received {} argument(s))",
                bound_names.iter().map(ToString::to_string).collect::<Vec<_>>().join(", "),
                args.len()
            ),
        };
        Err(TacticError::ElaborationFailed { detail })
    })
}

/// A bound variable inside a tactic `elab_rules` pattern.
struct TacticElabBoundVar {
    name: SurfaceName,
    category: Option<String>,
}

/// A trailing repetition variable (`xs:ident*` / `xs:term*`) in a tactic or
/// term `elab` pattern. Phase 6 supports a SINGLE trailing repetition; the var
/// binds the entire variadic tail of the call-site arguments as a LIST.
struct TacticElabRepetition {
    name: SurfaceName,
    category: Option<String>,
}

/// A tactic `elab_rules` pattern decomposed into its keyword, the fixed (flat)
/// bound vars, and an optional single TRAILING repetition variable.
struct TacticElabPattern {
    name: String,
    bound_vars: Vec<TacticElabBoundVar>,
    /// `Some` when the pattern ends in a single repetition var (`xs:ident*` or
    /// `xs:term*`). `None` for the flat (Phases 1-5) shape.
    repetition: Option<TacticElabRepetition>,
}

/// Decompose an `elab_rules` tactic pattern into a leading keyword literal, the
/// bound term/ident antiquotations that follow it, and (Phase 6) an optional
/// single TRAILING repetition variable.
///
/// Categorized repetition is carried by `SyntaxPatternItem::Repetition`, not
/// inferred from opaque tokens or literal underscores. The executable bridge
/// supports one trailing zero-or-more ident/term repetition without separators.
///
/// Returns `None` (deferred) for patterns that are not a single leading literal
/// followed by plain `Variable` items and at most one trailing repetition — i.e.
/// non-trailing/multiple repetitions, optional groups, bare category references,
/// precedence specifiers, or interspersed literals. Those require a full
/// custom-grammar re-parse that is not yet available.
fn parse_tactic_elab_pattern(pattern: &[SyntaxPatternItem]) -> Option<TacticElabPattern> {
    let (first, rest) = pattern.split_first()?;
    let SyntaxPatternItem::Literal(name) = first else {
        return None;
    };

    // Consume only the parser's explicit repetition structure.
    let (rest, repetition) = split_trailing_repetition(rest);

    let mut bound_vars = Vec::with_capacity(rest.len());
    for item in rest {
        match item {
            SyntaxPatternItem::Variable { name, category } => {
                bound_vars.push(TacticElabBoundVar {
                    name: name.clone(),
                    category: category.clone(),
                });
            }
            // Anything more structured than a flat variable list is deferred.
            _ => return None,
        }
    }
    Some(TacticElabPattern {
        name: name.clone(),
        bound_vars,
        repetition,
    })
}

/// Split the supported structural repetition off a tactic pattern's tail.
/// Unsupported quantifiers, separators and groups remain deferred.
fn split_trailing_repetition(
    rest: &[SyntaxPatternItem],
) -> (&[SyntaxPatternItem], Option<TacticElabRepetition>) {
    let Some((
        SyntaxPatternItem::Repetition {
            pattern,
            separator: None,
            at_least_one: false,
        },
        prefix,
    )) = rest.split_last()
    else {
        return (rest, None);
    };
    match pattern.as_slice() {
        [SyntaxPatternItem::Variable {
            name,
            category: Some(category),
        }] if matches!(category.as_str(), "ident" | "term") => (
            prefix,
            Some(TacticElabRepetition {
                name: name.clone(),
                category: Some(category.clone()),
            }),
        ),
        _ => (rest, None),
    }
}

/// Choose the parser-level argument pattern for a tactic elaborator from its
/// bound variables and optional trailing repetition variable. `term`-category
/// vars map to term/expr argument parsing; `ident`-category vars map to
/// identifier-list parsing.
///
/// Phase 6: a trailing repetition variable (`xs:ident*` / `xs:term*`) makes the
/// tactic VARIADIC, so the parser must consume a list. An `ident` repetition (or
/// an all-ident pattern) parses as an identifier list; anything else falls back
/// to the generic expression list. Both list patterns already accept "zero or
/// more" call-site arguments, which is exactly the variadic shape.
/// The result of classifying a flat bound-variable list for optional patterns.
enum OptionalClassification {
    /// The pattern is tractable. The payload is `true` iff the FINAL bound
    /// variable is an optional (`x:term?`) binder.
    Tractable(bool),
    /// The pattern has an optional marker (`?`) on a NON-trailing binder, which
    /// the positional substitute-and-reelaborate bridge cannot represent. Defer.
    DeferNonTrailingOptional,
}

/// True iff a category string carries the optional-pattern suffix `?`
/// (e.g. `"term?"` for `x:term?`). The parser appends `?` to the category of an
/// optional antiquotation rather than emitting a separate marker item.
fn category_is_optional(category: Option<&String>) -> bool {
    category.is_some_and(|c| c.ends_with('?'))
}

/// Classify a flat (non-repetition) bound-variable list for optional-binder
/// support.
///
/// Recognizes a SINGLE trailing optional binder (`x:term?`): the last variable's
/// category ends in `?` and no earlier variable does. Returns
/// `Tractable(false)` when there is no optional binder, `Tractable(true)` when
/// exactly the trailing binder is optional, and `DeferNonTrailingOptional` when
/// any non-trailing binder carries the `?` suffix (the positional bridge cannot
/// bind a present argument after an absent hole).
fn classify_optional_trailing(bound_vars: &[TacticElabBoundVar]) -> OptionalClassification {
    let Some((last, prefix)) = bound_vars.split_last() else {
        return OptionalClassification::Tractable(false);
    };
    // An optional marker on any non-trailing binder is not tractable.
    if prefix
        .iter()
        .any(|v| category_is_optional(v.category.as_ref()))
    {
        return OptionalClassification::DeferNonTrailingOptional;
    }
    OptionalClassification::Tractable(category_is_optional(last.category.as_ref()))
}

fn arg_pattern_for_bound_vars(
    bound_vars: &[TacticElabBoundVar],
    repetition: Option<&TacticElabRepetition>,
) -> TacticArgPattern {
    let all_fixed_ident = bound_vars
        .iter()
        .all(|v| v.category.as_deref() == Some("ident"));

    if let Some(rep) = repetition {
        let rep_ident = rep.category.as_deref() == Some("ident");
        if all_fixed_ident && rep_ident {
            return TacticArgPattern::IdentList;
        }
        // Mixed or term repetition: parse a generic expression list.
        return TacticArgPattern::ExprList;
    }

    if bound_vars.is_empty() {
        return TacticArgPattern::Nullary;
    }
    if all_fixed_ident {
        return TacticArgPattern::IdentList;
    }
    if bound_vars.len() == 1 {
        // A single non-ident variable (typically `term`) is a single term arg.
        return TacticArgPattern::TermArg;
    }
    // Multiple / mixed variables fall back to generic expression-list parsing.
    TacticArgPattern::ExprList
}

fn find_throw_error_message(expr: &SurfaceExpr) -> Option<String> {
    match expr {
        SurfaceExpr::Do(_, elems) => elems.iter().find_map(find_throw_error_message_in_do_elem),
        SurfaceExpr::App(_, func, args) => {
            if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name.is_unescaped_component("throwError"))
            {
                return args.first().and_then(string_arg);
            }
            find_throw_error_message(func).or_else(|| {
                args.iter()
                    .find_map(|arg| find_throw_error_message(&arg.expr))
            })
        }
        // A tactic-category body is parsed as a `by` block; a deferred
        // `do`-notation body appears as a `Term(Do(..))` tactic. Descend through
        // the wrapped term tactics so a static `throwError` message still
        // surfaces in the deferred-handler diagnostic.
        SurfaceExpr::ByTactic(_, tactics) => tactics.iter().find_map(|tac| match tac {
            SurfaceTactic::Term(_, inner) => find_throw_error_message(inner),
            _ => None,
        }),
        _ => None,
    }
}

fn find_throw_error_message_in_do_elem(elem: &DoElem) -> Option<String> {
    match elem {
        DoElem::Expr(_, expr) | DoElem::Return(_, expr) => find_throw_error_message(expr),
        DoElem::Bind(_, _, expr)
        | DoElem::Let(_, _, expr)
        | DoElem::Have(_, _, expr)
        | DoElem::LetMut(_, _, expr) => find_throw_error_message(expr),
        DoElem::LetRec(_, defs) => defs
            .iter()
            .find_map(|(_, expr)| find_throw_error_message(expr)),
        DoElem::If(_, cond, then_elems, else_elems)
        | DoElem::IfDecidable(_, _, cond, then_elems, else_elems) => find_throw_error_message(cond)
            .or_else(|| {
                then_elems
                    .iter()
                    .find_map(find_throw_error_message_in_do_elem)
            })
            .or_else(|| {
                else_elems
                    .as_ref()
                    .and_then(|elems| elems.iter().find_map(find_throw_error_message_in_do_elem))
            }),
        DoElem::IfLet(_, _, scrutinee, then_elems, else_elems) => {
            find_throw_error_message(scrutinee)
                .or_else(|| {
                    then_elems
                        .iter()
                        .find_map(find_throw_error_message_in_do_elem)
                })
                .or_else(|| {
                    else_elems.as_ref().and_then(|elems| {
                        elems.iter().find_map(find_throw_error_message_in_do_elem)
                    })
                })
        }
        DoElem::For(_, _, collection, body) => find_throw_error_message(collection)
            .or_else(|| body.iter().find_map(find_throw_error_message_in_do_elem)),
        DoElem::Match(_, discrs, arms) => {
            discrs
                .iter()
                .find_map(find_throw_error_message)
                .or_else(|| {
                    arms.iter()
                        .flat_map(|arm| arm.body.iter())
                        .find_map(find_throw_error_message_in_do_elem)
                })
        }
        DoElem::TryCatch(_, body, catches, finally_body) => body
            .iter()
            .find_map(find_throw_error_message_in_do_elem)
            .or_else(|| {
                catches
                    .iter()
                    .flat_map(|catch| catch.body.iter())
                    .find_map(find_throw_error_message_in_do_elem)
            })
            .or_else(|| {
                finally_body
                    .as_ref()
                    .and_then(|elems| elems.iter().find_map(find_throw_error_message_in_do_elem))
            }),
        DoElem::LetElse(_, _, expr, fallback) | DoElem::LetExpr(_, _, expr, _, fallback) => {
            find_throw_error_message(expr).or_else(|| {
                fallback
                    .iter()
                    .find_map(find_throw_error_message_in_do_elem)
            })
        }
        DoElem::Repeat(_, body) => body.iter().find_map(find_throw_error_message_in_do_elem),
        DoElem::While(_, cond, body) => find_throw_error_message(cond)
            .or_else(|| body.iter().find_map(find_throw_error_message_in_do_elem)),
        DoElem::DbgTrace(_, expr)
        | DoElem::Reassign(_, _, expr)
        | DoElem::PatternReassign(_, _, expr) => find_throw_error_message(expr),
        DoElem::Break(_) | DoElem::Continue(_) => None,
    }
}

fn string_arg(arg: &SurfaceArg) -> Option<String> {
    match &arg.expr {
        SurfaceExpr::Lit(_, SurfaceLit::String(message)) => Some(message.clone()),
        _ => None,
    }
}

/// What [`ElabCtx::declared_surface_name`] finds a source declaration
/// introduces.
pub(super) enum DeclaredSurfaceName<'a> {
    /// One declared name, as written.
    One(&'a SurfaceName),
    /// A `mutual` block: its members declare the names.
    Block(&'a [SurfaceDecl]),
    /// No declared name (`example`, a command).
    None,
}

/// The declaration kinds whose `private` names get Lean's module-local kernel
/// name. Staged (`designs/2026-10-08-private-name-mangling.md`): B1 mangles
/// theorems and axioms, B2 definitions (`def`, `abbrev`, `opaque`, `partial`,
/// `instance`, `mutual` defs and the auxiliaries derived from them), B3 the
/// inductive families (`inductive`, `structure`, `class`, a `mutual`
/// inductive block — constructors, recursors and projections inherit the
/// prefix); `coinductive`, whose greatest-fixpoint lowering mints its own
/// names, keeps the plain name plus the private mark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PrivateNameKind {
    /// `theorem` (also a `mutual` member and a staged header).
    Theorem,
    /// `axiom`.
    Axiom,
    /// `def` / `abbrev` / `opaque` / `partial def` / `instance`, a `mutual`
    /// def member and a staged header of one (B2).
    Definition,
    /// `inductive` / `structure` / `class` and a `mutual` inductive block
    /// (B3): the type's name, and so every name derived from it.
    Family,
    /// Every other kind (`coinductive`).
    NotYetMangled,
}

/// `Some(kind)` when `modifiers` make the declaration `private`.
pub(crate) fn private_kind_of(
    modifiers: &clean_parser::DeclModifiers,
    kind: PrivateNameKind,
) -> Option<PrivateNameKind> {
    (modifiers.visibility == clean_parser::Visibility::Private).then_some(kind)
}

/// Whether a `private` declaration of `kind` is registered under its mangled
/// name.
pub(crate) const fn mangles_private_names(kind: PrivateNameKind) -> bool {
    match kind {
        PrivateNameKind::Theorem
        | PrivateNameKind::Axiom
        | PrivateNameKind::Definition
        | PrivateNameKind::Family => true,
        PrivateNameKind::NotYetMangled => false,
    }
}

#[cfg(test)]
mod elab_pattern_tests {
    use super::*;

    fn lit(s: &str) -> SyntaxPatternItem {
        SyntaxPatternItem::Literal(s.to_owned())
    }

    fn var(name: SurfaceName, category: Option<&str>) -> SyntaxPatternItem {
        SyntaxPatternItem::Variable {
            name,
            category: category.map(str::to_owned),
        }
    }

    fn source_pattern(source: &str) -> Vec<SyntaxPatternItem> {
        match clean_parser::parse_decl(source).expect("actual elab source should parse") {
            SurfaceDecl::Elab { pattern, .. } => pattern,
            other => panic!("expected an elab declaration, got {other:?}"),
        }
    }

    /// The actual parser carries `xs:ident*` as structural repetition.
    #[test]
    fn test_parse_pattern_recognizes_star_repetition() {
        let pattern = source_pattern(r#"elab "intros2" xs:ident* : tactic => intro xs"#);
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.name, "intros2");
        assert!(parsed.bound_vars.is_empty(), "no fixed vars before the rep");
        let rep = parsed.repetition.expect("should have a repetition var");
        assert_eq!(rep.name, SurfaceName::generated_path("xs"));
        assert_eq!(rep.category.as_deref(), Some("ident"));
        let old_markers = vec![
            lit("intros2"),
            var(SurfaceName::generated_path("xs"), Some("ident")),
            lit("_"),
        ];
        assert!(parse_tactic_elab_pattern(&old_markers).is_none());
    }

    /// A separated repetition is preserved by the parser and deferred by this
    /// bounded executable bridge, which supports an unseparated trailing star.
    #[test]
    fn test_parse_pattern_defers_comma_star_repetition() {
        let pattern = source_pattern(r#"elab "mk" xs:term,* : tactic => exact Nat.zero"#);
        assert!(matches!(
            pattern.last(),
            Some(SyntaxPatternItem::Repetition {
                separator: Some(separator),
                at_least_one: false,
                ..
            }) if separator == ","
        ));
        assert!(parse_tactic_elab_pattern(&pattern).is_none());
    }

    /// A fixed prefix var followed by a trailing repetition:
    /// `elab "kw" x:term xs:ident*` -> one fixed var `x`, repetition `xs`.
    #[test]
    fn test_parse_pattern_fixed_prefix_plus_repetition() {
        let pattern = source_pattern(r#"elab "kw" x:term xs:ident* : tactic => intro xs"#);
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, SurfaceName::generated_path("x"));
        assert_eq!(
            parsed.repetition.expect("trailing repetition").name,
            SurfaceName::generated_path("xs")
        );
    }

    /// A flat pattern (no repetition) must parse byte-for-byte as before: all
    /// items become fixed bound vars and `repetition` is `None`.
    #[test]
    fn test_parse_pattern_flat_has_no_repetition() {
        let pattern = vec![
            lit("myexact"),
            var(SurfaceName::generated_path("e"), Some("term")),
        ];
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, SurfaceName::generated_path("e"));
        assert!(
            parsed.repetition.is_none(),
            "flat pattern must not be classified as repetition"
        );
    }

    /// A trailing bare (uncategorized) variable followed by a marker is NOT a
    /// repetition (the guard requires an explicit category), so it is deferred.
    #[test]
    fn test_parse_pattern_uncategorized_trailing_var_not_repetition() {
        // `[Literal, Variable{xs, None}, Literal("_")]` — the var has no category.
        let pattern = vec![
            lit("kw"),
            var(SurfaceName::generated_path("xs"), None),
            lit("_"),
        ];
        let parsed = parse_tactic_elab_pattern(&pattern);
        // The `_` is a flat literal item, which the loop rejects -> deferred.
        assert!(
            parsed.is_none(),
            "uncategorized trailing var + marker should defer, not be a repetition"
        );
    }

    /// A trailing optional binder (`x:term?`) is recognized: the parser carries
    /// the `?` as a category suffix (`"term?"`), and `classify_optional_trailing`
    /// reports `Tractable(true)`.
    #[test]
    fn test_classify_optional_trailing_single_optional() {
        let vars = vec![TacticElabBoundVar {
            name: SurfaceName::generated_path("x"),
            category: Some("term?".to_owned()),
        }];
        assert!(
            matches!(
                classify_optional_trailing(&vars),
                OptionalClassification::Tractable(true)
            ),
            "a single trailing `x:term?` must be a tractable optional binder"
        );
    }

    /// A mandatory prefix followed by a trailing optional binder
    /// (`a:term b:term?`) is tractable with the optional flag set.
    #[test]
    fn test_classify_optional_trailing_prefix_then_optional() {
        let vars = vec![
            TacticElabBoundVar {
                name: SurfaceName::generated_path("a"),
                category: Some("term".to_owned()),
            },
            TacticElabBoundVar {
                name: SurfaceName::generated_path("b"),
                category: Some("term?".to_owned()),
            },
        ];
        assert!(
            matches!(
                classify_optional_trailing(&vars),
                OptionalClassification::Tractable(true)
            ),
            "a mandatory prefix with a trailing optional must be tractable-optional"
        );
    }

    /// A flat all-mandatory pattern is `Tractable(false)` (no optional binder).
    #[test]
    fn test_classify_optional_trailing_all_mandatory() {
        let vars = vec![TacticElabBoundVar {
            name: SurfaceName::generated_path("e"),
            category: Some("term".to_owned()),
        }];
        assert!(
            matches!(
                classify_optional_trailing(&vars),
                OptionalClassification::Tractable(false)
            ),
            "an all-mandatory pattern has no optional trailing binder"
        );
    }

    /// An optional marker on a NON-trailing binder (`a:term? b:term`) is NOT
    /// tractable for the positional bridge — it must be deferred.
    #[test]
    fn test_classify_optional_trailing_non_trailing_optional_defers() {
        let vars = vec![
            TacticElabBoundVar {
                name: SurfaceName::generated_path("a"),
                category: Some("term?".to_owned()),
            },
            TacticElabBoundVar {
                name: SurfaceName::generated_path("b"),
                category: Some("term".to_owned()),
            },
        ];
        assert!(
            matches!(
                classify_optional_trailing(&vars),
                OptionalClassification::DeferNonTrailingOptional
            ),
            "a `?` on a non-trailing binder must defer (positional bridge cannot skip a hole)"
        );
    }

    /// An empty bound-variable list (nullary keyword) is `Tractable(false)`.
    #[test]
    fn test_classify_optional_trailing_empty_is_tractable_non_optional() {
        assert!(
            matches!(
                classify_optional_trailing(&[]),
                OptionalClassification::Tractable(false)
            ),
            "a nullary keyword has no optional binder"
        );
    }

    /// The argument pattern for an `ident` repetition (with all-ident fixed
    /// prefix) is `IdentList`; a `term` repetition falls back to `ExprList`.
    #[test]
    fn test_arg_pattern_for_repetition() {
        let ident_rep = TacticElabRepetition {
            name: SurfaceName::generated_path("xs"),
            category: Some("ident".to_owned()),
        };
        assert_eq!(
            arg_pattern_for_bound_vars(&[], Some(&ident_rep)),
            TacticArgPattern::IdentList
        );
        let term_rep = TacticElabRepetition {
            name: SurfaceName::generated_path("xs"),
            category: Some("term".to_owned()),
        };
        assert_eq!(
            arg_pattern_for_bound_vars(&[], Some(&term_rep)),
            TacticArgPattern::ExprList
        );
    }
}
