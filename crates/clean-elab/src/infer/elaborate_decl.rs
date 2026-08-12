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

use crate::tactic::{TacticArgPattern, TacticEntry, TacticError};
use crate::ElabError;
use clean_parser::{DoElem, SurfaceArg, SurfaceDecl, SurfaceExpr, SurfaceLit, SyntaxPatternItem};
use std::sync::Arc;

use super::{ElabCtx, ElabResult};

impl<'a> ElabCtx<'a> {
    pub(super) fn qualify_name(&self, name: &str) -> String {
        if self.namespace_prefix.is_empty() {
            name.to_owned()
        } else {
            format!("{}.{}", self.namespace_prefix, name)
        }
    }

    fn elab_namespace(
        &mut self,
        name: &str,
        decls: &[SurfaceDecl],
    ) -> Result<ElabResult, ElabError> {
        let prev_prefix = std::mem::take(&mut self.namespace_prefix);
        self.namespace_prefix = if prev_prefix.is_empty() {
            name.to_owned()
        } else {
            format!("{prev_prefix}.{name}")
        };
        // Update NamespaceState so that name resolution inside the block
        // can qualify bare identifiers with the current namespace prefix.
        // Without this, elab_ident cannot resolve `Ty` as `TMir.Ty` inside
        // `namespace TMir { ... }`. Fixes #3410 (UnknownFVar in namespace).
        self.namespace_state
            .enter_namespace(clean_kernel::name::Name::from_string(name));
        // A namespace block is an alias-scope boundary (Lean pushes a Scope per
        // `namespace`; `end` pops it, discarding its `open` decls —
        // `Lean/Elab/BuiltinCommand.lean` `elabNamespace`/`elabEnd`). Without
        // this, an `open` inside the block leaked file-wide (gap sweep B13).
        // `export` aliases intentionally SURVIVE the pop: they are inserted
        // scope-immune (`insert_alias_unscoped`), mirroring Lean's permanent
        // env alias table.
        self.namespace_state.push_scope();
        let mut results = Vec::new();
        for inner in decls {
            let result = match self.elab_decl(inner) {
                Ok(r) => r,
                Err(e) => {
                    self.namespace_state.pop_scope();
                    self.namespace_state.exit_namespace();
                    self.namespace_prefix = prev_prefix;
                    return Err(e);
                }
            };
            if !matches!(result, ElabResult::Skipped) {
                results.push(result);
            }
        }
        self.namespace_state.pop_scope();
        self.namespace_state.exit_namespace();
        self.namespace_prefix = prev_prefix;
        Ok(ElabResult::Multiple(results))
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
        // SOUNDNESS (#section-drops-all-but-last): this used to keep only `last_result`, so in a
        // section with several declarations ONLY THE LAST was returned — and since registration
        // happens on the returned `ElabResult`, every non-final declaration silently vanished
        // (elaborated but never registered; no error). Collect EVERY non-skipped result into
        // `ElabResult::Multiple`, which `register_elab_result` registers element-by-element —
        // exactly how `elab_namespace` (above) already reports its inner declarations.
        let mut results: Vec<ElabResult> = Vec::new();
        for decl in decls {
            let used = used_section_binders(&self.section_binder_stack, decl);
            let processed = if used.is_empty() {
                None
            } else {
                let mut fc = crate::FileContext::new();
                fc.add_variables(&used);
                Some(crate::preprocess::preprocess_decl_with_context(
                    decl, &mut fc,
                ))
            };
            match self.elab_decl_inner(processed.as_ref().unwrap_or(decl)) {
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
                    let short = crate::preprocess_ext::decl_name(decl).unwrap_or("");
                    results.push(ElabResult::Failed {
                        name: self.qualify_name(short),
                        decl: Box::new(decl.clone()),
                        error: Box::new(e),
                    });
                }
            }
            if let SurfaceDecl::Variable { binders, .. } = decl {
                self.section_binder_stack.extend(binders.iter().cloned());
            }
        }
        self.local_options = saved_options;
        self.macro_ctx = saved_macro_ctx;
        self.section_binder_stack.truncate(saved_section_binders);
        self.namespace_state.pop_scope();
        // Preserve the historical shape for degenerate sections (empty / commands-only → Skipped;
        // exactly one declaration → that declaration) so downstream matchers keep working; the
        // fix is that MULTIPLE declarations now ALL surface (and thus all register).
        Ok(match results.len() {
            0 => ElabResult::Skipped,
            1 => results.pop().expect("len == 1"),
            _ => ElabResult::Multiple(results),
        })
    }

    fn elab_tactic_elab_decl(
        &mut self,
        pattern: &[SyntaxPatternItem],
        category: &str,
        body: &SurfaceExpr,
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
        let bound_names: Vec<String> = bound_vars.into_iter().map(|v| v.name).collect();
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
        // (`xs:ident*` / `xs:term,*`), register the VARIADIC handler instead. It
        // binds the fixed prefix args 1:1, collects the remaining call-site args
        // into a list for the repetition var, and expands each body tactic that
        // mentions the repetition var once per list element. Soundness is
        // unchanged: the expanded sequence is still delegated to the existing
        // tactic evaluator (no new way to close a goal).
        if let SurfaceExpr::ByTactic(_, tactics) = body {
            if super::user_tactic::is_executable_tactic_body(tactics) {
                if let Some(rep_name) = repetition_name {
                    self.tactic_registry.register_compound(
                        super::user_tactic::build_variadic_tactic_handler(
                            name,
                            bound_names,
                            rep_name,
                            tactics.clone(),
                        ),
                    );
                } else {
                    self.tactic_registry.register_compound(
                        super::user_tactic::build_user_tactic_handler(
                            name,
                            bound_names,
                            tactics.clone(),
                        ),
                    );
                }
            }
        }
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
        let bound_names: Vec<String> = bound_vars.into_iter().map(|v| v.name).collect();
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
        // Enable auto-implicits for declaration elaboration (#164)
        // Save previous state to restore after (for nested calls)
        let prev_in_decl_context = self.in_decl_context;
        self.in_decl_context = true;

        let result = self
            .elab_decl_inner(decl)
            .map(|result| self.canonicalize_levels_in_elab_result(result))
            // B07: rewrite `Pure.pure`/`Bind.bind` stub applications over
            // concrete instance-resolvable monads into instance-projected
            // form so the kernel can value-certify do-notation output via
            // ordinary delta + proj-of-mk iota (elab_monad_materialize.rs).
            .and_then(|result| self.materialize_monad_instances_in_elab_result(result));

        // Restore context state after elaboration
        self.in_decl_context = prev_in_decl_context;
        result
    }

    /// Inner implementation of declaration elaboration
    pub(super) fn elab_decl_inner(&mut self, decl: &SurfaceDecl) -> Result<ElabResult, ElabError> {
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
                self.universe_params = universe_params.clone();
                let qname = self.qualify_name(name);
                self.elab_inductive(
                    &qname,
                    universe_params,
                    binders,
                    ty,
                    ctors,
                    deriving,
                    modifiers,
                )
            }

            // Coinductive (#191): parsed but NOT semantically supported yet.
            // Fail closed: elaborating a greatest-fixpoint declaration through
            // `elab_inductive` would silently mint the least fixpoint (with an
            // induction principle it must not have) — proofs would check while
            // meaning something other than what the user wrote. The planned
            // closure is a gfp lowering over complete lattices (Lean 4.25-style
            // coinductive predicates), not kernel codata; until that lands this
            // arm must reject.
            SurfaceDecl::Coinductive { name, .. } => {
                let qname = self.qualify_name(name);
                Err(ElabError::Unsupported {
                    feature: format!(
                        "coinductive declaration `{qname}`: greatest-fixpoint \
                         semantics are not implemented; refusing to elaborate \
                         it as an inductive (least fixpoint)"
                    ),
                })
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
                let qname = self.qualify_name(name);
                self.elab_structure(
                    &qname,
                    universe_params,
                    binders,
                    extends,
                    ty.as_deref(),
                    ctor_name.as_deref(),
                    fields,
                    deriving,
                    modifiers,
                    super::elab_structure::StructureKind::Structure,
                )
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
                let qname = self.qualify_name(name);
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
                ..
            } => {
                self.universe_params = universe_params.clone();
                let qname = name.as_ref().map(|n| self.qualify_name(n));
                self.elab_instance(
                    qname.as_deref(),
                    universe_params,
                    binders,
                    class_type,
                    fields,
                    *priority,
                    modifiers,
                )
            }

            // Macro-related declarations: register with macro context
            SurfaceDecl::Syntax {
                name,
                precedence,
                pattern,
                category,
                ..
            } => {
                self.macro_ctx
                    .register_syntax(name.as_deref(), *precedence, pattern, category)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::DeclareSyntaxCat { name, .. } => {
                self.macro_ctx.register_syntax_category(name);
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Macro {
                pattern,
                category,
                expansion,
                ..
            } => {
                self.macro_ctx
                    .register_macro(pattern, category, expansion)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::MacroRules { name, arms, .. } => {
                self.macro_ctx
                    .register_macro_rules(name.as_deref(), arms)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }
            SurfaceDecl::Notation {
                kind,
                precedence,
                pattern,
                expansion,
                scope,
                ..
            } => {
                // `scoped notation` (Lean: active only when the declaring
                // namespace is opened / current — `Lean/Elab/Notation.lean`
                // attrKind `scoped`) has no honest implementation in the main
                // elaborate path: the macro registry has no namespace gating,
                // so registering it globally would ACTIVATE it in scopes where
                // Lean says it is invisible, and DROPPING it silently made its
                // token auto-bind at the use site (gap sweep B13,
                // namespaces_scoping/p10). Reject loudly — and thereby COUNT
                // it as a failed declaration — rather than silently dropping
                // it. (`open scoped Foo` remains a tolerated no-op: it merely
                // activates a namespace's scoped notations, of which clean
                // honors none, so it hides nothing and stays faithful to the
                // valid Lean program `open scoped Foo`.)
                if *scope == clean_parser::DeclScope::Scoped {
                    return Err(ElabError::Unsupported {
                        feature: "scoped notation (namespace-gated notation is not yet \
                                  implemented; the declaration cannot be honored honestly, so \
                                  it is rejected loudly rather than silently dropped)"
                            .to_string(),
                    });
                }
                // `local notation` and plain `notation` both register in the
                // macro context; section/namespace blocks snapshot-restore the
                // macro context, which bounds `local` to its block.
                self.macro_ctx
                    .register_notation(*kind, *precedence, pattern, expansion)
                    .map_err(|e| ElabError::MacroError(e.to_string()))?;
                Ok(ElabResult::Skipped)
            }

            SurfaceDecl::Check { expr, .. } => {
                let kernel_expr = self.elaborate(expr)?;
                let result = crate::commands::elab_check(self.env, &kernel_expr)?;
                Ok(ElabResult::Command(super::CommandOutput::Check(result)))
            }
            SurfaceDecl::Eval { expr, .. } => {
                let kernel_expr = self.elaborate(expr)?;
                let result = crate::commands::elab_eval(self.env, &kernel_expr)?;
                Ok(ElabResult::Command(super::CommandOutput::Eval(result)))
            }
            SurfaceDecl::Print { name, .. } => {
                let result = crate::commands::elab_print(self.env, name)?;
                Ok(ElabResult::Command(super::CommandOutput::Print(result)))
            }
            SurfaceDecl::Variable { binders, .. } => {
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
                // elaborated regardless of scoped-ness: `open scoped` affects only scoped
                // notations/attributes (which clean does not model), so for a scoped open the
                // body is elaborated WITHOUT bringing names into scope; a plain `open … in`
                // additionally opens the names for the body, as before.
                if let Some(inner) = body {
                    self.namespace_state.push_scope();
                    let open_result = if *scoped {
                        Ok(())
                    } else {
                        crate::namespace::process_open(self.env, paths, &mut self.namespace_state)
                            .map_err(|e| ElabError::Unsupported {
                                feature: e.to_string(),
                            })
                    };
                    let result = open_result.and_then(|()| self.elab_decl_inner(inner));
                    self.namespace_state.pop_scope();
                    return result;
                }
                if *scoped {
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
                let current_ns = if self.namespace_prefix.is_empty() {
                    None
                } else {
                    Some(self.namespace_prefix.as_str())
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
                let (ty_expr, val_expr) = match self.elab_def_body(binders, ty.as_deref(), val) {
                    Ok(pair) => pair,
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
                    crate::options_registry::validate_command_option_lenient(name, value.as_deref())?;
                if let Some(inner_decl) = body {
                    // Per-declaration scoping: `set_option ... in <decl>`
                    // Set the option, elaborate the inner decl, then remove it.
                    self.set_local_option(name.clone(), value.clone());
                    let result = self.elab_decl_inner(inner_decl);
                    // Remove the scoped option (best-effort — local options don't
                    // currently support removal, so we rely on the outer handler
                    // in lib.rs doing the real env-level restore).
                    result
                } else {
                    // Store option locally so it is visible within the current
                    // elaboration context (sections, namespaces). The file-scope
                    // handler in lib.rs persists options to Environment and
                    // FileContext for cross-declaration visibility.
                    self.set_local_option(name.clone(), value.clone());
                    Ok(ElabResult::Skipped)
                }
            }
            SurfaceDecl::Elab {
                pattern,
                category,
                body,
                ..
            } => self.elab_tactic_elab_decl(pattern, category, body),
            SurfaceDecl::Import { .. }
            | SurfaceDecl::UniverseDecl { .. }
            | SurfaceDecl::DerivingInstance { .. }
            | SurfaceDecl::DeclareAesopRuleSets { .. }
            // `library_note «title»` carries no checkable content — a no-op.
            | SurfaceDecl::LibraryNote { .. } => Ok(ElabResult::Skipped),
            SurfaceDecl::RawDecl { content, .. } => Err(ElabError::ParseError(format!(
                "parser recovery produced raw declaration: {content}"
            ))),
        }
    }
}

/// Free surface identifiers of a value declaration (binder types, result
/// type, value/proof, `where` bodies), plus the decl's own binder names.
///
/// Returns `None` for declaration kinds that never receive section-variable
/// binders (mirroring which kinds `preprocess` prepends variables to:
/// `Def`/`Theorem`/`Example`/`Instance`).
fn decl_free_surface_idents(
    decl: &SurfaceDecl,
) -> Option<(
    std::collections::HashSet<String>,
    std::collections::HashSet<String>,
)> {
    use crate::where_desugar_ext::collect_free_idents;
    let mut free = std::collections::HashSet::new();
    let collect_binders = |binders: &[clean_parser::SurfaceBinder],
                           free: &mut std::collections::HashSet<String>| {
        for b in binders {
            if let Some(ty) = &b.ty {
                free.extend(collect_free_idents(ty));
            }
        }
    };
    let own: std::collections::HashSet<String> = match decl {
        SurfaceDecl::Def {
            binders,
            ty,
            val,
            where_decls,
            ..
        } => {
            collect_binders(binders, &mut free);
            if let Some(ty) = ty {
                free.extend(collect_free_idents(ty));
            }
            free.extend(collect_free_idents(val));
            for w in where_decls {
                collect_binders(&w.binders, &mut free);
                if let Some(rt) = &w.ret_ty {
                    free.extend(collect_free_idents(rt));
                }
                free.extend(collect_free_idents(&w.body));
            }
            binders.iter().map(|b| b.name.clone()).collect()
        }
        SurfaceDecl::Theorem {
            binders,
            ty,
            proof,
            where_decls,
            ..
        } => {
            collect_binders(binders, &mut free);
            free.extend(collect_free_idents(ty));
            free.extend(collect_free_idents(proof));
            for w in where_decls {
                collect_binders(&w.binders, &mut free);
                if let Some(rt) = &w.ret_ty {
                    free.extend(collect_free_idents(rt));
                }
                free.extend(collect_free_idents(&w.body));
            }
            binders.iter().map(|b| b.name.clone()).collect()
        }
        SurfaceDecl::Example {
            binders, ty, val, ..
        } => {
            collect_binders(binders, &mut free);
            if let Some(ty) = ty {
                free.extend(collect_free_idents(ty));
            }
            free.extend(collect_free_idents(val));
            binders.iter().map(|b| b.name.clone()).collect()
        }
        SurfaceDecl::Instance {
            binders,
            class_type,
            fields,
            ..
        } => {
            collect_binders(binders, &mut free);
            free.extend(collect_free_idents(class_type));
            for f in fields {
                free.extend(collect_free_idents(&f.val));
            }
            binders.iter().map(|b| b.name.clone()).collect()
        }
        _ => return None,
    };
    Some((free, own))
}

/// The subset of section `variable` binders a declaration actually USES,
/// closed under type dependencies, in declaration order.
///
/// Lean includes a section variable in a declaration only when the
/// declaration mentions it (`Lean/Elab/MutualDef.lean` section-variable
/// inclusion); instance-implicit variables are additionally included when
/// their TYPE mentions an included variable (so `variable {α} [Add α]` adds
/// `[Add α]` to any decl that uses `α`). A decl binder with the same name
/// shadows the section variable.
fn used_section_binders(
    section_binders: &[clean_parser::SurfaceBinder],
    decl: &SurfaceDecl,
) -> Vec<clean_parser::SurfaceBinder> {
    use crate::where_desugar_ext::collect_free_idents;
    if section_binders.is_empty() {
        return Vec::new();
    }
    let Some((mut used, own_binders)) = decl_free_surface_idents(decl) else {
        return Vec::new();
    };
    for name in &own_binders {
        used.remove(name);
    }

    let mut include = vec![false; section_binders.len()];
    // Fixpoint: including a binder can make its type's free idents "used"
    // (dependency closure, e.g. `a : α` pulls in `α`), and an included
    // variable can activate an instance-implicit binder whose type mentions
    // it. The stack is small; loop until stable.
    loop {
        let mut changed = false;
        for (i, binder) in section_binders.iter().enumerate() {
            if include[i] {
                continue;
            }
            let directly_used = used.contains(&binder.name);
            let inst_activated = binder.info == clean_parser::SurfaceBinderInfo::Instance
                && binder
                    .ty
                    .as_ref()
                    .is_some_and(|ty| collect_free_idents(ty).iter().any(|n| used.contains(n)));
            if directly_used || inst_activated {
                include[i] = true;
                changed = true;
                used.insert(binder.name.clone());
                if let Some(ty) = &binder.ty {
                    used.extend(collect_free_idents(ty));
                }
            }
        }
        if !changed {
            break;
        }
    }

    section_binders
        .iter()
        .zip(include)
        .filter(|&(_, inc)| inc)
        .map(|(binder, _)| binder.clone())
        .collect()
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
    bound_names: Vec<String>,
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
                bound_names.join(", "),
                args.len()
            ),
        };
        Err(TacticError::ElaborationFailed { detail })
    })
}

/// A bound variable inside a tactic `elab_rules` pattern.
struct TacticElabBoundVar {
    name: String,
    category: Option<String>,
}

/// A trailing repetition variable (`xs:ident*` / `xs:term,*`) in a tactic or
/// term `elab` pattern. Phase 6 supports a SINGLE trailing repetition; the var
/// binds the entire variadic tail of the call-site arguments as a LIST.
struct TacticElabRepetition {
    name: String,
    category: Option<String>,
}

/// A tactic `elab_rules` pattern decomposed into its keyword, the fixed (flat)
/// bound vars, and an optional single TRAILING repetition variable.
struct TacticElabPattern {
    name: String,
    bound_vars: Vec<TacticElabBoundVar>,
    /// `Some` when the pattern ends in a single repetition var (`xs:ident*` or
    /// `xs:term,*`). `None` for the flat (Phases 1-5) shape.
    repetition: Option<TacticElabRepetition>,
}

/// Decompose an `elab_rules` tactic pattern into a leading keyword literal, the
/// bound term/ident antiquotations that follow it, and (Phase 6) an optional
/// single TRAILING repetition variable.
///
/// The surface parser does not emit `SyntaxPatternItem::Repetition` for the
/// categorized antiquotation forms `xs:ident*` and `xs:term,*` — the
/// `:category` suffix is consumed eagerly, so the trailing `*` (or `,*`) lands
/// as one (or two) bare `Literal("_")` marker items right after the categorized
/// `Variable`. Phase 6 recognizes exactly that shape: a final categorized
/// `Variable` immediately followed by one or two trailing `Literal("_")` markers
/// and nothing else. The marker(s) are stripped and the final variable is
/// promoted to a repetition var (1 marker = `cat*`, 2 markers = `cat,*`).
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

    // Phase 6: detect a single trailing repetition variable from its parser
    // residue (a categorized `Variable` followed by trailing `Literal("_")`
    // markers). Split the markers off the tail before the flat-var loop so the
    // flat path stays byte-for-byte identical when there is no repetition.
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

/// Split a trailing repetition var off the end of a pattern's item list.
///
/// Recognizes the parser residue for `xs:ident*` / `xs:term,*`: a categorized
/// `Variable` immediately followed by one or two `Literal("_")` marker items at
/// the very end of the slice. On a match, returns the prefix (everything before
/// the repetition var) and the promoted [`TacticElabRepetition`]. Otherwise
/// returns the slice unchanged with `None`, so non-repetition patterns are
/// untouched.
///
/// A bare (uncategorized) trailing `Variable` followed by markers is NOT treated
/// as a repetition here: the supported variadic forms always carry an explicit
/// category (`ident`/`term`), and keeping the guard tight avoids
/// mis-classifying an ordinary pattern that happens to end in a literal `_`.
fn split_trailing_repetition(
    rest: &[SyntaxPatternItem],
) -> (&[SyntaxPatternItem], Option<TacticElabRepetition>) {
    // Count the trailing `Literal("_")` markers (the residue of `*` / `,*`).
    let marker_count = rest
        .iter()
        .rev()
        .take_while(|item| matches!(item, SyntaxPatternItem::Literal(s) if s == "_"))
        .count();
    // `cat*` leaves 1 marker, `cat,*` leaves 2. More than that is not a shape
    // Phase 6 recognizes (defer); zero means no repetition.
    if marker_count == 0 || marker_count > 2 {
        return (rest, None);
    }
    let before_markers = &rest[..rest.len() - marker_count];
    let Some((last, prefix)) = before_markers.split_last() else {
        return (rest, None);
    };
    // The item immediately preceding the markers must be the repetition var: a
    // categorized antiquotation. (A literal there would mean the trailing `_`
    // markers are ordinary pattern literals, not a repetition suffix.)
    match last {
        SyntaxPatternItem::Variable {
            name,
            category: Some(category),
        } => (
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
/// Phase 6: a trailing repetition variable (`xs:ident*` / `xs:term,*`) makes the
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
            if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "throwError") {
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
            clean_parser::SurfaceTactic::Term(_, inner) => find_throw_error_message(inner),
            _ => None,
        }),
        _ => None,
    }
}

fn find_throw_error_message_in_do_elem(elem: &DoElem) -> Option<String> {
    match elem {
        DoElem::Expr(_, expr) | DoElem::Return(_, expr) => find_throw_error_message(expr),
        DoElem::Bind(_, _, expr) | DoElem::Let(_, _, expr) | DoElem::LetMut(_, _, expr) => {
            find_throw_error_message(expr)
        }
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

#[cfg(test)]
mod elab_pattern_tests {
    use super::*;

    fn lit(s: &str) -> SyntaxPatternItem {
        SyntaxPatternItem::Literal(s.to_owned())
    }

    fn var(name: &str, category: Option<&str>) -> SyntaxPatternItem {
        SyntaxPatternItem::Variable {
            name: name.to_owned(),
            category: category.map(str::to_owned),
        }
    }

    /// `elab "intros2" xs:ident*` parses (via the surface parser residue) to
    /// `[Literal("intros2"), Variable{xs, ident}, Literal("_")]`. The elab
    /// pattern parser must promote `xs` to a repetition var with no fixed vars.
    #[test]
    fn test_parse_pattern_recognizes_star_repetition() {
        let pattern = vec![lit("intros2"), var("xs", Some("ident")), lit("_")];
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.name, "intros2");
        assert!(parsed.bound_vars.is_empty(), "no fixed vars before the rep");
        let rep = parsed.repetition.expect("should have a repetition var");
        assert_eq!(rep.name, "xs");
        assert_eq!(rep.category.as_deref(), Some("ident"));
    }

    /// `elab "mk" xs:term,*` leaves TWO `_` markers (the `,` and the `*`). Both
    /// are stripped and `xs` is promoted to the single repetition var.
    #[test]
    fn test_parse_pattern_recognizes_comma_star_repetition() {
        let pattern = vec![lit("mk"), var("xs", Some("term")), lit("_"), lit("_")];
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        let rep = parsed.repetition.expect("comma-star is a repetition");
        assert_eq!(rep.name, "xs");
        assert_eq!(rep.category.as_deref(), Some("term"));
    }

    /// A fixed prefix var followed by a trailing repetition:
    /// `elab "kw" x:term xs:ident*` -> one fixed var `x`, repetition `xs`.
    #[test]
    fn test_parse_pattern_fixed_prefix_plus_repetition() {
        let pattern = vec![
            lit("kw"),
            var("x", Some("term")),
            var("xs", Some("ident")),
            lit("_"),
        ];
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, "x");
        assert_eq!(parsed.repetition.expect("trailing repetition").name, "xs");
    }

    /// A flat pattern (no repetition) must parse byte-for-byte as before: all
    /// items become fixed bound vars and `repetition` is `None`.
    #[test]
    fn test_parse_pattern_flat_has_no_repetition() {
        let pattern = vec![lit("myexact"), var("e", Some("term"))];
        let parsed = parse_tactic_elab_pattern(&pattern).expect("should parse");
        assert_eq!(parsed.bound_vars.len(), 1);
        assert_eq!(parsed.bound_vars[0].name, "e");
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
        let pattern = vec![lit("kw"), var("xs", None), lit("_")];
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
            name: "x".to_owned(),
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
                name: "a".to_owned(),
                category: Some("term".to_owned()),
            },
            TacticElabBoundVar {
                name: "b".to_owned(),
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
            name: "e".to_owned(),
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
                name: "a".to_owned(),
                category: Some("term?".to_owned()),
            },
            TacticElabBoundVar {
                name: "b".to_owned(),
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
            name: "xs".to_owned(),
            category: Some("ident".to_owned()),
        };
        assert_eq!(
            arg_pattern_for_bound_vars(&[], Some(&ident_rep)),
            TacticArgPattern::IdentList
        );
        let term_rep = TacticElabRepetition {
            name: "xs".to_owned(),
            category: Some("term".to_owned()),
        };
        assert_eq!(
            arg_pattern_for_bound_vars(&[], Some(&term_rep)),
            TacticArgPattern::ExprList
        );
    }
}
