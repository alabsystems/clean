// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection and qualified-name elaboration.
//!
//! Handles `SurfaceExpr::Proj` (dotted notation like `x.y`) including:
//! - Structure field projection (`s.field`)
//! - Dot notation for non-structure types (`expr.method` → `T.method expr`)
//! - Qualified name disambiguation (`Foo.bar.baz` → constant lookup)

use super::elab_core::DottedIdent;
use super::*;
use crate::stack_safe;

impl<'a> ElabCtx<'a> {
    /// Interpret a simple named projection as a namespace path only when its
    /// base is not an actual receiver. Inaccessible patterns use the same rule
    /// before converting projection syntax into a constructor-name candidate.
    pub(in crate::infer) fn namespace_projection_name(
        &self,
        base: &SurfaceName,
        field: &SurfaceName,
    ) -> Option<SurfaceName> {
        let explicit_root = base.is_unescaped_component("_root_")
            && base.component_syntax().first() == Some(&clean_parser::NameComponentSyntax::Plain);
        (explicit_root
            || !self.ident_resolves_to_value(base)
            || self.ident_resolves_to_type_former(base))
        .then(|| base.append(field))
    }

    /// Resolve only an authored local reference, without elaborating a term or
    /// allocating metavariables. Script consumers borrow this same name and
    /// receiver disambiguation with the actual goal's local FVar identities.
    pub(crate) fn resolve_local_surface_reference(&self, surface: &SurfaceExpr) -> Option<Expr> {
        match Self::unwrap_surface_parens(surface) {
            SurfaceExpr::Ident(_, name) => {
                if name.qualify_under(&SurfaceName::default()).name() != name.name() {
                    return None;
                }
                self.lookup_local(name).map(|(fvar, _)| Expr::fvar(fvar))
            }
            SurfaceExpr::Proj(_, base, projection) => self
                .resolve_qualified_local_reference(Self::unwrap_surface_parens(base), projection),
            _ => None,
        }
    }

    fn resolve_qualified_local_reference(
        &self,
        base: &SurfaceExpr,
        proj: &Projection,
    ) -> Option<Expr> {
        let qualified = Self::try_collect_qualified_name(base, proj)?;
        let mut leading = qualified.clone();
        while !leading.parent().is_anonymous() {
            leading = leading.parent();
        }
        let explicit_root =
            qualified.qualify_under(&SurfaceName::default()).name() != qualified.name();
        if qualified.is_relative_constructor()
            || explicit_root
            || (self.ident_resolves_to_value(&leading)
                && !self.ident_resolves_to_type_former(&leading))
        {
            return None;
        }
        self.lookup_local(&qualified)
            .map(|(fvar, _)| Expr::fvar(fvar))
    }

    /// Elaborate a projection expression (`base.field` or `base.0`).
    ///
    /// Handles three cases:
    /// 1. Structure projection: `s.field` → `proj(StructName, idx, s)`
    /// 2. Dot notation: `expr.method` → `T.method expr` where `T = typeof(expr)`
    /// 3. Qualified name: `Foo.bar` where `Foo` is a namespace, not a value
    pub(crate) fn elab_proj(
        &mut self,
        expr: &SurfaceExpr,
        proj: &Projection,
    ) -> Result<Expr, ElabError> {
        // How this term was reached decides an explicit-motive eliminator
        // head (`elab_dot_elim.rs`); the frame is restored on every exit.
        let saved = self.open_dot_elim_frame(expr, proj);
        let result = self.elab_proj_framed(expr, proj);
        self.dot_elim.restore_frame(saved);
        result
    }

    fn elab_proj_framed(
        &mut self,
        expr: &SurfaceExpr,
        proj: &Projection,
    ) -> Result<Expr, ElabError> {
        // Projection/qualified-name disambiguation (#497, #501):
        // The parser produces Proj for all dotted terms like `x.y`.
        // If the base fails to elaborate with UnknownIdent and it's a simple Ident,
        // try resolving the concatenated name `x.y` as a constant first.
        // This handles namespace-only prefixes where `x` isn't a value but `x.y` is.

        // Unwrap parentheses to handle cases like (Foo).bar
        let unwrapped = Self::unwrap_surface_parens(expr);

        // A dotted source spelling can also name an exact qualified local
        // (including a temporarily bound inductive self). Reassemble its typed
        // components before elaborating an otherwise unknown namespace prefix.
        // A real receiver still wins: local `x` keeps `x.field` projection
        // semantics even if an unrelated qualified local `x.field` exists.
        if let Some(local) = self.resolve_qualified_local_reference(unwrapped, proj) {
            return Ok(local);
        }

        // Namespace-qualified constant has priority over auto-implicit binding.
        //
        // `Proj(Ident(base), field)` where `base` names a *namespace* (not a
        // value in scope) and `base.field` is an accessible constant must
        // resolve to that constant — e.g. `apply Nat.eq_of_testBit_eq` or
        // `Foo.mylem`. Without this, elaborating the bare `base` first can
        // auto-bind it as an auto-implicit whose type is the current expected
        // type (the goal), after which dot notation mis-resolves the field
        // against the goal's head type (`Eq.field`) rather than the namespace
        // (Track R dot-notation bug). We only short-circuit when `base` is NOT a
        // genuine local/term value, so method dot-notation `x.f` (x a local) is
        // unaffected.
        if let SurfaceExpr::Ident(_, base_name) = unwrapped {
            if let Projection::Named(field) = proj {
                // Root-namespace escape: `_root_.Bool` parses as
                // `Proj(Ident("_root_"), "Bool")`. Resolve the field as a global
                // name with the marker stripped (Track R: `Ty.isSigned : Ty →
                // _root_.Bool`). Defer to `elab_ident` which knows how to resolve
                // a top-level constant / inductive / constructor.
                if base_name.is_unescaped_component("_root_")
                    && base_name.component_syntax().first()
                        == Some(&clean_parser::NameComponentSyntax::Plain)
                {
                    return self.elab_ident(&base_name.append(field));
                }
                // A WRITTEN dotted identifier (not `(base).field`, which
                // projects a term) is one name, resolved by Lean's rules
                // (`resolve_dotted_ident`): a global `base.field` wins over a
                // field of a global value `base` (a namespace member included)
                // and over a field of a `where`/`let rec` auxiliary
                // declaration `base`; only an ordinary local `base` is a
                // receiver regardless. Projecting instead read `Foo.x` with a
                // `where`-bound `Foo : S` and a global `Foo.x := 9` as the
                // field (measured 2026-09-26; Lean 4.8.0: `9`).
                if matches!(expr, SurfaceExpr::Ident(..)) {
                    match self.resolve_dotted_ident(base_name, field) {
                        DottedIdent::Global(name) => {
                            if self.is_known_accessible_global(&name) {
                                return Ok(self.mk_const(&name));
                            }
                            return Err(ElabError::Unsupported {
                                feature: format!(
                                    "`{name}` other than applied (Clean supplies this Lean \
                                     core constant only in its applied form)"
                                ),
                            });
                        }
                        DottedIdent::FieldOfShadowedLocal(_) => {
                            return Err(Self::shadowed_receiver_error(base_name, field));
                        }
                        DottedIdent::FieldOfGlobal { receiver, fields } => {
                            return self.elab_global_receiver_chain(expr.span(), receiver, &fields);
                        }
                        DottedIdent::UnsupportedGlobalReceiver => {
                            return Err(Self::unsupported_global_receiver_error(base_name, field));
                        }
                        DottedIdent::CoreUnavailable(name) => {
                            return Err(Self::core_unavailable_error(&name));
                        }
                        DottedIdent::Field => {}
                    }
                }
                // Reached only when no global of the full dotted name exists
                // (or the base is parenthesized): the namespace reading then
                // applies to a *pure namespace* base — not a value in scope. If
                // `base` itself denotes a value (a local, a struct instance, an
                // inductive/constructor), keep the structure-projection /
                // method dot-notation path. A TYPE-FORMER base (`Eq.symm`,
                // `Nat.myLemma`) is namespace-like even though the type constant
                // is in scope: Lean resolves `T.member` as one identifier
                // (`resolveGlobalName`), never as a projection OF the type
                // former, and elaborating `T` as a receiver mints a stray
                // universe param for it that nothing later pins.
                // A parenthesized `(base).field` projects the TERM `(base)`
                // (Lean elaborates the parenthesized term first), never a
                // namespace member.
                let written = matches!(expr, SurfaceExpr::Ident(..));
                if let Some(qualified) = written
                    .then(|| self.namespace_projection_name(base_name, field))
                    .flatten()
                {
                    // Resolve the dotted name namespace-relatively too (B03):
                    // `B.c` written inside `namespace A` must find `A.B.c`
                    // (Lean `Lean/ResolveName.lean` `resolveUsingNamespace`
                    // prepends the current namespace outward before trying the
                    // root).
                    if let Some(name) = self.resolve_qualified_chain(&qualified) {
                        return Ok(self.mk_const(&name));
                    }
                }
            }
        }

        // Multi-segment qualified names (B03): `A.B.y` parses as
        // `Proj(Proj(Ident("A"), "B"), "y")`. Before elaborating the base —
        // which would AUTO-BIND the namespace root `A` as an implicit in
        // signature positions and then fail dot-notation with the opaque
        // "cannot extract type name from opaque type variable" error
        // (namespaces_scoping/p02/p03) — try to resolve the whole collected
        // dotted chain as a global, namespace-relatively then at root. Lean
        // treats `A.B.y` as ONE identifier resolved by `resolveGlobalName`
        // (`Lean/ResolveName.lean`); the parser split it, so we reassemble.
        // Gated on the chain's LEADING segment not denoting a value in scope,
        // so genuine receiver chains `x.y.z` (x a local/constant) keep the
        // structure-projection / dot-notation path.
        if let SurfaceExpr::Proj(_, inner_base, inner_proj) = unwrapped {
            if let Projection::Named(field) = proj {
                if let Some(base_qualified) =
                    Self::try_collect_qualified_name(inner_base, inner_proj)
                {
                    let mut leading = base_qualified.clone();
                    while !leading.parent().is_anonymous() {
                        leading = leading.parent();
                    }
                    // Lean resolves the written chain as ONE identifier
                    // (`resolve_dotted_ident`): a global of the whole
                    // spelling wins unless the leading component is an
                    // ORDINARY local; a `where`/`let rec` auxiliary
                    // declaration or a global value as the leading component
                    // does not stop it.
                    let qualified = base_qualified.append(field);
                    // `(A.B).c` projects the term `(A.B)`: not one identifier.
                    let written = !matches!(expr, SurfaceExpr::Paren(..));
                    if written {
                        match self.resolve_dotted_ident(&base_qualified, field) {
                            DottedIdent::Global(name) => {
                                if self.is_known_accessible_global(&name) {
                                    return Ok(self.mk_const(&name));
                                }
                            }
                            DottedIdent::FieldOfShadowedLocal(_) => {
                                return Err(Self::shadowed_receiver_error(&base_qualified, field));
                            }
                            DottedIdent::FieldOfGlobal { receiver, fields } => {
                                return self.elab_global_receiver_chain(
                                    expr.span(),
                                    receiver,
                                    &fields,
                                );
                            }
                            DottedIdent::UnsupportedGlobalReceiver => {
                                return Err(Self::unsupported_global_receiver_error(
                                    &base_qualified,
                                    field,
                                ));
                            }
                            DottedIdent::CoreUnavailable(name) => {
                                return Err(Self::core_unavailable_error(&name));
                            }
                            DottedIdent::Field => {}
                        }
                    }
                    if written && !self.ident_resolves_to_value(&leading) {
                        // `_root_.A.B.c`: the marker forces ROOT-only
                        // resolution of the remainder (Lean `rootNamespace`
                        // handling in `Lean/ResolveName.lean`).
                        let root_name = qualified.qualify_under(&SurfaceName::default());
                        if root_name.name() != qualified.name() {
                            let root = root_name.into_name();
                            if self.is_known_accessible_global(&root) {
                                return Ok(self.mk_const(&root));
                            }
                        } else if let Some(name) = self.resolve_qualified_chain(&qualified) {
                            return Ok(self.mk_const(&name));
                        }
                    }
                }
            }
        }

        // Expected-type leakage guard (Track R dot-notation bug).
        //
        // `elaborate_with_expected_type` sets `current_expected_type` to the type
        // the WHOLE projection must have (e.g. `Eq`'s implicit element type `?α`
        // when elaborating the LHS of `xs.length = 3`), then calls `elaborate`,
        // which routes here. The expected type legitimately constrains the
        // projection's RESULT (`Nat`), NEVER its RECEIVER. But a receiver that
        // consumes the expected type — a list literal `[1,2,3]`, or anything that
        // unifies a free element-type metavariable against `current_expected_type`
        // — would wrongly bind `?α := List Nat` (the receiver's own type). The
        // projection then resolves `xs.length : Nat` correctly, but its `Nat`
        // result is checked against the corrupted `?α = List Nat`, raising a
        // spurious `Const(Nat)` vs `App(List, Nat)` shape mismatch.
        //
        // Hide the result-level expected type from the receiver pass: take it
        // before elaborating the receiver and restore it immediately after, so the
        // dot/structure resolution that follows (and the caller's own
        // expected-type check on the projection's result) still sees it. The
        // kernel re-checks the produced term, so this only stops a spurious
        // metavar contamination; it never relaxes a check.
        let saved_expected = self.current_expected_type.take();

        // Receiver elaboration has two successful outcomes: either continue
        // projection resolution with a value receiver, or finish immediately
        // with a qualified constant discovered by the namespace fallback. Keep
        // both outcomes inside one Result so the outer expected type is restored
        // before success or failure is propagated.
        enum ReceiverAttempt {
            Receiver(Expr),
            QualifiedConstant(Expr),
        }

        let receiver_attempt = (|| -> Result<ReceiverAttempt, ElabError> {
            match unwrapped {
                SurfaceExpr::Ident(_, base_name) => {
                    match self.elaborate(expr) {
                        Ok(val) => Ok(ReceiverAttempt::Receiver(val)),
                        Err(
                            // The recursion- and batch-aware variants are
                            // minted only after identifier resolution has
                            // already failed. Keep them in the same fallback
                            // class as `UnknownIdent`: the failed base may be
                            // only the namespace prefix of the dotted name the
                            // author actually wrote (`foo` in `foo.missing`).
                            err @ (ElabError::UnknownIdent(_)
                            | ElabError::UnknownIdentWithSuggestions { .. }
                            | ElabError::UnknownIdentDeferred { .. }
                            | ElabError::RecursionOutsideFragment { .. }
                            | ElabError::SameBatchHeaderUnavailable { .. }),
                        ) => {
                            // Base identifier not found - try qualified name fallback
                            if let Projection::Named(field) = proj {
                                let qualified = base_name.append(field);
                                let name = self.with_private_step(qualified.name().clone());
                                if let Some(info) = self.env.get_const(&name) {
                                    // Enforce private visibility on qualified name fallback
                                    // (#3410): without this, `Foo.helper` resolves even
                                    // when `helper` is private and we're outside `Foo`.
                                    if self.is_const_accessible(&name) {
                                        let levels: Vec<Level> = info
                                            .level_params
                                            .iter()
                                            .map(|_| self.fresh_universe_param())
                                            .collect();
                                        return Ok(ReceiverAttempt::QualifiedConstant(
                                            Expr::const_(name, levels),
                                        ));
                                    }
                                }
                                // Forward the qualified-name diagnostic whenever
                                // it is MORE SPECIFIC than a bare unknown-ident:
                                // suggestions, a protected-name pointer, a
                                // same-batch sibling, or the self-reference
                                // recursion report all name the identifier AS
                                // WRITTEN (`foo.a`), which the base error has
                                // already truncated to its root (`foo`). A
                                // signal-free bare `UnknownIdent` falls back
                                // only when the base error is itself an ordinary
                                // unknown-ident diagnostic. A recursion- or
                                // same-batch-aware error describes the PREFIX,
                                // not the complete authored name, so even a bare
                                // full-name `UnknownIdent` is more accurate.
                                // (The old filter forwarded ONLY the suggestion
                                // variant, so the richer self-reference report
                                // introduced for recursive defs was silently
                                // DISCARDED here in favor of the truncated one.)
                                let qualified_err = self.unknown_ident_error(&qualified);
                                let qualified_is_bare =
                                    matches!(&qualified_err, ElabError::UnknownIdent(_));
                                let base_error_is_rich_prefix = matches!(
                                    &err,
                                    ElabError::RecursionOutsideFragment { .. }
                                        | ElabError::SameBatchHeaderUnavailable { .. }
                                );
                                if !qualified_is_bare || base_error_is_rich_prefix {
                                    // A DEFERRED qualified-name error decides
                                    // "has suggestions" only when reported:
                                    // with them it names the qualified
                                    // identifier, without them it is the base
                                    // error — exactly the choice made here
                                    // before the scan was deferred.
                                    return Err(match qualified_err {
                                        ElabError::UnknownIdentDeferred {
                                            name,
                                            namespace_prefix,
                                            fallback: None,
                                        } if !base_error_is_rich_prefix => {
                                            ElabError::UnknownIdentDeferred {
                                                name,
                                                namespace_prefix,
                                                fallback: Some(Box::new(err)),
                                            }
                                        }
                                        other => other,
                                    });
                                }
                            }
                            // Fallback failed - re-raise original error
                            Err(err)
                        }
                        Err(e) => Err(e),
                    }
                }
                // For non-Ident bases (e.g., nested projections like x.y.z),
                // first try to elaborate; if that fails with UnknownIdent,
                // recursively collect the qualified name chain
                SurfaceExpr::Proj(_, inner_base, inner_proj) => {
                    match self.elaborate(expr) {
                        Ok(val) => Ok(ReceiverAttempt::Receiver(val)),
                        Err(
                            // Same fallback class as the Ident-base arm: a
                            // rich diagnostic for an inner prefix must not
                            // prevent trying the complete qualified chain.
                            err @ (ElabError::UnknownIdent(_)
                            | ElabError::UnknownIdentWithSuggestions { .. }
                            | ElabError::UnknownIdentDeferred { .. }
                            | ElabError::RecursionOutsideFragment { .. }
                            | ElabError::SameBatchHeaderUnavailable { .. }),
                        ) => {
                            // Try to collect full qualified name from nested projections
                            if let Projection::Named(field) = proj {
                                if let Some(base_qualified) =
                                    Self::try_collect_qualified_name(inner_base, inner_proj)
                                {
                                    let qualified = base_qualified.append(field);
                                    let name = self.with_private_step(qualified.name().clone());
                                    if let Some(info) = self.env.get_const(&name) {
                                        // Enforce private visibility (#3410)
                                        if self.is_const_accessible(&name) {
                                            let levels: Vec<Level> = info
                                                .level_params
                                                .iter()
                                                .map(|_| self.fresh_universe_param())
                                                .collect();
                                            return Ok(ReceiverAttempt::QualifiedConstant(
                                                Expr::const_(name, levels),
                                            ));
                                        }
                                    }
                                    // Same forwarding rule as the Ident-base arm
                                    // above: anything more specific than a bare
                                    // `UnknownIdent` wins over the truncated
                                    // base-name error.
                                    let qualified_err = self.unknown_ident_error(&qualified);
                                    // A deferred error materializes to exactly
                                    // these two outcomes: suggestions for the
                                    // qualified name, or a plain unknown
                                    // identifier naming it.
                                    if !matches!(qualified_err, ElabError::UnknownIdent(_)) {
                                        return Err(qualified_err);
                                    }
                                    // Return error with full qualified name for better message
                                    return Err(ElabError::UnknownIdent(qualified.to_string()));
                                }
                            }
                            // Can't collect qualified name - re-raise
                            Err(err)
                        }
                        Err(e) => Err(e),
                    }
                }
                _ => self.elaborate(expr).map(ReceiverAttempt::Receiver),
            }
        })();

        // Restore the result-level expected type before inspecting the attempt:
        // `?` here is now safe, and a qualified-name success cannot bypass the
        // restoration with an early return.
        self.current_expected_type = saved_expected;
        let expr_val = match receiver_attempt? {
            ReceiverAttempt::Receiver(value) => value,
            ReceiverAttempt::QualifiedConstant(value) => return Ok(value),
        };
        self.dot_elim.set_frame_receiver(&expr_val);
        // G28: Lean postpones field notation on a receiver whose type is a
        // metavariable (`tryPostponeIfMVar`); record it for a watched lambda
        // or arrow-domain attempt (`elab_app_postpone_lambda.rs`). Changes no verdict here.
        self.note_field_notation_receiver(&expr_val);

        // Try single-constructor-inductive projection first.
        match self.resolve_projection_target(&expr_val) {
            Ok((struct_name, num_fields, is_structure)) => {
                // Single-ctor projection: expr.field -> proj(struct_name, idx, expr)
                match proj {
                    Projection::Named(name) => {
                        // Named `.field` requires structure field-name metadata.
                        // For a plain (non-structure) single-ctor inductive there
                        // is no field accessor, so fall straight through to
                        // dot-notation (e.g. `τ.eval` where `T` is an inductive
                        // with a def `T.eval`, not a structure field). This
                        // mirrors Lean's `resolveLValAux`, which only emits the
                        // named projection function when `isStructure`.
                        if !is_structure {
                            return self.elab_dot_notation(&expr_val, proj);
                        }
                        let field_name = name.name().clone();
                        match self
                            .env
                            .get_structure_field_index(&struct_name, &field_name)
                        {
                            Some(idx) => {
                                // Another module's private structure: Lean
                                // refuses the field from an importer (G21 B3).
                                self.check_imported_private_field(&struct_name, &field_name)?;
                                Ok(Expr::proj(struct_name, idx, expr_val))
                            }
                            None => {
                                // Not a real field — but it may be a *method* in the
                                // structure's namespace (Track UU: `ms.lookupValue id`
                                // where `MachineState` is a structure and
                                // `MachineState.lookupValue : MachineState → ValueId →
                                // Option Value` is a def, not a field). Lean 4 method
                                // dot-notation resolves this. Fall through to
                                // `elab_dot_notation`; only if THAT also fails do we
                                // report the (more informative) unknown-field error.
                                if let Ok(method_expr) = self.elab_dot_notation(&expr_val, proj) {
                                    return Ok(method_expr);
                                }
                                // INHERITED FIELD, composed ON THE FLY — Lean's
                                // `mkBaseProjections` (`src/Lean/Elab/App.lean`).
                                // `field_name` is not an own field of `struct_name`,
                                // but it may be projectable through an `extends`
                                // parent SUBOBJECT, in which case Lean emits the
                                // composition `Parent.f (Child.toParent self)` at THIS
                                // use site and declares no constant for it. Clean
                                // additionally MATERIALIZES that composition as a
                                // constant `Child.f` (`elab_structure::
                                // build_inherited_projections`), so the arm above
                                // normally resolves first.
                                //
                                // SAFETY PROPERTY, precisely: this arm CANNOT change
                                // any term that elaborates today — wherever the
                                // constant exists `elab_dot_notation` already
                                // returned, and wherever it does not the old code had
                                // already failed. It only ever turns a loud
                                // unknown-field error into a resolved projection, and
                                // the kernel re-checks every `Proj` it emits, so a
                                // wrong walk fails closed. Three real places reach it:
                                // a field `collect_flattened_projectable_instantiated`
                                // DROPPED fail-closed (level-param mismatch,
                                // under-shaped telescope, self-dependent after
                                // instantiation — all cases the kernel's own `Proj`
                                // typing rule handles natively, which is why the chain
                                // succeeds where the constant could not be built); an
                                // `.olean`-IMPORTED structure (no `structure_parents`
                                // metadata, so the walk declines there today); and the
                                // Lean-4-parity mode measured in
                                // `designs/2026-08-24-inherited-projection-parity.md`.
                                //
                                // The composed chain is a pure kernel `Proj` spine, so
                                // it needs no name lookup and no universe params, and
                                // it is definitionally equal to the generated
                                // constant's application by delta (pinned by
                                // `composed_inherited_projection_is_def_eq_to_generated_constant`).
                                if let Some(chain) =
                                    crate::name_resolution::compose_subobject_projection(
                                        self.env,
                                        &struct_name,
                                        &field_name,
                                        expr_val.clone(),
                                        0,
                                    )
                                {
                                    return Ok(chain);
                                }
                                let field_names: Vec<String> = self
                                    .env
                                    .get_structure_field_names(&struct_name)
                                    .map(|fields| fields.iter().map(ToString::to_string).collect())
                                    .unwrap_or_default();
                                let suggestions =
                                    crate::agent_diagnostics::nearest_string_candidates(
                                        &name.to_string(),
                                        field_names.iter().map(String::as_str),
                                        5,
                                    );
                                Err(ElabError::UnknownProjectionField {
                                    struct_name: struct_name.clone(),
                                    field: name.to_string(),
                                    suggestions,
                                })
                            }
                        }
                    }
                    Projection::Index(idx) => {
                        // Surface `.1`/`.2` are 1-based (Lean convention); the kernel
                        // `Proj(S, i, e)` index is 0-based. Mirror Lean's elaborator
                        // (Lean/Elab/App.lean: `if idx - 1 < numFields`): reject `.0`,
                        // and require `idx - 1 < num_fields` (i.e. `idx <= num_fields`).
                        if *idx == 0 || *idx > num_fields {
                            return Err(ElabError::ProjectionIndexOutOfBounds {
                                struct_name: struct_name.clone(),
                                idx: *idx,
                                field_count: num_fields,
                            });
                        }

                        // Another module's private structure: Lean's
                        // `resolveLValAux` turns `.i` on a `structure` into
                        // the i-th field's projection function, which the
                        // named-field refusal then covers ("field 'x' from
                        // structure '…' is private", G21 B3). A plain
                        // one-constructor `inductive` has no projection
                        // function and Lean projects it with no check.
                        if is_structure {
                            self.check_imported_private_field_index(&struct_name, *idx)?;
                        }
                        // `*idx >= 1` is guaranteed by the `== 0` guard above, so the
                        // subtraction cannot underflow.
                        Ok(Expr::proj(struct_name, *idx - 1, expr_val))
                    }
                }
            }
            Err(ElabError::InvalidProjectionTarget(_)) => {
                // Numeric `.1`/`.2` projection through a receiver whose type is a
                // LEADING-IMPLICIT Pi (Track: `Ne.ne_or_ne`'s `not_and_or.1`, where
                // `not_and_or : {a b : Prop} → (¬(a ∧ b) ↔ ¬a ∨ ¬b)` — an
                // implicit-led Pi ending in the single-constructor structure
                // `Iff`). `resolve_projection_target` bails on the Pi head, and
                // `elab_dot_notation`'s Index arm rejects it outright ("index
                // projection on non-structure type"). Peel the leading
                // implicit/instance binders to expose the structure head, then
                // project by index. The NAMED `.field` counterpart on the same
                // shape already resolves via `elab_dot_notation`'s Fix A, so this
                // only closes the Index path. SOUNDNESS: the peeled application is
                // fully instantiated and the emitted `Expr::proj` is kernel-
                // re-checked; this only lets the elaborator NAME the projection
                // target it previously could not.
                if let Projection::Index(idx) = proj {
                    if let Some(result) = self.try_index_proj_through_implicits(&expr_val, *idx)? {
                        return Ok(result);
                    }
                }
                // Fallback: dot notation for non-structure types (#155)
                // For `expr.field` where expr : T (non-structure), look for T.field constant
                // and apply as `T.field expr`
                self.elab_dot_notation(&expr_val, proj)
            }
            Err(e) => Err(e),
        }
    }

    /// Is `name` a known global (constant, inductive, constructor, or
    /// recursor) that is accessible from the current namespace?
    pub(super) fn is_known_accessible_global(&self, name: &Name) -> bool {
        (self.env.get_const(name).is_some()
            || self.env.get_inductive(name).is_some()
            || self.env.get_constructor(name).is_some()
            || self.env.get_recursor(name).is_some())
            && self.is_const_accessible(name)
    }

    /// Resolve a dotted name chain (`"A.B.y"`, `"B.c"`) the way Lean's
    /// `resolveGlobalName` resolves an identifier (`Lean/ResolveName.lean`):
    /// current-namespace-outward first (`resolveUsingNamespace` — inside
    /// `namespace A`, `B.c` tries `A.B.c` before the root), then `open`
    /// aliases, then the root-level exact name. Returns the fully-qualified
    /// global name, or `None` when no accessible global matches. Read-only:
    /// never auto-binds.
    pub(super) fn resolve_qualified_chain(&self, dotted: &SurfaceName) -> Option<Name> {
        self.resolve_qualified_chain_with_pending(dotted, &[])
    }

    /// The refusal for a dotted identifier whose receiver Lean takes to be
    /// an ordinary local that a same-named `where`/`let rec` auxiliary
    /// declaration shadows (`DottedIdent::FieldOfShadowedLocal`): Clean's
    /// projection path would read the auxiliary declaration instead.
    fn shadowed_receiver_error(base: &SurfaceName, field: &SurfaceName) -> ElabError {
        ElabError::Unsupported {
            feature: format!(
                "`{base}.{field}`: Lean reads this as a field of the ordinary local `{base}` \
                 that a `where`/`let rec` declaration of the same name shadows; rename one of them"
            ),
        }
    }

    /// The refusal for a dotted identifier whose receiver Lean takes to be
    /// a global that Clean supplies only as a builtin
    /// (`DottedIdent::UnsupportedGlobalReceiver`).
    fn unsupported_global_receiver_error(base: &SurfaceName, field: &SurfaceName) -> ElabError {
        ElabError::Unsupported {
            feature: format!(
                "`{base}.{field}`: Lean reads this as a field of the global `{base}`, which a \
                 `where`/`let rec` declaration of the same name shadows; rename the declaration"
            ),
        }
    }

    /// The refusal for a dotted identifier naming a Lean core constant that
    /// Clean's prelude lacks (`DottedIdent::CoreUnavailable`).
    fn core_unavailable_error(name: &Name) -> ElabError {
        ElabError::Unsupported {
            feature: format!("`{name}`: a Lean core constant Clean's prelude does not provide"),
        }
    }

    /// `receiver.f₁.….fₙ` with `receiver` the resolved GLOBAL constant
    /// (`DottedIdent::FieldOfGlobal`): each field is projected from the
    /// term, exactly as for `(receiver).f₁.….fₙ`, so no local of the
    /// receiver's spelling can be read instead.
    fn elab_global_receiver_chain(
        &mut self,
        span: clean_parser::Span,
        receiver: Name,
        fields: &[SurfaceName],
    ) -> Result<Expr, ElabError> {
        let head = SurfaceExpr::Paren(
            span,
            Box::new(SurfaceExpr::Ident(
                span,
                SurfaceName::global_constant(receiver),
            )),
        );
        let chain = fields.iter().fold(head, |acc, field| {
            SurfaceExpr::Paren(
                span,
                Box::new(SurfaceExpr::Proj(
                    span,
                    Box::new(acc),
                    Projection::Named(field.clone()),
                )),
            )
        });
        self.elaborate(&chain)
    }

    /// Ordinary typed namespace lookup, including exact pending recursive members.
    /// A distinct existing global keeps its normal lookup priority.
    pub(super) fn resolve_qualified_chain_with_pending(
        &self,
        dotted: &SurfaceName,
        pending: &[Name],
    ) -> Option<Name> {
        if dotted.is_anonymous() || dotted.is_relative_constructor() {
            return None;
        }
        let known = |name: &Name| pending.contains(name) || self.is_known_accessible_global(name);
        let root_selected = dotted.qualify_under(&SurfaceName::default());
        if root_selected.name() != dotted.name() {
            let root = self.with_private_step(root_selected.into_name());
            return known(&root).then_some(root);
        }
        // A notation template's free spelling: what it resolved to where
        // the template was declared (`TemplateResolution`).
        if let Some(resolution) = self.template_resolution(dotted) {
            return resolution.chain.clone();
        }
        // A user template's free reference walks from its declaring namespace.
        let namespace_prefix = match dotted.template_origin() {
            Some(origin) => SurfaceName::from_name(origin.namespace.clone()),
            None => self.namespace_prefix.clone(),
        };
        if !namespace_prefix.is_anonymous() {
            let mut prefix = namespace_prefix;
            loop {
                let qualified = prefix.append(dotted).into_name();
                let declared = self.with_private_step(qualified.clone());
                // Lean's `resolveQualifiedName` at this prefix: the
                // declaration and the aliases named `prefix.dotted` (an
                // `export` inside the namespace) are one candidate set;
                // several distinct ones are ambiguous (measured on Lean
                // 4.8.0: inside `namespace K.K` with `export A (y)` there,
                // `K.y` is the alias's `A.y`, not a root `K.y`).
                let mut found: Vec<Name> = Vec::new();
                if known(&declared) && self.namespace_candidate_visible(&declared, dotted) {
                    found.push(declared);
                }
                for target in self
                    .namespace_state
                    .resolve_all(&qualified)
                    .into_iter()
                    .chain(self.env.export_alias_targets(&qualified))
                {
                    if known(target) && !found.contains(target) {
                        found.push(target.clone());
                    }
                }
                match found.len() {
                    0 => {}
                    1 => return found.pop(),
                    _ => return None,
                }
                prefix = prefix.parent();
                if prefix.is_anonymous() {
                    break;
                }
            }
        }
        // Lean's `resolveExact`: a DOTTED name that exists as written wins
        // before any alias or `open` (measured on Lean 4.8.0: `def K.x := 3`
        // with `namespace K; export N.M (x); end K` gives `K.x = 3`; Clean
        // read the alias and credited `K.x = 1`).
        let root = self.with_private_step(dotted.name().clone());
        if !dotted.parent().is_anonymous() && known(&root) {
            return Some(root);
        }
        let file_aliased: Vec<&Name> = self
            .namespace_state
            .resolve_all(dotted.name())
            .into_iter()
            .filter(|target| known(target))
            .collect();
        match file_aliased.as_slice() {
            [only] => return Some((*only).clone()),
            [] => {}
            _ => return None,
        }
        // The environment's alias table: an `export` another module made
        // (`namespace K; export N (x)` gives `K.x ↦ N.x`), when it names one
        // declaration (Lean's `getAliases`; several are ambiguous).
        let aliased: Vec<&Name> = self
            .env
            .export_alias_targets(dotted.name())
            .into_iter()
            .filter(|target| known(target))
            .collect();
        match aliased.as_slice() {
            [only] => return Some((*only).clone()),
            [] => {}
            _ => return None,
        }
        if known(&root) {
            return Some(root);
        }
        // Lean's `resolveOpenDecls`: `ns ++ dotted` for every simple `open
        // ns` in force (measured on Lean 4.8.0: after `open A`, `N.y` is
        // `A.N.y`); several are ambiguous.
        let mut opened: Vec<Name> = Vec::new();
        for (open_ns, hidden) in self.namespace_state.open_namespaces_with_hidden() {
            if hidden.iter().any(|h| h == dotted.name()) {
                continue;
            }
            let candidate =
                self.with_private_step(crate::namespace::append_names(open_ns, dotted.name()));
            if known(&candidate) && !opened.contains(&candidate) {
                opened.push(candidate);
            }
        }
        // …and `OpenDecl.explicit` whose short name is a proper prefix of
        // `dotted` (after `open Foo (Bar)`, `Bar.a` is `Foo.Bar.a`).
        for candidate in self
            .namespace_state
            .explicit_open_prefix_targets(dotted.name())
        {
            let candidate = self.with_private_step(candidate);
            if known(&candidate) && !opened.contains(&candidate) {
                opened.push(candidate);
            }
        }
        match opened.len() {
            1 => opened.pop(),
            _ => None,
        }
    }

    /// Does the bare identifier `name` denote a *value* in the current scope?
    ///
    /// True when `name` is a local, or resolves (directly, via the current
    /// namespace, or via an enclosing-namespace prefix) to an accessible
    /// constant, inductive, or constructor. False for a pure *namespace* prefix
    /// (e.g. `Nat` qualifying `Nat.eq_of_testBit_eq`, or a user `namespace Foo`)
    /// or an unknown identifier that would only auto-bind. Used to decide
    /// whether `base.field` should prefer namespace-qualified constant
    /// resolution over value-based dot notation. Read-only: never auto-binds.
    pub(super) fn ident_resolves_to_value(&self, name: &SurfaceName) -> bool {
        if self.lookup_local(name).is_some() {
            return true;
        }
        if let Some(resolution) = self.template_resolution(name) {
            return resolution.is_value;
        }
        let direct = name.name().clone();
        let is_known = |n: &Name| {
            (self.env.get_const(n).is_some() && self.is_const_accessible(n))
                || self.env.get_inductive(n).is_some()
                || self.env.get_constructor(n).is_some()
                || self.env.get_recursor(n).is_some()
                || (self.env.get_const(n).is_none() && self.private_candidate(n).is_some())
        };
        if is_known(&direct) {
            return true;
        }
        if let Some(qualified) = self.namespace_state.resolve(name.name()) {
            if is_known(qualified) {
                return true;
            }
        }
        if !self.namespace_prefix.is_anonymous() {
            let mut prefix = self.namespace_prefix.clone();
            loop {
                let qualified = prefix.append(name).into_name();
                if is_known(&qualified) {
                    return true;
                }
                prefix = prefix.parent();
                if prefix.is_anonymous() {
                    break;
                }
            }
        }
        false
    }

    /// Does the bare identifier `name` denote a *type former* — a registered
    /// inductive, or an accessible constant whose declared type strips Pi
    /// binders down to a `Sort`? Locals shadow globals and are never type
    /// formers here (`lookup_local` first), so a receiver that merely reuses a
    /// type's name keeps the projection / dot-notation path. Resolution order
    /// mirrors `ident_resolves_to_value` (direct, `open` aliases, enclosing
    /// namespaces). Read-only: never auto-binds. Syntactic Pi-stripping only —
    /// no whnf — so a defined alias that only REDUCES to a Sort is not
    /// classified; such a base keeps the receiver path, which still resolves
    /// it via `elab_dot_notation`'s namespace walk.
    pub(super) fn ident_resolves_to_type_former(&self, name: &SurfaceName) -> bool {
        if self.lookup_local(name).is_some() {
            return false;
        }
        if let Some(resolution) = self.template_resolution(name) {
            return resolution.is_type_former;
        }
        let is_type_former = |n: &Name| {
            if self.env.get_inductive(n).is_some() {
                return true;
            }
            let Some(info) = self.env.get_const(n) else {
                return false;
            };
            if !self.is_const_accessible(n) {
                return false;
            }
            let mut ty = &info.type_;
            while let ExprKind::Pi(_, _, body) = ty.kind() {
                ty = body;
            }
            matches!(ty.kind(), ExprKind::Sort(_))
        };
        let direct = name.name().clone();
        if is_type_former(&direct) {
            return true;
        }
        if let Some(qualified) = self.namespace_state.resolve(name.name()) {
            if is_type_former(qualified) {
                return true;
            }
        }
        if !self.namespace_prefix.is_anonymous() {
            let mut prefix = self.namespace_prefix.clone();
            loop {
                let qualified = prefix.append(name).into_name();
                if is_type_former(&qualified) {
                    return true;
                }
                prefix = prefix.parent();
                if prefix.is_anonymous() {
                    break;
                }
            }
        }
        false
    }

    /// Dot notation fallback for non-structure types.
    ///
    /// For `expr.field` where `expr : T` and `T` is not a structure,
    /// looks up `T.field` as a constant and applies it: `T.field expr`.
    fn elab_dot_notation(&mut self, expr_val: &Expr, proj: &Projection) -> Result<Expr, ElabError> {
        let field_name = match proj {
            Projection::Named(n) => n.clone(),
            Projection::Index(_) => {
                // Index projection doesn't make sense for non-structures
                return Err(ElabError::InvalidProjectionTarget(
                    "index projection on non-structure type".to_string(),
                ));
            }
        };

        // Namespace lookup: resolve dotted constants like `Id.mk` or `whnf_to.refl`
        if let ExprKind::Const(const_name, _) = expr_val.kind() {
            let namespaced = crate::namespace::append_names(const_name, field_name.name());
            // Check if this matches a recursive function being defined (#522)
            // During recursive definition elaboration, the function isn't in env yet
            // but should be recognized as a valid recursive call target.
            if let Some(ref ctx) = self.recursive_def_ctx {
                let namespaced_source = SurfaceName::from_name(namespaced.clone());
                if ctx.matches_call_name(&namespaced_source) {
                    // This is a recursive call to the function being defined.
                    // Return a placeholder constant that will be handled by the
                    // recursor elaboration when arguments are applied.
                    // Use empty levels for now - will be properly instantiated later.
                    return Ok(Expr::const_(namespaced, vec![]));
                }
            }
            if let Some(info) = self.env.get_const(&namespaced) {
                // Use fresh universe parameters for universe-polymorphic constants
                let levels: Vec<Level> = info
                    .level_params
                    .iter()
                    .map(|_| self.fresh_universe_param())
                    .collect();
                return Ok(Expr::const_(namespaced, levels));
            }
            // Namespace-qualified resolution of `T.field`. The receiver const `T`
            // may itself be namespace-relative: inside `namespace TrustIr`, a
            // reference `Set.denote` resolves `Set` to the *prelude* `Set : Type u
            // → Type u` axiom (a Pi-typed type constant) even though the intended
            // target is the in-namespace def `TrustIr.Set.denote`. The bare
            // `Set.denote` lookup above misses it, and `infer_type` then yields a
            // Pi head that `get_type_name` cannot name ("cannot extract type name
            // from Pi …"). Walk the active namespace chain joined with the full
            // dotted `T.field`, mirroring `elab_ident`'s namespace walk, so the
            // genuine in-namespace constant is found first. Only accessible
            // constants are returned; the kernel re-checks the result, so a wrong
            // resolution fails closed.
            let dotted = SurfaceName::from_name(namespaced.clone());
            if let Some(q) = self.namespace_state.resolve(dotted.name()) {
                if self.is_const_accessible(q) {
                    if let Some(info) = self.env.get_const(q) {
                        let q = q.clone();
                        let levels: Vec<Level> = info
                            .level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        return Ok(Expr::const_(q, levels));
                    }
                }
            }
            if !self.namespace_prefix.is_anonymous() {
                let mut prefix = self.namespace_prefix.clone();
                loop {
                    let qualified = self.with_private_step(prefix.append(&dotted).into_name());
                    if self.is_const_accessible(&qualified) {
                        if let Some(info) = self.env.get_const(&qualified) {
                            let levels: Vec<Level> = info
                                .level_params
                                .iter()
                                .map(|_| self.fresh_universe_param())
                                .collect();
                            return Ok(Expr::const_(qualified, levels));
                        }
                    }
                    prefix = prefix.parent();
                    if prefix.is_anonymous() {
                        break;
                    }
                }
            }
        }

        let expr_ty = self.infer_type(expr_val)?;

        // Opaque-receiver namespace fallback.
        //
        // When `get_type_name` cannot recover a concrete inductive head from the
        // receiver's type — because that type's head is an opaque type *variable*
        // (an `FVar`: an auto-bound implicit / loose placeholder) — the resolver
        // would error out. But the receiver's *own surface name* `N` may itself be
        // a namespace: `N.field` (e.g. `Sequence.denote`) can be a genuine
        // accessible constant that the parser split into `Proj(Ident("N"), field)`
        // because a same-named placeholder local was in scope. Prefer that
        // qualified constant here.
        //
        // Tightly gated: only when the receiver type head is an `FVar` (the
        // failure case — never true for a concretely-typed `x` in genuine method
        // dot-notation `x.f`) and the receiver is an `FVar` local whose name
        // resolves a real accessible const through the active namespace chain.
        // The kernel re-checks the produced constant, so a wrong resolution fails
        // closed. (The distinct Pi-head case — a type constant like prelude `Set`
        // used as a namespace — is intentionally left to the existing logic.)
        //
        // ONLY an AUTO-BOUND receiver qualifies. A user-written binder `foo`
        // makes `foo.x` a projection of that local in Lean
        // (`resolveLocalName`), whatever globals exist; its type being still
        // an unassigned metavariable (which is also an `FVar` here — the
        // `META_FVAR_TAG` encoding) does not change that. Taking the local's
        // NAME as a namespace made `def k1 : S → Nat := fun foo => foo.x`,
        // with a global `foo.x := 9`, compute `∀ s, k1 s = 9` (measured
        // 2026-09-26; Lean 4.8.0: `k1 ⟨5⟩ = 5`). An auto-bound implicit is
        // Clean's own placeholder for an identifier that resolved to nothing,
        // so reading its spelling as the namespace it failed to name is the
        // only case this fallback exists for.
        if matches!(self.whnf(&expr_ty).kind(), ExprKind::FVar(_)) {
            if let ExprKind::FVar(_) = expr_val.kind() {
                let recv_name = self.auto_bound_head_name(expr_val);
                if let Some(recv_name) = recv_name {
                    let dotted = recv_name.append(&field_name);
                    // Resolve `recv_name.field` through the same namespace chain
                    // `ident_resolves_to_value` consults: the bare name, the active
                    // `open`/`namespace` resolution, then each enclosing namespace
                    // prefix (so `Sequence.denote` finds `TrustIr.Sequence.denote`).
                    let mut candidates: Vec<Name> = vec![dotted.name().clone()];
                    if let Some(q) = self.namespace_state.resolve(dotted.name()) {
                        candidates.push(q.clone());
                    }
                    if !self.namespace_prefix.is_anonymous() {
                        let mut prefix = self.namespace_prefix.clone();
                        loop {
                            candidates.push(prefix.append(&dotted).into_name());
                            prefix = prefix.parent();
                            if prefix.is_anonymous() {
                                break;
                            }
                        }
                    }
                    for name in candidates {
                        let name = self.with_private_step(name);
                        if let Some(info) = self.env.get_const(&name) {
                            if self.is_const_accessible(&name) {
                                let levels: Vec<Level> = info
                                    .level_params
                                    .iter()
                                    .map(|_| self.fresh_universe_param())
                                    .collect();
                                return Ok(Expr::const_(name, levels));
                            }
                        }
                    }
                }
            }
        }

        // Function-typed receiver field (Track UU): `x.f` where `x : T` and `T`
        // is a *definition* that unfolds to a Pi (function) type — e.g.
        // `def ValueMap := ValueId → Option Value`, with `ms.locals.get id`.
        // Lean 4 dot notation takes the namespace from the **un-reduced** head
        // of the receiver's type, NOT from its WHNF. Unfolding `T` first turns
        // the type into a `Pi`, after which neither the `Sort`/`Pi` special
        // cases nor `get_type_name` (which WHNFs) can recover the namespace, and
        // the resolver fails with "cannot extract type name from Pi(...)".
        //
        // Try the syntactic (un-whnf'd) head constant `T` of `expr_ty` first: if
        // `T.field` resolves to an accessible constant, build it via the same
        // receiver-slot logic as the constant path below. For ordinary
        // inductives/structures the syntactic head already equals the WHNF head,
        // so this is a no-op there; it only adds resolution for type
        // abbreviations whose head would otherwise be lost to unfolding. If
        // `T.field` does not resolve we fall through to the existing logic
        // unchanged (so a `def Foo := Bar` alias still finds `Bar.field`).
        if let ExprKind::Const(head_name, _) = expr_ty.get_app_fn().kind() {
            let name = self
                .with_private_step(crate::namespace::append_names(head_name, field_name.name()));
            if let Some(info) = self.env.get_const(&name) {
                if self.is_const_accessible(&name) {
                    let const_level_params = info.level_params.clone();
                    let const_type = info.type_.clone();
                    let levels: Vec<Level> = const_level_params
                        .iter()
                        .map(|_| self.fresh_universe_param())
                        .collect();
                    let fn_type = if levels.is_empty() {
                        const_type
                    } else {
                        const_type.instantiate_level_params_direct(&const_level_params, &levels)
                    };
                    let fn_expr = Expr::const_(name, levels);
                    let type_name = head_name.clone();
                    return self
                        .apply_dot_receiver(fn_expr, &fn_type, expr_val, &expr_ty, &type_name);
                }
            }
        }

        // When the expression's type is a Sort, the expression is a type constructor
        // (e.g., `Nat : Type`). Standard type-based projection doesn't apply — instead
        // try namespace lookup on the WHNF of the expression itself. This handles cases
        // like `(id Nat).add` where the base reduces to `Nat` after WHNF.
        let expr_ty_whnf = self.whnf(&expr_ty);
        if matches!(expr_ty_whnf.kind(), ExprKind::Sort(_)) {
            let val_whnf = self.whnf(expr_val);
            if let ExprKind::Const(const_name, _) = val_whnf.get_app_fn().kind() {
                let namespaced = crate::namespace::append_names(const_name, field_name.name());
                // Mutual forward-declaration: inside a `mutual ... end` block the
                // sibling functions are pushed as *locals* (under their dotted
                // names) so cross-references resolve before they are registered
                // as constants. `T.method` parses as a projection on the type
                // `T`, so a sibling call `Tree.sizeList ts` reaches here with
                // `namespaced == "Tree.sizeList"` while that name is still only a
                // local. Resolve it to the forward-declaration fvar (the
                // `elab_mutual` body pass later rewrites the fvar to the proper
                // `Const`). Without this the dotted sibling call hard-fails as an
                // unknown type-valued projection.
                if let Some((fvar, _)) =
                    self.lookup_local(&SurfaceName::from_name(namespaced.clone()))
                {
                    return Ok(Expr::fvar(fvar));
                }
                // The forward-declaration local is pushed under the *surface*
                // dotted name exactly as written (`elab_mutual` calls
                // `push_local(name, …)` with the unqualified surface spelling).
                // When the receiver type `T` resolved to a namespace-qualified
                // constant (e.g. `Value` → `TrustIr.Value` inside
                // `namespace TrustIr`), `namespaced` becomes
                // `TrustIr.Value.ofConstantList` and misses the local keyed
                // `Value.ofConstantList`. Walk progressively-shorter suffixes of
                // the receiver's qualified name joined with the field, mirroring
                // the namespace walk in `elab_ident`, so a sibling call written
                // `Value.ofConstantList` inside `namespace TrustIr` still finds
                // its forward-declaration fvar. Only locals are consulted here
                // (constants are handled by the qualified lookups below), so this
                // cannot shadow a genuine global.
                {
                    let mut suffix = SurfaceName::from_name(const_name.clone());
                    loop {
                        let key = suffix.append(&field_name);
                        if let Some((fvar, _)) = self.lookup_local(&key) {
                            return Ok(Expr::fvar(fvar));
                        }
                        let Some((_, rest)) = suffix.split_first() else {
                            break;
                        };
                        if rest.is_anonymous() {
                            break;
                        }
                        suffix = rest;
                    }
                }
                if let Some(info) = self.env.get_const(&namespaced) {
                    let levels: Vec<Level> = info
                        .level_params
                        .iter()
                        .map(|_| self.fresh_universe_param())
                        .collect();
                    return Ok(Expr::const_(namespaced, levels));
                }
                // Also check inductives/constructors/recursors that might not
                // be in the constants map but are registered separately.
                // This handles cases like `Int.land` where `land` was defined
                // inside `namespace Int` and registered as an inductive/ctor.
                // (Part of #3410)
                if self.env.get_inductive(&namespaced).is_some()
                    || self.env.get_constructor(&namespaced).is_some()
                    || self.env.get_recursor(&namespaced).is_some()
                {
                    return Ok(self.mk_const(&namespaced));
                }
                if field_name == SurfaceName::generated_path("decEq") {
                    let dec_eq = Name::from_string("decEq");
                    if let Some(info) = self.env.get_const(&dec_eq) {
                        let levels: Vec<Level> = info
                            .level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        return Ok(Expr::const_(dec_eq, levels));
                    }
                }
            }
            // #3139 / B18: dot notation on an auto-implicit / opaque FVar
            // (`G : Type u` used as `G.Adj`) has no namespace to resolve against.
            // This is a LOUD `UnknownIdent` — it previously fell back to a
            // synthetic `sorryAx` placeholder "so the rest of the file can
            // elaborate", which silently smuggled `sorryAx` into the term (and
            // bumped the sorry-axiom trust counter) on an unresolvable field.
            // A failed elaboration must never inject `sorryAx`.
            if matches!(val_whnf.get_app_fn().kind(), ExprKind::FVar(_)) {
                return Err(ElabError::UnknownIdent(format!(
                    "{field_name} (dot notation on a variable with no namespace)"
                )));
            }
            return Err(ElabError::UnknownIdent(format!(
                "{field_name} (dot notation on type-valued expression)"
            )));
        }

        // When the expression's type is a Pi, dot notation resolves in one of
        // several ways depending on whether the Pi's LEADING binder is implicit
        // or explicit. Insert the leading implicit/instance args once (#2680:
        // a wrapped inductive local has implicit Pi binders for header
        // auto-implicits before the first default binder); `insert_implicit_args`
        // stops at the first explicit binder, so the peel is exactly the leading
        // implicit/inst run.
        if let ExprKind::Pi(bi, _, _) = expr_ty_whnf.kind() {
            let leading_implicit = Self::is_implicit_binder(*bi);
            // Lean's order first: consume the receiver's leading implicits
            // WITHOUT unfolding, then resolve against the consumed type's own
            // head, unfolding one definition at a time only on a miss. The
            // Clean-specific attempts below run only when that finds nothing.
            if leading_implicit {
                self.metas.push_scope();
                match self.resolve_field_through_consumed_implicits(expr_val, &expr_ty, &field_name)
                {
                    Ok(Some(resolved)) => {
                        self.metas.commit();
                        return Ok(resolved);
                    }
                    Ok(None) => {
                        self.metas.pop_scope();
                    }
                    Err(err) => {
                        self.metas.pop_scope();
                        return Err(err);
                    }
                }
            }
            // Lean's `consumeImplicits` fills a receiver's `⦃x⦄` binder only
            // when the field access has arguments; this path does not see them,
            // so it keeps the arg-less reading (`ArgsFollow::No`).
            let (applied_expr, resolved_ty) =
                self.insert_implicit_args(expr_val.clone(), &expr_ty_whnf, ArgsFollow::No);
            let resolved_ty_whnf = self.whnf(&resolved_ty);

            // `.field` as a leading-dot constructor applied to the receiver.
            if let ExprKind::Pi(_, domain, _) = resolved_ty_whnf.kind() {
                let ctor_expr = self.elab_leading_dot_ctor_with_expected_type(
                    &field_name.clone().with_relative_constructor(),
                    domain.as_ref(),
                );
                if let Ok(ctor_expr) = ctor_expr {
                    return Ok(Expr::app(applied_expr, ctor_expr));
                }
            }

            // Fix A — method dot-notation on a receiver whose type is a Pi of
            // LEADING IMPLICIT/INSTANCE binders. For `lemma.mpr` / `lemma.trans`
            // / `lemma.symm` where `lemma : {α} … [inst] … → Iff X Y` (or
            // `→ Eq …`), the leading binders are all Implicit/InstImplicit, so
            // the `get_type_name` below bails ("cannot extract type name from
            // Pi(...)"). `insert_implicit_args` above already peeled exactly
            // those leading binders (applying fresh metavars/instances, stopping
            // at the first explicit binder), yielding `applied_expr : resolved_ty`
            // with `resolved_ty` the now-concrete head type (`Iff X Y`). Resolve
            // `<Head>.<field>` against that head with the peeled application as
            // the receiver. Explicit (Default) arrows are NOT peeled here — a
            // genuine function type is handled by Fix B below.
            //
            // SOUNDNESS: elaboration-completeness only. This changes only HOW the
            // dot-notation HEAD is resolved (which constant + inserted
            // implicit/instance args); the resulting application is still fully
            // elaborated and kernel-re-checked (`apply_dot_receiver` unifies the
            // receiver into the self-slot; the kernel re-checks the produced
            // term). No kernel/TCB touched.
            if leading_implicit && !matches!(resolved_ty_whnf.kind(), ExprKind::Pi(_, _, _)) {
                if let Ok(type_name) = self.get_type_identity(&resolved_ty) {
                    let name = self.with_private_step(crate::namespace::append_names(
                        &type_name,
                        field_name.name(),
                    ));
                    if let Some(info) = self.env.get_const(&name) {
                        if self.is_const_accessible(&name) {
                            let const_level_params = info.level_params.clone();
                            let const_type = info.type_.clone();
                            let levels: Vec<Level> = const_level_params
                                .iter()
                                .map(|_| self.fresh_universe_param())
                                .collect();
                            let fn_type = if levels.is_empty() {
                                const_type
                            } else {
                                const_type
                                    .instantiate_level_params_direct(&const_level_params, &levels)
                            };
                            let fn_expr = Expr::const_(name, levels);
                            return self.apply_dot_receiver(
                                fn_expr,
                                &fn_type,
                                &applied_expr,
                                &resolved_ty,
                                &type_name,
                            );
                        }
                    }
                }
            }

            // Fix B — dot-notation on a genuinely function-typed (explicit-arrow
            // Pi) receiver resolves in the `Function` namespace. `g.Injective`
            // where `g : β → α` has type `Pi(Default, β, α)` (an explicit arrow):
            // Lean resolves this as `Function.Injective g`. When the receiver
            // type's LEADING binder is explicit (a real function value, not an
            // implicit-led lemma), resolve `Function.<field>` and apply the
            // receiver as its first explicit (function) argument, inserting
            // `Function.<field>`'s own leading implicits first and pinning their
            // carrier metavariables from the receiver's actual function type.
            //
            // SOUNDNESS: elaboration-completeness only (see the Fix A note); the
            // produced `Function.<field> … receiver` application is kernel-
            // re-checked. No kernel/TCB touched.
            if !leading_implicit {
                if let Some(applied) =
                    self.apply_function_namespace_field(&field_name, expr_val, &expr_ty)
                {
                    return Ok(applied);
                }
            }
        }

        // Name the target instead of dumping the receiver's normalised type.
        //
        // `get_type_name` (`infer/elab_match/helpers.rs`) WHNFs before reading
        // the head, so a `def`-based alias or a projection stuck on an opaque
        // instance variable has no nameable head by the time it looks — and its
        // refusal, `NotImplemented("cannot extract type name from <Expr dump>")`,
        // deleted the identifier that failed to resolve and printed a raw
        // expression in its place. That message is 44 of the 497 failures in the
        // 2026-08-25 five-file Mathlib-source measurement
        // (`docs/analysis/frontier-next-class-2026-08-25.md` §5), and it named
        // neither the identifier nor which of `get_type_name`'s ~15 call sites
        // raised it, so the class could not be triaged from the artifact.
        //
        // This is a MESSAGE repair and nothing else: it runs only where
        // resolution has already failed, on the `?` path this line always took,
        // and no site selects on the error's shape (the `UnknownIdent` matches
        // in `elab_proj` above are on the RECEIVER's elaboration, which has long
        // since succeeded here). Which declarations elaborate is byte-identical
        // — verified probe-by-probe against `tests/fixtures/source_frontier/`.
        //
        // Naming the target is honest here specifically because the un-reduced
        // head has already been tried: the Track-UU pre-whnf lookup above ran
        // `<head>.<field>` through `get_const` + `is_const_accessible` and found
        // nothing, so `<head>.<field>` is known-unresolvable at this point. The
        // repair also makes this site self-identifying: any
        // `cannot extract type name from …` still left in a future corpus report
        // is definitively one of the OTHER callers (the match-lowering family),
        // which is the per-site attribution the artifact could not give.
        // Generalized field notation reads the receiver type's head constant
        // BEFORE reducing it — `hf.injective.comp_left` with
        // `hf.injective : Function.Injective f` looks up
        // `Function.Injective.comp_left` — and reduces only when no such
        // constant exists (Lean's `resolveLValLoop` unfolds one step at a
        // time). `get_type_identity` reduces first, so a receiver whose type is
        // a `∀`-bodied definition lost its head ("whose head does not name a
        // type after reduction (Pi)": `Function.Bijective.comp_left` in
        // `Mathlib/Logic/Function/Basic.lean`, measured 2026-09-11).
        let head_first = match self.metas.instantiate(&expr_ty).get_app_fn().kind() {
            ExprKind::Const(head, _)
                if {
                    let candidate = self.with_private_step(
                        SurfaceName::from_name(head.clone())
                            .append(&field_name)
                            .into_name(),
                    );
                    self.env.get_const(&candidate).is_some() && self.is_const_accessible(&candidate)
                } =>
            {
                Some(head.clone())
            }
            _ => None,
        };
        let type_name = match head_first {
            Some(type_name) => type_name,
            None => match self.get_type_identity(&expr_ty) {
                Ok(type_name) => type_name,
                Err(_) => return Err(self.unresolved_dot_target(&expr_ty, &field_name)),
            },
        };
        let const_name = SurfaceName::from_name(type_name.clone()).append(&field_name);
        let name = self.with_private_step(const_name.name().clone());

        // Recursive self-call via method dot-notation (#522, Track R).
        //
        // `elemTy.bitWidth` inside `def Ty.bitWidth` resolves to
        // `Ty.bitWidth elemTy`. During the function's own elaboration the
        // constant is not yet registered, so the lookup below would fail. When
        // `elemTy` is the recursive sub-field of the decreasing argument it has
        // an induction hypothesis bound in the current arm; substitute that IH
        // (the value of the recursive call) so the structural lowering routes
        // the call through `Ty.rec` instead of a dangling self-reference.
        if let Some(ctx) = self.recursive_def_ctx.clone() {
            if ctx.matches_call_name(&const_name) {
                if let ExprKind::FVar(recv_fvar) = expr_val.kind() {
                    if let Some(&ih_fvar) = ctx.ih_map.get(recv_fvar) {
                        // The generalized parameters are whatever this IH is
                        // later applied to, which this path does not see:
                        // count every one as changed by a recursive call
                        // (`recursion_site`).
                        for &index in &ctx.generalized_params {
                            if let Some(param) = ctx.parameters.get(index) {
                                self.recursive_changed_params.insert(param.fvar);
                            }
                        }
                        return Ok(Expr::fvar(ih_fvar));
                    }
                }
            }
        }

        // Check if the constant exists and get its type. Another module's
        // `private` declaration does not exist here: Lean's `resolveLValLoop`
        // looks up `T.f` and the CURRENT module's private `T.f` only, so an
        // imported `private def Nat.three` is no target for `(0 : Nat).three`
        // (Clean used to find it and credit `(0 : Nat).three = 3`).
        let accessible = self.is_const_accessible(&name);
        let const_info = match self.env.get_const(&name).filter(|_| accessible) {
            Some(info) => info,
            None => {
                // Nested-aux container coercion (#3239 follow-up).
                //
                // When the receiver's type is a nested-aux mirror (e.g.
                // `Value._List`, synthesised for `List Value` during nested
                // inductive elimination), container methods like `xs.length`
                // do not resolve as `Value._List.length`. If the kernel
                // generated `<aux>.toContainer : <aux> → <Container args>`,
                // route the method through the real container by inserting the
                // (axiom-free) conversion: `xs.length` becomes
                // `List.length (Value._List.toContainer xs)`.
                if let Some(result) =
                    self.try_aux_container_dot(&type_name, &field_name, expr_val)?
                {
                    return Ok(result);
                }
                return Err(self.unknown_ident_error(&const_name));
            }
        };
        let const_level_params = const_info.level_params.clone();
        let const_type = const_info.type_.clone();

        // Build T.field and place the receiver in the correct argument slot.
        // Use fresh universe parameters for universe-polymorphic constants.
        let levels: Vec<Level> = const_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        // CRITICAL: substitute the fresh levels into the function's type so it is
        // consistent with `fn_expr`'s level instantiation. The raw `const_info.type_`
        // still mentions the *declared* universe params (e.g. `u`), whereas
        // `fn_expr` is `T.field.{u_1}`. For a universe-polymorphic projection such
        // as an imported `Subtype.val : {α : Sort u} {p : α → Prop} → Subtype p → α`,
        // `apply_dot_receiver` unifies the receiver's actual type into the self
        // slot; if the slot still names the declared `u`, the solver constrains `u`
        // (which never appears in `fn_expr`) and leaves the term's `u_1` unsolved —
        // the kernel then rejects `T.field.{u_1} α …` because `α : Sort 1` cannot be
        // checked against the rigid `Sort u_1`. Substituting first means the unifier
        // solves the *same* level metavariable that the emitted term carries.
        let fn_type = if levels.is_empty() {
            const_type
        } else {
            const_type.instantiate_level_params_direct(&const_level_params, &levels)
        };
        let fn_expr = Expr::const_(name, levels);
        self.apply_dot_receiver(fn_expr, &fn_type, expr_val, &expr_ty, &type_name)
    }

    /// Build the named refusal for a dot-notation target that did not resolve
    /// on a receiver whose type has no nameable head after normalisation.
    ///
    /// Diagnostic only — see the call site in `elab_dot_notation` for why this
    /// changes no verdict and why the named identifier is known-unresolvable by
    /// the time it is reported.
    ///
    /// The name is taken from the receiver type's UN-REDUCED head, which is the
    /// namespace Lean resolves dot notation against (`resolveLValLoop`,
    /// `Lean/Elab/App.lean`) and the one the pre-whnf lookup above already
    /// consulted. When that head is not a constant there is no namespace to
    /// name, so the field is reported alone rather than guessed at.
    fn unresolved_dot_target(&self, expr_ty: &Expr, field_name: &SurfaceName) -> ElabError {
        let name = match expr_ty.get_app_fn().kind() {
            ExprKind::Const(head, _) => format!("{head}.{field_name}"),
            _ => field_name.to_string(),
        };
        ElabError::UnresolvedDotTarget {
            name,
            field: field_name.to_string(),
            receiver: format!("{expr_ty}"),
            normalized_head: self.describe_normalized_head(expr_ty),
        }
    }

    /// Compact label for the head `get_type_name` could not name.
    ///
    /// Mirrors that function's own walk — normalise, then descend the
    /// application spine, re-normalising each function head — so the label
    /// describes the expression it actually rejected. Only the constructor is
    /// reported (plus the structure and index for a projection, which is what
    /// separates this class's stuck-projection face from its unfolded-alias
    /// face); the full `Expr` dump this replaces is what made the class
    /// untriageable in the first place.
    fn describe_normalized_head(&self, expr_ty: &Expr) -> String {
        // Spine depth is bounded so a pathological term cannot turn a
        // diagnostic into a hang; `get_type_name` is stack-safe for the same
        // reason. A spine this deep has no nameable head anyway.
        const MAX_SPINE: usize = 256;
        let mut head = self.whnf(expr_ty);
        for _ in 0..MAX_SPINE {
            let ExprKind::App(func, _) = head.kind() else {
                break;
            };
            head = self.whnf(func);
        }
        match head.kind() {
            ExprKind::Pi(..) => "Pi".to_string(),
            ExprKind::Lam(..) => "Lam".to_string(),
            ExprKind::Sort(_) => "Sort".to_string(),
            ExprKind::Let(..) => "Let".to_string(),
            ExprKind::Lit(_) => "Lit".to_string(),
            ExprKind::BVar(_) => "BVar".to_string(),
            ExprKind::Proj(struct_name, idx, _) => format!("Proj({struct_name}, {idx})"),
            ExprKind::FVar(_) => "opaque type variable".to_string(),
            ExprKind::Const(head_name, _) => format!("Const({head_name})"),
            _ => "unnameable head".to_string(),
        }
    }

    /// Nested-aux container coercion for dot notation (#3239 follow-up).
    ///
    /// If `type_name` is a nested-aux mirror type with a generated conversion
    /// `<type_name>.toContainer : <type_name> → <Container args>`, and the
    /// requested `field` resolves as a container method `<Container>.field`,
    /// build `<Container>.field … (<type_name>.toContainer receiver)`.
    ///
    /// Returns `Ok(None)` if no `toContainer` exists or the container method is
    /// not found — callers then fall through to the usual unknown-ident error.
    fn try_aux_container_dot(
        &mut self,
        type_name: &Name,
        field_name: &SurfaceName,
        receiver: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        let to_container_name = type_name.clone().str("toContainer");
        let tc_info = match self.env.get_const(&to_container_name) {
            Some(info) => info,
            None => return Ok(None),
        };
        let tc_level_params = tc_info.level_params.clone();
        let tc_type = tc_info.type_.clone();

        // toContainer : <aux> → <Container args...>. The codomain is the
        // container application; its head names the container inductive.
        let container_app = match tc_type.kind() {
            ExprKind::Pi(_, _, body) => (**body).clone(),
            _ => return Ok(None),
        };
        let container_head = container_app.get_app_fn();
        let container_name = match container_head.kind() {
            ExprKind::Const(n, _) => n.clone(),
            _ => return Ok(None),
        };

        // The container method must exist (e.g. `List.length`).
        let method_name = crate::namespace::append_names(&container_name, field_name.name());
        let method_info = match self.env.get_const(&method_name) {
            Some(info) => info,
            None => return Ok(None),
        };
        let method_level_params = method_info.level_params.clone();
        let method_type = method_info.type_.clone();

        // Build the conversion `<aux>.toContainer.{u…} receiver`, instantiating
        // toContainer's own universe params with fresh metavariables.
        let tc_levels: Vec<Level> = tc_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        let tc_fn = Expr::const_(to_container_name, tc_levels.clone());
        let converted = Expr::app(tc_fn, receiver.clone());
        // The converted receiver's type is the container application with the
        // same universe instantiation applied.
        let converted_ty = if tc_levels.is_empty() {
            container_app
        } else {
            container_app.instantiate_level_params_direct(&tc_level_params, &tc_levels)
        };

        // Resolve the container method with the converted value as receiver.
        let method_levels: Vec<Level> = method_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        let method_fn_type = if method_levels.is_empty() {
            method_type
        } else {
            method_type.instantiate_level_params_direct(&method_level_params, &method_levels)
        };
        let method_fn = Expr::const_(method_name, method_levels);
        let result = self.apply_dot_receiver(
            method_fn,
            &method_fn_type,
            &converted,
            &converted_ty,
            &container_name,
        )?;
        Ok(Some(result))
    }

    /// Apply a dot-notation receiver to `T.field`, placing it in the correct
    /// argument slot.
    ///
    /// Lean 4 dot notation does **not** simply apply the receiver as the first
    /// explicit argument: it inserts the receiver at the *first explicit
    /// parameter whose type's head is the namespace type* `T`, filling any
    /// preceding explicit parameters with metavariables (solved by unification)
    /// and inserting implicit/instance arguments as usual. This matters for any
    /// `T.field` whose type binds parameters before the "self" argument — most
    /// notably **imported structure projections**: a Lean-compiled structure
    /// `MyPair (α β : Type)` imports `MyPair.fst : (α β : Type) → MyPair α β → α`
    /// with the two *explicit* type parameters preceding the receiver. Treating
    /// the receiver as the first explicit argument would pass it where `α : Type`
    /// is expected, so the projection would fail to type-check rather than
    /// reduce to the field.
    ///
    /// We locate the receiver slot by matching the binder type's head constant
    /// against `type_name`, unify the receiver's actual type into that binder's
    /// expected type so the leading metavariables (here `α`, `β`) get solved,
    /// then continue inserting any trailing implicit arguments. If no explicit
    /// binder's head matches `T` (e.g. a plain namespaced function), we fall back
    /// to the historical behavior of applying the receiver after implicit-arg
    /// insertion, preserving existing dot-notation semantics.
    pub(super) fn apply_dot_receiver(
        &mut self,
        fn_expr: Expr,
        fn_type: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
        type_name: &Name,
    ) -> Result<Expr, ElabError> {
        // A recursor-family head with an EXPLICIT motive (`x.casesOn`,
        // `x : Empty`) is Lean's eliminator elaboration, not a lambda over
        // the motive (`elab_dot_elim.rs`).
        if let Some(decided) =
            self.dot_explicit_motive_eliminator(&fn_expr, fn_type, receiver, receiver_ty, type_name)
        {
            return decided;
        }
        let mut result = fn_expr;
        let mut ty = self.whnf(fn_type);

        // Explicit binders encountered *before* the receiver slot. Rather than
        // filling them with metavariables (which would saturate the term and
        // leave no room for the caller's trailing positional arguments — e.g.
        // `(List.range n).foldl f init`, where `foldl`'s explicit order is
        // `f, init, l` and the receiver lands in the *third* slot), we re-bind
        // them as lambda parameters so the surrounding application can supply
        // them. This matches Lean 4's generalized field-notation, which inserts
        // the receiver at its matching slot and routes the remaining explicit
        // arguments to the other parameters positionally.
        let mut pre_receiver_binders: Vec<(FVarId, BinderInfo, Expr)> = Vec::new();
        // Instance-implicit binders that appear BEFORE the receiver slot must not
        // be resolved eagerly: their carrier (e.g. `?α` in `[BEq ?α]` of
        // `List.contains {α} [BEq α] (l : List α) (a : α)`) is pinned only by the
        // *receiver* (`l : List Int`), which is applied later. Eager
        // `resolve_instance(BEq ?α)` would unify against the first registered `BEq`
        // instance (`instBEqNat`, pinning `?α := Nat`) and then the element type
        // mismatches (`Int` vs `Nat`). Defer them exactly like elab_app's leading
        // instances (`resolve_deferred_instances`), and resolve after the receiver
        // unification below pins the carrier.
        let mut pending_insts: Vec<(Expr, Expr)> = Vec::new();

        while let ExprKind::Pi(bi, arg_ty, body_ty) = ty.kind() {
            let arg_ty_inst = self.metas.instantiate(arg_ty);

            // Receiver ("self") slot detection, computed for EVERY binder (not
            // just explicit ones): the slot is the receiver's when its type head
            // is the namespace type `T`.
            //
            // Check the *syntactic* (un-WHNF'd) head first: when `T` is a
            // definition that unfolds to a `Pi` (Track UU, e.g.
            // `def ValueMap := ValueId → Option Value`, so the self-slot of
            // `ValueMap.get : ValueMap → ValueId → Option Value` is written
            // `ValueMap` but WHNFs to a function type), WHNFing the slot type
            // destroys the `ValueMap` head and the self-slot would never match.
            // Matching the syntactic head recovers it. Fall back to the WHNF
            // head for the ordinary case where the slot type only reveals its
            // head constant after reduction (e.g. an abbreviation
            // `def MyNat := Nat` used as the self type).
            let syntactic_head_matches = matches!(
                arg_ty_inst.get_app_fn().kind(),
                ExprKind::Const(n, _) if n == type_name
            );
            let arg_head = self.whnf(&arg_ty_inst);
            let head_matches = syntactic_head_matches
                || matches!(
                    arg_head.get_app_fn().kind(),
                    ExprKind::Const(n, _) if n == type_name
                );

            // A CLASS projection carries its receiver as an INSTANCE-IMPLICIT
            // `self` (`@B.f : {α} → [self : B α] → …` — B06/`mkProjections`), so
            // the receiver slot is not an explicit binder. When an implicit /
            // inst-implicit binder's type head IS the receiver type `T`, treat it
            // as the receiver slot and plug the receiver in (rather than
            // synthesizing/deferring it as an ordinary instance argument, which
            // left `b.f` mis-applied — the receiver landed AFTER the fully-applied
            // result, a `NotAFunction`). Other inst-implicit binders (e.g.
            // `[BEq ?α]`, whose head is `BEq`, not `T`) are still deferred.
            if !head_matches && Self::is_implicit_binder(*bi) {
                // Implicit / strict-implicit / instance argument: synthesize as
                // `insert_implicit_args` would, then continue. Instance args are
                // deferred (see `pending_insts` above) rather than resolved here.
                let arg = self.fresh_meta(arg_ty_inst.clone());
                if bi.info == BinderInfo::InstImplicit {
                    pending_insts.push((arg.clone(), arg_ty_inst.clone()));
                }
                result = Expr::app(result, arg.clone());
                ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&arg)));
                continue;
            }

            if head_matches {
                // Unify the receiver's actual type into the expected slot type so
                // the leading explicit metavariables (the structure's type
                // parameters) are solved from the receiver. This is best-effort:
                // the kernel re-checks the final term regardless.
                self.try_unify(&arg_ty_inst, receiver_ty);
                // Receiver unification has now pinned the carrier metavars (e.g.
                // `?α := Int`); resolve the instance-implicit args deferred above
                // against the pinned carrier (`BEq Int -> instBEqInt`). A goal
                // the receiver did NOT pin (`[Monad ?m]` of `ids.mapM look`,
                // pinned only by `look` or the expected type) is QUEUED for the
                // application's drain, never dropped (G37).
                self.resolve_or_queue_dot_receiver_instances(&pending_insts);
                let applied = Expr::app(result, receiver.clone());
                // Substitute all solved type/universe params before the term
                // leaves the dot path (mirrors elab_app's "all solved level
                // constraints substituted" contract). The self-slot unification
                // above solves the leading element-type metavariable (`?α := Nat`)
                // and the fresh universe params (`u := 0`); without instantiating
                // here the emitted `T.f.{u} ?α receiver` would still carry a raw
                // universe param and an unsolved metavar, which the caller's
                // result-type check then mis-reads. The kernel re-checks the
                // substituted term, so this only normalizes — it relaxes nothing.
                let applied = self.metas.instantiate(&applied);
                let applied = self.metas.instantiate_levels(&applied);
                // Re-bind the pre-receiver explicit binders (if any) as lambda
                // parameters wrapping the receiver-applied term, abstracting each
                // recorded fvar in reverse (innermost binder first).
                return Ok(Self::wrap_pre_receiver_lambdas(
                    applied,
                    &pre_receiver_binders,
                ));
            }

            // Explicit binder *before* the receiver slot: record it as a lambda
            // parameter (a genuine fvar, not a metavariable) so the trailing
            // application arguments can fill it positionally.
            let fvar_id = self.fresh_fvar();
            let fvar = Expr::fvar(fvar_id);
            pre_receiver_binders.push((fvar_id, bi.info, arg_ty_inst.clone()));
            result = Expr::app(result, fvar.clone());
            ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&fvar)));
        }

        // No explicit `T`-headed parameter found: preserve historical behavior of
        // applying the receiver after implicit-argument insertion. Any explicit
        // binders we tentatively re-bound above are still abstracted so the term
        // stays well-formed.
        // The receiver is applied next, so `⦃x⦄` binders before it are filled.
        let (fn_with_implicits, _) = self.insert_implicit_args(result, &ty, ArgsFollow::Yes);
        let applied = Expr::app(fn_with_implicits, receiver.clone());
        // Substitute solved type/universe params before the term leaves the dot
        // path (see the receiver-slot return above for rationale).
        let applied = self.metas.instantiate(&applied);
        let applied = self.metas.instantiate_levels(&applied);
        Ok(Self::wrap_pre_receiver_lambdas(
            applied,
            &pre_receiver_binders,
        ))
    }

    /// Resolve each instance-implicit goal of a dot-notation head that the
    /// receiver unification has made resolvable; QUEUE every other goal that
    /// still mentions a metavariable for the postponed-instance drain
    /// (`retry_postponed_open_carrier_instances`, run at the end of the
    /// enclosing application and of the declaration body), as Lean's
    /// synthetic instance metavariables are resumed by
    /// `synthesizeSyntheticMVars` (G37, ledger class (107)).
    ///
    /// The result of `resolve_deferred_instances` was discarded here, so such
    /// a goal's metavariable stayed unassigned with nothing left to solve it:
    /// `ids.mapM look` failed "failed to synthesize instance `Monad Option`"
    /// on a goal that WAS resolvable once `look` had pinned `?m := Option`.
    /// A GROUND goal with no instance is not queued: its metavariable stays
    /// unassigned and the declaration-close residual guard reports it, as
    /// before.
    fn resolve_or_queue_dot_receiver_instances(&mut self, pending: &[(Expr, Expr)]) {
        for (meta_arg, goal_ty) in pending {
            let goal = self.whnf(&self.metas.instantiate(goal_ty));
            let meta_id = match meta_arg.kind() {
                ExprKind::FVar(fvar) => MetaState::from_fvar(*fvar),
                _ => None,
            };
            let Some(meta_id) = meta_id else {
                continue;
            };
            if self.metas.is_assigned(meta_id) {
                continue;
            }
            let assigned = self
                .resolve_instance(&goal)
                .is_some_and(|inst| self.metas.assign(meta_id, inst));
            if !assigned {
                self.record_postponed_stuck_instance(meta_arg, &goal);
            }
        }
    }

    /// Wrap `body` in lambdas for each recorded pre-receiver explicit binder,
    /// abstracting their fvars. Binders are abstracted innermost-first so the
    /// resulting `λ a₁ … aₙ => body` re-exposes them in source order for the
    /// caller's positional arguments.
    fn wrap_pre_receiver_lambdas(body: Expr, binders: &[(FVarId, BinderInfo, Expr)]) -> Expr {
        let mut acc = body;
        for (fvar_id, info, arg_ty) in binders.iter().rev() {
            let closed = acc.abstract_fvar(*fvar_id);
            acc = Expr::lam(*info, arg_ty.clone(), closed);
        }
        acc
    }

    /// Try to collect a qualified name from nested projections.
    /// For `Foo.bar.baz` parsed as `Proj(Proj(Ident("Foo"), "bar"), "baz")`,
    /// this returns `Some("Foo.bar")` when called with the inner projection.
    ///
    /// Used for namespace-only prefix disambiguation (#497, #501):
    /// When `Foo` isn't a constant but `Foo.bar` or `Foo.bar.baz` is,
    /// we need to collect the full dotted name and look it up.
    pub(crate) fn try_collect_qualified_name(
        base: &SurfaceExpr,
        proj: &Projection,
    ) -> Option<SurfaceName> {
        stack_safe(|| {
            let field = match proj {
                Projection::Named(n) if !n.is_relative_constructor() && !n.is_anonymous() => n,
                Projection::Named(_) => return None,
                Projection::Index(_) => return None,
            };

            match base {
                SurfaceExpr::Ident(_, name) => Some(name.append(field)),
                SurfaceExpr::Proj(_, inner_base, inner_proj) => {
                    let base_qualified = Self::try_collect_qualified_name(inner_base, inner_proj)?;
                    Some(base_qualified.append(field))
                }
                _ => None,
            }
        })
    }

    /// Resolve the projection target for a single-constructor inductive.
    ///
    /// Ensures the receiver's type reduces to a single-constructor inductive and
    /// returns `(struct_name, num_fields, is_registered_structure)`. The
    /// `is_registered_structure` flag is `true` iff the inductive was declared
    /// (or registered) as a Lean `structure` and therefore has field-name
    /// metadata.
    ///
    /// This mirrors Lean's `resolveLValAux` (`Lean/Elab/App.lean`,
    /// `LVal.fieldIdx` case): numeric `.N` projection is valid on ANY
    /// one-constructor inductive (`matchConstStructure`), with the field count
    /// taken from the constructor — NOT gated on `structure`-ness. Only the
    /// *named* `.field` accessor requires `structure` metadata. The caller
    /// (`elab_proj`) is responsible for branching on the projection kind:
    /// `Index` proceeds for any single-ctor inductive (kernel `Expr.proj`),
    /// while `Named` requires `is_structure` (else falls through to
    /// dot-notation, e.g. `τ.eval` where `T` is a plain inductive with a def
    /// `T.eval`, not a structure field).
    pub(crate) fn resolve_projection_target(
        &self,
        expr: &Expr,
    ) -> Result<(Name, u32, bool), ElabError> {
        let expr_ty = self.infer_type(expr)?;
        let expr_ty_whnf = self.whnf(&expr_ty);

        let struct_name = match expr_ty_whnf.get_app_fn().kind() {
            ExprKind::Const(name, _) => name.clone(),
            // The receiver's whole type, not the bare head kind — same reason
            // as the sibling site in `elab_app`.
            _ => {
                return Err(ElabError::InvalidProjectionTarget(
                    crate::error_render::term(&expr_ty_whnf),
                ))
            }
        };

        let ind = self.env.get_inductive(&struct_name).ok_or_else(|| {
            ElabError::InvalidProjectionTarget(crate::error_render::term(&expr_ty_whnf))
        })?;

        if ind.constructor_names.len() != 1 {
            return Err(ElabError::InvalidProjectionTarget(
                crate::error_render::term(&expr_ty_whnf),
            ));
        }

        // A single-constructor inductive is projectable. Whether it carries
        // structure field-name metadata distinguishes the *named* accessor path
        // (`structure`s) from the raw `Expr.proj` index path (plain
        // `inductive`s like `And`/`Iff`). See the per-kind branch in
        // `elab_proj`.
        let is_registered_structure = self.env.get_structure_field_names(&struct_name).is_some();

        let ctor_name = &ind.constructor_names[0];
        let ctor = self.env.get_constructor(ctor_name).ok_or_else(|| {
            ElabError::InvalidProjectionTarget(format!("missing constructor {ctor_name}"))
        })?;

        Ok((struct_name, ctor.num_fields, is_registered_structure))
    }

    /// Numeric `.idx` projection on a receiver whose type is a LEADING-IMPLICIT
    /// `Pi`, by peeling the leading implicit/instance binders to expose a
    /// single-constructor inductive head, then emitting the kernel projection.
    ///
    /// Handles e.g. `not_and_or.1` where
    /// `not_and_or : {a b : Prop} → (¬(a ∧ b) ↔ ¬a ∨ ¬b)`: the receiver type is
    /// an implicit-led Pi that `resolve_projection_target` cannot name, but after
    /// `insert_implicit_args` peels `{a} {b}` the applied receiver has type
    /// `Iff …` — a single-constructor structure projectable by index.
    ///
    /// Returns `Ok(None)` when the receiver type is NOT a leading-implicit Pi (so
    /// ordinary receivers are untouched) or the peeled head is still not a
    /// single-constructor inductive (so the caller falls through to its existing
    /// dot-notation error). The `Index` bounds are mirrored from `elab_proj`'s
    /// direct-structure path (`.0` rejected, `idx <= num_fields` required).
    fn try_index_proj_through_implicits(
        &mut self,
        expr_val: &Expr,
        idx: u32,
    ) -> Result<Option<Expr>, ElabError> {
        let expr_ty = self.infer_type(expr_val)?;
        let expr_ty_whnf = self.whnf(&expr_ty);
        // Only engage when the receiver's type is a leading-implicit/instance Pi —
        // the exact shape `resolve_projection_target` rejects for an unapplied
        // implicit-parameterized lemma. A concretely-typed receiver (`Const`-headed
        // structure application) never reaches here.
        if !matches!(
            expr_ty_whnf.kind(),
            ExprKind::Pi(bi, _, _) if Self::is_implicit_binder(*bi)
        ) {
            return Ok(None);
        }
        let (applied_expr, _) =
            self.insert_implicit_args(expr_val.clone(), &expr_ty_whnf, ArgsFollow::No);
        match self.resolve_projection_target(&applied_expr) {
            Ok((struct_name, num_fields, is_structure)) => {
                if idx == 0 || idx > num_fields {
                    return Err(ElabError::ProjectionIndexOutOfBounds {
                        struct_name,
                        idx,
                        field_count: num_fields,
                    });
                }
                // The direct path's private-field refusal (G21 B3).
                if is_structure {
                    self.check_imported_private_field_index(&struct_name, idx)?;
                }
                // Substitute the metavariables/levels the implicit peel introduced
                // before the projected term leaves the dot path (mirrors
                // `apply_dot_receiver`); the kernel re-checks the result.
                let applied_expr = self.metas.instantiate(&applied_expr);
                let applied_expr = self.metas.instantiate_levels(&applied_expr);
                Ok(Some(Expr::proj(struct_name, idx - 1, applied_expr)))
            }
            Err(_) => Ok(None),
        }
    }
}

#[cfg(test)]
mod typed_local_projection_tests {
    use super::*;

    #[test]
    fn scoped_self_alias_uses_one_existing_binder_and_restores_after_refusal() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let owner = ctx.push_local(SurfaceName::generated_path("B"), Expr::prop());
        let alias = SurfaceName::generated_path("A.B");
        let result: Result<(), ElabError> =
            ctx.with_local_name_alias(alias.clone(), owner, |ctx| {
                assert_eq!(ctx.locals.len(), 1);
                assert_eq!(
                    ctx.elaborate(&clean_parser::parse_expr("A.B").unwrap())?,
                    Expr::fvar(owner)
                );
                assert!(ctx
                    .lookup_local(&SurfaceName::component("A.B", true))
                    .is_none());
                let shadow = ctx.push_local(alias.clone(), Expr::prop());
                assert_eq!(ctx.lookup_local(&alias).map(|(id, _)| id), Some(shadow));
                ctx.pop_local();
                assert_eq!(ctx.lookup_local(&alias).map(|(id, _)| id), Some(owner));
                Err(ElabError::Unsupported {
                    feature: "intentional alias-scope refusal".into(),
                })
            });
        assert!(result.is_err());
        assert!(ctx.local_name_aliases.is_empty());
        assert_eq!(ctx.locals.len(), 1);
        assert!(ctx.lookup_local(&alias).is_none());
        assert_eq!(
            ctx.lookup_local(&SurfaceName::generated_path("B"))
                .map(|(id, _)| id),
            Some(owner)
        );
    }

    #[test]
    fn qualified_local_lookup_preserves_typed_identity_and_receiver_priority() {
        let env = Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let nested = ctx.push_local(SurfaceName::generated_path("A.B"), Expr::prop());
        let quoted = ctx.push_local(SurfaceName::component("A.B", true), Expr::prop());
        assert_eq!(
            ctx.elaborate(&clean_parser::parse_expr("A.B").unwrap())
                .unwrap(),
            Expr::fvar(nested)
        );
        assert_eq!(
            ctx.elaborate(&clean_parser::parse_expr("«A.B»").unwrap())
                .unwrap(),
            Expr::fvar(quoted)
        );

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let product = Expr::apps(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone()],
        );
        let receiver = ctx.push_local(SurfaceName::generated_path("x"), product);
        let other = ctx.push_local(SurfaceName::generated_path("x.fst"), nat);
        let result = ctx
            .elaborate(&clean_parser::parse_expr("x.fst").unwrap())
            .unwrap();
        assert_ne!(result.abstract_fvar(receiver), result);
        assert_eq!(result.abstract_fvar(other), result);
    }
}

#[cfg(test)]
#[path = "elab_proj_instance_tests.rs"]
mod instance_tests;
