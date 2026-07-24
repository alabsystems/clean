// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection and qualified-name elaboration.
//!
//! Handles `SurfaceExpr::Proj` (dotted notation like `x.y`) including:
//! - Structure field projection (`s.field`)
//! - Dot notation for non-structure types (`expr.method` → `T.method expr`)
//! - Qualified name disambiguation (`Foo.bar.baz` → constant lookup)

use super::*;
use crate::stack_safe;

impl<'a> ElabCtx<'a> {
    /// Elaborate a projection expression (`base.field` or `base.0`).
    ///
    /// Handles three cases:
    /// 1. Structure projection: `s.field` → `proj(StructName, idx, s)`
    /// 2. Dot notation: `expr.method` → `T.method expr` where `T = typeof(expr)`
    /// 3. Qualified name: `Foo.bar` where `Foo` is a namespace, not a value
    pub(crate) fn elab_proj(
        &mut self,
        expr: &SurfaceExpr,
        proj: &clean_parser::Projection,
    ) -> Result<Expr, ElabError> {
        // Projection/qualified-name disambiguation (#497, #501):
        // The parser produces Proj for all dotted terms like `x.y`.
        // If the base fails to elaborate with UnknownIdent and it's a simple Ident,
        // try resolving the concatenated name `x.y` as a constant first.
        // This handles namespace-only prefixes where `x` isn't a value but `x.y` is.

        // Unwrap parentheses to handle cases like (Foo).bar
        let unwrapped = Self::unwrap_surface_parens(expr);

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
            if let clean_parser::Projection::Named(field) = proj {
                // Root-namespace escape: `_root_.Bool` parses as
                // `Proj(Ident("_root_"), "Bool")`. Resolve the field as a global
                // name with the marker stripped (Track R: `Ty.isSigned : Ty →
                // _root_.Bool`). Defer to `elab_ident` which knows how to resolve
                // a top-level constant / inductive / constructor.
                if base_name == "_root_" {
                    return self.elab_ident(&format!("_root_.{field}"));
                }
                // Only short-circuit when `base` is a *pure namespace* — not a
                // value in scope. If `base` itself denotes a value (a local, a
                // struct instance, an inductive/constructor), keep the existing
                // structure-projection / method dot-notation path so e.g.
                // `pairVal.snd` projects the field even when a `pairVal.snd`
                // constant also happens to exist.
                if !self.ident_resolves_to_value(base_name) {
                    let qualified = format!("{base_name}.{field}");
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
            if let clean_parser::Projection::Named(field) = proj {
                if let Some(base_qualified) =
                    Self::try_collect_qualified_name(inner_base, inner_proj)
                {
                    let leading = base_qualified
                        .split('.')
                        .next()
                        .unwrap_or(base_qualified.as_str());
                    if !self.ident_resolves_to_value(leading) {
                        let qualified = format!("{base_qualified}.{field}");
                        // `_root_.A.B.c`: the marker forces ROOT-only
                        // resolution of the remainder (Lean `rootNamespace`
                        // handling in `Lean/ResolveName.lean`).
                        if let Some(rest) = qualified.strip_prefix("_root_.") {
                            let root = Name::from_string(rest);
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
                            err @ (ElabError::UnknownIdent(_)
                            | ElabError::UnknownIdentWithSuggestions { .. }),
                        ) => {
                            // Base identifier not found - try qualified name fallback
                            if let clean_parser::Projection::Named(field) = proj {
                                let qualified = format!("{base_name}.{field}");
                                let name = Name::from_string(&qualified);
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
                                let qualified_err = self.unknown_ident_error(&qualified);
                                if matches!(
                                    qualified_err,
                                    ElabError::UnknownIdentWithSuggestions { .. }
                                ) {
                                    return Err(qualified_err);
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
                            err @ (ElabError::UnknownIdent(_)
                            | ElabError::UnknownIdentWithSuggestions { .. }),
                        ) => {
                            // Try to collect full qualified name from nested projections
                            if let clean_parser::Projection::Named(field) = proj {
                                if let Some(base_qualified) =
                                    Self::try_collect_qualified_name(inner_base, inner_proj)
                                {
                                    let qualified = format!("{base_qualified}.{field}");
                                    let name = Name::from_string(&qualified);
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
                                    let qualified_err = self.unknown_ident_error(&qualified);
                                    if matches!(
                                        qualified_err,
                                        ElabError::UnknownIdentWithSuggestions { .. }
                                    ) {
                                        return Err(qualified_err);
                                    }
                                    // Return error with full qualified name for better message
                                    return Err(ElabError::UnknownIdent(qualified));
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

        // Try single-constructor-inductive projection first.
        match self.resolve_projection_target(&expr_val) {
            Ok((struct_name, num_fields, is_structure)) => {
                // Single-ctor projection: expr.field -> proj(struct_name, idx, expr)
                match proj {
                    clean_parser::Projection::Named(name) => {
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
                        let field_name = Name::from_string(name);
                        match self
                            .env
                            .get_structure_field_index(&struct_name, &field_name)
                        {
                            Some(idx) => Ok(Expr::proj(struct_name, idx, expr_val)),
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
                                let field_names: Vec<String> = self
                                    .env
                                    .get_structure_field_names(&struct_name)
                                    .map(|fields| fields.iter().map(ToString::to_string).collect())
                                    .unwrap_or_default();
                                let suggestions =
                                    crate::agent_diagnostics::nearest_string_candidates(
                                        name,
                                        field_names.iter().map(String::as_str),
                                        5,
                                    );
                                Err(ElabError::UnknownProjectionField {
                                    struct_name: struct_name.clone(),
                                    field: name.clone(),
                                    suggestions,
                                })
                            }
                        }
                    }
                    clean_parser::Projection::Index(idx) => {
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
                if let clean_parser::Projection::Index(idx) = proj {
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
    fn is_known_accessible_global(&self, name: &Name) -> bool {
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
    fn resolve_qualified_chain(&self, dotted: &str) -> Option<Name> {
        if !self.namespace_prefix.is_empty() {
            let mut prefix = self.namespace_prefix.as_str();
            loop {
                let qualified = Name::from_string(&format!("{prefix}.{dotted}"));
                if self.is_known_accessible_global(&qualified) {
                    return Some(qualified);
                }
                match prefix.rsplit_once('.') {
                    Some((parent, _)) => prefix = parent,
                    None => break,
                }
            }
        }
        if let Some(qualified) = self.namespace_state.resolve(dotted) {
            if self.is_known_accessible_global(qualified) {
                return Some(qualified.clone());
            }
        }
        let root = Name::from_string(dotted);
        if self.is_known_accessible_global(&root) {
            return Some(root);
        }
        None
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
    fn ident_resolves_to_value(&self, name: &str) -> bool {
        if self.lookup_local(name).is_some() {
            return true;
        }
        let direct = Name::from_string(name);
        let is_known = |n: &Name| {
            (self.env.get_const(n).is_some() && self.is_const_accessible(n))
                || self.env.get_inductive(n).is_some()
                || self.env.get_constructor(n).is_some()
                || self.env.get_recursor(n).is_some()
        };
        if is_known(&direct) {
            return true;
        }
        if let Some(qualified) = self.namespace_state.resolve(name) {
            if is_known(qualified) {
                return true;
            }
        }
        if !self.namespace_prefix.is_empty() {
            let mut prefix = self.namespace_prefix.as_str();
            loop {
                let qualified = Name::from_string(&format!("{prefix}.{name}"));
                if is_known(&qualified) {
                    return true;
                }
                match prefix.rsplit_once('.') {
                    Some((parent, _)) => prefix = parent,
                    None => break,
                }
            }
        }
        false
    }

    /// Dot notation fallback for non-structure types.
    ///
    /// For `expr.field` where `expr : T` and `T` is not a structure,
    /// looks up `T.field` as a constant and applies it: `T.field expr`.
    fn elab_dot_notation(
        &mut self,
        expr_val: &Expr,
        proj: &clean_parser::Projection,
    ) -> Result<Expr, ElabError> {
        let field_name = match proj {
            clean_parser::Projection::Named(n) => n.clone(),
            clean_parser::Projection::Index(_) => {
                // Index projection doesn't make sense for non-structures
                return Err(ElabError::InvalidProjectionTarget(
                    "index projection on non-structure type".to_string(),
                ));
            }
        };

        // Namespace lookup: resolve dotted constants like `Id.mk` or `whnf_to.refl`
        if let ExprKind::Const(const_name, _) = expr_val.kind() {
            let namespaced = Name::append(const_name, &field_name);
            // Check if this matches a recursive function being defined (#522)
            // During recursive definition elaboration, the function isn't in env yet
            // but should be recognized as a valid recursive call target.
            if let Some(ref ctx) = self.recursive_def_ctx {
                let namespaced_str = namespaced.to_string();
                if ctx.matches_call_name(&namespaced_str) {
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
            let dotted = namespaced.to_string();
            if let Some(q) = self.namespace_state.resolve(&dotted) {
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
            if !self.namespace_prefix.is_empty() {
                let mut prefix = self.namespace_prefix.as_str();
                loop {
                    let qualified = Name::from_string(&format!("{prefix}.{dotted}"));
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
                    match prefix.rsplit_once('.') {
                        Some((parent, _)) => prefix = parent,
                        None => break,
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
        if matches!(self.whnf(&expr_ty).kind(), ExprKind::FVar(_)) {
            if let ExprKind::FVar(id) = expr_val.kind() {
                let recv_name = self
                    .locals
                    .iter()
                    .rev()
                    .find(|(_, fv, _)| fv == id)
                    .map(|(n, _, _)| n.clone());
                if let Some(recv_name) = recv_name {
                    let dotted = format!("{recv_name}.{field_name}");
                    // Resolve `recv_name.field` through the same namespace chain
                    // `ident_resolves_to_value` consults: the bare name, the active
                    // `open`/`namespace` resolution, then each enclosing namespace
                    // prefix (so `Sequence.denote` finds `TrustIr.Sequence.denote`).
                    let mut candidates: Vec<Name> = vec![Name::from_string(&dotted)];
                    if let Some(q) = self.namespace_state.resolve(&dotted) {
                        candidates.push(q.clone());
                    }
                    if !self.namespace_prefix.is_empty() {
                        let mut prefix = self.namespace_prefix.as_str();
                        loop {
                            candidates.push(Name::from_string(&format!("{prefix}.{dotted}")));
                            match prefix.rsplit_once('.') {
                                Some((parent, _)) => prefix = parent,
                                None => break,
                            }
                        }
                    }
                    for name in candidates {
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
            let const_name = format!("{head_name}.{field_name}");
            let name = Name::from_string(&const_name);
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
                    let type_name = head_name.to_string();
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
                let namespaced = Name::append(const_name, &field_name);
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
                if let Some((fvar, _)) = self.lookup_local(&namespaced.to_string()) {
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
                    let head_str = const_name.to_string();
                    let mut suffix = head_str.as_str();
                    loop {
                        let key = format!("{suffix}.{field_name}");
                        if let Some((fvar, _)) = self.lookup_local(&key) {
                            return Ok(Expr::fvar(fvar));
                        }
                        match suffix.split_once('.') {
                            Some((_, rest)) => suffix = rest,
                            None => break,
                        }
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
                if field_name == "decEq" {
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
            let (applied_expr, resolved_ty) =
                self.insert_implicit_args(expr_val.clone(), &expr_ty_whnf);
            let resolved_ty_whnf = self.whnf(&resolved_ty);

            // `.field` as a leading-dot constructor applied to the receiver.
            if let ExprKind::Pi(_, domain, _) = resolved_ty_whnf.kind() {
                let ctor_expr = self.elab_leading_dot_ctor_with_expected_type(
                    &format!(".{field_name}"),
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
                if let Ok(type_name) = self.get_type_name(&resolved_ty) {
                    let name = Name::from_string(&format!("{type_name}.{field_name}"));
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
                let fn_ns_name = Name::from_string(&format!("Function.{field_name}"));
                if let Some(info) = self.env.get_const(&fn_ns_name) {
                    if self.is_const_accessible(&fn_ns_name) {
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
                        let fn_expr = Expr::const_(fn_ns_name, levels);
                        let (fn_with_implicits, fn_rest_ty) =
                            self.insert_implicit_args(fn_expr, &fn_type);
                        // Pin `Function.<field>`'s domain metavars (the function's
                        // source/target types) from the receiver's actual type
                        // before applying it, so no metavariable is left unsolved.
                        let fn_rest_ty = self.whnf(&fn_rest_ty);
                        if let ExprKind::Pi(_, arg_ty, _) = fn_rest_ty.kind() {
                            let arg_ty = self.metas.instantiate(arg_ty);
                            self.try_unify(&arg_ty, &expr_ty);
                        }
                        let applied = Expr::app(fn_with_implicits, expr_val.clone());
                        let applied = self.metas.instantiate(&applied);
                        let applied = self.metas.instantiate_levels(&applied);
                        return Ok(applied);
                    }
                }
            }
        }

        let type_name = self.get_type_name(&expr_ty)?;
        let const_name = format!("{type_name}.{field_name}");
        let name = Name::from_string(&const_name);

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
                    if let Some(ih_fvar) = ctx
                        .ih_map
                        .iter()
                        .find(|(var_name, _)| {
                            self.lookup_local(var_name)
                                .is_some_and(|(fv, _)| fv == *recv_fvar)
                        })
                        .map(|(_, ih)| *ih)
                    {
                        return Ok(Expr::fvar(ih_fvar));
                    }
                }
            }
        }

        // Check if the constant exists and get its type
        let const_info = match self.env.get_const(&name) {
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
        type_name: &str,
        field_name: &str,
        receiver: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        let to_container_name = Name::from_string(&format!("{type_name}.toContainer"));
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
        let method_name = Name::append(&container_name, field_name);
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
            &container_name.to_string(),
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
    fn apply_dot_receiver(
        &mut self,
        fn_expr: Expr,
        fn_type: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
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
                ExprKind::Const(n, _) if n.to_string() == type_name
            );
            let arg_head = self.whnf(&arg_ty_inst);
            let head_matches = syntactic_head_matches
                || matches!(
                    arg_head.get_app_fn().kind(),
                    ExprKind::Const(n, _) if n.to_string() == type_name
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
                // against the pinned carrier (`BEq Int -> instBEqInt`).
                self.resolve_deferred_instances(&pending_insts);
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
        let (fn_with_implicits, _) = self.insert_implicit_args(result, &ty);
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
        proj: &clean_parser::Projection,
    ) -> Option<String> {
        stack_safe(|| {
            let field = match proj {
                clean_parser::Projection::Named(n) => n,
                clean_parser::Projection::Index(_) => return None,
            };

            match base {
                SurfaceExpr::Ident(_, name) => Some(format!("{name}.{field}")),
                SurfaceExpr::Proj(_, inner_base, inner_proj) => {
                    let base_qualified = Self::try_collect_qualified_name(inner_base, inner_proj)?;
                    Some(format!("{base_qualified}.{field}"))
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
            other => return Err(ElabError::InvalidProjectionTarget(format!("{other:?}"))),
        };

        let ind = self
            .env
            .get_inductive(&struct_name)
            .ok_or_else(|| ElabError::InvalidProjectionTarget(format!("{expr_ty_whnf:?}")))?;

        if ind.constructor_names.len() != 1 {
            return Err(ElabError::InvalidProjectionTarget(format!(
                "{expr_ty_whnf:?}"
            )));
        }

        // A single-constructor inductive is projectable. Whether it carries
        // structure field-name metadata distinguishes the *named* accessor path
        // (`structure`s) from the raw `Expr.proj` index path (plain
        // `inductive`s like `And`/`Iff`). See the per-kind branch in
        // `elab_proj`.
        let is_registered_structure = self.env.get_structure_field_names(&struct_name).is_some();

        let ctor_name = &ind.constructor_names[0];
        let ctor = self.env.get_constructor(ctor_name).ok_or_else(|| {
            ElabError::InvalidProjectionTarget(format!("missing constructor {ctor_name:?}"))
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
        let (applied_expr, _) = self.insert_implicit_args(expr_val.clone(), &expr_ty_whnf);
        match self.resolve_projection_target(&applied_expr) {
            Ok((struct_name, num_fields, _is_structure)) => {
                if idx == 0 || idx > num_fields {
                    return Err(ElabError::ProjectionIndexOutOfBounds {
                        struct_name,
                        idx,
                        field_count: num_fields,
                    });
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
