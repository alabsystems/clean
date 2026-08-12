// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested constructor sub-pattern support (#796).
//!
//! When a match arm has a sub-pattern like `Nat.succ Nat.zero` or
//! `Option.some (Option.some x)`, the outer casesOn binds the field variable
//! and this module recursively wraps the arm body in nested `T.casesOn`
//! applications for the inner constructor structure.

use super::super::*;
use super::{
    desugar_nonzero_nat_lit, ensure_supported_literal_pattern, numeral_add_pattern_binder_name,
    NestedPatternFieldPlan, NestedPatternPlan,
};

impl<'a> ElabCtx<'a> {
    fn inaccessible_expr_ctor_name(&self, expr: &SurfaceExpr) -> Option<String> {
        match expr {
            SurfaceExpr::Ident(_, name) => Some(name.clone()),
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                if let SurfaceExpr::Ident(_, namespace) = base.as_ref() {
                    Some(format!("{namespace}.{field}"))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn inaccessible_expr_to_nested_pattern(
        &self,
        field_ty: &Expr,
        expr: &SurfaceExpr,
    ) -> Result<Option<SurfacePattern>, ElabError> {
        let pattern = match expr {
            SurfaceExpr::Lit(_, SurfaceLit::Nat(k)) => Some(desugar_nonzero_nat_lit(*k)),
            SurfaceExpr::Ident(_, name) => Some(SurfacePattern::Var(name.clone())),
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                if let SurfaceExpr::Ident(_, namespace) = base.as_ref() {
                    Some(SurfacePattern::Var(format!("{namespace}.{field}")))
                } else {
                    None
                }
            }
            SurfaceExpr::Paren(_, inner) => {
                return self.inaccessible_expr_to_nested_pattern(field_ty, inner);
            }
            SurfaceExpr::App(_, func, args) => {
                if args.iter().any(|arg| arg.name.is_some()) {
                    return Ok(None);
                }
                let Some(ctor_name) = self.inaccessible_expr_ctor_name(func) else {
                    return Ok(None);
                };
                let Ok(type_name) = self.get_type_name(field_ty) else {
                    return Ok(None);
                };
                let full_ctor = self.ctor_pattern_full_name(&ctor_name, &type_name);
                let expected_inductive = Name::from_string(&type_name);
                let Some(ctor_info) = self.env.get_constructor(&Name::from_string(&full_ctor))
                else {
                    return Ok(None);
                };
                if ctor_info.inductive_name != expected_inductive {
                    return Ok(None);
                }
                let ctor_field_types =
                    self.compute_ctor_field_types(&Name::from_string(&full_ctor), field_ty)?;
                if args.len() != ctor_field_types.len() {
                    return Ok(None);
                }
                let mut sub_pats = Vec::with_capacity(args.len());
                for (arg, arg_ty) in args.iter().zip(&ctor_field_types) {
                    let Some(sub_pat) =
                        self.inaccessible_expr_to_nested_pattern(arg_ty, &arg.expr)?
                    else {
                        return Ok(None);
                    };
                    sub_pats.push(sub_pat);
                }
                Some(SurfacePattern::Ctor(ctor_name, sub_pats))
            }
            _ => None,
        };
        Ok(pattern)
    }

    fn resolve_nested_ctor_pattern(
        &self,
        context: &str,
        field_ty: &Expr,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
    ) -> Result<(String, Vec<Expr>, Vec<SurfacePattern>), ElabError> {
        let type_name = self.get_type_name(field_ty)?;
        let expected_inductive = Name::from_string(&type_name);
        // Resolve through opened namespaces too, falling back to the literal
        // qualification so the UnknownIdent diagnostic names what the user wrote.
        let mut full_ctor = self.ctor_pattern_full_name(ctor_name, &type_name);
        let mut ctor_name = Name::from_string(&full_ctor);
        let ctor_info = self
            .env
            .get_constructor(&ctor_name)
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        if ctor_info.inductive_name != expected_inductive {
            // Nested-aux mirror (#3396 FIX-FV Part 2): the field has the
            // synthesised aux type (`Value._List`) but the user wrote a
            // container constructor (`List.nil`/`List.cons`). Remap onto the
            // mirrored aux constructor when it genuinely exists; this is the
            // pattern-direction counterpart of `toContainer` and keeps the
            // kernel-checked `casesOn` sound. When no mirror exists, report the
            // original "does not belong" diagnostic unchanged.
            match self
                .remap_container_ctor_to_field_aux(&type_name, &full_ctor)
                .or_else(|| {
                    // Anonymous-tuple placeholder (`⟨…⟩` → `Prod.mk`) destructuring
                    // a single-constructor inductive that is not `Prod` (`And`,
                    // `Exists`, `Sigma`, …): remap to that type's sole constructor
                    // so the nested `casesOn` names a real constructor.
                    self.remap_anonymous_tuple_ctor(&type_name, &full_ctor, sub_pats.len())
                }) {
                Some(remapped) => {
                    full_ctor = remapped;
                    ctor_name = Name::from_string(&full_ctor);
                }
                None => {
                    return Err(ElabError::NotImplemented(format!(
                        "{context}: nested constructor {full_ctor} does not belong to field type {type_name}"
                    )));
                }
            }
        }
        // Expand explicit-only field patterns to full field length (wildcard at
        // each implicit field position). This narrows the arity check to the
        // explicit-field count and yields a `num_fields`-length list so the
        // caller's per-field loop lines up against `compute_ctor_field_types`.
        let expanded_sub_pats =
            self.expand_implicit_ctor_field_patterns(context, &full_ctor, sub_pats)?;
        Ok((
            full_ctor,
            self.compute_ctor_field_types(&ctor_name, field_ty)?,
            expanded_sub_pats,
        ))
    }

    pub(in crate::infer) fn bind_nested_pattern_plan(
        &mut self,
        context: &str,
        pat: &SurfacePattern,
        field_expr: Expr,
        field_ty: &Expr,
    ) -> Result<NestedPatternPlan, ElabError> {
        self.with_local_scope_rollback(|this| {
            this.bind_nested_pattern_plan_inner(context, pat, field_expr, field_ty)
        })
    }

    fn bind_nested_pattern_plan_inner(
        &mut self,
        context: &str,
        pat: &SurfacePattern,
        field_expr: Expr,
        field_ty: &Expr,
    ) -> Result<NestedPatternPlan, ElabError> {
        match pat {
            SurfacePattern::Wildcard => Ok(NestedPatternPlan::None),
            SurfacePattern::Inaccessible(inaccessible_expr) => {
                if let Some(pat) =
                    self.inaccessible_expr_to_nested_pattern(field_ty, inaccessible_expr)?
                {
                    let plan =
                        self.bind_nested_pattern_plan_inner(context, &pat, field_expr, field_ty)?;
                    if matches!(plan, NestedPatternPlan::None)
                        && self.get_type_name(field_ty).is_ok()
                    {
                        Err(ElabError::NotImplemented(format!(
                            "{context}: nested inaccessible pattern requires field-level definitional equality checking: {inaccessible_expr:?}"
                        )))
                    } else {
                        Ok(plan)
                    }
                } else if self.get_type_name(field_ty).is_ok() {
                    Err(ElabError::NotImplemented(format!(
                        "{context}: nested inaccessible pattern requires field-level definitional equality checking: {inaccessible_expr:?}"
                    )))
                } else {
                    Ok(NestedPatternPlan::None)
                }
            }
            SurfacePattern::Var(name) => {
                // Check if this variable name is a nullary constructor of the field type.
                // E.g., `Var("Nat.zero")` in a Prod sub-pattern should trigger a nested
                // casesOn for correct dispatch, not just a variable binding (#1848).
                // Resolution also consults opened namespaces, so an opened ctor
                // alias in a nested position dispatches as a constructor too.
                let type_name = match self.get_type_name(field_ty) {
                    Ok(type_name) => type_name,
                    Err(_) => return Ok(NestedPatternPlan::None),
                };
                let nullary_ctor = self
                    .resolve_ctor_name(name, &type_name)
                    .filter(|full_ctor| {
                        self.env
                            .get_constructor(&Name::from_string(full_ctor))
                            .is_some_and(|info| info.num_fields == 0)
                    });
                if let Some(full_ctor) = nullary_ctor {
                    Ok(NestedPatternPlan::CasesOn {
                        field_expr,
                        field_ty: field_ty.clone(),
                        target_ctor_name: full_ctor,
                        target_fields: vec![],
                    })
                } else {
                    Ok(NestedPatternPlan::None)
                }
            }
            SurfacePattern::As(name, inner_pat) => {
                let alias_fvar = self.push_local(name.clone(), field_ty.clone());
                let inner = self.bind_nested_pattern_plan_inner(
                    context,
                    inner_pat,
                    field_expr.clone(),
                    field_ty,
                )?;
                Ok(NestedPatternPlan::Alias {
                    alias_fvar,
                    alias_ty: field_ty.clone(),
                    alias_expr: field_expr,
                    inner: Box::new(inner),
                })
            }
            SurfacePattern::Lit(lit) => {
                let type_name = self.get_type_name(field_ty)?;
                ensure_supported_literal_pattern(context, &type_name, lit)?;
                Ok(NestedPatternPlan::CasesOn {
                    field_expr,
                    field_ty: field_ty.clone(),
                    target_ctor_name: "Nat.zero".to_string(),
                    target_fields: vec![],
                })
            }
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                let type_name = self.get_type_name(field_ty)?;
                let var_name =
                    numeral_add_pattern_binder_name(context, &type_name, inner_pat.as_ref(), *k)?;
                let inner_fvar = self.push_local(var_name, field_ty.clone());
                Ok(NestedPatternPlan::CasesOn {
                    field_expr,
                    field_ty: field_ty.clone(),
                    target_ctor_name: "Nat.succ".to_string(),
                    target_fields: vec![NestedPatternFieldPlan {
                        fvar: inner_fvar,
                        ty: field_ty.clone(),
                        plan: NestedPatternPlan::None,
                    }],
                })
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => {
                let (full_ctor, field_tys, sub_pats) =
                    self.resolve_nested_ctor_pattern(context, field_ty, ctor_name, sub_pats)?;
                if field_tys.len() != sub_pats.len() {
                    return Err(ElabError::InternalInvariant(format!(
                        "constructor metadata `{full_ctor}` exposes {} fields but the normalized pattern has {} slots",
                        field_tys.len(),
                        sub_pats.len()
                    )));
                }
                let mut target_fields = Vec::with_capacity(sub_pats.len());
                let mut prior_field_fvars: Vec<FVarId> = Vec::new();
                for (sub_pat, raw_field_ty) in sub_pats.iter().zip(field_tys) {
                    // Beta-reduce a bare-predicate sub-field type against the
                    // preceding witness sub-field, so a *deeper* anonymous-tuple
                    // destructure of a nested `Exists`/`Sigma` (e.g. `⟨a, b, c⟩`
                    // on `∃ x, ∃ y, R x y`) exposes a `Const`-headed field type at
                    // every level (see `beta_reduce_predicate_field_ty`).
                    let target_field_ty =
                        self.beta_reduce_predicate_field_ty(&raw_field_ty, &prior_field_fvars);
                    let var_name = match sub_pat {
                        SurfacePattern::Var(name) => name.clone(),
                        _ => "_".to_string(),
                    };
                    let field_fvar = self.push_local(var_name, target_field_ty.clone());
                    prior_field_fvars.push(field_fvar);
                    let plan = self.bind_nested_pattern_plan_inner(
                        context,
                        sub_pat,
                        Expr::fvar(field_fvar),
                        &target_field_ty,
                    )?;
                    target_fields.push(NestedPatternFieldPlan {
                        fvar: field_fvar,
                        ty: target_field_ty,
                        plan,
                    });
                }
                Ok(NestedPatternPlan::CasesOn {
                    field_expr,
                    field_ty: field_ty.clone(),
                    target_ctor_name: full_ctor,
                    target_fields,
                })
            }
            _ => Err(ElabError::NotImplemented(format!(
                "{context}: nested constructor field pattern is not currently supported: {pat:?}"
            ))),
        }
    }

    pub(in crate::infer) fn collect_nested_field_plans(
        &mut self,
        context: &str,
        sub_pats: &[SurfacePattern],
        fvar_tys: &[(FVarId, Expr)],
    ) -> Result<Vec<NestedPatternPlan>, ElabError> {
        self.with_local_scope_rollback(|this| {
            sub_pats
                .iter()
                .enumerate()
                .map(|(index, pat)| {
                    let (fvar, field_ty) = &fvar_tys[index];
                    this.bind_nested_pattern_plan_inner(context, pat, Expr::fvar(*fvar), field_ty)
                })
                .collect()
        })
    }

    fn cleanup_nested_pattern_plan(&mut self, plan: &NestedPatternPlan) {
        match plan {
            NestedPatternPlan::None => {}
            NestedPatternPlan::Alias { inner, .. } => {
                self.cleanup_nested_pattern_plan(inner);
                self.pop_local();
            }
            NestedPatternPlan::CasesOn { target_fields, .. } => {
                for target_field in target_fields.iter().rev() {
                    self.cleanup_nested_pattern_plan(&target_field.plan);
                    self.pop_local();
                }
            }
        }
    }

    pub(in crate::infer) fn cleanup_nested_field_plans(&mut self, plans: &[NestedPatternPlan]) {
        for plan in plans.iter().rev() {
            self.cleanup_nested_pattern_plan(plan);
        }
    }

    pub(in crate::infer) fn apply_nested_pattern_plan(
        &mut self,
        body: Expr,
        plan: &NestedPatternPlan,
        branch_ty: &Expr,
        fallback_body: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        self.with_local_scope_rollback(|this| {
            this.apply_nested_pattern_plan_inner(body, plan, branch_ty, fallback_body)
        })
    }

    fn apply_nested_pattern_plan_inner(
        &mut self,
        mut body: Expr,
        plan: &NestedPatternPlan,
        branch_ty: &Expr,
        fallback_body: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        match plan {
            NestedPatternPlan::None => Ok(body),
            NestedPatternPlan::Alias {
                alias_fvar,
                alias_ty,
                alias_expr,
                inner,
            } => {
                let body =
                    self.apply_nested_pattern_plan_inner(body, inner, branch_ty, fallback_body)?;
                self.pop_local();
                let body = body.abstract_fvar(*alias_fvar);
                Ok(Expr::let_named(
                    Name::anon(),
                    alias_ty.clone(),
                    alias_expr.clone(),
                    body,
                    false,
                ))
            }
            NestedPatternPlan::CasesOn {
                field_expr,
                field_ty,
                target_ctor_name,
                target_fields,
            } => {
                // Curried-nesting fix (nested ctor at 2nd+ field position).
                //
                // We destructure the matched constructor's `target_fields` in
                // reverse: each later field is `abstract`-ed into a `fun`, so the
                // running `body` accumulates a Pi over that field. When an EARLIER
                // field itself needs a nested `casesOn` (its sub-pattern is a
                // constructor, not a plain binder), that inner `casesOn` sits
                // OUTSIDE the already-abstracted later fields — so its result type
                // is no longer the bare `branch_ty` but `branch_ty` prefixed by one
                // Pi per later field already folded in. Both the inner `casesOn`'s
                // MOTIVE and its caller-supplied fallback minor must be built at
                // that grown type, or the kernel sees a minor of type `Nat → Nat` where it
                // expects `(x : Nat) → (fun _ => List → Nat) (some x)` and rejects
                // the whole match. Grow `cur_branch_ty` by each abstracted field's
                // Pi and thread it into the next inner recursion so motive and minor
                // grow in lockstep. For a plain (non-ctor) later field the inner
                // recursion is a no-op, so `cur_branch_ty` is only ever consumed by a
                // genuine nested `casesOn`, keeping every previously-working shape
                // (single field, var-tail, nested-at-position-0) byte-identical.
                let mut cur_branch_ty = branch_ty.clone();
                let mut cur_fallback = fallback_body.cloned();
                for target_field in target_fields.iter().rev() {
                    body = self.apply_nested_pattern_plan_inner(
                        body,
                        &target_field.plan,
                        &cur_branch_ty,
                        cur_fallback.as_ref(),
                    )?;
                    self.pop_local();
                    body = body.abstract_fvar(target_field.fvar);
                    body = Expr::lam(BinderInfo::Default, target_field.ty.clone(), body);
                    // Grow branch_ty AND the threaded fallback by this field's Pi in
                    // lockstep. The fallback (the enclosing match's covering arm value)
                    // is threaded down from the top typed at the un-grown
                    // `branch_ty`; an inner nested `casesOn` on an EARLIER field expects
                    // its non-matching minors — which reference this same fallback — to
                    // have the GROWN type. Wrap the fallback in a constant lambda over
                    // the just-abstracted field so `fun x => fallback` has type
                    // `(field) → cur_branch_ty`, matching what the inner casesOn's
                    // motive `fun _ => cur_branch_ty` demands. Without this the motive
                    // grows but the minor body stays `Nat`, and the kernel rejects the
                    // match ("(x:Nat)→(fun _=>List→Nat)(some x)" vs "Nat→Nat"). The
                    // extra binder is dead (the fallback ignores the field), so the
                    // reduced value is unchanged.
                    cur_branch_ty =
                        Expr::pi(BinderInfo::Default, target_field.ty.clone(), cur_branch_ty);
                    cur_fallback = cur_fallback
                        .map(|fb| Expr::lam(BinderInfo::Default, target_field.ty.clone(), fb));
                }
                match fallback_body {
                    Some(fallback) => self.wrap_with_nested_ctor_caseson_with_fallback(
                        body,
                        field_expr.clone(),
                        field_ty,
                        target_ctor_name,
                        branch_ty,
                        fallback.clone(),
                    ),
                    None => self.wrap_with_nested_ctor_caseson(
                        body,
                        field_expr.clone(),
                        field_ty,
                        target_ctor_name,
                        branch_ty,
                    ),
                }
            }
        }
    }

    pub(in crate::infer) fn apply_nested_field_plans(
        &mut self,
        plans: &[NestedPatternPlan],
        body: Expr,
        branch_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        self.with_local_scope_rollback(|this| {
            let mut body = body;
            for plan in plans.iter().rev() {
                body = this.apply_nested_pattern_plan_inner(body, plan, branch_ty, None)?;
            }
            Ok(body)
        })
    }

    /// Wrap an expression in a nested `casesOn` that selects one constructor.
    ///
    /// For pattern `Nat.succ Nat.zero => body`, the `Nat.zero` sub-pattern needs
    /// a nested casesOn on the field variable (Lean-faithful casesOn order:
    /// motive, (indices,) major, then minors):
    ///   `Nat.casesOn motive field_var body ...`
    ///
    /// This no-fallback entry point succeeds only when the target constructor is
    /// the sole required minor. A partial nested pattern is non-exhaustive and
    /// must be combined with a real later arm by the caller; it is never filled
    /// with a synthetic proof/value.
    pub(in crate::infer) fn wrap_with_nested_ctor_caseson(
        &mut self,
        body: Expr,
        field_expr: Expr,
        field_ty: &Expr,
        target_ctor_name: &str,
        branch_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        // This builder has no intentional local-state output. Keep its internal
        // motive/minor probes and fallback placeholder fully temporary so an
        // identity-check failure restores the exact caller context.
        self.with_temporary_local_scope(|this| {
            this.wrap_with_nested_ctor_caseson_impl(
                body,
                field_expr,
                field_ty,
                target_ctor_name,
                branch_ty,
                None,
            )
        })
    }

    /// Wrap an expression in a nested casesOn, using a caller-supplied fallback
    /// for non-matching constructors.
    pub(in crate::infer) fn wrap_with_nested_ctor_caseson_with_fallback(
        &mut self,
        body: Expr,
        field_expr: Expr,
        field_ty: &Expr,
        target_ctor_name: &str,
        branch_ty: &Expr,
        fallback_body: Expr,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.wrap_with_nested_ctor_caseson_impl(
                body,
                field_expr,
                field_ty,
                target_ctor_name,
                branch_ty,
                Some(fallback_body),
            )
        })
    }

    fn wrap_with_nested_ctor_caseson_impl(
        &mut self,
        body: Expr,
        field_expr: Expr,
        field_ty: &Expr,
        target_ctor_name: &str,
        branch_ty: &Expr,
        fallback_body: Option<Expr>,
    ) -> Result<Expr, ElabError> {
        let type_name = self.get_type_name(field_ty)?;

        let ind_name = Name::from_string(&type_name);
        let ind_info =
            self.env
                .get_inductive(&ind_name)
                .cloned()
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: format!("inductive type for nested pattern on {type_name}"),
                    actual: format!("{field_ty:?}"),
                })?;

        let cases_on_name = Name::from_string(&format!("{type_name}.casesOn"));

        let elim_levels = self.eliminator_levels(&cases_on_name, field_ty, branch_ty)?;
        let eliminator = self.apply_eliminator_params(
            Expr::const_(cases_on_name.clone(), elim_levels),
            field_ty,
            &type_name,
        )?;
        let mut cases_result = eliminator;

        // Nested-aux mutual block (#3239 / #3396): when `field_ty` belongs to a
        // nested-inductive mutual block (e.g. `Value` with `aggregate : List
        // Value`, or the synthesised aux mirror `Value._List` itself),
        // elimination created auxiliary types and `<T>.casesOn` carries ONE
        // motive per type in the block (in declaration order) and a minor
        // premise for EVERY constructor across the block (also in declaration
        // order), regardless of which member's `casesOn` is invoked. We
        // therefore emit motives and minors **positionally** over `all_names`,
        // never assuming `field_ty` is the primary (first) member. This is what
        // lets a nested sub-pattern whose field type is the AUX type (e.g.
        // `| .aggregate (x :: xs) =>`, where the `aggregate` field is bound at
        // `Value._List`) lower against `Value._List.casesOn` with the motive for
        // `Value` in slot 0 and the motive for `Value._List` in slot 1 — the
        // #3396 FIX-FV Part 2 pattern direction.
        let eliminator_metadata =
            self.match_eliminator_metadata(&type_name, &cases_on_name, true)?;
        let num_motives = eliminator_metadata.recursor.num_motives as usize;
        if num_motives == 0 {
            return Err(ElabError::InternalInvariant(format!(
                "nested-pattern eliminator `{cases_on_name}` declares no motives"
            )));
        }
        // Emit each motive from the eliminator telescope. Nested restore removes
        // auxiliary names from `all_names` and rewrites their motive domains to
        // real container applications, so positional name reconstruction is no
        // longer sound. The signature remains complete and authoritative.
        for _ in 0..num_motives {
            let cases_ty = self.infer_type(&cases_result)?;
            let cases_ty = self.whnf(&cases_ty);
            let ExprKind::Pi(_, expected_motive, _) = cases_ty.kind() else {
                return Err(ElabError::TypeMismatch {
                    expected: "nested-pattern motive premise".to_string(),
                    actual: format!("{cases_ty:?}"),
                });
            };
            let motive = self.constant_over_telescope(expected_motive, branch_ty.clone());
            cases_result = Expr::app(cases_result, motive);
        }

        // Eliminator-layout discriminator, mirroring the top-level match lowering
        // in `mod.rs`. Lean-faithful casesOn order: motive, (indices,) major, then
        // minors. A *native* `T.casesOn` is now generated as a recursor with the
        // `MajorAfterMotive` layout, and an *imported* `T.casesOn` from a real Lean
        // `.olean` (only a definitional constant — `get_recursor` returns `None`)
        // follows the same convention: the major premise (the bound field) comes
        // immediately after the motive(s), BEFORE the minors.
        //
        // Placing the major in the wrong slot puts the field in a minor-premise
        // slot: the inner casesOn no longer iota-reduces (and could bind the inner
        // field to the wrong slot). Consulting the recursor's declared `arg_order`
        // — exactly as the top-level lowering does — also keeps any recursor still
        // declaring `MajorAfterMinors` on the major-last path.
        let major_after_motive = eliminator_metadata.major_after_motive;
        if major_after_motive {
            cases_result = Expr::app(cases_result, field_expr.clone());
        }

        // Resolve target constructor name (already qualified when produced by
        // pattern resolution; re-resolve defensively for any bare/aliased name).
        let full_target = self.ctor_pattern_full_name(target_ctor_name, &type_name);

        // PERF ROOT FIX (trk-yy): let-share the duplicated fallback branch.
        //
        // The accumulated `fallback_body` is replicated into EVERY non-matching
        // minor premise (and every aux-constructor minor). Because `Expr` children
        // are `Arc`, the lowered term is a *linear* memory DAG, but it is
        // *exponential* when walked as a tree: whnf / def-eq / infer_type /
        // abstract / instantiate and the debug ProofCert tree all traverse it as a
        // tree and blow up (heartbeat / OOM) on `Ty.Vector` literal+ctor matches
        // such as `Ty.executableIntVectorWidth?` / `Ty.executableBoolVectorLanes?`.
        //
        // Fix: bind the fallback to ONE shared `let` binder lifted out of the whole
        // `casesOn`, and reference it from each minor via a single placeholder
        // free variable. `let fb := <fallback> in <casesOn … fb …>` is definitionally
        // equal to the inlined form (zeta-reduces / `abstract_fvar`∘`instantiate`
        // round-trips), so the kernel re-checks an identical term — accept/reject is
        // unchanged — while every consumer now traverses the fallback ONCE.
        //
        // We only introduce the binder when the fallback would actually be
        // duplicated (>= 2 occurrences). For 0/1 occurrences the inlined form is
        // emitted byte-for-byte unchanged, keeping native / already-passing shapes
        // identical.
        // The full minor telescope, in block declaration order. For a
        // single-type inductive this is just the type's own constructors; for a
        // nested-aux mutual block `<T>.casesOn` carries a minor for EVERY
        // constructor across ALL members (in `all_names` order), regardless of
        // which member owns the major. We materialise that exact order here,
        // pairing each constructor with the member it belongs to (so its field
        // types are computed against the right member-applied type).
        let minor_plan: Vec<clean_kernel::RecursorRule> =
            self.recursor_minor_rules(&ind_info, &eliminator_metadata.recursor)?;

        let fallback_uses = minor_plan
            .iter()
            .filter(|rule| rule.constructor_name.to_string() != full_target)
            .count();
        let matching_uses = minor_plan.len().saturating_sub(fallback_uses);
        if matching_uses != 1 {
            return Err(ElabError::TypeMismatch {
                expected: format!("exactly one nested-pattern minor for {full_target}"),
                actual: format!("{matching_uses} matching minors"),
            });
        }
        if fallback_uses > 0 && fallback_body.is_none() {
            return Err(ElabError::NotImplemented(format!(
                "non-exhaustive nested constructor pattern `{full_target}` on `{type_name}`; \
                 add a covering constructor or wildcard arm"
            )));
        }

        let share_fallback = fallback_body.is_some() && fallback_uses >= 2;
        // Placeholder for the shared fallback. When sharing, every minor references
        // `FVar(fb_fvar)`; we abstract it into the lifted `let` binder afterwards.
        // `abstract_fvar` rewrites each occurrence to the correct `BVar(depth)` for
        // the lambdas it sits under and shifts the casesOn's own loose bvars up by 1
        // to account for the new binder, so de Bruijn indices stay correct.
        let fb_fvar = if share_fallback {
            // Keep the placeholder in the local context while telescope-driven
            // construction infers the type of partially-applied eliminators.
            Some(self.push_local("_nested_fallback".to_string(), branch_ty.clone()))
        } else {
            None
        };
        let fallback_ref = match (fb_fvar, fallback_body.as_ref()) {
            (Some(id), _) => Some(Expr::fvar(id)),
            (None, fallback) => fallback.cloned(),
        };

        // Everything below may fail while inferring a partially-applied
        // eliminator or validating a restored minor telescope. Keep that work in
        // one result-producing scope, then unconditionally remove the optional
        // placeholder before propagating the result. In particular, a `?` must
        // never leak `_nested_fallback` into later error recovery.
        let result = (|mut cases_result: Expr| -> Result<Expr, ElabError> {
            // Add constructor alternatives (minor premises) in block order. The
            // matching constructor (`full_target`) uses the arm `body` (already a
            // field-abstracted lambda built by `apply_nested_pattern_plan`); every
            // other minor — including sibling-member minors that are dead code for a
            // major of `type_name` — uses the fallback, wrapped in one lambda per
            // field. Field types are computed against the OWNING member's applied
            // type, so a restored companion minor binds the declared field types.
            for rule in &minor_plan {
                if rule.constructor_name.to_string() == full_target {
                    // Matching constructor: use the arm body.
                    cases_result = Expr::app(cases_result, body.clone());
                } else {
                    // Non-matching constructor: consume exactly the field binders
                    // declared by the current minor premise. This retains dependent
                    // domains and works for restored real-container constructors.
                    let Some(fallback_ref) = fallback_ref.clone() else {
                        return Err(ElabError::NotImplemented(format!(
                            "non-exhaustive nested constructor pattern `{full_target}` on \
                             `{type_name}`; add a covering constructor or wildcard arm"
                        )));
                    };
                    let cases_ty = self.infer_type(&cases_result)?;
                    let cases_ty = self.whnf(&cases_ty);
                    let ExprKind::Pi(_, expected_minor, _) = cases_ty.kind() else {
                        return Err(ElabError::TypeMismatch {
                            expected: format!("minor premise for {}", rule.constructor_name),
                            actual: format!("{cases_ty:?}"),
                        });
                    };
                    let fallback = self
                        .constant_over_telescope_prefix(
                            expected_minor,
                            rule.num_fields as usize,
                            fallback_ref,
                        )
                        .ok_or_else(|| ElabError::TypeMismatch {
                            expected: format!(
                                "{} field binders for {}",
                                rule.num_fields, rule.constructor_name
                            ),
                            actual: format!("{expected_minor:?}"),
                        })?;
                    cases_result = Expr::app(cases_result, fallback);
                }
            }

            // For a recursor still declaring the `MajorAfterMinors` layout, the
            // major premise comes AFTER the minors. For `MajorAfterMotive` it was
            // already emitted before the minors above.
            if !major_after_motive {
                cases_result = Expr::app(cases_result, field_expr);
            }

            // Lift the shared fallback out into a single `let` binder while its
            // placeholder is still meaningful. The local-context entry itself is
            // removed unconditionally after this closure returns.
            if let Some(id) = fb_fvar {
                let Some(fallback_body) = fallback_body.clone() else {
                    return Err(ElabError::NotImplemented(format!(
                        "non-exhaustive nested constructor pattern `{full_target}` on \
                         `{type_name}`; add a covering constructor or wildcard arm"
                    )));
                };
                let body_abs = cases_result.abstract_fvar(id);
                cases_result = Expr::let_named(
                    Name::anon(),
                    branch_ty.clone(),
                    fallback_body,
                    body_abs,
                    false,
                );
            }

            Ok(cases_result)
        })(cases_result);

        if let Some(expected_fvar) = fb_fvar {
            let actual_fvar = self.locals.last().map(|(_, fvar, _)| *fvar);
            if actual_fvar != Some(expected_fvar) {
                return Err(ElabError::InternalInvariant(format!(
                    "nested fallback placeholder local-stack mismatch: expected top {expected_fvar:?}, got {actual_fvar:?}"
                )));
            }
            self.pop_local();
        }
        result
    }

    /// Compute field types for a constructor from authenticated registry data.
    ///
    /// Looks up the constructor by name and instantiates its type parameters
    /// from the scrutinee type to recover the field types.
    pub(in crate::infer) fn compute_ctor_field_types(
        &self,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
    ) -> Result<Vec<Expr>, ElabError> {
        let (info, ind_info) = self.authenticate_constructor_metadata(ctor_name)?;
        let scrutinee_ty = self.metas.instantiate(scrutinee_ty);
        let scrutinee_ty = self.metas.instantiate_levels(&scrutinee_ty);
        let scrutinee_ty = self.whnf(&scrutinee_ty);
        let (scrutinee_head, scrutinee_levels) = match scrutinee_ty.get_app_fn().kind() {
            ExprKind::Const(name, levels) => (name, levels),
            _ => {
                return Err(ElabError::TypeMismatch {
                    expected: format!("fully applied inductive `{}`", info.inductive_name),
                    actual: format!("{scrutinee_ty:?}"),
                });
            }
        };
        if scrutinee_head != &info.inductive_name {
            return Err(ElabError::TypeMismatch {
                expected: format!("constructor `{ctor_name}` of `{}`", info.inductive_name),
                actual: format!("scrutinee headed by `{scrutinee_head}`"),
            });
        }
        if scrutinee_levels.len() != info.level_params.len() {
            return Err(ElabError::InternalInvariant(format!(
                "scrutinee for constructor `{ctor_name}` supplies {} universe levels, metadata requires {}",
                scrutinee_levels.len(),
                info.level_params.len()
            )));
        }
        let scrutinee_args = scrutinee_ty.get_app_args();
        let expected_scrutinee_args = ind_info.num_params as usize + ind_info.num_indices as usize;
        if scrutinee_args.len() != expected_scrutinee_args {
            return Err(ElabError::InternalInvariant(format!(
                "scrutinee for constructor `{ctor_name}` supplies {} type arguments, inductive metadata requires {expected_scrutinee_args}",
                scrutinee_args.len()
            )));
        }
        let type_args = &scrutinee_args[..info.num_params as usize];
        let level_subst = info
            .level_params
            .iter()
            .cloned()
            .zip(scrutinee_levels.iter().cloned())
            .collect::<Vec<_>>();
        let mut ctor_ty = info.type_.instantiate_level_params(&level_subst);
        for (i, type_arg) in type_args[..info.num_params as usize].iter().enumerate() {
            if let ExprKind::Pi(_, _, codomain) = ctor_ty.kind() {
                ctor_ty = codomain.instantiate(type_arg);
            } else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` telescope ends before parameter {i}"
                )));
            }
        }
        let mut types = Vec::new();
        for field_index in 0..info.num_fields {
            if let ExprKind::Pi(_, domain, codomain) = ctor_ty.kind() {
                types.push((**domain).clone());
                ctor_ty = (**codomain).clone();
            } else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` telescope ends before field {field_index}"
                )));
            }
        }
        let (return_name, return_levels) = match ctor_ty.get_app_fn().kind() {
            ExprKind::Const(name, levels) => (name, levels),
            _ => {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` does not have a constant-headed return type after instantiation: {ctor_ty:?}"
                )));
            }
        };
        if return_name != &info.inductive_name || return_levels != scrutinee_levels {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` returns `{return_name}` at levels {return_levels:?}, expected `{}` at {scrutinee_levels:?}",
                info.inductive_name,
            )));
        }
        let return_args = ctor_ty.get_app_args();
        if return_args.len() != expected_scrutinee_args {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` instantiated return spine supplies {} arguments, inductive metadata requires {expected_scrutinee_args}",
                return_args.len()
            )));
        }
        for (param_index, (return_param, scrutinee_param)) in return_args
            .iter()
            .take(info.num_params as usize)
            .zip(type_args.iter())
            .enumerate()
        {
            if return_param != scrutinee_param {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` instantiated return parameter {param_index} disagrees with its scrutinee parameter"
                )));
            }
        }
        Ok(types)
    }

    /// Open a constructor field type against the free variables already bound
    /// for the *preceding* fields of the same constructor.
    ///
    /// `compute_ctor_field_types` returns each field's domain relative to the
    /// constructor's Pi telescope: field `i`'s type may contain loose de Bruijn
    /// variables referring to earlier fields (`BVar(0)` = field `i-1`,
    /// `BVar(1)` = field `i-2`, …). That telescope-relative encoding is only
    /// valid while the fields stay bound as a contiguous binder run. The match /
    /// do-match / if-let arm elaborators, however, bind each field as an
    /// independent `FVar` local and later re-abstract them one at a time. During
    /// that staged `abstract_fvar`, the loose sibling-`BVar`s in a *dependent*
    /// field type (e.g. `tl : IVec n` in `IVec.icons (n : Nat) (h : Nat)
    /// (tl : IVec n)`) get lifted away from the field they were meant to name,
    /// producing an out-of-scope `BVar` and a kernel `UnboundVariable` failure.
    ///
    /// Substituting the preceding fields' `FVar`s into the loose `BVar` slots
    /// *before* the type is bound makes the dependency explicit: the type then
    /// references the sibling fields by `FVar`, so the staged `abstract_fvar`
    /// rewrites each reference to the correct `BVar` exactly as it does for the
    /// body. For non-dependent fields (no loose sibling `BVar`s) this is a
    /// no-op, so native and previously-working shapes are byte-for-byte
    /// unchanged. `prior_fvars` is the in-order list of `FVar`s already bound for
    /// fields `0..i`; the innermost binder (`BVar(0)` = field `i-1`) maps to the
    /// last entry, matching `instantiate_rev`'s reverse convention.
    pub(in crate::infer) fn open_field_type_with_fvars(
        field_ty: &Expr,
        prior_fvars: &[FVarId],
    ) -> Expr {
        if prior_fvars.is_empty() {
            return field_ty.clone();
        }
        let vals: Vec<Expr> = prior_fvars.iter().rev().map(|f| Expr::fvar(*f)).collect();
        field_ty.instantiate_rev(&vals)
    }
}
