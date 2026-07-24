// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match arm elaboration helpers.
//!
//! First-arm branch type inference and per-arm pattern dispatch logic,
//! extracted from `mod.rs` to stay under the 500-line file limit.

use super::super::*;
use super::{
    desugar_nat_numeral_add_pattern, desugar_nonzero_nat_lit, ensure_supported_literal_pattern,
    normalize_nested_nat_numeral_add_pattern, numeral_add_pattern_binder_name,
    wrap_alias_surface_body, wrap_with_extra_params, ExtraParamBinding,
};

impl<'a> ElabCtx<'a> {
    fn infer_first_arm_body_ty(&mut self, body: &SurfaceExpr) -> Result<Expr, ElabError> {
        let body = self.elaborate_with_expected_type(body, self.current_expected_type.clone())?;
        let ty = self.infer_type(&body)?;
        // Resolve solved metavars and canonicalize level params before returning (#2781).
        // Without this, callers see stale FVars (unresolved metas) and level params
        // in the branch type, causing Const-vs-FVar unification failures in nested
        // recursor calls (e.g., Nat.rec inside a match arm body — see #469).
        let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
        Ok(self.whnf(&ty))
    }

    /// Infer the result type from the first arm of a match expression.
    ///
    /// Binds any pattern variables in the first arm's pattern, elaborates
    /// the body, and returns the inferred type. Used to determine the
    /// motive for casesOn/rec construction.
    pub(in crate::infer) fn infer_first_arm_branch_ty(
        &mut self,
        first_arm: &clean_parser::SurfaceMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        match &first_arm.pattern {
            SurfacePattern::Var(name) => {
                // Check if this "variable" is actually a nullary constructor (#386).
                // Resolution also consults opened namespaces so an opened ctor
                // alias is recognized as a constructor, not bound as a variable.
                let is_nullary_ctor = self.resolve_ctor_name(name, type_name).is_some();

                if is_nullary_ctor {
                    self.infer_first_arm_body_ty(&first_arm.body)
                } else {
                    let _fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let ty = self.infer_first_arm_body_ty(&first_arm.body)?;
                    self.pop_local();
                    Ok(ty)
                }
            }
            SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                self.infer_first_arm_body_ty(&first_arm.body)
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => self.infer_ctor_arm_branch_ty(
                first_arm,
                ctor_name,
                sub_pats,
                scrutinee_ty,
                type_name,
            ),
            SurfacePattern::Lit(lit) => {
                ensure_supported_literal_pattern("match arm pattern", type_name, lit)?;
                self.infer_first_arm_body_ty(&first_arm.body)
            }
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                let var_name = numeral_add_pattern_binder_name(
                    "match arm pattern",
                    type_name,
                    inner_pat.as_ref(),
                    *k,
                )?;
                let _fvar = self.push_local(var_name, scrutinee_ty.clone());
                let ty = self.infer_first_arm_body_ty(&first_arm.body)?;
                self.pop_local();
                Ok(ty)
            }
            SurfacePattern::As(name, inner_pat) => {
                let (pattern, alias_value) =
                    self.rewrite_as_pattern_inner("match arm pattern", scrutinee_ty, inner_pat)?;
                let rewritten_arm = clean_parser::SurfaceMatchArm {
                    span: first_arm.span,
                    pattern,
                    body: wrap_alias_surface_body(name, alias_value, &first_arm.body),
                };
                self.infer_first_arm_branch_ty(&rewritten_arm, scrutinee_ty, type_name)
            }
            _ => self.infer_first_arm_body_ty(&first_arm.body),
        }
    }

    /// Resolve an open constant motive from the remaining match arms before
    /// any minor premise is retained.
    ///
    /// In inference position the first arm defines the motive. A polymorphic
    /// constructor such as `Or.inr hp` can infer `Or ?q p`, leaving `?q` to be
    /// learned from a later arm. If we immediately elaborate and retain that
    /// first minor, it receives a *fresh* result-only metavariable which is not
    /// scope-safe to alias to `?q`; the later arm resolves the motive but the
    /// first minor's independent meta escapes to kernel registration.
    ///
    /// Probe the remaining arms transactionally, unify their inferred result
    /// types with the first-arm motive, and keep only a fully resolved motive.
    /// The probe always rolls back its temporary locals/metas. We then replay
    /// the ground solution into the original motive scope, after which normal
    /// minor elaboration is bidirectionally pinned from the start. Dependent
    /// and indexed motives are deliberately excluded because their arm result
    /// types may legitimately differ.
    pub(in crate::infer) fn stabilize_open_constant_match_motive(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: Expr,
    ) -> Result<Expr, ElabError> {
        let branch_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&branch_ty));
        let nonindexed = self
            .env
            .get_inductive(&Name::from_string(type_name))
            .is_some_and(|ind| ind.num_indices == 0);
        if arms.len() < 2
            || !self.has_metavars(&branch_ty)
            || self.match_dependent_motive.is_some()
            || !nonindexed
        {
            return Ok(branch_ty);
        }

        let mut resolved_motive: Option<Expr> = None;
        self.with_optional_temporary_local_scope(|this| -> Result<Option<()>, ElabError> {
            for arm in &arms[1..] {
                let candidate = match this.infer_first_arm_branch_ty(arm, scrutinee_ty, type_name) {
                    Ok(candidate) => candidate,
                    // This is a completeness probe only. The ordinary arm
                    // compiler below remains authoritative for diagnostics.
                    Err(_) => return Ok(None),
                };
                let branch_now = this.metas.instantiate(&branch_ty);
                let candidate_now = this.metas.instantiate(&candidate);
                let ctx = this.build_local_ctx();
                let mut unifier = Unifier::with_env(&mut this.metas, this.env, ctx);
                if matches!(
                    unifier.unify(&branch_now, &candidate_now),
                    UnifyResult::Failure(_)
                ) {
                    return Ok(None);
                }
            }
            let resolved = this
                .metas
                .instantiate_levels(&this.metas.instantiate(&branch_ty));
            if !this.has_metavars(&resolved) {
                resolved_motive = Some(resolved);
            }
            // `None` intentionally rolls the whole probe back; only the closed
            // expression copied into `resolved_motive` crosses the boundary.
            Ok(None)
        })?;

        let Some(resolved) = resolved_motive else {
            return Ok(branch_ty);
        };
        let ctx = self.build_local_ctx();
        let replayed = {
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            matches!(unifier.unify(&branch_ty, &resolved), UnifyResult::Success)
        };
        if !replayed {
            return Ok(branch_ty);
        }
        Ok(self
            .metas
            .instantiate_levels(&self.metas.instantiate(&branch_ty)))
    }

    /// Infer branch type for a constructor pattern in the first arm.
    fn infer_ctor_arm_branch_ty(
        &mut self,
        first_arm: &clean_parser::SurfaceMatchArm,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.infer_ctor_arm_branch_ty_inner(
                first_arm,
                ctor_name,
                sub_pats,
                scrutinee_ty,
                type_name,
            )
        })
    }

    fn infer_ctor_arm_branch_ty_inner(
        &mut self,
        first_arm: &clean_parser::SurfaceMatchArm,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        let user_sub_pats: Vec<SurfacePattern> = sub_pats
            .iter()
            .map(normalize_nested_nat_numeral_add_pattern)
            .collect();
        let full_ctor = self.ctor_pattern_full_name(ctor_name, type_name);
        // Mirror `elaborate_ctor_arm_inner`: resolve the anonymous-tuple
        // placeholder against the scrutinee's sole real constructor before the
        // authenticated ctor/inductive check. Identity for a genuine Prod.
        let full_ctor = self
            .remap_anonymous_tuple_ctor(type_name, &full_ctor, user_sub_pats.len())
            .unwrap_or(full_ctor);
        let _ctor_info = self
            .env
            .get_constructor(&Name::from_string(&full_ctor))
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        // Mirror `elaborate_ctor_arm`: expand explicit-only patterns to full
        // field length so motive inference binds one fvar per field, including
        // implicit index-witness fields, and the arity check is narrowed to the
        // explicit-field count.
        let normalized_sub_pats = self.expand_implicit_ctor_field_patterns(
            "match arm pattern",
            &full_ctor,
            &user_sub_pats,
        )?;

        if normalized_sub_pats.is_empty() {
            return self.infer_first_arm_body_ty(&first_arm.body);
        }

        let field_types =
            self.compute_ctor_field_types(&Name::from_string(&full_ctor), scrutinee_ty)?;
        if field_types.len() != normalized_sub_pats.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{full_ctor}` exposes {} fields but the normalized pattern has {} slots",
                field_types.len(),
                normalized_sub_pats.len()
            )));
        }

        let mut fvar_tys = Vec::new();
        for (pat, field_ty) in normalized_sub_pats.iter().zip(field_types) {
            // Open dependent field types against the fields already bound (see
            // `elaborate_ctor_arm` / `open_field_type_with_fvars`).
            let prior_fvars: Vec<FVarId> =
                fvar_tys.iter().map(|(f, _): &(FVarId, Expr)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);
            // Mirror `elaborate_ctor_arm`: beta-reduce a bare-predicate field
            // type against the preceding witness so motive inference binds the
            // field at a `Const`-headed (nameable) type (see
            // `beta_reduce_predicate_field_ty`).
            let field_ty = self.beta_reduce_predicate_field_ty(&field_ty, &prior_fvars);
            let var_name = match pat {
                SurfacePattern::Var(n) => n.clone(),
                _ => "_".to_string(),
            };
            let fvar = self.push_local(var_name, field_ty.clone());
            fvar_tys.push((fvar, field_ty));
        }
        let nested_plans =
            self.collect_nested_field_plans("match arm pattern", &normalized_sub_pats, &fvar_tys)?;

        let ty = self.infer_first_arm_body_ty(&first_arm.body)?;

        self.cleanup_nested_field_plans(&nested_plans);
        for _ in &fvar_tys {
            self.pop_local();
        }

        // DEPENDENT-INDEX BRANCH TYPE (Track S — `Vec.tail`). The inferred body
        // type can reference a *field-bound* fvar that is now out of scope — the
        // index-unification case where the body is the constructor's recursive
        // field itself:
        //
        //   def Vec.tail … (v : Vec α (Nat.succ n)) : Vec α n :=
        //     match v with | Vec.cons _ tl => tl
        //
        // Here `tl : Vec α n'` with `n'` the cons-bound implicit index, so the
        // first-arm type is `Vec α n'` — leaking `n'` after the field locals are
        // popped. Using that as the constant `branch_ty` would later surface as an
        // `UnknownFVar`. When the inferred type still mentions a just-bound field
        // fvar AND the match runs under an explicit expected type (the function's
        // declared return `Vec α n`), use that expected type as the branch type
        // instead: it is closed, well-scoped, and the dependent (index-refining)
        // motive built downstream recovers each arm's real per-branch type from it.
        let field_ids: std::collections::HashSet<FVarId> =
            fvar_tys.iter().map(|(f, _)| *f).collect();
        let leaks_field_fvar = crate::tactic::hypothesis::collect_fvars(&ty)
            .iter()
            .any(|f| field_ids.contains(f));
        if leaks_field_fvar {
            if let Some(expected) = self.current_expected_type.clone() {
                let expected = self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&expected));
                // Only substitute a *closed* expected type — never trade one
                // leaked fvar for another.
                if !crate::tactic::hypothesis::collect_fvars(&expected)
                    .iter()
                    .any(|f| field_ids.contains(f))
                {
                    return Ok(expected);
                }
            }
        }
        Ok(ty)
    }

    /// Elaborate a single match arm into a casesOn alternative expression.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn elaborate_match_arm(
        &mut self,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
        use_rec: bool,
    ) -> Result<Expr, ElabError> {
        match &arm.pattern {
            SurfacePattern::Var(name) => self.elaborate_var_arm(
                name,
                arm,
                arm_idx,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            ),
            SurfacePattern::Wildcard => {
                let arm_body =
                    self.elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))?;
                if arm_idx > 0 {
                    self.check_arm_type(&arm_body, branch_ty, arm_idx)?;
                }
                Ok(wrap_with_extra_params(arm_body, extra_param_info))
            }
            SurfacePattern::Inaccessible(_) => Err(ElabError::NotImplemented(
                "top-level inaccessible patterns in multi-arm match require discriminant refinement"
                    .to_string(),
            )),
            SurfacePattern::Ctor(ctor_name, sub_pats) => self.elaborate_ctor_arm(
                ctor_name,
                sub_pats,
                arm,
                arm_idx,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
                use_rec,
                None,
            ),
            SurfacePattern::As(name, inner_pat) => self.elaborate_as_arm(
                name,
                inner_pat,
                arm,
                arm_idx,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
                use_rec,
            ),
            SurfacePattern::Lit(lit) => self.elaborate_lit_arm(
                type_name,
                lit,
                arm,
                arm_idx,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            ),
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                let _ = numeral_add_pattern_binder_name(
                    "match arm pattern",
                    type_name,
                    inner_pat.as_ref(),
                    *k,
                )?;
                if use_rec {
                    if *k > 1 {
                        return Err(ElabError::NotImplemented(format!(
                            "match arm pattern: recursive `n + {k}` numeral-add patterns are not currently supported"
                        )));
                    }
                    let succ_sub_pats = [inner_pat.as_ref().clone()];
                    let succ_ctor = format!("{type_name}.succ");
                    self.elaborate_rec_arm(
                        &succ_ctor,
                        &succ_sub_pats,
                        &arm.body,
                        scrutinee_ty,
                        branch_ty,
                        arm_idx,
                        extra_param_info,
                    )
                } else if *k <= 1 {
                    self.elaborate_numeral_add_arm(
                        type_name,
                        inner_pat,
                        *k,
                        arm,
                        arm_idx,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                    )
                } else {
                    let desugared = desugar_nat_numeral_add_pattern(inner_pat.as_ref(), *k);
                    if let SurfacePattern::Ctor(ref ctor_name, ref sub_pats) = desugared {
                        self.elaborate_ctor_arm(
                            ctor_name,
                            sub_pats,
                            arm,
                            arm_idx,
                            type_name,
                            scrutinee_ty,
                            branch_ty,
                            extra_param_info,
                            false,
                            None,
                        )
                    } else {
                        unreachable!("desugar_nat_numeral_add_pattern returns Ctor for k > 1")
                    }
                }
            }
            _ => Err(ElabError::NotImplemented(format!(
                "match arm pattern: {:?}",
                arm.pattern
            ))),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elaborate_var_arm(
        &mut self,
        name: &str,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Expr, ElabError> {
        // Recognize an opened-namespace ctor alias as a nullary constructor,
        // not a fresh pattern variable binding.
        let nullary_ctor = self.resolve_ctor_name(name, type_name);

        if let Some(full_ctor) = nullary_ctor {
            // Per-arm expected type for the (nullary) constructor `full_ctor`.
            let arm_ty = self.dependent_arm_branch_ty(branch_ty, &full_ctor, scrutinee_ty, &[])?;
            let arm_body = self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
            if arm_idx > 0 {
                self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
            }
            Ok(wrap_with_extra_params(arm_body, extra_param_info))
        } else {
            let fvar = self.push_local(name.to_string(), scrutinee_ty.clone());
            let arm_body = self.elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))?;
            if arm_idx > 0 {
                self.check_arm_type(&arm_body, branch_ty, arm_idx)?;
            }
            let arm_body = wrap_with_extra_params(arm_body, extra_param_info);
            self.pop_local();
            let body_abs = arm_body.abstract_fvar(fvar);
            Ok(Expr::lam(
                BinderInfo::Default,
                scrutinee_ty.clone(),
                body_abs,
            ))
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elaborate_ctor_arm(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
        use_rec: bool,
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.elaborate_ctor_arm_inner(
                ctor_name,
                sub_pats,
                arm,
                arm_idx,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
                use_rec,
                fallback_alt,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn elaborate_ctor_arm_inner(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
        use_rec: bool,
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        // The parser represents an anonymous constructor pattern as a
        // right-nested `Prod.mk`. For a native single-constructor structure,
        // authenticate and remap that placeholder to the registered flat
        // constructor before normal field expansion. Genuine `Prod` and the
        // non-structure two-field shapes remain on their existing path.
        let anon_remap = if ctor_name == "Prod.mk" {
            self.remap_anon_tuple_to_structure(type_name, sub_pats)
        } else {
            None
        };
        let ctor_name = anon_remap
            .as_ref()
            .map_or(ctor_name, |(ctor, _)| ctor.as_str());
        let sub_pats = anon_remap
            .as_ref()
            .map_or(sub_pats, |(_, patterns)| patterns.as_slice());

        let user_sub_pats: Vec<SurfacePattern> = sub_pats
            .iter()
            .map(normalize_nested_nat_numeral_add_pattern)
            .collect();
        let full_ctor = self.ctor_pattern_full_name(ctor_name, type_name);
        // Resolve the parser's anonymous-tuple placeholder (`⟨a, b⟩` → Prod.mk)
        // against the scrutinee's sole real constructor (And.intro, Exists.intro,
        // Iff.intro, …) so the authenticated ctor/inductive check below sees the
        // constructor that actually belongs. Identity for a genuine Prod.
        let full_ctor = self
            .remap_anonymous_tuple_ctor(type_name, &full_ctor, user_sub_pats.len())
            .unwrap_or(full_ctor);
        let _ctor_info = self
            .env
            .get_constructor(&Name::from_string(&full_ctor))
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        // Expand explicit-only field patterns to full field length, inserting a
        // wildcard at each implicit field position (e.g. the `{n : Nat}` index
        // witness of an indexed family). This both narrows the arity check to the
        // explicit-field count and produces a `num_fields`-length list so the
        // downstream field-binding loops line up unchanged.
        let normalized_sub_pats = self.expand_implicit_ctor_field_patterns(
            "match arm pattern",
            &full_ctor,
            &user_sub_pats,
        )?;

        if use_rec && !normalized_sub_pats.is_empty() {
            return self.elaborate_rec_arm(
                &full_ctor,
                &normalized_sub_pats,
                &arm.body,
                scrutinee_ty,
                branch_ty,
                arm_idx,
                extra_param_info,
            );
        }
        if normalized_sub_pats.is_empty() {
            // Per-arm expected type. For a dependent motive this is
            // `R[scrutinee := ctorᵢ]`; for a constant motive it is `branch_ty`.
            let arm_ty = self.dependent_arm_branch_ty(branch_ty, &full_ctor, scrutinee_ty, &[])?;
            let arm_body = self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
            if arm_idx > 0 {
                self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
            }
            return Ok(wrap_with_extra_params(arm_body, extra_param_info));
        }

        let field_types =
            self.compute_ctor_field_types(&Name::from_string(&full_ctor), scrutinee_ty)?;
        if field_types.len() != normalized_sub_pats.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{full_ctor}` exposes {} fields but the normalized pattern has {} slots",
                field_types.len(),
                normalized_sub_pats.len()
            )));
        }

        let mut fvar_tys: Vec<(FVarId, Expr)> = Vec::new();
        for (pat, field_ty) in normalized_sub_pats.iter().zip(field_types) {
            // Open dependent field types against the fields already bound, so a
            // later field's type (e.g. `tl : IVec n`) references its sibling by
            // `FVar` rather than a loose telescope-relative `BVar` (#bug:
            // indexed-family dependent field binders shift out of scope).
            let prior_fvars: Vec<FVarId> = fvar_tys.iter().map(|(f, _)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);
            // Beta-reduce a bare-predicate field type (the anonymous-tuple
            // `Prod.mk`-over-dependent-`Exists`/`Sigma` case) against the
            // preceding witness field, so the binder is `Const`-headed (`p x`
            // rather than an un-applied `fun x => …`). Definitionally equal, so
            // the kernel re-checks the same term; a non-`Lam` type is unchanged.
            let field_ty = self.beta_reduce_predicate_field_ty(&field_ty, &prior_fvars);
            let var_name = match pat {
                SurfacePattern::Var(n) => n.clone(),
                SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => "_".to_string(),
                _ => "_".to_string(),
            };
            let fvar = self.push_local(var_name, field_ty.clone());
            fvar_tys.push((fvar, field_ty.clone()));
        }
        let nested_plans =
            self.collect_nested_field_plans("match arm pattern", &normalized_sub_pats, &fvar_tys)?;

        // Per-arm expected type. For a dependent motive this is
        // `R[scrutinee := ctorᵢ field₀ … fieldₙ]` (built from the just-bound
        // field fvars); for a constant motive it stays `branch_ty`.
        let field_ids: Vec<FVarId> = fvar_tys.iter().map(|(fvar, _)| *fvar).collect();
        let arm_ty =
            self.dependent_arm_branch_ty(branch_ty, &full_ctor, scrutinee_ty, &field_ids)?;

        let arm_body = self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
        if arm_idx > 0 {
            self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
        }
        let arm_body = wrap_with_extra_params(arm_body, extra_param_info);
        let mut result = if let Some(fallback_alt) = fallback_alt {
            let fallback_body = fvar_tys
                .iter()
                .fold(fallback_alt.clone(), |acc, (fvar, _)| {
                    Expr::app(acc, Expr::fvar(*fvar))
                });
            let mut result = arm_body;
            for plan in nested_plans.iter().rev() {
                result =
                    self.apply_nested_pattern_plan(result, plan, &arm_ty, Some(&fallback_body))?;
            }
            result
        } else {
            self.apply_nested_field_plans(&nested_plans, arm_body, &arm_ty)?
        };

        for (fvar, fvar_ty) in fvar_tys.iter().rev() {
            self.pop_local();
            result = result.abstract_fvar(*fvar);
            result = Expr::lam(BinderInfo::Default, fvar_ty.clone(), result);
        }
        Ok(result)
    }

    #[allow(clippy::too_many_arguments)]
    fn elaborate_as_arm(
        &mut self,
        name: &str,
        inner_pat: &SurfacePattern,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
        use_rec: bool,
    ) -> Result<Expr, ElabError> {
        let (pattern, alias_value) =
            self.rewrite_as_pattern_inner("match arm pattern", scrutinee_ty, inner_pat)?;
        let rewritten_arm = clean_parser::SurfaceMatchArm {
            span: arm.span,
            pattern,
            body: wrap_alias_surface_body(name, alias_value, &arm.body),
        };
        self.elaborate_match_arm(
            &rewritten_arm,
            arm_idx,
            type_name,
            scrutinee_ty,
            branch_ty,
            extra_param_info,
            use_rec,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elaborate_lit_arm(
        &mut self,
        type_name: &str,
        lit: &SurfaceLit,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Expr, ElabError> {
        ensure_supported_literal_pattern("match arm pattern", type_name, lit)?;

        match lit {
            SurfaceLit::Nat(0) => {
                // Per-arm expected type under a DEPENDENT motive: this arm's
                // pattern instance is the nullary `<T>.zero` (e.g. the
                // equation-wrapped `match h :` motive expects
                // `e = Nat.zero → C` here, audit d01). Constant motives get
                // `branch_ty` back unchanged.
                let arm_ty = self.dependent_arm_branch_ty(
                    branch_ty,
                    &format!("{type_name}.zero"),
                    scrutinee_ty,
                    &[],
                )?;
                let arm_body =
                    self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                if arm_idx > 0 {
                    self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
                }
                Ok(wrap_with_extra_params(arm_body, extra_param_info))
            }
            SurfaceLit::Nat(k) => {
                // Non-zero Nat literal: desugar Nat(k) to Ctor("Nat.succ", [Nat(k-1)])
                // and route through the existing Ctor elaboration path (#796).
                let desugared = desugar_nonzero_nat_lit(*k);
                if let SurfacePattern::Ctor(ref ctor_name, ref sub_pats) = desugared {
                    self.elaborate_ctor_arm(
                        ctor_name,
                        sub_pats,
                        arm,
                        arm_idx,
                        type_name,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                        false,
                        None,
                    )
                } else {
                    unreachable!("desugar_nonzero_nat_lit returns Ctor for k > 0")
                }
            }
            _ => Err(ElabError::NotImplemented(format!(
                "match arm pattern: non-Nat literal {lit:?}"
            ))),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elaborate_numeral_add_arm(
        &mut self,
        type_name: &str,
        inner_pat: &SurfacePattern,
        k: u64,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Expr, ElabError> {
        let var_name =
            numeral_add_pattern_binder_name("match arm pattern", type_name, inner_pat, k)?;
        let fvar = self.push_local(var_name, scrutinee_ty.clone());
        // Under a DEPENDENT motive the arm's expected type is the motive at
        // this arm's pattern instance `succ^k(var)`, not the shared
        // `branch_ty` — e.g. the equation-wrapped `match h :` motive gives
        // this arm `e = var + k → C` (audit d01). Constant motives keep the
        // old `branch_ty` byte-for-byte (`arm_branch_ty` returns the default).
        let arm_ty = if self.match_dependent_motive.is_some() {
            let mut ctor_value = Expr::fvar(fvar);
            for _ in 0..k {
                ctor_value = Expr::app(
                    Expr::const_(Name::from_string(&format!("{type_name}.succ")), vec![]),
                    ctor_value,
                );
            }
            self.arm_branch_ty(branch_ty, &ctor_value)
        } else {
            branch_ty.clone()
        };
        let arm_body = self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
        if arm_idx > 0 {
            self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
        }
        let arm_body = wrap_with_extra_params(arm_body, extra_param_info);
        self.pop_local();
        let body_abs = arm_body.abstract_fvar(fvar);
        Ok(Expr::lam(
            BinderInfo::Default,
            scrutinee_ty.clone(),
            body_abs,
        ))
    }
}
