// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Do-notation match elaboration (casesOn dispatch for `match` inside do blocks).

use super::*;
use crate::infer::elab_match::{
    desugar_nat_numeral_add_pattern, desugar_nonzero_nat_lit, ensure_ctor_pattern_arity,
    ensure_supported_literal_pattern, expand_do_or_match_arms,
    normalize_nested_nat_numeral_add_pattern, numeral_add_pattern_binder_name,
    prepend_do_alias_binding,
};

impl<'a> ElabCtx<'a> {
    fn infer_do_body_ty(&mut self, body: &[DoElem]) -> Result<Expr, ElabError> {
        match body {
            [DoElem::Return(_, expr)] => {
                let (u, _, m) = self.get_or_create_monad_info();

                if let Some((loop_u, sigma)) = self.do_loop_ctx.as_ref().and_then(|ctx| {
                    ctx.return_type
                        .as_ref()
                        .map(|_| (ctx.u_level.clone(), ctx.sigma.clone()))
                }) {
                    let for_in_step = Expr::const_(Name::from_string("ForInStep"), vec![loop_u]);
                    return Ok(Expr::app(m, Expr::app(for_in_step, sigma)));
                }

                if self
                    .do_control_stack
                    .as_ref()
                    .and_then(|stack| stack.return_layer_idx)
                    .is_some()
                {
                    let alpha = self.fresh_meta(Expr::sort(u));
                    return Ok(Expr::app(m, alpha));
                }

                let val = self.elaborate(expr)?;
                let val_ty = self.infer_type(&val)?;
                Ok(Expr::app(m, val_ty))
            }
            _ => {
                let body_expr = self.elab_do_elems(body)?;
                let ty = self.infer_type(&body_expr)?;
                // A do-element body that is itself a `match` desugars to a
                // `T.casesOn (fun _ : T => R) … scrutinee`, whose inferred type is
                // the *beta-redex* `(fun _ : T => R) scrutinee`. When that body is
                // a match arm, its pattern binders (e.g. the `addr` of an outer
                // `| .ptr addr =>` arm) are popped right after this type is read
                // — but `scrutinee` still references them. Using the redex as the
                // enclosing match's `branch_ty` then leaks those popped fvars into
                // `eliminator_levels`/`infer_sort`, surfacing as
                // `UnknownFVar(addr)` (the `getAllocIdFromPtrARC` /
                // Borrow/Aggregate/Memory `match … find?` shape). Head-beta-reduce
                // the redex so the constant motive body `R` is exposed and the
                // scrutinee — hence the arm fvars — drops out. We only peel `App(Lam,
                // arg)` redexes (never definitional unfolding), so a genuine
                // monadic abbreviation head `m α` is preserved.
                Ok(Self::beta_reduce_motive_redex(ty))
            }
        }
    }

    /// Repeatedly head-beta-reduce `App(Lam(_, _, body), arg)` redexes.
    ///
    /// Only peels surface beta-redexes (the casesOn-motive-applied-to-scrutinee
    /// form a nested `match` body produces); it does NOT whnf-unfold constants,
    /// so a monadic-abbreviation result type such as `MySem Nat` is returned
    /// unchanged rather than expanded into its transformer stack.
    fn beta_reduce_motive_redex(mut ty: Expr) -> Expr {
        loop {
            let reduced = match ty.kind() {
                ExprKind::App(func, arg) => match func.kind() {
                    ExprKind::Lam(_, _, lam_body) => Some(lam_body.instantiate(arg)),
                    _ => None,
                },
                _ => None,
            };
            match reduced {
                Some(next) => ty = next,
                None => return ty,
            }
        }
    }

    /// Desugar `match discrs with | pat => do_seq ...` inside a do block.
    /// Single-discriminant → casesOn, multi-discriminant → nested `Prod.mk`.
    pub(super) fn elab_do_match(
        &mut self,
        discrs: &[SurfaceExpr],
        arms: &[DoMatchArm],
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| this.elab_do_match_inner(discrs, arms))
    }

    fn elab_do_match_inner(
        &mut self,
        discrs: &[SurfaceExpr],
        arms: &[DoMatchArm],
    ) -> Result<Expr, ElabError> {
        if discrs.is_empty() {
            return Err(ElabError::NotImplemented(
                "match with no discriminants in do block".into(),
            ));
        }
        if arms.is_empty() {
            return Err(ElabError::NotImplemented(
                "match with no arms in do block".into(),
            ));
        }

        let expanded_arms = expand_do_or_match_arms(arms);

        // Two-discriminant do-match (`match a, b with | p1, p2 => …`) — Track FF.
        //
        // The plain-`match` parser tuples both discriminants and arm patterns
        // into a right-nested `Prod.mk` (see `grammar/expr_match.rs::match_body`),
        // so expression-level multi-discriminant matches "just work" through
        // `Prod.casesOn`. The *do*-block parser (`grammar/expr_do.rs::parse_do_match`)
        // deliberately leaves both un-tupled, deferring to the elaborator. The
        // scrutinee is tupled below; here we apply the SAME right-nested `Prod.mk`
        // tupling to each arm's two patterns, so every arm carries exactly one
        // pattern and the rest of the pipeline (single-pattern `casesOn` dispatch)
        // handles it unchanged. Without this, `elab_do_match_arm` hard-rejected
        // multi-pattern arms with "multi-discriminant match in do block with
        // casesOn" — the wall hit by `semOverflow`/`semAtomicRMW`/`semFCmpInst`
        // (`match lhs, rhs with | .int …, .int … => …`). The kernel re-checks the
        // resulting `Prod.casesOn` term, so soundness is unchanged: this is the
        // same surface-syntax desugaring the parser performs for the
        // expression-level form.
        //
        // Scope gate: only the exactly-two-discriminant form. Three-or-more
        // discriminants with a leading *variable*-binding pattern (`match ty,
        // lhs, rhs with | ty, .vector …, .vector … => …` in
        // `semICmpInst`/`semBinOp`) drive a nested mixed var/ctor `Prod.casesOn`
        // the do-match path does not yet build correctly — it produced a
        // kernel-rejected term and synthetic-sorry recovery. Those fall through
        // to the existing honest "multi-discriminant" error, keeping every file
        // free of new sorry/kernel-fail artifacts while still landing the
        // two-discriminant win.
        let two_discriminant = discrs.len() == 2
            && expanded_arms
                .iter()
                .all(|arm| arm.patterns.len() == discrs.len());
        let tupled_arms: Vec<DoMatchArm>;
        let arms = if two_discriminant {
            tupled_arms = expanded_arms
                .iter()
                .map(|arm| {
                    let pattern = arm
                        .patterns
                        .iter()
                        .cloned()
                        .rev()
                        .reduce(|acc, pat| {
                            SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc])
                        })
                        // The `two_discriminant` gate guarantees every arm has
                        // exactly two patterns, so `reduce` always yields the
                        // nested `Prod.mk`; the `unwrap_or_else` is a defensive
                        // fallback that simply preserves a lone pattern so any
                        // malformed arm still reaches an honest downstream error.
                        .unwrap_or_else(|| {
                            arm.patterns
                                .first()
                                .cloned()
                                .unwrap_or(SurfacePattern::Wildcard)
                        });
                    DoMatchArm {
                        span: arm.span,
                        patterns: vec![pattern],
                        body: arm.body.clone(),
                    }
                })
                .collect();
            &tupled_arms
        } else {
            &expanded_arms
        };

        let scrutinee = if discrs.len() == 1 {
            self.elaborate(&discrs[0])?
        } else {
            let mut exprs: Vec<Expr> = discrs
                .iter()
                .map(|d| self.elaborate(d))
                .collect::<Result<_, _>>()?;
            let last = exprs.pop().ok_or_else(|| {
                ElabError::InternalInvariant(
                    "nonempty do-match discriminants produced an empty elaborated tuple".into(),
                )
            })?;
            let mut acc = last;
            for e in exprs.into_iter().rev() {
                let e_ty = self.infer_type(&e)?;
                let acc_ty = self.infer_type(&acc)?;
                acc = elab_do_prod::build_prod_value(self, &e_ty, &acc_ty, e, acc)?;
            }
            acc
        };

        let scrutinee_ty = self.infer_type(&scrutinee)?;

        if Self::do_match_has_q_patterns(arms) {
            if discrs.len() != 1 {
                return Err(ElabError::NotImplemented(
                    "q-pattern do-match with multiple discriminants".into(),
                ));
            }
            return self.elaborate_do_q_match(&scrutinee, &scrutinee_ty, arms);
        }

        if arms.len() == 1 {
            let rewritten_simple_arm = if arms[0].patterns.len() == 1 {
                match &arms[0].patterns[0] {
                    SurfacePattern::As(name, inner_pat)
                        if matches!(
                            inner_pat.as_ref(),
                            SurfacePattern::Var(_) | SurfacePattern::Wildcard
                        ) =>
                    {
                        let (pattern, alias_value) = self.rewrite_as_pattern_inner(
                            "do-match arm pattern",
                            &scrutinee_ty,
                            inner_pat,
                        )?;
                        Some(DoMatchArm {
                            span: arms[0].span,
                            patterns: vec![pattern],
                            body: prepend_do_alias_binding(name, alias_value, &arms[0].body),
                        })
                    }
                    _ => None,
                }
            } else {
                None
            };
            let arm = rewritten_simple_arm.as_ref().unwrap_or(&arms[0]);
            if arm.patterns.len() == 1 {
                match &arm.patterns[0] {
                    SurfacePattern::Var(name) => {
                        let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                        let body_expr = self.elab_do_body_with_outer_continuation(&arm.body)?;
                        self.pop_local();
                        // Fix #3419: Instantiate metas before abstracting FVars.
                        let body_inst = self.metas.instantiate(&body_expr);
                        let body_abs = body_inst.abstract_fvar(fvar);
                        return Ok(Expr::let_named(
                            Name::from_string(name),
                            scrutinee_ty,
                            scrutinee,
                            body_abs,
                            false,
                        ));
                    }
                    SurfacePattern::Wildcard => {
                        let body_expr = self.elab_do_body_with_outer_continuation(&arm.body)?;
                        return Ok(Expr::let_named(
                            Name::from_string("_"),
                            scrutinee_ty,
                            scrutinee,
                            body_expr,
                            true,
                        ));
                    }
                    _ => {}
                }
            }
        }

        let type_name = self.get_type_name(&scrutinee_ty)?;
        let cases_on_name = Name::from_string(&format!("{type_name}.casesOn"));
        let branch_ty = self.infer_do_match_branch_ty(&arms[0], &scrutinee_ty, &type_name)?;
        let elim_levels = self.eliminator_levels(&cases_on_name, &scrutinee_ty, &branch_ty)?;
        let eliminator = self.apply_eliminator_params(
            Expr::const_(cases_on_name.clone(), elim_levels),
            &scrutinee_ty,
            &type_name,
        )?;
        let motive = Expr::lam(BinderInfo::Default, scrutinee_ty.clone(), branch_ty.clone());
        let ind_info = self
            .env
            .get_inductive(&Name::from_string(&type_name))
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(type_name.clone()))?;
        let eliminator_metadata =
            self.match_eliminator_metadata(&type_name, &cases_on_name, true)?;
        let num_motives = eliminator_metadata.recursor.num_motives as usize;
        if num_motives == 0 {
            return Err(ElabError::InternalInvariant(format!(
                "do-match eliminator `{cases_on_name}` declares no motives"
            )));
        }
        let selected_motive_idx =
            self.selected_motive_index(&ind_info, num_motives, "do mutual-inductive match")?;

        // Nested inductives (#3396) lower into a mutual block: `Value` with a
        // `List Value` field becomes `Value` + an auxiliary `Value._List`. The
        // generated native `Value.casesOn` is therefore a *multi-motive* mutual
        // recursor — it takes one motive per type in the block and minor premises
        // for every constructor of every type, in declaration order:
        //
        //   Value.casesOn motive_Value motive_List minor_Value… minor_List… major
        //
        // The plain-`match` lowering (`elab_match::mod`) handles this; the
        // do-block lowering historically supplied ONLY the primary motive + the
        // primary minors, so the first (`.int`) arm landed in the `motive_List`
        // slot and the kernel rejected the term with `expected Value._List →
        // Sort 1` — the wall the trust-ir gating decls `getAllocIdFromPtrARC`,
        // `semAlloca`, and `semHeapAlloc` hit (each a `do { let s ← getState;
        // match ptrVal with … }`). Emit every motive in the recursor's global
        // member order. A later ordinary mutual member must not be forced into
        // motive slot zero.
        let aux_punit = if num_motives > 1 {
            self.punit_dummy_at_result_sort(&branch_ty)?
        } else {
            None
        };
        let aux_motive_body = aux_punit
            .as_ref()
            .map(|(punit, _)| punit.clone())
            .unwrap_or_else(|| branch_ty.clone());
        let aux_punit_unit = aux_punit.map(|(_, unit)| unit);
        let mut result = eliminator;
        for motive_idx in 0..num_motives {
            if motive_idx == selected_motive_idx {
                result = Expr::app(result, motive.clone());
            } else {
                let result_ty = self.infer_type(&result)?;
                let result_ty = self.whnf(&result_ty);
                let ExprKind::Pi(_, expected_motive, _) = result_ty.kind() else {
                    return Err(ElabError::TypeMismatch {
                        expected: format!("do-match motive slot {motive_idx}"),
                        actual: format!("{result_ty:?}"),
                    });
                };
                let aux_motive =
                    self.constant_over_telescope(expected_motive, aux_motive_body.clone());
                result = Expr::app(result, aux_motive);
            }
        }

        // Native metadata is authoritative for application layout. Imported
        // `casesOn` definitions use Lean's motive(s) → major → minors wrapper.
        if eliminator_metadata.major_after_motive {
            result = Expr::app(result, scrutinee.clone());
        }

        let mut primary_alts: Vec<Expr> = Vec::new();
        let mut applied_primary_minor_names: Vec<Option<Name>> = Vec::new();
        if let Some(ordered_alts) =
            self.try_build_ctor_ordered_do_match_alts(arms, &type_name, &scrutinee_ty, &branch_ty)?
        {
            let ind_info = self.env.get_inductive(&Name::from_string(&type_name));
            for (index, alt) in ordered_alts.into_iter().enumerate() {
                primary_alts.push(alt);
                applied_primary_minor_names
                    .push(ind_info.and_then(|info| info.constructor_names.get(index).cloned()));
            }
        } else {
            for arm in arms.iter() {
                let alt = self.elab_do_match_arm(arm, &scrutinee_ty, &type_name, &branch_ty)?;
                primary_alts.push(alt);
                applied_primary_minor_names.push(arm.patterns.first().and_then(|pattern| {
                    self.top_level_ctor_target_name(&type_name, pattern)
                        .map(|name| Name::from_string(&name))
                }));
            }
        }

        // Emit the complete global minor order. Auxiliary/sibling constructors
        // may occur before or after this member's authenticated constructor
        // slice; their PUnit inhabitant (or genuine wildcard/default value)
        // discharges the unreachable slots without an axiom.
        self.apply_do_match_aux_minors(
            &mut result,
            arms,
            &type_name,
            &scrutinee_ty,
            &branch_ty,
            aux_punit_unit.as_ref(),
            &primary_alts,
            &applied_primary_minor_names,
            &eliminator_metadata.recursor,
        )?;

        if !eliminator_metadata.major_after_motive {
            result = Expr::app(result, scrutinee);
        }

        Ok(result)
    }

    /// Emit the minor premises for a multi-motive `casesOn` in its authenticated
    /// global order (#3396, #3420). Each auxiliary constructor needs a minor
    /// premise with one lambda per field. When the auxiliary motives use
    /// PUnit, `aux_punit_unit` is their genuine inhabitant. Otherwise the body
    /// must come from a do-block wildcard/var arm or a nullary default of
    /// `branch_ty`; absence of either is an explicit elaboration error. Runtime
    /// unreachability never licenses an axiom or an ill-typed type-as-term.
    fn apply_do_match_aux_minors(
        &mut self,
        result: &mut Expr,
        arms: &[DoMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        aux_punit_unit: Option<&Expr>,
        primary_alts: &[Expr],
        applied_primary_minor_names: &[Option<Name>],
        rec: &clean_kernel::RecursorVal,
    ) -> Result<(), ElabError> {
        let Some(ind_info) = self
            .env
            .get_inductive(&Name::from_string(type_name))
            .cloned()
        else {
            return Ok(());
        };
        if rec.num_motives <= 1 {
            for alt in primary_alts {
                *result = Expr::app(result.clone(), alt.clone());
            }
            return Ok(());
        }
        let minor_rules = self.recursor_minor_rules(&ind_info, rec)?;
        let primary_range = self.validate_primary_minor_boundary(
            &ind_info,
            &minor_rules,
            applied_primary_minor_names,
            "do multi-motive match",
        )?;
        if primary_alts.len() != primary_range.len() {
            return Err(ElabError::InternalInvariant(format!(
                "do multi-motive match compiled {} primary alternatives for authenticated range {primary_range:?}",
                primary_alts.len()
            )));
        }

        // Without the PUnit motive, prefer a wildcard/var do-arm body (the
        // catch-all) for dead aux minors; otherwise a nullary default
        // constructor of `branch_ty`.
        let default_branch_value: Option<Expr> = if aux_punit_unit.is_none() {
            // A real catch-all body that fails to elaborate is an error, not
            // permission to silently substitute a different default.
            let wildcard_body = arms
                .iter()
                .rev()
                .find(|arm| {
                    arm.patterns.len() == 1
                        && matches!(
                            &arm.patterns[0],
                            SurfacePattern::Wildcard | SurfacePattern::Var(_)
                        )
                })
                .map(|arm| self.elab_do_body_with_outer_continuation(&arm.body))
                .transpose()?;
            match wildcard_body {
                some @ Some(_) => some,
                None => self.try_default_value_of_type(branch_ty)?,
            }
        } else {
            None
        };

        let _ = scrutinee_ty;
        for (rule_idx, rule) in minor_rules.iter().enumerate() {
            if primary_range.contains(&rule_idx) {
                *result = Expr::app(
                    result.clone(),
                    primary_alts[rule_idx - primary_range.start].clone(),
                );
                continue;
            }
            let minor_body = if let Some(unit) = aux_punit_unit {
                unit.clone()
            } else if let Some(db) = &default_branch_value {
                db.clone()
            } else {
                return Err(ElabError::NotImplemented(format!(
                    "cannot construct a sound do-match auxiliary minor for `{}` while matching \
                     `{type_name}`; add a wildcard arm or use an inhabited result type",
                    rule.constructor_name
                )));
            };
            let result_ty = self.infer_type(result)?;
            let result_ty = self.whnf(&result_ty);
            let ExprKind::Pi(_, expected_minor, _) = result_ty.kind() else {
                return Err(ElabError::TypeMismatch {
                    expected: format!("do-match minor for {}", rule.constructor_name),
                    actual: format!("{result_ty:?}"),
                });
            };
            let Some(alt) = self.constant_over_telescope_prefix(
                expected_minor,
                rule.num_fields as usize,
                minor_body,
            ) else {
                return Err(ElabError::TypeMismatch {
                    expected: format!(
                        "{} do-match field binders for {}",
                        rule.num_fields, rule.constructor_name
                    ),
                    actual: format!("{expected_minor:?}"),
                });
            };
            *result = Expr::app(result.clone(), alt);
        }
        Ok(())
    }

    fn infer_do_match_branch_ty(
        &mut self,
        first_arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        if first_arm.patterns.len() != 1 {
            return self.infer_do_body_ty(&first_arm.body);
        }

        match &first_arm.patterns[0] {
            SurfacePattern::Var(name) => {
                let full_ctor_name = format!("{type_name}.{name}");
                let is_nullary_ctor = self
                    .env
                    .get_constructor(&Name::from_string(&full_ctor_name))
                    .is_some();
                if is_nullary_ctor {
                    self.infer_do_body_ty(&first_arm.body)
                } else {
                    let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let ty = self.infer_do_body_ty(&first_arm.body)?;
                    self.pop_local();
                    let _ = fvar;
                    Ok(ty)
                }
            }
            SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                self.infer_do_body_ty(&first_arm.body)
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => self.infer_do_match_ctor_branch_ty(
                ctor_name,
                sub_pats,
                first_arm,
                scrutinee_ty,
                type_name,
            ),
            SurfacePattern::Lit(lit) => {
                ensure_supported_literal_pattern("do-match arm pattern", type_name, lit)?;
                self.infer_do_body_ty(&first_arm.body)
            }
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                let var_name = numeral_add_pattern_binder_name(
                    "do-match arm pattern",
                    type_name,
                    inner_pat.as_ref(),
                    *k,
                )?;
                let fvar = self.push_local(var_name, scrutinee_ty.clone());
                let ty = self.infer_do_body_ty(&first_arm.body)?;
                self.pop_local();
                let _ = fvar;
                Ok(ty)
            }
            SurfacePattern::As(name, inner_pat) => {
                let (pattern, alias_value) =
                    self.rewrite_as_pattern_inner("do-match arm pattern", scrutinee_ty, inner_pat)?;
                let rewritten_arm = DoMatchArm {
                    span: first_arm.span,
                    patterns: vec![pattern],
                    body: prepend_do_alias_binding(name, alias_value, &first_arm.body),
                };
                self.infer_do_match_branch_ty(&rewritten_arm, scrutinee_ty, type_name)
            }
            _ => self.infer_do_body_ty(&first_arm.body),
        }
    }

    fn infer_do_match_ctor_branch_ty(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.infer_do_match_ctor_branch_ty_inner(
                ctor_name,
                sub_pats,
                arm,
                scrutinee_ty,
                type_name,
            )
        })
    }

    fn infer_do_match_ctor_branch_ty_inner(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        let normalized_sub_pats: Vec<SurfacePattern> = sub_pats
            .iter()
            .map(normalize_nested_nat_numeral_add_pattern)
            .collect();
        let full_ctor = if ctor_name.contains('.') {
            ctor_name.to_string()
        } else {
            format!("{type_name}.{ctor_name}")
        };
        let ctor_info = self
            .env
            .get_constructor(&Name::from_string(&full_ctor))
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        ensure_ctor_pattern_arity(
            "do-match arm pattern",
            &full_ctor,
            Some(ctor_info.num_fields as usize),
            normalized_sub_pats.len(),
        )?;
        if normalized_sub_pats.is_empty() {
            return self.infer_do_body_ty(&arm.body);
        }
        let field_types =
            self.compute_ctor_field_types(&Name::from_string(&full_ctor), scrutinee_ty)?;
        if field_types.len() != normalized_sub_pats.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{full_ctor}` exposes {} fields but the do-match pattern has {} slots",
                field_types.len(),
                normalized_sub_pats.len()
            )));
        }
        let mut fvar_tys: Vec<(FVarId, Expr)> = Vec::new();
        for (pat, field_ty) in normalized_sub_pats.iter().zip(field_types) {
            // Open dependent field types against the fields already bound
            // (see `open_field_type_with_fvars`).
            let prior_fvars: Vec<FVarId> = fvar_tys.iter().map(|(f, _)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);
            let var_name = match pat {
                SurfacePattern::Var(n) => n.clone(),
                _ => "_".to_string(),
            };
            let fvar = self.push_local(var_name, field_ty.clone());
            fvar_tys.push((fvar, field_ty));
        }
        let nested_plans = self.collect_nested_field_plans(
            "do-match arm pattern",
            &normalized_sub_pats,
            &fvar_tys,
        )?;
        let ty = self.infer_do_body_ty(&arm.body)?;
        self.cleanup_nested_field_plans(&nested_plans);
        for _ in &fvar_tys {
            self.pop_local();
        }
        Ok(ty)
    }

    pub(super) fn elab_do_match_arm(
        &mut self,
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let pattern = if arm.patterns.len() == 1 {
            &arm.patterns[0]
        } else {
            return Err(ElabError::NotImplemented(
                "multi-discriminant match in do block with casesOn".into(),
            ));
        };

        match pattern {
            SurfacePattern::Var(name) => {
                let full_ctor_name = if name.contains('.') {
                    name.clone()
                } else {
                    format!("{type_name}.{name}")
                };
                let is_nullary_ctor = self
                    .env
                    .get_constructor(&Name::from_string(&full_ctor_name))
                    .is_some();
                if is_nullary_ctor {
                    self.elab_do_body_with_outer_continuation(&arm.body)
                } else {
                    let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let arm_body = self.elab_do_body_with_outer_continuation(&arm.body)?;
                    self.pop_local();
                    // Fix #3419: Instantiate metas before abstracting FVars.
                    let arm_inst = self.metas.instantiate(&arm_body);
                    let body_abs = arm_inst.abstract_fvar(fvar);
                    Ok(Expr::lam(
                        BinderInfo::Default,
                        scrutinee_ty.clone(),
                        body_abs,
                    ))
                }
            }
            SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                self.elab_do_body_with_outer_continuation(&arm.body)
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => self.elab_do_match_ctor_arm(
                ctor_name,
                sub_pats,
                arm,
                scrutinee_ty,
                type_name,
                branch_ty,
            ),
            SurfacePattern::Lit(lit) => {
                ensure_supported_literal_pattern("do-match arm pattern", type_name, lit)?;
                match lit {
                    SurfaceLit::Nat(0) => self.elab_do_body_with_outer_continuation(&arm.body),
                    SurfaceLit::Nat(k) => {
                        let desugared = desugar_nonzero_nat_lit(*k);
                        if let SurfacePattern::Ctor(ref ctor_name, ref sub_pats) = desugared {
                            self.elab_do_match_ctor_arm(
                                ctor_name,
                                sub_pats,
                                arm,
                                scrutinee_ty,
                                type_name,
                                branch_ty,
                            )
                        } else {
                            unreachable!("desugar_nonzero_nat_lit returns Ctor for k > 0")
                        }
                    }
                    _ => Err(ElabError::NotImplemented(format!(
                        "do-match arm pattern: non-Nat literal {lit:?}"
                    ))),
                }
            }
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                if *k <= 1 {
                    let var_name = numeral_add_pattern_binder_name(
                        "do-match arm pattern",
                        type_name,
                        inner_pat.as_ref(),
                        *k,
                    )?;
                    let fvar = self.push_local(var_name, scrutinee_ty.clone());
                    let arm_body = self.elab_do_body_with_outer_continuation(&arm.body)?;
                    self.pop_local();
                    // Fix #3419: Instantiate metas before abstracting FVars.
                    let arm_inst = self.metas.instantiate(&arm_body);
                    let body_abs = arm_inst.abstract_fvar(fvar);
                    Ok(Expr::lam(
                        BinderInfo::Default,
                        scrutinee_ty.clone(),
                        body_abs,
                    ))
                } else {
                    let desugared = desugar_nat_numeral_add_pattern(inner_pat.as_ref(), *k);
                    if let SurfacePattern::Ctor(ref ctor_name, ref sub_pats) = desugared {
                        self.elab_do_match_ctor_arm(
                            ctor_name,
                            sub_pats,
                            arm,
                            scrutinee_ty,
                            type_name,
                            branch_ty,
                        )
                    } else {
                        unreachable!("desugar_nat_numeral_add_pattern returns Ctor for k > 1")
                    }
                }
            }
            SurfacePattern::As(name, inner_pat) => {
                let (pattern, alias_value) =
                    self.rewrite_as_pattern_inner("do-match arm pattern", scrutinee_ty, inner_pat)?;
                let rewritten_arm = DoMatchArm {
                    span: arm.span,
                    patterns: vec![pattern],
                    body: prepend_do_alias_binding(name, alias_value, &arm.body),
                };
                self.elab_do_match_arm(&rewritten_arm, scrutinee_ty, type_name, branch_ty)
            }
            _ => Err(ElabError::NotImplemented(format!(
                "do-match arm pattern: {pattern:?}"
            ))),
        }
    }

    fn elab_do_match_ctor_arm(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        self.elab_do_match_ctor_arm_with_fallback(
            ctor_name,
            sub_pats,
            arm,
            scrutinee_ty,
            type_name,
            branch_ty,
            None,
        )
    }

    /// `elab_do_match_ctor_arm` with an optional fallback minor for non-matching
    /// nested sub-patterns. When several do-match arms share the same head
    /// constructor (e.g. `| some .arcRef => …` and `| some _perm => …`, or the
    /// numeral arms `| 1 => …` and `| n+2 => …` that both desugar to `Nat.succ`),
    /// the constructor's single `casesOn` minor must dispatch the *inner*
    /// sub-pattern, falling through to the next arm sharing this constructor.
    /// `fallback_alt`, when present, is the already-compiled minor for the
    /// later-in-source same-constructor arm: a function over THIS constructor's
    /// fields. It is applied to the current arm's field fvars and threaded into
    /// the nested-pattern plans, exactly as the plain-match `elaborate_ctor_arm`
    /// does — so the inner casesOn falls back to a real arm body. With `None`, a
    /// multi-constructor inner pattern fails closed as non-exhaustive; only a
    /// genuinely single-constructor inner type needs no fallback.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn elab_do_match_ctor_arm_with_fallback(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.elab_do_match_ctor_arm_with_fallback_inner(
                ctor_name,
                sub_pats,
                arm,
                scrutinee_ty,
                type_name,
                branch_ty,
                fallback_alt,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn elab_do_match_ctor_arm_with_fallback_inner(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        arm: &DoMatchArm,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        let normalized_sub_pats: Vec<SurfacePattern> = sub_pats
            .iter()
            .map(normalize_nested_nat_numeral_add_pattern)
            .collect();
        let full_ctor = if ctor_name.contains('.') {
            ctor_name.to_string()
        } else {
            format!("{type_name}.{ctor_name}")
        };
        let ctor_info = self
            .env
            .get_constructor(&Name::from_string(&full_ctor))
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        ensure_ctor_pattern_arity(
            "do-match arm pattern",
            &full_ctor,
            Some(ctor_info.num_fields as usize),
            normalized_sub_pats.len(),
        )?;
        if normalized_sub_pats.is_empty() {
            return self.elab_do_body_with_outer_continuation(&arm.body);
        }
        let field_types =
            self.compute_ctor_field_types(&Name::from_string(&full_ctor), scrutinee_ty)?;
        if field_types.len() != normalized_sub_pats.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{full_ctor}` exposes {} fields but the do-match pattern has {} slots",
                field_types.len(),
                normalized_sub_pats.len()
            )));
        }
        let mut fvar_tys: Vec<(FVarId, Expr)> = Vec::new();
        for (pat, field_ty) in normalized_sub_pats.iter().zip(field_types) {
            // Open dependent field types against the fields already bound
            // (see `open_field_type_with_fvars`).
            let prior_fvars: Vec<FVarId> = fvar_tys.iter().map(|(f, _)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);
            let var_name = match pat {
                SurfacePattern::Var(n) => n.clone(),
                _ => "_".to_string(),
            };
            let fvar = self.push_local(var_name, field_ty.clone());
            fvar_tys.push((fvar, field_ty.clone()));
        }
        let nested_plans = self.collect_nested_field_plans(
            "do-match arm pattern",
            &normalized_sub_pats,
            &fvar_tys,
        )?;
        let arm_body = self.elab_do_body_with_outer_continuation(&arm.body)?;
        // Thread the same-constructor fallback (when grouping multiple arms under
        // one minor), mirroring the plain-match `elaborate_ctor_arm`: apply the
        // prior compiled minor to this arm's field fvars to obtain a `branch_ty`
        // value, and feed it as the non-matching-sub-pattern fallback. With no
        // fallback this reduces to the legacy `apply_nested_field_plans` call.
        let mut alt_expr = if let Some(fallback_alt) = fallback_alt {
            let fallback_body = fvar_tys
                .iter()
                .fold(fallback_alt.clone(), |acc, (fvar, _)| {
                    Expr::app(acc, Expr::fvar(*fvar))
                });
            let mut result = arm_body;
            for plan in nested_plans.iter().rev() {
                result =
                    self.apply_nested_pattern_plan(result, plan, branch_ty, Some(&fallback_body))?;
            }
            result
        } else {
            self.apply_nested_field_plans(&nested_plans, arm_body, branch_ty)?
        };
        // Fix #3419: Instantiate metas before abstracting FVars.
        alt_expr = self.metas.instantiate(&alt_expr);
        for (fvar, fvar_ty) in fvar_tys.iter().rev() {
            self.pop_local();
            alt_expr = alt_expr.abstract_fvar(*fvar);
            alt_expr = Expr::lam(BinderInfo::Default, fvar_ty.clone(), alt_expr);
        }
        Ok(alt_expr)
    }
}
