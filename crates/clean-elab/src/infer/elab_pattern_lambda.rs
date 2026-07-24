// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern-match lambda elaboration helpers.

use super::*;
use clean_kernel::name::Name;

impl<'a> ElabCtx<'a> {
    fn top_level_prod_pattern_arity(pattern: &SurfacePattern) -> usize {
        match pattern {
            SurfacePattern::Ctor(name, fields)
                if matches!(name.as_str(), "Prod.mk" | "PProd.mk") && fields.len() == 2 =>
            {
                1 + Self::top_level_prod_pattern_arity(&fields[1])
            }
            _ => 1,
        }
    }

    /// Peel a nested Prod.mk pattern into per-argument sub-patterns.
    ///
    /// `Prod.mk(a, Prod.mk(b, c))` with arity 3 → `[a, b, c]`
    fn peel_prod_pattern(pattern: &SurfacePattern, arity: usize) -> Vec<SurfacePattern> {
        let mut result = Vec::with_capacity(arity);
        let mut current = pattern;
        for _ in 0..arity.saturating_sub(1) {
            match current {
                SurfacePattern::Ctor(name, fields)
                    if matches!(name.as_str(), "Prod.mk" | "PProd.mk") && fields.len() == 2 =>
                {
                    result.push(fields[0].clone());
                    current = &fields[1];
                }
                _ => break,
            }
        }
        result.push(current.clone());
        result
    }

    /// Check if any eta_local's type references a prior eta_local's FVar.
    ///
    /// When this returns true, the Pi telescope is dependent and the non-dependent
    /// Prod/PProd tuple approach cannot correctly represent the scrutinee type.
    fn eta_locals_have_dependency(eta_locals: &[(FVarId, Expr, BinderData, bool)]) -> bool {
        for (i, (_, ty, _, _)) in eta_locals.iter().enumerate() {
            if !ty.has_fvar_quick() {
                continue;
            }
            for (prior_fvar, _, _, _) in &eta_locals[..i] {
                // If abstracting the prior fvar changes the type, there is a dependency
                if ty.abstract_fvar(*prior_fvar) != *ty {
                    return true;
                }
            }
        }
        false
    }

    fn rewrite_pattern_lambda_tuple_pattern(
        pattern: &SurfacePattern,
        tuple_ctor_name: &str,
    ) -> SurfacePattern {
        match pattern {
            SurfacePattern::Ctor(name, fields) if name == "Prod.mk" && fields.len() == 2 => {
                SurfacePattern::Ctor(
                    tuple_ctor_name.to_string(),
                    vec![
                        fields[0].clone(),
                        Self::rewrite_pattern_lambda_tuple_pattern(&fields[1], tuple_ctor_name),
                    ],
                )
            }
            _ => pattern.clone(),
        }
    }

    fn rewrite_pattern_lambda_tuple_arms(
        arms: &[clean_parser::SurfaceMatchArm],
        tuple_ctor_name: &str,
    ) -> Vec<clean_parser::SurfaceMatchArm> {
        if tuple_ctor_name == "Prod.mk" {
            return arms.to_vec();
        }

        arms.iter()
            .map(|arm| clean_parser::SurfaceMatchArm {
                span: arm.span,
                pattern: Self::rewrite_pattern_lambda_tuple_pattern(&arm.pattern, tuple_ctor_name),
                body: arm.body.clone(),
            })
            .collect()
    }

    fn pattern_lambda_tuple_level(&self, ty: &Expr, use_pprod: bool) -> Result<Level, ElabError> {
        let sort_level = self.infer_sort(ty)?;
        if use_pprod {
            return Ok(sort_level);
        }

        match sort_level {
            Level::Succ(level) => Ok(level.as_ref().clone()),
            actual => Err(ElabError::TypeMismatch {
                expected: "Type-valued pattern-lambda binder".to_string(),
                actual: format!("{actual:?}"),
            }),
        }
    }

    fn build_pattern_lambda_scrutinee(
        &mut self,
        eta_locals: &[(FVarId, Expr, BinderData, bool)],
    ) -> Result<(Expr, Expr, &'static str), ElabError> {
        let use_pprod = eta_locals.iter().try_fold(false, |acc, (_, ty, _, _)| {
            Ok::<_, ElabError>(acc || !matches!(self.infer_sort(ty)?, Level::Succ(_)))
        })?;
        let tuple_type_name = if use_pprod { "PProd" } else { "Prod" };
        let tuple_ctor_name = if use_pprod { "PProd.mk" } else { "Prod.mk" };

        let (last_fvar, last_ty, _, _) = eta_locals
            .last()
            .expect("pattern lambda scrutinee requires locals");
        let mut value = Expr::fvar(*last_fvar);
        let mut value_ty = last_ty.clone();

        for (fvar, ty, _, _) in eta_locals.iter().rev().skip(1) {
            let left_level = self.pattern_lambda_tuple_level(ty, use_pprod)?;
            let right_level = self.pattern_lambda_tuple_level(&value_ty, use_pprod)?;
            let prod_mk = Expr::const_(
                Name::from_string(tuple_ctor_name),
                vec![left_level.clone(), right_level.clone()],
            );
            let step = Expr::app(prod_mk, ty.clone());
            let step = Expr::app(step, value_ty.clone());
            let step = Expr::app(step, Expr::fvar(*fvar));
            value = Expr::app(step, value);
            let prod = Expr::const_(
                Name::from_string(tuple_type_name),
                vec![left_level, right_level],
            );
            value_ty = Expr::app(Expr::app(prod, ty.clone()), value_ty);
        }

        Ok((value, value_ty, tuple_ctor_name))
    }

    fn try_elab_curried_pattern_lambda(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Option<Expr>, ElabError> {
        if binders.len() != 1 {
            return Ok(None);
        }

        let binder = &binders[0];
        let SurfaceExpr::Match(_, None, scrutinee, arms) = body else {
            return Ok(None);
        };
        let SurfaceExpr::Ident(_, scrutinee_name) = scrutinee.as_ref() else {
            return Ok(None);
        };
        if scrutinee_name != &binder.name || arms.is_empty() {
            return Ok(None);
        }

        let tuple_arity = Self::top_level_prod_pattern_arity(&arms[0].pattern);
        if tuple_arity <= 1 {
            return Ok(None);
        }

        let prev_expected = self.current_expected_type.clone();
        let Some(mut current_expected) = prev_expected.clone() else {
            return Ok(None);
        };

        let mut eta_locals: Vec<(FVarId, Expr, BinderData, bool)> = Vec::with_capacity(tuple_arity);
        for idx in 0..tuple_arity {
            let expected_pi = {
                let expected = self.metas.instantiate(&current_expected);
                let expected = self.metas.instantiate_levels(&expected);
                let expected = self.whnf(&expected);
                match expected.kind() {
                    ExprKind::Pi(bi, domain, codomain) => {
                        Some((*bi, domain.as_ref().clone(), codomain.as_ref().clone()))
                    }
                    _ => None,
                }
            };
            let Some((bi, domain, codomain)) = expected_pi else {
                self.current_expected_type = prev_expected;
                while let Some((_, _, _, is_inst_implicit)) = eta_locals.pop() {
                    if is_inst_implicit {
                        self.pop_local_instance();
                    }
                    self.pop_local();
                }
                return Ok(None);
            };

            let local_name = format!("{}_{}", binder.name, idx);
            let fvar = self.push_local(local_name.clone(), domain.clone());
            let is_inst_implicit = bi.info == BinderInfo::InstImplicit;
            if is_inst_implicit {
                self.push_local_instance(fvar, domain.clone());
            }

            current_expected = {
                let codomain = codomain.instantiate(&Expr::fvar(fvar));
                let codomain = self.metas.instantiate(&codomain);
                self.metas.instantiate_levels(&codomain)
            };

            eta_locals.push((fvar, domain, bi, is_inst_implicit));
        }

        self.current_expected_type = Some(current_expected);

        // When the Pi telescope is dependent (e.g., {b : β} → Imf f b → α),
        // the non-dependent Prod/PProd tuple cannot represent the scrutinee type
        // correctly. Use nested lambdas with an inner match instead.
        let body_result = if Self::eta_locals_have_dependency(&eta_locals) {
            self.elab_curried_dependent_match(arms, &eta_locals)
        } else {
            self.elab_curried_prod_match(arms, &eta_locals)
        };
        self.current_expected_type = prev_expected;

        let mut result = match body_result {
            Ok(expr) => expr,
            Err(err) => {
                while let Some((_, _, _, is_inst_implicit)) = eta_locals.pop() {
                    if is_inst_implicit {
                        self.pop_local_instance();
                    }
                    self.pop_local();
                }
                return Err(err);
            }
        };

        while let Some((fvar, ty, bi, is_inst_implicit)) = eta_locals.pop() {
            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();
            result = Expr::lam(bi, ty, result.abstract_fvar(fvar));
        }

        Ok(Some(result))
    }

    /// Non-dependent path: build a Prod/PProd tuple scrutinee and match on it.
    fn elab_curried_prod_match(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        eta_locals: &[(FVarId, Expr, BinderData, bool)],
    ) -> Result<Expr, ElabError> {
        let (scrutinee_expr, scrutinee_ty, tuple_ctor_name) =
            self.build_pattern_lambda_scrutinee(eta_locals)?;
        let rewritten_arms = Self::rewrite_pattern_lambda_tuple_arms(arms, tuple_ctor_name);
        self.elab_match_with_scrutinee(scrutinee_expr, scrutinee_ty, None, &rewritten_arms)
    }

    /// Dependent path: create nested lambdas and match only the last argument.
    ///
    /// For `{b : β} → Imf f b → α` with arms like `| _, Imf.mk a => a`, this
    /// builds `fun {b} (x : Imf f b) => match x with | Imf.mk a => a` instead
    /// of packing into a non-dependent Prod/PProd tuple.
    fn elab_curried_dependent_match(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        eta_locals: &[(FVarId, Expr, BinderData, bool)],
    ) -> Result<Expr, ElabError> {
        let arity = eta_locals.len();

        // Peel each arm's Prod pattern into per-argument sub-patterns
        let peeled_arms: Vec<Vec<SurfacePattern>> = arms
            .iter()
            .map(|arm| Self::peel_prod_pattern(&arm.pattern, arity))
            .collect();

        // Find the rightmost position with a constructor pattern in any arm.
        // Positions before it that are all wildcard/var get bound as plain lambdas.
        let match_pos = (0..arity)
            .rev()
            .find(|&pos| {
                peeled_arms.iter().any(|pats| {
                    !matches!(
                        pats.get(pos),
                        Some(SurfacePattern::Wildcard) | Some(SurfacePattern::Var(_))
                    )
                })
            })
            .unwrap_or(arity - 1);

        // No-silent-wrong: this lowering keeps only the column at `match_pos`;
        // a pattern VARIABLE in any other column is bound only by the alias
        // mechanism below (position before `match_pos` where the first arm has
        // a Var and every arm has Wildcard/Var). Any other pattern variable
        // would be silently discarded and its uses would die `UnknownIdent`
        // far downstream. Descope loudly instead — full multi-column
        // dependent matching is a separate future brick.
        for pats in &peeled_arms {
            for (pos, pat) in pats.iter().enumerate() {
                if pos == match_pos {
                    continue;
                }
                let SurfacePattern::Var(name) = pat else {
                    continue;
                };
                let aliasable = pos < match_pos
                    && matches!(peeled_arms[0].get(pos), Some(SurfacePattern::Var(_)))
                    && peeled_arms.iter().all(|row| {
                        matches!(
                            row.get(pos),
                            Some(SurfacePattern::Wildcard) | Some(SurfacePattern::Var(_))
                        )
                    });
                if !aliasable {
                    return Err(ElabError::NotImplemented(format!(
                        "curried dependent match: pattern variable `{name}` at position \
                         {pos} is not bound by this lowering (descope)"
                    )));
                }
            }
        }

        // Push alias locals for variable patterns in positions before the match
        // position so arm bodies can reference them by name.
        let mut alias_fvars: Vec<Option<FVarId>> = Vec::new();
        for (pos, (_, ref local_ty, _, _)) in eta_locals[..match_pos].iter().enumerate() {
            if let Some(SurfacePattern::Var(name)) = peeled_arms[0].get(pos) {
                let all_agree = peeled_arms.iter().all(|pats| {
                    matches!(
                        pats.get(pos),
                        Some(SurfacePattern::Wildcard) | Some(SurfacePattern::Var(_))
                    )
                });
                if all_agree {
                    let fvar = self.push_local(name.clone(), local_ty.clone());
                    alias_fvars.push(Some(fvar));
                } else {
                    alias_fvars.push(None);
                }
            } else {
                alias_fvars.push(None);
            }
        }

        // Build inner match arms using only the sub-pattern at match_pos
        let (match_fvar, ref match_ty, _, _) = eta_locals[match_pos];
        let inner_arms: Vec<clean_parser::SurfaceMatchArm> = arms
            .iter()
            .zip(peeled_arms.iter())
            .map(|(arm, pats)| clean_parser::SurfaceMatchArm {
                span: arm.span,
                pattern: pats
                    .get(match_pos)
                    .cloned()
                    .unwrap_or(SurfacePattern::Wildcard),
                body: arm.body.clone(),
            })
            .collect();

        let match_result = self.elab_match_with_scrutinee(
            Expr::fvar(match_fvar),
            match_ty.clone(),
            None,
            &inner_arms,
        );

        // Pop alias locals in reverse order
        for alias in alias_fvars.iter().rev() {
            if alias.is_some() {
                self.pop_local();
            }
        }

        let mut result = match_result?;

        // Wrap alias variable bindings as let-expressions so the arm body
        // can reference the pattern variable name.
        for (pos, alias) in alias_fvars.iter().enumerate().rev() {
            if let Some(alias_fvar) = alias {
                let (eta_fvar, ref ty, _, _) = eta_locals[pos];
                result = Expr::let_named(
                    Name::anon(),
                    ty.clone(),
                    Expr::fvar(eta_fvar),
                    result.abstract_fvar(*alias_fvar),
                    false,
                );
            }
        }

        Ok(result)
    }

    pub(super) fn elab_pattern_lambda(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        if let Some(expr) = self.try_elab_curried_pattern_lambda(binders, body)? {
            return Ok(expr);
        }
        self.elab_lambda(binders, body)
    }
}
