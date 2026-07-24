// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor arm elaboration, arm type checking, and pattern lambda wrapping.
//!
//! When using `T.rec` instead of `T.casesOn`, constructor arguments that are
//! of the inductive type require additional induction hypothesis (IH) lambdas.

use super::super::*;
use super::{
    ensure_ctor_pattern_arity, generalize_with_extra_params, wrap_with_extra_params,
    ExtraParamBinding,
};

impl<'a> ElabCtx<'a> {
    /// Elaborate a match arm for a recursor application (#381)
    ///
    /// When using `T.rec` instead of `T.casesOn`, constructor arguments that are
    /// of the inductive type require additional induction hypothesis (IH) lambdas.
    /// For example, `List.rec`'s cons case has signature:
    ///   `(head : A) → (tail : List A) → (ih : C tail) → C (head :: tail)`
    ///
    /// This method:
    /// 1. Determines which pattern variables are recursive (need IH)
    /// 2. Pushes locals for pattern variables and their IHs
    /// 3. Elaborates the body with IH substitution for recursive calls
    /// 4. Builds the appropriate lambda structure
    ///
    /// For List.rec's cons case, produces: `fun (head : A) (tail : List A) (ih : C tail) => body`.
    /// For constructors with multiple recursive fields, all field binders come first, followed
    /// by IH binders in the same left-to-right field order as the recursor minor premise.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn elaborate_rec_arm(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        body: &SurfaceExpr,
        scrutinee_ty: &Expr,
        result_ty: &Expr,
        arm_idx: usize,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Expr, ElabError> {
        self.elaborate_rec_arm_with_fallback(
            ctor_name,
            sub_pats,
            body,
            scrutinee_ty,
            result_ty,
            arm_idx,
            extra_param_info,
            None,
        )
    }

    /// Like [`Self::elaborate_rec_arm`], but for a constructor minor that several
    /// surface arms map to via *nested* sub-patterns (Track G3). `fallback_alt`,
    /// when `Some`, is the already-compiled minor body for the SAME recursor
    /// constructor produced by the *later* (lower-priority) arms — i.e. a value
    /// of the same `fun fields… ihs… => …` shape this arm produces. It fills the
    /// non-matching branches of each nested `casesOn` dispatch, so a chain like
    ///   `| .bool b :: rest => …  | _ :: rest => …`   (both `List.cons`)
    /// becomes ONE `List.rec` cons minor that dispatches on the head via
    /// `Value.casesOn`, using this arm's body for the `.bool` head and the
    /// fallback (the catch-all arm's minor) for every other head. The fallback is
    /// applied to this arm's field fvars so it sits at the right binder depth.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn elaborate_rec_arm_with_fallback(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        body: &SurfaceExpr,
        scrutinee_ty: &Expr,
        result_ty: &Expr,
        arm_idx: usize,
        extra_param_info: &[ExtraParamBinding],
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.elaborate_rec_arm_with_fallback_inner(
                ctor_name,
                sub_pats,
                body,
                scrutinee_ty,
                result_ty,
                arm_idx,
                extra_param_info,
                fallback_alt,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn elaborate_rec_arm_with_fallback_inner(
        &mut self,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
        body: &SurfaceExpr,
        scrutinee_ty: &Expr,
        result_ty: &Expr,
        arm_idx: usize,
        extra_param_info: &[ExtraParamBinding],
        fallback_alt: Option<&Expr>,
    ) -> Result<Expr, ElabError> {
        // Expand explicit-only field patterns to full field length (a wildcard at
        // each implicit field position, e.g. an indexed family's `{n : Nat}`
        // index witness) before the arity check and the field-binding loops, so
        // they walk one binder per `num_fields` position unchanged. Callers pass a
        // fully-qualified (dotted) constructor name; when the constructor is
        // unknown the helper returns the patterns unchanged. Idempotent: an
        // already-expanded list (len == num_fields) is returned as-is.
        let expanded_pats =
            self.expand_implicit_ctor_field_patterns("match arm pattern", ctor_name, sub_pats)?;
        let sub_pats: &[SurfacePattern] = &expanded_pats;

        // A sub-pattern that is neither a plain variable nor a wildcard is a
        // *nested* constructor (or literal/numeral-add) head — e.g. `.int w l ::
        // rest` over `List Value`, whose cons HEAD `.int w l` is itself a ctor
        // pattern. The recursor arm still has to bind every field, install the
        // induction hypothesis for each recursive field, AND dispatch the nested
        // sub-pattern. Previously such an arm fell straight back to a fabricated
        // fresh-meta lambda telescope, which NEVER installed the IH — so the self-call
        // on the recursive tail field stayed an unsolved placeholder fvar
        // ("Too many arguments … FVar(…) is not a function type" /
        // "contains free variables"). Instead, route through the same nested-plan
        // machinery the non-recursive `elaborate_ctor_arm` uses (Track G3): bind
        // fields + IHs in recursor-minor order, collect a nested `casesOn` plan
        // for each non-trivial sub-pattern, and wrap the IH-aware body in those
        // plans. The flag only changes behavior for nested sub-patterns; the
        // pure var/wildcard path below is byte-for-byte unchanged.
        let has_nested_sub_pats = sub_pats
            .iter()
            .any(|pat| !matches!(pat, SurfacePattern::Var(_) | SurfacePattern::Wildcard));

        let scrutinee_whnf = self.whnf(scrutinee_ty);
        let scrutinee_head = scrutinee_whnf.get_app_fn().clone();
        let scrutinee_args: Vec<Expr> =
            scrutinee_whnf.get_app_args().into_iter().cloned().collect();

        let (ind_name, scrutinee_levels) = match scrutinee_head.kind() {
            ExprKind::Const(name, levels) => (name.clone(), levels.to_vec()),
            _ => {
                return Err(ElabError::TypeMismatch {
                    expected: "fully-applied inductive scrutinee type for recursive match"
                        .to_string(),
                    actual: format!("{scrutinee_whnf:?}"),
                });
            }
        };

        let ind_info =
            self.env
                .get_inductive(&ind_name)
                .cloned()
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: "registered inductive scrutinee type for recursive match".to_string(),
                    actual: ind_name.to_string(),
                })?;
        if scrutinee_levels.len() != ind_info.level_params.len()
            || scrutinee_args.len()
                != (ind_info.num_params as usize + ind_info.num_indices as usize)
        {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} universe levels and {} type arguments for recursive scrutinee `{ind_name}`",
                    ind_info.level_params.len(),
                    ind_info.num_params + ind_info.num_indices
                ),
                actual: format!(
                    "{} universe levels and {} type arguments",
                    scrutinee_levels.len(),
                    scrutinee_args.len()
                ),
            });
        }

        let ctor_full_name = if ctor_name.contains('.') {
            Name::from_string(ctor_name)
        } else {
            ind_info
                .constructor_names
                .iter()
                .find(|name| {
                    name.to_string()
                        .rsplit('.')
                        .next()
                        .is_some_and(|short| short == ctor_name)
                })
                .cloned()
                .unwrap_or_else(|| Name::from_string(ctor_name))
        };

        let ctor_info_value = self
            .env
            .get_constructor(&ctor_full_name)
            .cloned()
            .ok_or_else(|| {
                ElabError::InternalInvariant(format!(
                    "recursive match arm references constructor `{ctor_full_name}` without constructor metadata"
                ))
            })?;
        if ctor_info_value.inductive_name != ind_name
            || !ind_info.constructor_names.contains(&ctor_full_name)
        {
            return Err(ElabError::TypeMismatch {
                expected: format!("constructor of recursive scrutinee `{ind_name}`"),
                actual: ctor_full_name.to_string(),
            });
        }
        if ctor_info_value.num_params != ind_info.num_params
            || ctor_info_value.level_params.len() != scrutinee_levels.len()
        {
            return Err(ElabError::InternalInvariant(format!(
                "constructor `{ctor_full_name}` metadata declares {} parameters and {} universe levels, but `{ind_name}` requires {} parameters and {} levels",
                ctor_info_value.num_params,
                ctor_info_value.level_params.len(),
                ind_info.num_params,
                scrutinee_levels.len()
            )));
        }
        ensure_ctor_pattern_arity(
            "match arm pattern",
            &ctor_full_name.to_string(),
            Some(ctor_info_value.num_fields as usize),
            sub_pats.len(),
        )?;

        let rec_name = Name::from_string(&format!("{ind_name}.rec"));
        let rec_info = self.env.get_recursor(&rec_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "recursive match lowering selected `{rec_name}` without recursor metadata"
            ))
        })?;
        let rule = rec_info
            .rules
            .iter()
            .find(|rule| rule.constructor_name == ctor_full_name)
            .ok_or_else(|| {
                ElabError::InternalInvariant(format!(
                    "recursor `{rec_name}` has no rule for constructor `{ctor_full_name}`"
                ))
            })?;
        let expected_fields = ctor_info_value.num_fields as usize;
        if rule.num_fields as usize != expected_fields
            || rule.recursive_fields.len() != expected_fields
        {
            return Err(ElabError::InternalInvariant(format!(
                "recursor `{rec_name}` rule for `{ctor_full_name}` has field metadata ({}, {} flags), expected {expected_fields}",
                rule.num_fields,
                rule.recursive_fields.len()
            )));
        }
        let recursive_fields = rule.recursive_fields.clone();
        let pats: Vec<SurfacePattern> = sub_pats.to_vec();

        // Track all binders (both pattern vars and IHs) in the order they appear.
        // Each entry is (fvar_id, type, is_ih, associated_var_name).
        // For IHs, associated_var_name is the pattern var this IH corresponds to.
        let mut all_binders: Vec<(FVarId, Expr, bool, Option<String>)> = Vec::new();
        let mut ih_map: HashMap<String, FVarId> = HashMap::new();
        let mut first_ih_fvar: Option<FVarId> = None;

        // Instantiate the constructor telescope exactly. Universe/parameter
        // mismatches are malformed evidence, not permission to use the
        // unsubstituted declaration or synthesize a placeholder type.
        let level_subst: Vec<(Name, Level)> = ctor_info_value
            .level_params
            .iter()
            .cloned()
            .zip(scrutinee_levels.iter().cloned())
            .collect();
        let mut ctor_ty = ctor_info_value.type_.instantiate_level_params(&level_subst);
        for (i, scrutinee_arg) in scrutinee_args[..ctor_info_value.num_params as usize]
            .iter()
            .enumerate()
        {
            let ExprKind::Pi(_, _, codomain) = ctor_ty.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor `{ctor_full_name}` telescope ends before parameter {i}"
                )));
            };
            ctor_ty = codomain.instantiate(scrutinee_arg);
        }

        // Push binders in the order expected by the recursor's minor premise type:
        // all fields first (f, a, ...), then all IHs in field order (ih_f, ih_a, ...).
        // This matches build_minor_premise_type in the kernel (#643).
        //
        // Phase 1: Push all fields
        let mut field_var_names: Vec<String> = Vec::new();
        // (fvar, field_ty) per field, in field order — reused below to collect
        // nested-constructor sub-pattern plans (Track G3) keyed by field.
        let mut field_fvar_tys: Vec<(FVarId, Expr)> = Vec::new();
        for (idx, pat) in pats.iter().enumerate() {
            let var_name = match pat {
                SurfacePattern::Var(name) => name.clone(),
                SurfacePattern::Wildcard => "_".to_string(),
                _ => "_".to_string(),
            };
            field_var_names.push(var_name.clone());

            let ExprKind::Pi(_, domain, codomain) = ctor_ty.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor `{ctor_full_name}` telescope ends before field {idx} of {}",
                    pats.len()
                )));
            };
            let field_ty = domain.as_ref().clone();
            let fvar = self.push_local(var_name.clone(), field_ty.clone());
            ctor_ty = codomain.instantiate(&Expr::fvar(fvar));
            field_fvar_tys.push((fvar, field_ty.clone()));
            all_binders.push((fvar, field_ty, false, Some(var_name)));
        }

        // The field telescope must end in this inductive family, with exactly
        // its parameter/index spine. Validate the invariant before elaborating
        // a body or installing induction hypotheses.
        let ctor_result = self.whnf(&ctor_ty);
        let ExprKind::Const(result_ind, result_levels) = ctor_result.get_app_fn().kind() else {
            return Err(ElabError::InternalInvariant(format!(
                "constructor `{ctor_full_name}` field telescope does not return an inductive application: {ctor_result:?}"
            )));
        };
        let result_args: Vec<Expr> = ctor_result.get_app_args().into_iter().cloned().collect();
        if result_ind != &ind_name
            || result_levels.len() != scrutinee_levels.len()
            || result_args.len() != (ind_info.num_params as usize + ind_info.num_indices as usize)
        {
            return Err(ElabError::InternalInvariant(format!(
                "constructor `{ctor_full_name}` returns malformed family application `{ctor_result:?}`"
            )));
        }
        for (actual, expected) in result_args
            .iter()
            .take(ind_info.num_params as usize)
            .zip(scrutinee_args.iter())
        {
            if !self.is_def_eq(actual, expected) {
                return Err(ElabError::TypeMismatch {
                    expected: format!("parameter `{expected:?}` of `{ind_name}`"),
                    actual: format!("{actual:?}"),
                });
            }
        }

        // Phase 2: Push IHs in field order to match the recursor minor premise:
        // all fields first, then IHs for recursive fields from left to right.
        let recursive_indices: Vec<usize> = recursive_fields
            .iter()
            .enumerate()
            .filter(|(_, &is_rec)| is_rec)
            .map(|(i, _)| i)
            .collect();
        for &idx in &recursive_indices {
            let var_name = field_var_names
                .get(idx)
                .cloned()
                .unwrap_or_else(|| "_".to_string());
            // Generalize IH type with extra params (#1386):
            // IH type becomes P1_ty → P2_ty → ... → result_ty
            // so IH can be applied with different param values.
            let ih_type = generalize_with_extra_params(result_ty.clone(), extra_param_info);
            let ih_fvar = self.push_local(format!("ih_{}", var_name), ih_type.clone());
            all_binders.push((ih_fvar, ih_type, true, Some(var_name.clone())));

            // Track in ih_map for recursive call replacement
            if var_name != "_" {
                ih_map.insert(var_name, ih_fvar);
            }
            if first_ih_fvar.is_none() {
                first_ih_fvar = Some(ih_fvar);
            }
        }

        // Save and set up IH context for recursive call replacement during body elaboration
        let saved_ctx = self.recursive_def_ctx.clone();
        if let Some(ref mut ctx) = self.recursive_def_ctx {
            ctx.ih_fvar = first_ih_fvar;
            ctx.ih_type = Some(result_ty.clone());
            ctx.ih_map = ih_map;
        }

        // Nested-constructor sub-pattern plans (Track G3). With fields + IHs now
        // bound (and the IH for each recursive field installed in `ih_map`),
        // collect a nested `casesOn` plan for every non-trivial sub-pattern — a
        // ctor head like `.int w l` or a literal/numeral-add. `Var`/`Wildcard`
        // sub-patterns yield `NestedPatternPlan::None` (no extra binders, no
        // dispatch), so when `has_nested_sub_pats` is false this is an empty
        // no-op and the pure var/wildcard term is byte-for-byte unchanged.
        // Collection pushes the nested sub-field locals ON TOP of the field/IH
        // binders; `apply_nested_field_plans` (below) pops them again before the
        // `all_binders` loop pops the fields and IHs.
        let nested_plans = if has_nested_sub_pats {
            self.collect_nested_field_plans("match arm pattern", &pats, &field_fvar_tys)?
        } else {
            Vec::new()
        };

        // Set expected type for body elaboration (#469)
        // Without this, Nat.rec inside the arm body cannot unify its result type
        // with the expected arm result type, causing discriminant mismatch errors.
        let saved_expected = self.current_expected_type.clone();
        self.set_expected_type(Some(result_ty.clone()));

        // Elaborate the body
        let arm_body = self.elaborate_with_expected_type(body, Some(result_ty.clone()))?;

        // Check arm body type against motive (#1726)
        if arm_idx > 0 {
            self.check_arm_type(&arm_body, result_ty, arm_idx)?;
        }

        // Wrap the IH-aware body in the nested `casesOn` dispatch for each
        // non-trivial sub-pattern. This pops the nested sub-field locals that
        // `collect_nested_field_plans` pushed, abstracting them into the inner
        // `casesOn` lambdas — leaving only the field/IH binders on the stack for
        // the `all_binders` loop. The nested `casesOn` scrutinizes the field
        // fvar (e.g. the cons HEAD), which the field loop abstracts afterwards.
        //
        // When a `fallback_alt` is supplied (several arms map to this recursor
        // constructor — Track G3 multi-arm dispatch), apply it to THIS arm's
        // field + IH fvars so it sits at the matching binder depth, and thread it
        // into every nested-casesOn's non-matching branches. Without one, a
        // partial nested pattern fails closed rather than fabricating a branch.
        let arm_body = if has_nested_sub_pats {
            match fallback_alt {
                Some(fallback) => {
                    // `fallback` is a sibling minor `fun fields… ihs… => (P1 → …
                    // → result_ty)`: saturate it with this arm's field+IH fvars
                    // (same left-to-right order as `all_binders`), then with the
                    // varying extra-param fvars (#1386), to recover a plain
                    // `result_ty`-typed body for the nested-`casesOn` branches.
                    // The extra params are still in scope as locals here (the
                    // nested-plan application runs before the body's own
                    // `wrap_with_extra_params`), so applying their fvars is
                    // well-scoped and re-abstracted by `wrap_with_extra_params`
                    // below in lock-step with this arm's body.
                    let fallback_body = all_binders
                        .iter()
                        .fold(fallback.clone(), |acc, (fvar, _, _, _)| {
                            Expr::app(acc, Expr::fvar(*fvar))
                        });
                    let fallback_body = extra_param_info
                        .iter()
                        .fold(fallback_body, |acc, (fvar, _, _)| {
                            Expr::app(acc, Expr::fvar(*fvar))
                        });
                    let mut result = arm_body;
                    for plan in nested_plans.iter().rev() {
                        result = self.apply_nested_pattern_plan(
                            result,
                            plan,
                            result_ty,
                            Some(&fallback_body),
                        )?;
                    }
                    result
                }
                None => self.apply_nested_field_plans(&nested_plans, arm_body, result_ty)?,
            }
        } else {
            arm_body
        };

        // Restore expected type and IH context
        self.set_expected_type(saved_expected);
        self.recursive_def_ctx = saved_ctx;

        // Pop all locals (in reverse order)
        for _ in &all_binders {
            self.pop_local();
        }

        // Wrap body with extra param lambdas BEFORE field/IH abstraction (#1386).
        // This converts body from type ResultType to P1 → P2 → ... → ResultType.
        let arm_body = wrap_with_extra_params(arm_body, extra_param_info);

        // Build the lambda structure by abstracting in reverse order.
        // This produces: fun (field1) (field2) ... (ih1) (ih2) ... => body
        let mut result = arm_body;
        for (fvar, fvar_ty, _is_ih, _) in all_binders.iter().rev() {
            result = result.abstract_fvar(*fvar);
            result = Expr::lam(BinderInfo::Default, fvar_ty.clone(), result);
        }

        let _ = scrutinee_ty; // Will be used for type checking in full impl
        Ok(result)
    }

    /// Check that a match arm body type is definitionally equal to the expected
    /// branch type (motive). Returns an error if the types diverge (#1726).
    ///
    /// Called for arms after the first (arm_idx > 0), since the first arm
    /// *defines* the motive. The check uses `is_def_eq` to compare the
    /// instantiated arm type with the motive under kernel definitional
    /// equality; metavariable assignments happen during expected-type
    /// elaboration before this check.
    pub(in crate::infer) fn check_arm_type(
        &mut self,
        arm_body: &Expr,
        expected_ty: &Expr,
        arm_idx: usize,
    ) -> Result<(), ElabError> {
        let actual_ty = self.infer_type(arm_body)?;
        if !self.is_def_eq(&actual_ty, expected_ty) {
            return Err(ElabError::MatchArmTypeMismatch {
                arm_index: arm_idx,
                expected: format!("{expected_ty:?}"),
                actual: format!("{actual_ty:?}"),
            });
        }
        Ok(())
    }
}
