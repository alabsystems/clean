// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! If-let expression elaboration.
//!
//! Elaborates `if let pat := scrutinee then then_br else else_br`
//! by desugaring to `casesOn` with constructor ordering.

use super::super::*;
use super::{
    desugar_nat_numeral_add_pattern, desugar_nonzero_nat_lit, ensure_ctor_pattern_arity,
    ensure_nat_pattern_scrutinee, ensure_supported_literal_pattern,
    normalize_nested_nat_numeral_add_pattern, redundant_alternative, NestedPatternFieldPlan,
    NestedPatternPlan,
};
use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo};

impl<'a> ElabCtx<'a> {
    fn is_available_shared_if_let_scrutinee_name(&self, candidate: &SurfaceName) -> bool {
        self.lookup_local(candidate).is_none()
            && !self
                .shared_if_let_scrutinees
                .iter()
                .any(|active| active == candidate)
            && self.env.get_const(candidate.name()).is_none()
    }

    pub(crate) fn fresh_shared_if_let_scrutinee_name(&self) -> SurfaceName {
        const BASE: &str = "__iflet_scrutinee";

        let base = SurfaceName::generated_path(BASE);
        if self.is_available_shared_if_let_scrutinee_name(&base) {
            return base;
        }

        let mut suffix = self.next_fvar;
        loop {
            let candidate = SurfaceName::from_name(Name::anon().str(format!("{BASE}_{suffix}")));
            if self.is_available_shared_if_let_scrutinee_name(&candidate) {
                return candidate;
            }
            suffix += 1;
        }
    }

    fn elab_if_let_with_shared_scrutinee<F>(
        &mut self,
        scrutinee_expr: Expr,
        scrutinee_ty: Expr,
        f: F,
    ) -> Result<Expr, ElabError>
    where
        F: FnOnce(&mut Self, SurfaceExpr) -> Result<Expr, ElabError>,
    {
        let locals_len = self.locals.len();
        let shared_len = self.shared_if_let_scrutinees.len();
        let synth_name = self.fresh_shared_if_let_scrutinee_name();
        self.shared_if_let_scrutinees.push(synth_name.clone());
        let fvar = self.push_local(synth_name.clone(), scrutinee_ty.clone());
        let synth_ident = SurfaceExpr::Ident(Span::dummy(), synth_name.clone());
        let nested_result = f(self, synth_ident);
        self.locals.truncate(locals_len);
        self.shared_if_let_scrutinees.truncate(shared_len);
        let nested_result = nested_result?;
        let nested_abs = nested_result.abstract_fvar(fvar);
        Ok(Expr::let_named(
            synth_name.name().clone(),
            scrutinee_ty,
            scrutinee_expr,
            nested_abs,
            false,
        ))
    }

    /// Elaborate an if-let expression.
    ///
    /// if let pat := scrutinee then then_br else else_br
    /// Desugars to: match scrutinee with | pat => then_br | _ => else_br
    pub(in crate::infer) fn elab_if_let(
        &mut self,
        pat: &SurfacePattern,
        scrutinee: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Non-linear patterns are refused here as in `match` (class N,
        // `check_pattern_linear`): `if let some (x, x) := p` kept one binding.
        self.check_pattern_linear(pat)?;
        self.with_temporary_local_scope(|this| {
            this.elab_if_let_inner(pat, scrutinee, then_br, else_br)
        })
    }

    fn elab_if_let_inner(
        &mut self,
        pat: &SurfacePattern,
        scrutinee: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let scrutinee_expr = self.elaborate(scrutinee)?;
        let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
        let normalized = self.normalize_match_pattern_names(pat, &scrutinee_ty)?;
        let pat = &normalized;
        // Lean's `if let p := e then t else f` is `match e with | p => t | _ =>
        // f`: an irrefutable `p` leaves the `_` alternative redundant, which
        // Lean refuses (G62, ledger (89); `catch_all_reach.rs`).
        if self.pattern_matches_every_value(pat) {
            return Err(redundant_alternative("the `if let`", 1));
        }

        match pat {
            SurfacePattern::Var(name) => {
                // Variable pattern always matches - bind scrutinee to name
                // if let x := e then t else f  ==  let x := e in t
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                let then_expr = self.elaborate(then_br)?;
                self.pop_local();
                let body_abs = then_expr.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    name.name().clone(),
                    scrutinee_ty,
                    scrutinee_expr,
                    body_abs,
                    false,
                ))
            }
            SurfacePattern::Wildcard => {
                // Wildcard always matches - evaluate scrutinee, return then
                // if let _ := e then t else f  ==  let _ := e in t
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                let then_expr = self.elaborate(then_br)?;
                // Create a let binding that ignores the value
                Ok(Expr::let_named(
                    Name::from_string("_"),
                    scrutinee_ty,
                    scrutinee_expr,
                    then_expr,
                    true,
                ))
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => {
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                let type_name = self.get_type_name(&scrutinee_ty)?;
                let normalized_sub_pats: Vec<SurfacePattern> = sub_pats
                    .iter()
                    .map(normalize_nested_nat_numeral_add_pattern)
                    .collect();

                // Resolve the full constructor name, consulting opened
                // namespaces just like top-level match patterns do.
                let full_ctor = self.ctor_pattern_full_name(ctor_name, &type_name);

                // Look up constructor info for field types
                let ctor_info = self
                    .env
                    .get_constructor(full_ctor.name())
                    .cloned()
                    .ok_or_else(|| ElabError::UnknownIdent(full_ctor.to_string()))?;
                ensure_ctor_pattern_arity(
                    "if-let pattern",
                    &full_ctor,
                    Some(ctor_info.num_fields as usize),
                    normalized_sub_pats.len(),
                )?;

                // The else branch is OUTSIDE the pattern scope: a pattern
                // variable that reuses an outer binder's name (`if let some n
                // := o then n * 2 else n`) must resolve to the OUTER binder in
                // the else branch, exactly as in a `match` wildcard arm.
                // Elaborate it BEFORE the pattern fvars are pushed, or the
                // shadowing pattern fvar would capture the name and leak an
                // out-of-scope FVar into the else branch (B100, fifth instance
                // of the name-shadowing lineage).
                let else_expr = self.elaborate(else_br)?;

                // Push locals for pattern variables BEFORE elaborating then_br,
                // so the body can reference them via FVars.
                let field_types = self.compute_ctor_field_types(full_ctor.name(), &scrutinee_ty)?;
                if field_types.len() != normalized_sub_pats.len() {
                    return Err(ElabError::InternalInvariant(format!(
                        "constructor metadata `{full_ctor}` exposes {} fields but the if-let pattern has {} slots",
                        field_types.len(),
                        normalized_sub_pats.len()
                    )));
                }
                let mut fvars: Vec<(FVarId, Expr)> = Vec::new();
                for (pat, field_ty) in normalized_sub_pats.iter().zip(field_types) {
                    // Open dependent field types against the fields already bound
                    // (see `open_field_type_with_fvars`).
                    let prior_fvars: Vec<FVarId> = fvars.iter().map(|(f, _)| *f).collect();
                    let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);

                    let var_name = match pat {
                        SurfacePattern::Var(n) => n.clone(),
                        _ => SurfaceName::generated_path("_"),
                    };
                    fvars.push((
                        self.push_local(var_name, field_ty.clone()),
                        field_ty.clone(),
                    ));
                }
                let nested_plans = self.collect_nested_field_plans(
                    "if-let pattern",
                    &normalized_sub_pats,
                    &fvars,
                )?;

                let then_expr = self.elaborate(then_br)?;
                let branch_ty = self.infer_type(&then_expr)?;

                let top_level_plan = NestedPatternPlan::CasesOn {
                    field_expr: scrutinee_expr.clone(),
                    field_ty: scrutinee_ty.clone(),
                    target_ctor_name: full_ctor,
                    target_fields: fvars
                        .iter()
                        .cloned()
                        .zip(nested_plans)
                        .map(|((fvar, ty), plan)| NestedPatternFieldPlan { fvar, ty, plan })
                        .collect(),
                };

                // The else branch is the fallback of EVERY nested level: bind
                // it once (see `apply_nested_plans_with_fallback`).
                self.apply_nested_plans_with_fallback(
                    std::slice::from_ref(&top_level_plan),
                    then_expr,
                    &branch_ty,
                    &else_expr,
                )
            }
            SurfacePattern::Lit(lit) => {
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                let type_name = self.get_type_name(&scrutinee_ty)?;
                ensure_supported_literal_pattern("if-let pattern", &type_name, lit)?;

                match lit {
                    SurfaceLit::Nat(0) => {
                        let then_expr = self.elaborate(then_br)?;
                        let else_expr = self.elaborate(else_br)?;
                        let branch_ty = self.infer_type(&then_expr)?;

                        // Build casesOn targeting Nat.zero for literal 0
                        let plan = NestedPatternPlan::CasesOn {
                            field_expr: scrutinee_expr,
                            field_ty: scrutinee_ty.clone(),
                            target_ctor_name: SurfaceName::generated_path("Nat.zero"),
                            target_fields: vec![],
                        };
                        self.apply_nested_pattern_plan(
                            then_expr,
                            &plan,
                            &branch_ty,
                            Some(&else_expr),
                        )
                    }
                    SurfaceLit::Nat(k) => {
                        // Non-zero Nat literal: desugar Nat(k) to nested Ctor
                        // pattern and use the Ctor infrastructure for the
                        // predecessor chain (#796).
                        let desugared_inner = desugar_nonzero_nat_lit(k - 1);
                        let fvar =
                            self.push_local(SurfaceName::generated_path("_"), scrutinee_ty.clone());
                        let inner_plan = self.bind_nested_pattern_plan(
                            "if-let pattern",
                            &desugared_inner,
                            Expr::fvar(fvar),
                            &scrutinee_ty,
                        )?;

                        let then_expr = self.elaborate(then_br)?;
                        let else_expr = self.elaborate(else_br)?;
                        let branch_ty = self.infer_type(&then_expr)?;

                        let plan = NestedPatternPlan::CasesOn {
                            field_expr: scrutinee_expr,
                            field_ty: scrutinee_ty.clone(),
                            target_ctor_name: SurfaceName::generated_path("Nat.succ"),
                            target_fields: vec![NestedPatternFieldPlan {
                                fvar,
                                ty: scrutinee_ty.clone(),
                                plan: inner_plan,
                            }],
                        };
                        // `k + 1` nested levels share the one else branch
                        // (see `apply_nested_plans_with_fallback`).
                        self.apply_nested_plans_with_fallback(
                            std::slice::from_ref(&plan),
                            then_expr,
                            &branch_ty,
                            &else_expr,
                        )
                    }
                    _ => Err(ElabError::NotImplemented(format!(
                        "if-let pattern: non-Nat literal {}",
                        crate::error_render::lit(lit)
                    ))),
                }
            }
            SurfacePattern::NumeralAdd(inner_pat, k) => {
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                let type_name = self.get_type_name(&scrutinee_ty)?;
                ensure_nat_pattern_scrutinee("if-let pattern", &type_name, "numeral-add")?;
                // Elaborate the else branch BEFORE the pattern plan pushes the
                // numeral-add binder, so `if let n+1 := o then … else n`
                // resolves the else-branch `n` to the OUTER binder (see the
                // Ctor arm's shadowing note).
                let else_expr = self.elaborate(else_br)?;
                let desugared = desugar_nat_numeral_add_pattern(inner_pat.as_ref(), *k);
                let plan = self.bind_nested_pattern_plan(
                    "if-let pattern",
                    &desugared,
                    scrutinee_expr.clone(),
                    &scrutinee_ty,
                )?;
                let then_expr = self.elaborate(then_br)?;
                let branch_ty = self.infer_type(&then_expr)?;
                self.apply_nested_plans_with_fallback(
                    std::slice::from_ref(&plan),
                    then_expr,
                    &branch_ty,
                    &else_expr,
                )
            }
            SurfacePattern::As(name, inner_pat) => {
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                self.elab_if_let_with_shared_scrutinee(
                    scrutinee_expr,
                    scrutinee_ty,
                    |ctx, synth_ident| {
                        let wrapped_then = SurfaceExpr::Let(
                            Span::dummy(),
                            SurfaceBinder::new_typed(
                                name.clone(),
                                None,
                                SurfaceBinderInfo::Explicit,
                            ),
                            Box::new(synth_ident.clone()),
                            Box::new(then_br.clone()),
                        );
                        ctx.elab_if_let(inner_pat.as_ref(), &synth_ident, &wrapped_then, else_br)
                    },
                )
            }
            SurfacePattern::Or(left, right) => {
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                self.elab_if_let_with_shared_scrutinee(
                    scrutinee_expr,
                    scrutinee_ty,
                    |ctx, synth_ident| {
                        let rhs_if = SurfaceExpr::IfLet(
                            Span::dummy(),
                            right.as_ref().clone(),
                            Box::new(synth_ident.clone()),
                            Box::new(then_br.clone()),
                            Box::new(else_br.clone()),
                        );
                        ctx.elab_if_let(left.as_ref(), &synth_ident, then_br, &rhs_if)
                    },
                )
            }
            _ => {
                // Remaining complex patterns need bespoke elaboration rules.
                Err(ElabError::NotImplemented(format!(
                    "if-let with complex pattern: {}",
                    crate::error_render::pattern(pat)
                )))
            }
        }
    }
}
