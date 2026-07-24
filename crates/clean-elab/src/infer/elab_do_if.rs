// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! If/if-let/if-decidable elaboration for do-notation.
//!
//! Extracted from elab_do.rs to maintain the 500-line file limit.
//!
//! - `elab_do_if`: Desugars `if cond then doSeq else doSeq` to `ite`.
//! - `elab_do_if_let`: Desugars `if let pat := scrutinee then doSeq else doSeq`.
//! - `elab_do_if_decidable`: Desugars `if h : prop then doSeq else doSeq` to `dite`.

use super::*;
use clean_parser::{DoElem, DoMatchArm, Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

impl<'a> ElabCtx<'a> {
    /// Elaborate a branch body that may need to preserve an enclosing
    /// do-block's early-return continuation.
    pub(super) fn elab_do_body_with_outer_continuation(
        &mut self,
        body: &[DoElem],
    ) -> Result<Expr, ElabError> {
        match body {
            [DoElem::Return(_, expr)] => {
                if self.do_loop_ctx.is_some() {
                    return self.elab_do_early_return(expr);
                }
                if self
                    .do_control_stack
                    .as_ref()
                    .and_then(|stack| stack.return_layer_idx)
                    .is_some()
                {
                    return self.elab_do_early_return(expr);
                }
                self.elab_pure(expr)
            }
            _ => self.elab_do_elems(body),
        }
    }

    fn default_do_else_branch() -> Vec<DoElem> {
        vec![DoElem::Return(
            Span::dummy(),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
        )]
    }

    fn owned_do_else_branch(else_branch: Option<&[DoElem]>) -> Vec<DoElem> {
        else_branch.map_or_else(Self::default_do_else_branch, ToOwned::to_owned)
    }

    fn with_shared_do_if_let_scrutinee<F>(
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
        // Fix #3419: Instantiate metas before abstracting FVars.
        let nested_inst = self.metas.instantiate(&nested_result);
        let nested_abs = nested_inst.abstract_fvar(fvar);
        Ok(Expr::let_named(
            Name::from_string(&synth_name),
            scrutinee_ty,
            scrutinee_expr,
            nested_abs,
            false,
        ))
    }

    /// Desugar `if cond then do_seq else do_seq` in a do block.
    ///
    /// Each branch is desugared as an independent do-element sequence, then
    /// wrapped in an `ite` (if-then-else) expression.
    ///
    /// Lean 4 signature: `@ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α`
    /// Requires 1 universe level and 5 arguments: α, c, h, t, e.
    pub(super) fn elab_do_if(
        &mut self,
        cond: &SurfaceExpr,
        then_branch: &[DoElem],
        else_branch: Option<&[DoElem]>,
    ) -> Result<Expr, ElabError> {
        // The condition's expected type is `Bool`/`Prop`, never the branches'
        // monadic result type — clear `current_expected_type` while elaborating
        // it so the branches keep theirs (mirrors `elab_if`, Track KL).
        let cond_expr = self.elaborate_with_expected_type(cond, None)?;

        // `Unit` value type and `m Unit` action type for the no-else case.
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let unit_action_ty = self
            .do_monad_info
            .as_ref()
            .map(|info| Expr::app(info.m.clone(), unit_ty.clone()));

        // Elaborate the branches. With an explicit else both branches share the
        // do-block's expected type. With NO else the `if` is in statement
        // position: its synthesized else is `pure () : m Unit`, so the whole `if`
        // — hence the then-branch — has type `m Unit`. Elaborate the then-branch
        // against `m Unit` so a polymorphic action (`Sem.throwUB : m α`) resolves
        // `α := Unit` instead of leaving an unsolved metavar / a wrong `α`
        // (Track QR: memory-op `if addr == 0 then throwUB …` statements).
        let (then_expr, else_expr) = if let Some(else_elems) = else_branch {
            let t = self.elab_do_body_with_outer_continuation(then_branch)?;
            let e = self.elab_do_body_with_outer_continuation(else_elems)?;
            (t, e)
        } else {
            let saved = self.current_expected_type.take();
            self.current_expected_type = unit_action_ty.clone();
            let t = self.elab_do_body_with_outer_continuation(then_branch);
            self.current_expected_type = saved;
            let t = t?;
            // No else branch: `@Pure.pure m Unit ()`. Pin the value type to `Unit`
            // explicitly (not the do-block's result `α`, which need not be `Unit`).
            let unit_val = Expr::const_(Name::from_string("Unit.unit"), vec![]);
            let e = self.mk_pure_app_at(unit_ty.clone(), unit_val);
            (t, e)
        };

        // Recover the concrete result type `α = m β`. A fresh metavar — the
        // historical behaviour — is never solved here (nothing downstream
        // constrains it), leaving `α`/the `Decidable` instance as free variables
        // in the kernel term: the pre-existing do-`if` free-variable rejection
        // that gates Track QR's memory-op decls once `let x ← match` extraction is
        // fixed. Instantiate metas/levels so the type is concrete; for the no-else
        // case prefer `m Unit` directly.
        let result_ty = if else_branch.is_none() {
            match unit_action_ty.clone() {
                Some(unit_action_ty) => unit_action_ty,
                None => self.infer_type(&then_expr)?,
            }
        } else {
            self.infer_type(&then_expr)?
        };
        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        let level = self.infer_sort(&result_ty)?;

        // A `Bool` condition takes the Lean-faithful Bool→Prop lane
        // (`ite (c = true)` with the synthesized `Decidable` instance;
        // `Bool.rec` only when the environment has no such instance) — see
        // `mk_bool_if`. Mirrors the non-do `elab_if`.
        let cond_is_bool = self.condition_is_bool(&cond_expr)?;
        if cond_is_bool {
            return Ok(self.mk_bool_if(&level, &result_ty, cond_expr, then_expr, else_expr));
        }

        // Genuine `Prop` condition: `@ite.{u} α cond inst then else` with the
        // `Decidable` instance resolved by instance synthesis. A missing
        // instance is a typed elaboration error; proof authority is never
        // manufactured for an unreachable-looking branch.
        let ite_const = Expr::const_(Name::from_string("ite"), vec![level]);
        let inst = self.resolve_decidable(&cond_expr)?;
        Ok(Expr::apps(
            ite_const,
            [result_ty, cond_expr, inst, then_expr, else_expr],
        ))
    }

    /// Desugar `if let pat := scrutinee then doSeq else doSeq` in a do block.
    ///
    /// Elaborates the scrutinee, then desugars as a pattern match:
    /// - Variable/wildcard patterns always match (bind scrutinee, elaborate then-branch)
    /// - Constructor patterns produce casesOn with the pattern arm and else fallback
    ///
    /// Each branch is desugared as an independent do-element sequence.
    pub(super) fn elab_do_if_let(
        &mut self,
        pat: &SurfacePattern,
        scrutinee: &SurfaceExpr,
        then_branch: &[DoElem],
        else_branch: Option<&[DoElem]>,
    ) -> Result<Expr, ElabError> {
        match pat {
            // Keep the scrutinee in surface form here so do-match performs the
            // single elaboration and casesOn construction itself.
            SurfacePattern::Ctor(..) | SurfacePattern::Lit(..) | SurfacePattern::NumeralAdd(..) => {
                let else_body = Self::owned_do_else_branch(else_branch);
                let arms = vec![
                    DoMatchArm {
                        span: Span::dummy(),
                        patterns: vec![pat.clone()],
                        body: then_branch.to_vec(),
                    },
                    DoMatchArm {
                        span: Span::dummy(),
                        patterns: vec![SurfacePattern::Wildcard],
                        body: else_body,
                    },
                ];
                self.elab_do_match(std::slice::from_ref(scrutinee), &arms)
            }
            SurfacePattern::Var(name) => {
                let scrutinee_expr = self.elaborate(scrutinee)?;
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                // Variable pattern always matches — bind scrutinee to name
                let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                let then_expr = self.elab_do_body_with_outer_continuation(then_branch)?;
                self.pop_local();
                // Fix #3419: Instantiate metas before abstracting FVars.
                let then_inst = self.metas.instantiate(&then_expr);
                let body_abs = then_inst.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    Name::from_string(name),
                    scrutinee_ty,
                    scrutinee_expr,
                    body_abs,
                    false,
                ))
            }
            SurfacePattern::Wildcard | SurfacePattern::Inaccessible(_) => {
                let scrutinee_expr = self.elaborate(scrutinee)?;
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                // Wildcard always matches — evaluate scrutinee, return then branch
                let then_expr = self.elab_do_body_with_outer_continuation(then_branch)?;
                Ok(Expr::let_named(
                    Name::from_string("_"),
                    scrutinee_ty,
                    scrutinee_expr,
                    then_expr,
                    true,
                ))
            }
            SurfacePattern::As(name, inner_pat) => {
                let scrutinee_expr = self.elaborate(scrutinee)?;
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                self.with_shared_do_if_let_scrutinee(
                    scrutinee_expr,
                    scrutinee_ty,
                    |ctx, synth_ident| {
                        let mut wrapped_then = vec![DoElem::Let(
                            Span::dummy(),
                            SurfaceBinder::new(name.clone(), None, SurfaceBinderInfo::Explicit),
                            Box::new(synth_ident.clone()),
                        )];
                        wrapped_then.extend(then_branch.iter().cloned());
                        let owned_else = Self::owned_do_else_branch(else_branch);
                        ctx.elab_do_if_let(
                            inner_pat.as_ref(),
                            &synth_ident,
                            &wrapped_then,
                            Some(owned_else.as_slice()),
                        )
                    },
                )
            }
            SurfacePattern::Or(left, right) => {
                let scrutinee_expr = self.elaborate(scrutinee)?;
                let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
                self.with_shared_do_if_let_scrutinee(
                    scrutinee_expr,
                    scrutinee_ty,
                    |ctx, synth_ident| {
                        let owned_else = Self::owned_do_else_branch(else_branch);
                        let rhs_if = DoElem::IfLet(
                            Span::dummy(),
                            right.as_ref().clone(),
                            Box::new(synth_ident.clone()),
                            then_branch.to_vec(),
                            Some(owned_else.clone()),
                        );
                        let nested_else = vec![rhs_if];
                        ctx.elab_do_if_let(
                            left.as_ref(),
                            &synth_ident,
                            then_branch,
                            Some(nested_else.as_slice()),
                        )
                    },
                )
            }
            _ => Err(ElabError::NotImplemented(format!(
                "if-let with complex pattern: {pat:?}"
            ))),
        }
    }

    /// Desugar `if h : prop then doSeq else doSeq` in a do block.
    ///
    /// Desugars to: `dite prop (fun h : prop => thenBranch) (fun h : ¬prop => elseBranch)`
    ///
    /// Each branch is desugared as an independent do-element sequence, with the
    /// proof witness `h` bound as a local variable in scope.
    pub(super) fn elab_do_if_decidable(
        &mut self,
        witness_name: &str,
        prop: &SurfaceExpr,
        then_branch: &[DoElem],
        else_branch: Option<&[DoElem]>,
    ) -> Result<Expr, ElabError> {
        let prop_expr = self.elaborate(prop)?;

        // Then branch: (fun h : prop => thenBranch)
        let then_fvar = self.push_local(witness_name.to_string(), prop_expr.clone());
        let then_expr = self.elab_do_body_with_outer_continuation(then_branch)?;
        self.pop_local();
        // Fix #3419: Instantiate metas before abstracting FVars.
        let then_inst = self.metas.instantiate(&then_expr);
        let then_lambda = Expr::lam(
            BinderInfo::Default,
            prop_expr.clone(),
            then_inst.abstract_fvar(then_fvar),
        );

        // Else branch: (fun h : ¬prop => elseBranch)
        // ¬p = p → False
        let not_prop = Expr::pi(
            BinderInfo::Default,
            prop_expr.clone(),
            Expr::const_(Name::from_string("False"), vec![]),
        );
        let else_fvar = self.push_local(witness_name.to_string(), not_prop.clone());
        let else_expr = if let Some(else_elems) = else_branch {
            self.elab_do_body_with_outer_continuation(else_elems)?
        } else {
            let unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
            self.mk_pure_app(unit)
        };
        self.pop_local();
        // Fix #3419: Instantiate metas before abstracting FVars.
        let else_inst = self.metas.instantiate(&else_expr);
        let else_lambda = Expr::lam(
            BinderInfo::Default,
            not_prop,
            else_inst.abstract_fvar(else_fvar),
        );

        // Build: dite prop then_lambda else_lambda
        let dite = self.mk_const_str("dite");
        Ok(Expr::app(
            Expr::app(Expr::app(dite, prop_expr), then_lambda),
            else_lambda,
        ))
    }
}
