// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 4C: Control flow elaboration handlers for do-notation (#1818).
//!
//! Implements break/continue/return/reassign handlers and the transformer
//! unwrap chain. Split from elab_do.rs to stay under 500-line limit.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/BuiltinDo/

use super::elab_do::DoMonadInfo;
use super::*;
use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo};

impl<'a> ElabCtx<'a> {
    fn current_state_mut_var_info(&self) -> Vec<(String, FVarId, Expr)> {
        let mut vars: Vec<(String, FVarId, Expr)> = self
            .do_control_info
            .as_ref()
            .into_iter()
            .flat_map(|info| info.reassigns.iter())
            .filter_map(|name| {
                self.locals
                    .iter()
                    .rev()
                    .find(|(local_name, _, _)| local_name == name)
                    .map(|(local_name, fvar, ty)| (local_name.clone(), *fvar, ty.clone()))
            })
            .collect();
        vars.sort_by(|a, b| a.0.cmp(&b.0));
        vars
    }

    fn current_state_inner_monad(&self) -> Result<(Expr, Level, Level), ElabError> {
        let stack = self.do_control_stack.as_ref().ok_or_else(|| {
            ElabError::NotImplemented("mutable reassignment requires ControlStack".into())
        })?;
        let state_idx = stack.state_layer_idx.ok_or_else(|| {
            ElabError::NotImplemented(
                "mutable reassignment requires StateT layer in ControlStack".into(),
            )
        })?;
        let monad_info = self.do_monad_info.as_ref().ok_or_else(|| {
            ElabError::NotImplemented("mutable reassignment outside of do-block".into())
        })?;
        let inner_m = stack.compute_monad_at(state_idx.saturating_sub(1), monad_info);
        Ok((inner_m, monad_info.u.clone(), monad_info.v.clone()))
    }

    fn build_mut_var_state_value(
        &self,
        target_name: &str,
        target_value: &Expr,
        mut_var_info: &[(String, FVarId, Expr)],
    ) -> Result<Expr, ElabError> {
        match mut_var_info {
            [] => Ok(target_value.clone()),
            [(name, _, _)] if name == target_name => Ok(target_value.clone()),
            [_] => Ok(target_value.clone()),
            _ => {
                let vars: Vec<(String, Expr, Expr)> = mut_var_info
                    .iter()
                    .map(|(name, fvar, ty)| {
                        let value = if name == target_name {
                            target_value.clone()
                        } else {
                            Expr::fvar(*fvar)
                        };
                        (name.clone(), value, ty.clone())
                    })
                    .collect();
                elab_do_prod::build_sigma_value(self, &vars)
            }
        }
    }

    /// Elaborate `break` in a do-block.
    ///
    /// Two modes:
    /// 1. **Inside a for-loop** (DoLoopContext active): generate
    ///    `Pure.pure (ForInStep.done σ_value)` where σ_value is the current
    ///    accumulator. This directly terminates the loop iteration.
    ///    Reference: Lean 4 BuiltinDo/For.lean — break produces ForInStep.done.
    ///
    /// 2. **Inside a ControlStack** (BreakT layer active, e.g., break inside
    ///    tryCatch inside a loop): generate `OptionT.fail` at the break layer.
    ///    Reference: Lean 4 Control.lean — BreakT tunnels through tryCatch.
    pub(super) fn elab_do_break(&mut self) -> Result<Expr, ElabError> {
        // Mode 1: Direct ForInStep.done when inside a for-loop body.
        if let Some(loop_ctx) = &self.do_loop_ctx {
            let u = loop_ctx.u_level.clone();
            let sigma = loop_ctx.sigma.clone();
            let acc_value = self.build_loop_acc_value()?;
            // ForInStep.done : {β : Type u} → β → ForInStep β
            let done_const = Expr::const_(Name::from_string("ForInStep.done"), vec![u]);
            let done_val = Expr::app(Expr::app(done_const, sigma), acc_value);
            let result = self.mk_pure_app(done_val);
            return Ok(result);
        }

        // Mode 2: OptionT.fail at the ControlStack's break layer.
        let break_idx = self
            .do_control_stack
            .as_ref()
            .ok_or_else(|| {
                ElabError::NotImplemented(
                    "`break` outside of a loop or do-block with ControlStack".into(),
                )
            })?
            .break_layer_idx
            .ok_or_else(|| {
                ElabError::NotImplemented("`break` in do-block that has no break layer".into())
            })?;
        let u = self
            .do_monad_info
            .as_ref()
            .ok_or_else(|| ElabError::NotImplemented("`break` outside of do-block".into()))?
            .u
            .clone();

        let alpha = self.fresh_meta(Expr::sort(u));

        // Re-borrow after mutable fresh_meta call.
        // Invariant: both are Some — validated by ok_or_else above.
        let stack = self
            .do_control_stack
            .as_ref()
            .expect("invariant: do_control_stack validated above");
        let monad_info = self
            .do_monad_info
            .as_ref()
            .expect("invariant: do_monad_info validated above");
        Ok(stack.mk_option_t_fail(break_idx, alpha, monad_info))
    }

    /// Elaborate `continue` in a do-block.
    ///
    /// Two modes:
    /// 1. **Inside a for-loop** (DoLoopContext active): generate
    ///    `Pure.pure (ForInStep.yield σ_value)` where σ_value is the current
    ///    accumulator. This skips the rest of the body and moves to next iteration.
    ///    Reference: Lean 4 BuiltinDo/For.lean — continue produces ForInStep.yield.
    ///
    /// 2. **Inside a ControlStack** (ContinueT layer active): generate
    ///    `OptionT.fail` at the continue layer.
    pub(super) fn elab_do_continue(&mut self) -> Result<Expr, ElabError> {
        // Mode 1: Direct ForInStep.yield when inside a for-loop body.
        if let Some(loop_ctx) = &self.do_loop_ctx {
            let u = loop_ctx.u_level.clone();
            let sigma = loop_ctx.sigma.clone();
            let acc_value = self.build_loop_acc_value()?;
            // ForInStep.yield : {β : Type u} → β → ForInStep β
            let yield_const = Expr::const_(Name::from_string("ForInStep.yield"), vec![u]);
            let yield_val = Expr::app(Expr::app(yield_const, sigma), acc_value);
            let result = self.mk_pure_app(yield_val);
            return Ok(result);
        }

        // Mode 2: OptionT.fail at the ControlStack's continue layer.
        let continue_idx = self
            .do_control_stack
            .as_ref()
            .ok_or_else(|| {
                ElabError::NotImplemented(
                    "`continue` outside of a loop or do-block with ControlStack".into(),
                )
            })?
            .continue_layer_idx
            .ok_or_else(|| {
                ElabError::NotImplemented(
                    "`continue` in do-block that has no continue layer".into(),
                )
            })?;
        let u = self
            .do_monad_info
            .as_ref()
            .ok_or_else(|| ElabError::NotImplemented("`continue` outside of do-block".into()))?
            .u
            .clone();

        let alpha = self.fresh_meta(Expr::sort(u));

        let stack = self
            .do_control_stack
            .as_ref()
            .expect("invariant: do_control_stack validated above");
        let monad_info = self
            .do_monad_info
            .as_ref()
            .expect("invariant: do_monad_info validated above");
        Ok(stack.mk_option_t_fail(continue_idx, alpha, monad_info))
    }

    /// Elaborate non-terminal `return e` in a do-block.
    ///
    /// Two modes:
    /// 1. **Inside a for-loop** (DoLoopContext with return_type): generate
    ///    `Pure.pure (ForInStep.done (Option.some e, mutVars))` which tunnels
    ///    the return value through the loop accumulator.
    ///    Reference: Lean 4 BuiltinDo/For.lean:163-166 — returnCont wraps in done.
    ///
    /// 2. **ControlStack mode**: generate `ExceptT.throw` at the EarlyReturn layer.
    ///    Reference: Lean 4 BuiltinDo/Return.lean — `mkReturn` uses `ExceptT.throw`.
    pub(super) fn elab_do_early_return(&mut self, expr: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Every early-return payload is elaborated against the exact tunnel
        // type.  These applications are assembled by hand, so relying on a
        // later kernel pass would otherwise leave the tunnel metavariable
        // unassigned or report the mismatch far from the source return.
        let expected_return = self
            .do_loop_ctx
            .as_ref()
            .and_then(|ctx| ctx.return_type.clone())
            .or_else(|| {
                let stack = self.do_control_stack.as_ref()?;
                let idx = stack.return_layer_idx?;
                match &stack.layers[idx] {
                    elab_do_stack::ControlStackLayer::EarlyReturn { return_type } => {
                        Some(return_type.clone())
                    }
                    _ => None,
                }
            });
        let val = self.elaborate_with_expected_type(expr, expected_return.clone())?;
        if let Some(expected_return) = expected_return {
            self.enforce_expr_type(&val, &expected_return)?;
        }

        // Mode 1: ForInStep.done with Option.some when inside a for-loop.
        if let Some(loop_ctx) = &self.do_loop_ctx {
            if let Some(ref rho) = loop_ctx.return_type {
                let u = loop_ctx.u_level.clone();
                let sigma = loop_ctx.sigma.clone();
                let rho = rho.clone();
                let mut_vars = loop_ctx.mut_vars.clone();

                // Option.some.{u} : {α : Type u} → α → Option α
                let rho_level = elab_do_prod::type_universe(self, &rho)?;
                let some_const = Expr::const_(Name::from_string("Option.some"), vec![rho_level]);
                let some_val = Expr::app(Expr::app(some_const, rho.clone()), val);

                // Pack (Option.some e, mutVars...) into the accumulator.
                // The accumulator structure when return_type is Some is:
                // (Option ρ, mutVar1, mutVar2, ...) as a product tuple.
                let acc_value = self.build_loop_acc_with_return(some_val, &rho, &mut_vars)?;

                // ForInStep.done : {β : Type u} → β → ForInStep β
                let done_const = Expr::const_(Name::from_string("ForInStep.done"), vec![u]);
                let done_val = Expr::app(Expr::app(done_const, sigma), acc_value);
                return Ok(self.mk_pure_app(done_val));
            }
        }

        // Mode 2: ExceptT.throw at the ControlStack's EarlyReturn layer.
        let u = self
            .do_monad_info
            .as_ref()
            .ok_or_else(|| ElabError::NotImplemented("early return outside of do-block".into()))?
            .u
            .clone();

        let alpha = self.fresh_meta(Expr::sort(u));

        let stack = self
            .do_control_stack
            .as_ref()
            .ok_or_else(|| ElabError::NotImplemented("early return without ControlStack".into()))?;
        let monad_info = self
            .do_monad_info
            .as_ref()
            .expect("invariant: do_monad_info validated above");
        stack
            .mk_early_return(val, alpha, monad_info)
            .ok_or_else(|| {
                ElabError::NotImplemented(
                    "early return: no EarlyReturn layer in ControlStack".into(),
                )
            })
    }

    /// Elaborate `x := new_val` → `StateT.set` with updated state tuple.
    ///
    /// For a single mutable variable, this generates:
    /// `@StateT.set σ m new_val`
    ///
    /// For multiple mutable variables, the state is a product tuple and
    /// reassignment updates one component. This MVP handles the single-variable
    /// case; multi-variable product updates are deferred.
    ///
    /// Reference: Lean 4 BuiltinDo/Reassign.lean — generates `StateT.set`
    /// with the updated state value (or product projection update for multi-var).
    pub(super) fn elab_do_reassign(
        &mut self,
        name: &str,
        val: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let new_val = self.elaborate(val)?;
        let mut_var_info = self.current_state_mut_var_info();
        let target_ty = mut_var_info
            .iter()
            .find(|(mut_name, _, _)| mut_name == name)
            .map(|(_, _, ty)| ty.clone())
            .ok_or_else(|| {
                ElabError::NotImplemented(format!(
                    "mutable reassignment `{name} := ...` has no mutable locals in scope"
                ))
            })?;
        self.enforce_expr_type(&new_val, &target_ty)?;

        let sigma = elab_do_prod::build_sigma_type(
            self,
            &mut_var_info
                .iter()
                .map(|(mut_name, _, ty)| (mut_name.clone(), ty.clone()))
                .collect::<Vec<_>>(),
        )?;
        let new_state = self.build_mut_var_state_value(name, &new_val, &mut_var_info)?;
        let (inner_m, u, v) = self.current_state_inner_monad()?;

        // Generate: @StateT.set σ inner_m new_val
        // StateT.set : {σ : Type u} → {m : Type u → Type v} → σ → StateT σ m PUnit
        let set_const = Expr::const_(Name::from_string("StateT.set"), vec![u, v]);
        let e = Expr::app(set_const, sigma);
        let e = Expr::app(e, inner_m);
        Ok(Expr::app(e, new_state))
    }

    pub(super) fn elab_do_reassign_with_rest(
        &mut self,
        name: &str,
        val: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let reassign_expr = self.elab_do_reassign(name, val)?;
        let mut_var_info = self.current_state_mut_var_info();
        if mut_var_info.is_empty() {
            let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
            return self.elab_do_bind_expr(&binder, reassign_expr, rest);
        }

        let sigma = elab_do_prod::build_sigma_type(
            self,
            &mut_var_info
                .iter()
                .map(|(mut_name, _, ty)| (mut_name.clone(), ty.clone()))
                .collect::<Vec<_>>(),
        )?;
        let (inner_m, u, v) = self.current_state_inner_monad()?;
        let get_const = Expr::const_(Name::from_string("StateT.get"), vec![u, v]);
        let get_expr = Expr::app(Expr::app(get_const, sigma.clone()), inner_m);

        let state_fvar = self.push_local("__do_state".to_string(), sigma.clone());
        let shadow_vars = self.destructure_acc_from_expr(Expr::fvar(state_fvar), &mut_var_info)?;
        let mut rebound_rest = self.elab_do_elems(rest)?;
        // Fix #3419: Instantiate metas before abstracting FVars.
        rebound_rest = self.metas.instantiate(&rebound_rest);
        for (name, shadow_fvar, shadow_ty, proj_expr) in shadow_vars.iter().rev() {
            let abs = rebound_rest.abstract_fvar(*shadow_fvar);
            rebound_rest = Expr::let_named(
                Name::from_string(name),
                shadow_ty.clone(),
                proj_expr.clone(),
                abs,
                false,
            );
            self.pop_local();
        }
        let rebound_rest = rebound_rest.abstract_fvar(state_fvar);
        self.pop_local();
        let get_cont = Expr::lam(BinderInfo::Default, sigma, rebound_rest);
        let reassign_cont_body = self.mk_bind_app(get_expr, get_cont);

        let discard_ty = self.fresh_meta(Expr::type_());
        let discard_fvar = self.push_local("_".to_string(), discard_ty.clone());
        let reassign_cont_body = reassign_cont_body.abstract_fvar(discard_fvar);
        self.pop_local();
        let reassign_cont = Expr::lam(BinderInfo::Default, discard_ty, reassign_cont_body);

        Ok(self.mk_bind_app(reassign_expr, reassign_cont))
    }

    /// Apply the control transformer unwrapping chain after the do-block body.
    ///
    /// The do-block body was elaborated with the wrapped monad (e.g.,
    /// `ContinueT (BreakT (StateT σ (ExceptT ρ m)))` as the effective monad).
    /// After elaboration, each transformer layer must be peeled off to recover
    /// a value in the base monad `m`.
    ///
    /// Unwrapping order (outermost first, matching ControlStack build order reversed):
    /// 1. `ContinueT` → `OptionT.run` body
    /// 2. `BreakT` → `OptionT.run` body
    /// 3. `StateT σ` → rejected unless an authenticated initial state is
    ///    threaded by the caller (the current legacy stack cannot provide one)
    /// 4. `EarlyReturnT ρ` → `ExceptT.run` body
    ///
    /// Reference: Lean 4 Control.lean `ControlStack.restoreCont` and
    /// ControlLifter `ofCont` unwrapping at each layer.
    pub(super) fn apply_control_unwrap(
        &mut self,
        body: Expr,
        stack: &elab_do_stack::ControlStack,
        monad_info: &DoMonadInfo,
    ) -> Result<Expr, ElabError> {
        let mut result = body;

        for step in stack.unwrap_sequence(monad_info) {
            result = match step.kind {
                elab_do_stack::UnwrapKind::Continue | elab_do_stack::UnwrapKind::Break => {
                    // OptionT.run : {m} → {α} → OptionT m α → m (Option α)
                    let inner_m =
                        stack.compute_monad_at(step.layer_idx.saturating_sub(1), monad_info);
                    let alpha = self.fresh_meta(Expr::sort(monad_info.u.clone()));
                    // @OptionT.run inner_m α result
                    let e = Expr::app(step.run_const, inner_m);
                    let e = Expr::app(e, alpha);
                    Expr::app(e, result)
                }
                elab_do_stack::UnwrapKind::State { ref sigma } => {
                    return Err(ElabError::InternalInvariant(format!(
                        "StateT control unwrap reached without an authenticated initial state for {sigma:?}"
                    )));
                }
                elab_do_stack::UnwrapKind::EarlyReturn { ref return_type } => {
                    // ExceptT.run : {ε} → {m} → {α} → ExceptT ε m α → m (Except ε α)
                    let inner_m =
                        stack.compute_monad_at(step.layer_idx.saturating_sub(1), monad_info);
                    let alpha = self.fresh_meta(Expr::sort(monad_info.u.clone()));
                    // @ExceptT.run return_type inner_m α result
                    let e = Expr::app(step.run_const, return_type.clone());
                    let e = Expr::app(e, inner_m);
                    let e = Expr::app(e, alpha);
                    Expr::app(e, result)
                }
            };
        }

        Ok(result)
    }

    /// Desugar pattern reassignment `(a, b) := expr` into a let + individual reassigns.
    ///
    /// Produces: `let __reassign_tmp := expr; a := Prod.fst __reassign_tmp; b := Prod.snd __reassign_tmp; ...rest`
    ///
    /// For nested patterns like `(a, (b, c)) := expr`:
    /// `let __reassign_tmp := expr; a := Prod.fst __reassign_tmp; b := Prod.fst (Prod.snd __reassign_tmp); c := Prod.snd (Prod.snd __reassign_tmp); ...rest`
    ///
    /// Reference: Lean 4 `doReassignToCode` in `src/Lean/Elab/Do/Basic.lean`
    pub(super) fn desugar_pattern_reassign(
        &self,
        span: Span,
        pat: &SurfacePattern,
        val: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Vec<DoElem> {
        let tmp_name = "__reassign_tmp".to_string();
        let tmp_binder = SurfaceBinder::new(&tmp_name, None, SurfaceBinderInfo::Explicit);
        let tmp_ref = SurfaceExpr::Ident(span, tmp_name);

        let mut elems = Vec::new();
        elems.push(DoElem::Let(span, tmp_binder, Box::new(val.clone())));
        Self::emit_pattern_reassigns(span, pat, &tmp_ref, &mut elems);
        elems.extend_from_slice(rest);
        elems
    }

    /// Recursively emit `DoElem::Reassign` elements for each variable in a pattern,
    /// using `Prod.fst`/`Prod.snd` projections on the base expression.
    fn emit_pattern_reassigns(
        span: Span,
        pat: &SurfacePattern,
        base: &SurfaceExpr,
        out: &mut Vec<DoElem>,
    ) {
        match pat {
            SurfacePattern::Var(name) => {
                out.push(DoElem::Reassign(span, name.clone(), Box::new(base.clone())));
            }
            SurfacePattern::Ctor(ctor, args) if ctor == "Prod.mk" && args.len() == 2 => {
                let fst = SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, "Prod.fst".to_string())),
                    vec![SurfaceArg::positional(base.clone())],
                );
                let snd = SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, "Prod.snd".to_string())),
                    vec![SurfaceArg::positional(base.clone())],
                );
                Self::emit_pattern_reassigns(span, &args[0], &fst, out);
                Self::emit_pattern_reassigns(span, &args[1], &snd, out);
            }
            SurfacePattern::As(name, inner) => {
                out.push(DoElem::Reassign(span, name.clone(), Box::new(base.clone())));
                Self::emit_pattern_reassigns(span, inner, base, out);
            }
            SurfacePattern::NumeralAdd(inner, _) => {
                Self::emit_pattern_reassigns(span, inner, base, out);
            }
            SurfacePattern::Wildcard
            | SurfacePattern::Ellipsis
            | SurfacePattern::Inaccessible(_)
            | SurfacePattern::Lit(_)
            | SurfacePattern::Or(_, _)
            | SurfacePattern::QPattern(_) => {}
            SurfacePattern::Ctor(_, _) => {} // Non-Prod.mk ctors: no projection available
        }
    }

    // For-loop body handlers (build_loop_acc_value, wrap_with_for_loop_yield,
    // elab_do_reassign_in_loop, is_loop_mut_var, build_loop_acc_with_return,
    // maybe_yield_wrap) moved to elab_do_for_handlers.rs
}
