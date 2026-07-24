// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! For-loop body control flow handlers for do-notation (#1818).
//!
//! Inside a for-loop body, break/continue/return/reassign use different
//! mechanisms than the ControlStack path:
//! - break → `ForInStep.done` (not `OptionT.fail`)
//! - continue → `ForInStep.yield` (not `OptionT.fail`)
//! - return → `ForInStep.done (Option.some e, mutVars)`
//! - reassign → let-shadowing (not `StateT.set`)
//! - fall-through → `expr >>= fun _ => pure (ForInStep.yield acc)`
//!
//! Split from elab_do_handlers.rs to stay under 500-line limit.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/BuiltinDo/For.lean

use super::*;
use clean_kernel::{BinderInfo, Expr, FVarId, Level, Name};

impl<'a> ElabCtx<'a> {
    /// Build the accumulator value for break/continue inside a for-loop.
    ///
    /// When the DoLoopContext has `return_type`, prepends `Option.none ρ` to
    /// the accumulator (break/continue don't carry a return value).
    /// When the DoLoopContext has mutable variables, packs their current values.
    /// Otherwise returns the raw accumulator fvar reference.
    ///
    /// Panics if called without an active DoLoopContext.
    pub(super) fn build_loop_acc_value(&self) -> Result<Expr, ElabError> {
        let loop_ctx = self
            .do_loop_ctx
            .as_ref()
            .expect("build_loop_acc_value requires active DoLoopContext");

        // Build the mutable variable portion of the accumulator.
        let mut_value = if loop_ctx.mut_vars.is_empty() {
            None
        } else {
            let vars: Vec<(String, Expr, Expr)> = loop_ctx
                .mut_vars
                .iter()
                .map(|(name, fvar, ty)| (name.clone(), Expr::fvar(*fvar), ty.clone()))
                .collect();
            Some(elab_do_prod::build_sigma_value(self, &vars)?)
        };

        // If return_type is set, prepend Option.none to the accumulator.
        if let Some(ref rho) = loop_ctx.return_type {
            let rho_level = elab_do_prod::type_universe(self, rho)?;
            // Option.none.{u} : {α : Type u} → Option α
            let none_const = Expr::const_(Name::from_string("Option.none"), vec![rho_level]);
            let none_val = Expr::app(none_const, rho.clone());

            return self.build_loop_acc_with_return(none_val, rho, &loop_ctx.mut_vars.clone());
        }

        Ok(mut_value.unwrap_or_else(|| Expr::fvar(loop_ctx.acc_fvar)))
    }

    /// Wrap a monadic expression with ForInStep.yield for the for-loop fall-through.
    ///
    /// Generates: `expr >>= fun _ => pure (ForInStep.yield acc_value)`
    ///
    /// Called at terminal positions in the for-loop body for expressions that
    /// don't produce ForInStep themselves (break/continue/return already do).
    /// This inlines the yield into each fall-through path, fixing the bug where
    /// a separate post-body `bind yield` would overwrite break/continue results.
    ///
    /// Panics if called without an active DoLoopContext.
    pub(super) fn wrap_with_for_loop_yield(&mut self, expr: Expr) -> Result<Expr, ElabError> {
        let (u, sigma) = {
            let loop_ctx = self
                .do_loop_ctx
                .as_ref()
                .expect("wrap_with_for_loop_yield requires active DoLoopContext");
            (loop_ctx.u_level.clone(), loop_ctx.sigma.clone())
        };

        let acc_value = self.build_loop_acc_value()?;

        // ForInStep.yield : {β : Type u} → β → ForInStep β
        let yield_const = Expr::const_(Name::from_string("ForInStep.yield"), vec![u]);
        let yield_expr = Expr::app(Expr::app(yield_const, sigma), acc_value);
        let yield_pure = self.mk_pure_app(yield_expr);

        // expr >>= fun _ => pure (ForInStep.yield acc_value). The discard
        // binder's domain is the exact inner type authenticated by `expr : m
        // α`; a fresh hole here can survive because this application is assembled
        // by hand rather than passing through ordinary application elaboration.
        let discard_ty =
            self.try_extract_bind_inner_type(&expr)
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: "for-loop body action of type `m α`".into(),
                    actual: self
                        .infer_type(&expr)
                        .map(|ty| format!("{:?}", self.metas.instantiate(&ty)))
                        .unwrap_or_else(|err| format!("untypable body ({err})")),
                })?;
        let fvar_discard = self.push_local("_".to_string(), discard_ty.clone());
        let yield_abs = yield_pure.abstract_fvar(fvar_discard);
        self.pop_local();
        let yield_cont = Expr::lam(BinderInfo::Default, discard_ty, yield_abs);

        Ok(self.mk_bind_app(expr, yield_cont))
    }

    /// Conditionally wrap a result with ForInStep.yield when inside a for-loop.
    ///
    /// Compact helper for the common pattern in elab_do_elems terminal dispatch:
    /// inside a for-loop body, terminal expressions need yield wrapping;
    /// outside, they pass through unchanged.
    pub(super) fn maybe_yield_wrap(&mut self, result: Expr) -> Result<Expr, ElabError> {
        if self.do_loop_ctx.is_some() {
            self.wrap_with_for_loop_yield(result)
        } else {
            Ok(result)
        }
    }

    /// Elaborate `x := new_val` inside a for-loop body using let-shadowing.
    ///
    /// Inside a for-loop, mutable variable reassignment doesn't use StateT.set.
    /// Instead, the variable is let-rebound and the DoLoopContext is updated so
    /// that subsequent break/continue/yield picks up the new value.
    ///
    /// For terminal (rest is empty): produces
    ///   `let name := new_val in pure (ForInStep.yield acc_with_new_val)`
    /// For compound (rest is non-empty): produces
    ///   `let name := new_val in elab_do_elems(rest)`
    ///   where rest's terminals will produce ForInStep via the for-loop dispatch.
    ///
    /// Reference: Lean 4 BuiltinDo/For.lean — reassign inside loop body
    /// uses local rebinding, NOT StateT.set.
    pub(super) fn elab_do_reassign_in_loop(
        &mut self,
        name: &str,
        val: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        // Find the type of the mutable variable from the loop context.
        let var_ty = self
            .do_loop_ctx
            .as_ref()
            .and_then(|ctx| ctx.mut_vars.iter().find(|(n, _, _)| n == name))
            .map(|(_, _, ty)| ty.clone())
            .ok_or_else(|| {
                ElabError::NotImplemented(format!(
                    "reassignment `{name} := ...` inside for-loop: variable not in DoLoopContext"
                ))
            })?;
        let new_val = self.elaborate_with_expected_type(val, Some(var_ty.clone()))?;
        self.enforce_expr_type(&new_val, &var_ty)?;

        // Push a shadow local: let name := new_val
        let shadow_fvar = self.push_local(name.to_string(), var_ty.clone());

        // Save old fvar and update the DoLoopContext so that subsequent
        // break/continue/yield uses the new value.
        let old_fvar = self
            .do_loop_ctx
            .as_ref()
            .and_then(|ctx| ctx.mut_vars.iter().find(|(n, _, _)| n == name))
            .map(|(_, fvar, _)| *fvar);
        if let Some(ref mut ctx) = self.do_loop_ctx {
            for (n, fvar, _) in ctx.mut_vars.iter_mut() {
                if n == name {
                    *fvar = shadow_fvar;
                    break;
                }
            }
        }

        // Elaborate the continuation.
        let body = if rest.is_empty() {
            // Terminal reassign: produce ForInStep.yield with updated acc.
            let (u, sigma) = {
                let loop_ctx = self
                    .do_loop_ctx
                    .as_ref()
                    .expect("invariant: do_loop_ctx is active");
                (loop_ctx.u_level.clone(), loop_ctx.sigma.clone())
            };
            let acc_value = self.build_loop_acc_value()?;
            let yield_const = Expr::const_(Name::from_string("ForInStep.yield"), vec![u]);
            let yield_expr = Expr::app(Expr::app(yield_const, sigma), acc_value);
            self.mk_pure_app(yield_expr)
        } else {
            self.elab_do_elems(rest)?
        };

        // Restore old fvar in DoLoopContext (scoped to this let-binding).
        if let Some(old) = old_fvar {
            if let Some(ref mut ctx) = self.do_loop_ctx {
                for (n, fvar, _) in ctx.mut_vars.iter_mut() {
                    if n == name {
                        *fvar = old;
                        break;
                    }
                }
            }
        }

        // Fix #3419: Instantiate metas before abstracting FVars.
        let body_inst = self.metas.instantiate(&body);
        // Abstract over the shadow local and wrap in let.
        let abs = body_inst.abstract_fvar(shadow_fvar);
        self.pop_local();

        Ok(Expr::let_named(
            Name::from_string(name),
            var_ty,
            new_val,
            abs,
            false,
        ))
    }

    /// Check if a variable name is in the current DoLoopContext's mutable variables.
    pub(super) fn is_loop_mut_var(&self, name: &str) -> bool {
        self.do_loop_ctx
            .as_ref()
            .map(|ctx| ctx.mut_vars.iter().any(|(n, _, _)| n == name))
            .unwrap_or(false)
    }

    /// Build accumulator value with a return component (Some/None) prepended.
    ///
    /// The accumulator structure when return_type is active:
    /// - No mut vars: just the return value (Option ρ)
    /// - With mut vars: `Prod.mk (Option ρ) mutVarsProduct`
    ///
    /// `return_component` is either `Option.some e` or `Option.none`.
    pub(super) fn build_loop_acc_with_return(
        &self,
        return_component: Expr,
        rho: &Expr,
        mut_vars: &[(String, FVarId, Expr)],
    ) -> Result<Expr, ElabError> {
        if mut_vars.is_empty() {
            // No mut vars: accumulator IS the Option ρ value.
            return Ok(return_component);
        }

        // Build the mutable variable product value.
        let mut_var_vals: Vec<(String, Expr, Expr)> = mut_vars
            .iter()
            .map(|(name, fvar, ty)| (name.clone(), Expr::fvar(*fvar), ty.clone()))
            .collect();
        let mut_value = elab_do_prod::build_sigma_value(self, &mut_var_vals)?;

        // Build the mutable variable product type.
        let mut_var_types: Vec<(String, Expr)> = mut_vars
            .iter()
            .map(|(name, _, ty)| (name.clone(), ty.clone()))
            .collect();
        let mut_sigma = elab_do_prod::build_sigma_type(self, &mut_var_types)?;

        // Option ρ type
        let rho_level = elab_do_prod::type_universe(self, rho)?;
        let option_ty = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![rho_level]),
            rho.clone(),
        );

        elab_do_prod::build_prod_value(self, &option_ty, &mut_sigma, return_component, mut_value)
    }
}
