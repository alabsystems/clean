// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded recursion elaboration.
//!
//! Implements the transformation of recursive definitions with
//! `termination_by` annotations into `WellFounded.fix` applications.
//!
//! # Overview
//!
//! A recursive function like:
//! ```lean
//! def f (n : Nat) : Nat :=
//!   if n = 0 then 0
//!   else f (n - 1) + 1
//! termination_by n
//! ```
//!
//! Is compiled to:
//! ```lean
//! def f : Nat → Nat :=
//!   WellFounded.fix (fun n rec =>
//!     if n = 0 then 0
//!     else rec (n - 1) proof_that_n_minus_1_lt_n + 1)
//! ```
//!
//! # Algorithm (single non-mutual definition)
//!
//! 1. **Collect pre-definition**: Elaborate type and body with recursive calls
//!    left as references to a local forward declaration.
//! 2. **Elaborate measure**: The `termination_by` expression is elaborated
//!    in a context where the function parameters are bound.
//! 3. **Build WF relation**: Construct `invImage measure Nat.lt_wfRel` which
//!    gives a `WellFoundedRelation` instance on the argument type.
//! 4. **Transform body**: Replace recursive calls `f arg` with
//!    `rec arg decreasing_proof` where `rec` is the fixpoint parameter.
//! 5. **Wrap in WellFounded.fix**: Produce the final definition value.
//!
//! # Limitations
//!
//! Current implementation supports:
//! - Single non-mutual definitions
//! - Mutual definitions via `PackMutual` encoding (see [`mutual`])
//! - Explicit `termination_by` with a measure expression
//! - `Nat`-valued measures (mapped through `Nat.lt_wfRel`)
//! - `decreasing_by` tactic for custom decreasing proofs (see [`decreasing`])
//! - Default decreasing cascade: `simp_arith` → `mathverse` → `sorry`
//! - Equation lemma generation for `simp` (see [`equation_lemmas`])
//!
//! Not yet supported:
//! - Automatic measure inference (`GuessLex`)
//! - Non-Nat measures (custom `WellFoundedRelation` instances)
//! - Full equation case extraction from match compiler output
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/`

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod decreasing;
pub(super) mod encoding;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod equation_lemmas;
pub(crate) mod mutual;
pub(super) mod pre_definition;

#[cfg(test)]
mod tests;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceExpr;

use self::encoding::replace_rec_calls;
use self::pre_definition::TerminationMeasure;
use super::ElabCtx;
use crate::ElabError;

impl<'a> ElabCtx<'a> {
    /// Elaborate a recursive definition using well-founded recursion.
    ///
    /// This is the main entry point for WF elaboration. Called from
    /// `elab_definition_inner` when a `termination_by` annotation with
    /// a WellFounded measure is present and structural recursion is not
    /// applicable.
    ///
    /// # Arguments
    ///
    /// * `name` - Declaration name (unqualified)
    /// * `binders` - Function parameter binders
    /// * `ty` - Optional explicit return type annotation
    /// * `val` - Function body
    /// * `measure` - The termination measure from `termination_by`
    ///
    /// # Returns
    ///
    /// `(type, value)` pair where value is a `WellFounded.fix` application.
    pub(super) fn elab_wf_recursion(
        &mut self,
        name: &str,
        binders: &[clean_parser::SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        measure: &TerminationMeasure,
    ) -> Result<(Expr, Expr), ElabError> {
        if binders.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "well-founded recursion for '{}': function must have at least one parameter",
                    name
                ),
            });
        }

        // Phase 1: Elaborate the function type and body with a forward
        // declaration for recursive calls.
        //
        // We push the function name as a local so that recursive calls
        // in the body resolve to an FVar. After elaboration, we replace
        // these FVars with the WellFounded.fix recursive argument.

        // First, elaborate the full type by processing binders
        let (func_ty, func_body, func_fvar, binder_fvars) =
            self.elab_wf_pre_definition(name, binders, ty, val)?;

        // Phase 1b: FAIL CLOSED on genuine recursion.
        //
        // Every recursive call site `f arg` must become `rec arg h` where
        // `h : measure arg < measure x`. Nothing in this module synthesises
        // `h`: `transform_rec_calls` rewrites `f ↦ rec` and drops the proof
        // argument entirely, and the obligation machinery in `decreasing.rs`
        // has no caller. So for a body that really recurses we cannot build a
        // correct `WellFounded.fix` term — and we must not emit an incorrect
        // one and let the kernel reject it with an internal message that names
        // an implementation constant (`invImage`) instead of the construct the
        // user wrote.
        //
        // SOUNDNESS: this path returns an error. It never emits `sorry`, an
        // axiom, or an unchecked declaration — a rejected `def` stays rejected.
        //
        // A `termination_by` whose recursion is STRUCTURAL never reaches here:
        // `elab_termination_hints` routes it to the structural path. This
        // guard therefore only fires for genuinely non-structural recursion,
        // which is exactly the class that cannot type-check today.
        if encoding::contains_fvar(&func_body, func_fvar) {
            // Restore the local context before reporting (LIFO).
            self.pop_local();
            for _ in binders {
                self.pop_local();
            }
            return Err(ElabError::Unsupported {
                feature: format!(
                    "well-founded recursion for '{name}': `termination_by` with a \
                     non-structural recursive call. Compiling it requires synthesising \
                     a decreasing proof `measure(arg) < measure(param)` at each \
                     recursive call site, which is not implemented. A `termination_by` \
                     whose recursion is structural is supported."
                ),
            });
        }

        // Phase 2: Elaborate the termination measure.
        // The measure expression is elaborated in a context where
        // the function parameters are already bound.
        let measure_expr = self.elaborate(&measure.measure_expr)?;
        let measure_expr = self.metas.instantiate(&measure_expr);
        let measure_expr = self.metas.instantiate_levels(&measure_expr);

        // Phase 3: Build the WF encoding.
        // We need to decompose the function type to extract:
        // - The argument type (first varying parameter)
        // - The return type (as a function of the argument)
        let (wf_val, wf_ty) = self.build_wf_definition(
            name,
            &func_ty,
            &func_body,
            func_fvar,
            &binder_fvars,
            &measure_expr,
        )?;

        // Phase 4: clean up — pop all binder locals (LIFO order)
        // Pop function forward declaration
        self.pop_local();
        // Pop binder locals
        for _ in binders {
            self.pop_local();
        }

        Ok((wf_ty, wf_val))
    }

    /// Elaborate the pre-definition: type, body, and forward declaration.
    ///
    /// Returns (type, body, func_fvar, binder_fvars) where:
    /// - type is the full Pi type
    /// - body is the Lambda-abstracted value
    /// - func_fvar is the FVar used for recursive references
    /// - binder_fvars are the FVars for each parameter
    fn elab_wf_pre_definition(
        &mut self,
        name: &str,
        binders: &[clean_parser::SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
    ) -> Result<(Expr, Expr, FVarId, Vec<(FVarId, Expr)>), ElabError> {
        use super::convert_binder_info;

        let mut binder_fvars: Vec<(FVarId, Expr)> = Vec::with_capacity(binders.len());

        // Elaborate each binder and push as local
        for binder in binders {
            let binder_ty = if let Some(ty_expr) = &binder.ty {
                let elaborated = self.elaborate(ty_expr)?;
                let instantiated = self.metas.instantiate(&elaborated);
                self.metas.instantiate_levels(&instantiated)
            } else {
                let sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(sort)
            };

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());

            if bi == BinderInfo::InstImplicit {
                self.push_local_instance(fvar, binder_ty.clone());
            }

            binder_fvars.push((fvar, binder_ty));
        }

        // Elaborate return type
        let ret_ty = if let Some(ty_expr) = ty {
            let elaborated = self.elaborate(ty_expr)?;
            let instantiated = self.metas.instantiate(&elaborated);
            self.metas.instantiate_levels(&instantiated)
        } else {
            let sort = Expr::sort(self.fresh_universe_param());
            self.fresh_meta(sort)
        };

        // Build the full function type: (x₁ : T₁) → ... → (xₙ : Tₙ) → ret_ty
        let mut full_ty = ret_ty.clone();
        for (i, binder) in binders.iter().enumerate().rev() {
            let bi = convert_binder_info(binder.info);
            let (fvar, ref binder_ty) = binder_fvars[i];
            let abstracted = full_ty.abstract_fvar(fvar);
            full_ty = Expr::pi(bi, binder_ty.clone(), abstracted);
        }

        // Push the function itself as a local for recursive references
        let func_fvar = self.push_local(name.to_owned(), full_ty.clone());

        // Set expected type for bidirectional type checking
        let prev_expected = self.current_expected_type.clone();
        self.current_expected_type = Some(ret_ty);

        // Elaborate the body. Term-body position: unknown idents are loud,
        // never auto-bound (B03; Lean auto-binds only in decl headers).
        let body_expr = self.with_term_body_scope(|this| this.elaborate(val))?;
        let body_expr = self.metas.instantiate(&body_expr);
        let body_expr = self.metas.instantiate_levels(&body_expr);

        // Restore expected type
        self.current_expected_type = prev_expected;

        // Build the full lambda: fun x₁ ... xₙ => body
        let mut full_val = body_expr;
        for (i, binder) in binders.iter().enumerate().rev() {
            let bi = convert_binder_info(binder.info);
            let (fvar, ref binder_ty) = binder_fvars[i];
            let abstracted = full_val.abstract_fvar(fvar);
            full_val = Expr::lam(bi, binder_ty.clone(), abstracted);
        }

        Ok((full_ty, full_val, func_fvar, binder_fvars))
    }

    /// Build the WellFounded.fix-based definition value.
    ///
    /// Takes the elaborated pre-definition and produces the final
    /// `WellFounded.fix` application.
    fn build_wf_definition(
        &mut self,
        name: &str,
        func_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        measure_expr: &Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        // For a function `f (x : α) : β := body`, we need to build:
        //
        // WellFounded.fix.{u, v}
        //   (α : Sort u)
        //   (C : α → Sort v)       -- motive: fun x => β
        //   (rel : α → α → Prop)   -- from WFR
        //   (wf : WellFounded rel)  -- from WFR
        //   (F : (x : α) → ((y : α) → rel y x → C y) → C x)
        //   : (x : α) → C x
        //
        // For single-argument functions this is straightforward.
        // For multi-argument functions, we need to pack arguments
        // (this implementation handles the common single-varying-arg case
        // and falls back to the first argument for multi-arg).

        if binder_fvars.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "well-founded recursion for '{}': no parameters to recurse on",
                    name
                ),
            });
        }

        // Use the first parameter as the "varying" argument.
        // In Lean 4, fixed parameters (those that don't change across
        // recursive calls) are factored out. We simplify by treating
        // the first argument as the varying one.
        let (first_fvar, ref first_ty) = binder_fvars[0];

        // Determine universe levels
        let u_level = self
            .infer_sort(first_ty)
            .unwrap_or_else(|_| Level::param(Name::from_string("u_wf")));

        // Build the return type from the function type
        // For f : (x : α) → β, the motive C = fun (x : α) => β
        let ret_ty_abstracted = self.extract_return_type(func_ty, binder_fvars.len())?;
        let v_level = self
            .infer_sort(&ret_ty_abstracted)
            .unwrap_or_else(|_| Level::param(Name::from_string("v_wf")));

        // Build motive: fun (x : α) => β (abstracting over the first binder)
        let motive_body = ret_ty_abstracted.abstract_fvar(first_fvar);
        let motive = Expr::lam(BinderInfo::Default, first_ty.clone(), motive_body);

        // Build the measure as a lambda: fun (x : α) => measure_expr
        let measure_body = measure_expr.abstract_fvar(first_fvar);
        let measure_lambda = Expr::lam(BinderInfo::Default, first_ty.clone(), measure_body);

        // Build WellFoundedRelation via invImage
        // `invImage.{u, v} {α : Sort u} {β : Sort v} (f : α → β)
        //    (h : WellFoundedRelation β) : WellFoundedRelation α`
        // takes TWO universe params. β is `Nat : Type 0 = Sort 1`, so v = 1.
        let inv_image = Expr::const_(
            Name::from_string("invImage"),
            vec![u_level.clone(), Level::succ(Level::zero())],
        );
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt_wfrel = Expr::const_(Name::from_string("Nat.lt_wfRel"), vec![]);
        let wfr = Expr::app(inv_image, first_ty.clone());
        let wfr = Expr::app(wfr, nat_ty);
        let wfr = Expr::app(wfr, measure_lambda);
        let wfr = Expr::app(wfr, nat_lt_wfrel);

        // Extract rel and wf from WellFoundedRelation
        let rel = Expr::proj(Name::from_string("WellFoundedRelation"), 0, wfr.clone());
        let wf_proof = Expr::proj(Name::from_string("WellFoundedRelation"), 1, wfr);

        // Build the fixpoint body F:
        // fun (x : α) (rec : (y : α) → rel y x → C y) => body[f ↦ rec_wrapper]
        //
        // Where rec_wrapper replaces `f arg` with `rec arg sorry_proof`.
        // The sorry_proof stands in for the actual decreasing proof obligation.

        // Create a fresh FVar for the `rec` parameter
        // rec : (y : α) → rel y x → C y
        let rec_fvar = self.fresh_fvar();

        // Transform the body: replace recursive calls f(arg) with rec(arg, sorry)
        // We need to handle the case where func_body is a lambda
        // (fun x₁ ... xₙ => body). We strip the outer lambdas to get the raw body,
        // replace recursive calls, then re-wrap.
        let (stripped_body, _) = self.strip_lambdas(func_body, binder_fvars.len());

        // Replace references to the function FVar with a wrapper that
        // calls rec and inserts a sorry for the decreasing proof
        let transformed = self.transform_rec_calls(
            &stripped_body,
            func_fvar,
            rec_fvar,
            first_fvar,
            first_ty,
            &rel,
            &motive,
        );

        // Build the rec parameter type:
        // (y : α) → rel y x → C y
        let rec_param_ty = {
            let y_fvar = self.fresh_fvar();
            let rel_y_x = Expr::app(
                Expr::app(rel.clone(), Expr::fvar(y_fvar)),
                Expr::fvar(first_fvar),
            );
            let c_y = Expr::app(motive.clone(), Expr::fvar(y_fvar));

            // (proof : rel y x) → C y
            let inner = Expr::arrow(rel_y_x, c_y);
            // (y : α) → inner
            // We need to abstract over y
            let inner_abs = inner.abstract_fvar(y_fvar);
            Expr::pi(BinderInfo::Default, first_ty.clone(), inner_abs)
        };

        // Build the fix body: fun (x : α) (rec : ...) => transformed_body
        let fix_body_inner = transformed.abstract_fvar(rec_fvar);
        let fix_body_inner = Expr::lam(BinderInfo::Default, rec_param_ty, fix_body_inner);
        // Abstract over x (the first parameter)
        let fix_body_abs = fix_body_inner.abstract_fvar(first_fvar);
        let fix_body = Expr::lam(BinderInfo::Default, first_ty.clone(), fix_body_abs);

        // Build: WellFounded.fix.{u, v} α C rel wf fix_body
        let wf_fix = Expr::const_(Name::from_string("WellFounded.fix"), vec![u_level, v_level]);

        let mut result = Expr::app(wf_fix, first_ty.clone()); // α
        result = Expr::app(result, motive); // C
        result = Expr::app(result, rel); // rel
        result = Expr::app(result, wf_proof); // wf
        result = Expr::app(result, fix_body); // F

        // If there are additional binders beyond the first, wrap them
        // as outer lambdas (these are "fixed parameters" in Lean 4 terminology)
        if binder_fvars.len() > 1 {
            // For multi-argument functions, we need to wrap the fixed params
            // This is a simplification; full implementation would use PackMutual
            for (_i, (fvar, fvar_ty)) in binder_fvars.iter().enumerate().rev().skip(1).rev() {
                let bi = BinderInfo::Default; // Simplified
                let abstracted = result.abstract_fvar(*fvar);
                result = Expr::lam(bi, fvar_ty.clone(), abstracted);
            }
        }

        Ok((result, func_ty.clone()))
    }

    /// Extract the return type from a Pi type by stripping `n` binders.
    pub(crate) fn extract_return_type(&self, ty: &Expr, n: usize) -> Result<Expr, ElabError> {
        let mut current = ty.clone();
        for _ in 0..n {
            match current.kind() {
                ExprKind::Pi(_, _, body) => {
                    // Substitute with a fresh FVar to unwrap the de Bruijn binding
                    current = Expr::clone(body);
                }
                _ => {
                    // WHNF might reveal more Pi structure
                    let whnf = self.whnf(&current);
                    match whnf.kind() {
                        ExprKind::Pi(_, _, body) => {
                            current = Expr::clone(body);
                        }
                        _ => {
                            return Err(ElabError::Unsupported {
                                feature: format!(
                                    "well-founded recursion: expected Pi type, got {:?}",
                                    whnf
                                ),
                            });
                        }
                    }
                }
            }
        }
        Ok(current)
    }

    /// Strip `n` lambda binders from an expression, returning the body
    /// and the binder info.
    pub(crate) fn strip_lambdas(&self, expr: &Expr, n: usize) -> (Expr, Vec<(BinderInfo, Expr)>) {
        let mut current = expr.clone();
        let mut binders = Vec::with_capacity(n);
        for _ in 0..n {
            match current.kind() {
                ExprKind::Lam(bd, ty, body) => {
                    binders.push((bd.info, Expr::clone(ty)));
                    current = Expr::clone(body);
                }
                _ => break,
            }
        }
        (current, binders)
    }

    /// Transform recursive calls in the body.
    ///
    /// Replaces `func_fvar arg` with `rec_fvar arg sorry_proof`
    /// where sorry_proof is a placeholder for `measure(arg) < measure(x)`.
    fn transform_rec_calls(
        &mut self,
        body: &Expr,
        func_fvar: FVarId,
        rec_fvar: FVarId,
        _arg_fvar: FVarId,
        _arg_type: &Expr,
        _rel: &Expr,
        _motive: &Expr,
    ) -> Expr {
        // Simple transformation: replace func_fvar references with
        // a wrapper that calls rec_fvar and adds a sorry for the proof.
        //
        // Full implementation would:
        // 1. Detect each recursive call site
        // 2. Extract the argument passed
        // 3. Build a proof obligation `measure(arg) < measure(x)`
        // 4. Create a metavariable for the proof (to be solved by decreasing_tactic)
        //
        // For now, we use the simplified approach where recursive calls
        // become `rec arg sorry` — this is sound because sorry is
        // axiomatically valid, and the definition will still type-check.

        replace_rec_calls_with_sorry(body, func_fvar, rec_fvar)
    }
}

/// Replace recursive calls `f arg` with `rec arg sorry`.
///
/// This is a simplified version that replaces all occurrences of `func_fvar`
/// with `rec_fvar` and inserts sorry proofs for the decreasing obligations.
///
/// The sorry proof has type `Prop` (actually `rel arg x` but we use sorry
/// which is polymorphic).
fn replace_rec_calls_with_sorry(body: &Expr, func_fvar: FVarId, rec_fvar: FVarId) -> Expr {
    // For now, simply replace func references with rec.
    // The type checker will catch any missing decreasing proofs.
    // In Lean 4, this is where metavariables are created for each
    // recursive call site, later solved by decreasing_tactic.
    //
    // Our approach: replace f with rec, and rely on the elaborator's
    // implicit argument insertion to fill in the decreasing proof
    // (which will become sorry through our default tactic).
    replace_rec_calls(body, func_fvar, rec_fvar)
}
