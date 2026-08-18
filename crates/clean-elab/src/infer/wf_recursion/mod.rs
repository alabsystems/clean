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
//! 3. **Build WF relation**: Construct `rel := fun a b => Nat.lt (m a) (m b)`
//!    together with a constructive `WellFounded rel` witness (see
//!    [`measure_wf`]) — directly over `Acc`/`Acc.rec`, so it works against the
//!    builtin prelude, which has no `invImage`/`WellFoundedRelation`.
//! 4. **Transform body**: Replace recursive calls `f arg` with
//!    `rec arg decreasing_proof` where `rec` is the fixpoint parameter and the
//!    proof is synthesized per call site (see [`call_sites`]).
//! 5. **Wrap in WellFounded.fix**: Produce the final definition value.
//!
//! # Limitations
//!
//! Current implementation supports (phase 1, 2026-08-10):
//! - Single non-mutual definitions with exactly ONE parameter
//! - Explicit `termination_by` with a `Nat`-valued measure expression
//! - Per-call-site decreasing proofs synthesized by the discharge cascade in
//!   [`decreasing`] (hypothesis lookup → `Nat.sub_lt` → `omega` →
//!   `simp_arith`), threaded through the rewrite in [`call_sites`]
//! - Mutual definitions via `PackMutual` encoding (see [`mutual`])
//!
//! Not yet supported (all FAIL CLOSED with a diagnostic naming
//! `termination_by` — never `sorry`, an axiom, or an unchecked declaration):
//! - Multi-parameter definitions
//! - `decreasing_by` user tactic blocks (the default cascade still runs)
//! - Automatic measure inference (`GuessLex`)
//! - Non-Nat measures (custom `WellFoundedRelation` instances)
//! - Call sites whose decrease the cascade cannot discharge
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/`

pub(super) mod call_sites;
pub(crate) mod decreasing;
pub(super) mod encoding;
pub(super) mod measure_wf;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod equation_lemmas;
pub(crate) mod mutual;
pub(super) mod pre_definition;

#[cfg(test)]
mod tests;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};
use clean_parser::SurfaceExpr;

use self::pre_definition::TerminationMeasure;
use super::ElabCtx;
use crate::ElabError;

/// The canonical fail-closed diagnostic for the well-founded path.
///
/// Names the construct the user wrote (`termination_by`) and the declaration,
/// never an internal implementation constant — and states the fail-closed
/// contract explicitly.
///
/// SOUNDNESS: every refusal in this module goes through here and returns an
/// error. Nothing is ever registered via `sorry`, an axiom, or an unchecked
/// declaration for a definition the WF lowering cannot compile.
fn wf_unsupported(name: &str, reason: &str) -> ElabError {
    ElabError::Unsupported {
        feature: format!(
            "well-founded recursion for '{name}': `termination_by` with a \
             non-structural recursive call. {reason}. Fail closed: the \
             definition is rejected; nothing is registered via sorry, axiom, \
             or unchecked declaration."
        ),
    }
}

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

        // Phases 2-3 run with the binder locals still pushed (the measure and
        // the decreasing obligations reference them); clean up afterwards on
        // BOTH the success and the failure path (LIFO: forward decl, binders).
        let result = self.elab_wf_recursion_core(
            name,
            &func_ty,
            &func_body,
            func_fvar,
            &binder_fvars,
            measure,
        );
        self.pop_local();
        for _ in binders {
            self.pop_local();
        }
        result
    }

    /// Phases 2-3 of the WF lowering: measure elaboration, feasibility gates,
    /// and the `WellFounded.fix` term construction with per-call-site
    /// decreasing proofs.
    ///
    /// FAIL CLOSED: every unsupported shape and every undischargeable
    /// obligation returns [`wf_unsupported`]'s diagnostic (naming
    /// `termination_by` and the declaration, never an internal constant such
    /// as `invImage`). A `termination_by` whose recursion is STRUCTURAL never
    /// reaches here: `setup_recursion` routes it to the structural path.
    fn elab_wf_recursion_core(
        &mut self,
        name: &str,
        func_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        measure: &TerminationMeasure,
    ) -> Result<(Expr, Expr), ElabError> {
        // Phase-1 scope: exactly one parameter. Lean packs multi-parameter
        // definitions through PSigma before fixing; that packing is not wired
        // yet, and silently fixing on the first parameter alone would build
        // wrong obligations.
        if binder_fvars.len() != 1 {
            return Err(wf_unsupported(
                name,
                "only single-parameter definitions are supported by the \
                 well-founded lowering so far",
            ));
        }

        // Feasibility gate: the whole encoding (relation, accessibility
        // transport, fixpoint) references these constants. Refuse up front
        // with the construct-naming diagnostic instead of leaking an
        // unknown-constant kernel error from a partially built term.
        if let Some(missing) = measure_wf::REQUIRED_CONSTANTS
            .iter()
            .copied()
            .find(|c| self.env.get_const(&Name::from_string(c)).is_none())
        {
            return Err(wf_unsupported(
                name,
                &format!(
                    "the environment does not provide the well-founded \
                     foundation (missing constant `{missing}`)"
                ),
            ));
        }

        // Phase 2: Elaborate the termination measure in a context where the
        // function parameters are bound, and require it to be Nat-valued.
        let measure_expr = self.elaborate(&measure.measure_expr)?;
        let measure_expr = self.metas.instantiate(&measure_expr);
        let measure_expr = self.metas.instantiate_levels(&measure_expr);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        match self.infer_type_full(&measure_expr) {
            Ok(measure_ty) if self.is_def_eq(&measure_ty, &nat) => {}
            _ => {
                return Err(wf_unsupported(
                    name,
                    "only `Nat`-valued `termination_by` measures are supported",
                ));
            }
        }

        // Phase 3: build the `WellFounded.fix` definition value.
        let (first_fvar, first_ty) = &binder_fvars[0];
        self.build_wf_definition(
            name,
            func_ty,
            func_body,
            func_fvar,
            (*first_fvar, first_ty),
            &measure_expr,
        )
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
    /// For a function `f (x : α) : β := body` with measure `m` this builds:
    ///
    /// ```text
    /// WellFounded.fix.{u, v}
    ///   α                                      -- Sort u
    ///   (fun (x : α) => β)                     -- motive C
    ///   (fun (a b : α) => Nat.lt (m a) (m b))  -- rel  (measure_wf)
    ///   hwf                                    -- WellFounded rel (measure_wf)
    ///   (fun (x : α) (rec : (y : α) → rel y x → C y) =>
    ///      body[f arg ↦ rec arg decreasing_proof])   -- call_sites
    /// ```
    ///
    /// Returns `(type, value)`. The kernel re-checks the value in full at
    /// registration; every decreasing proof was already strictly re-checked
    /// at synthesis time.
    fn build_wf_definition(
        &mut self,
        name: &str,
        func_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        first: (FVarId, &Expr),
        measure_expr: &Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        let (first_fvar, first_ty) = first;

        // Universe levels. Failing to determine one is a hard refusal:
        // defaulting to a made-up level parameter would produce a term the
        // kernel rejects with a level-mismatch message naming internals.
        let u_level = self.infer_sort(first_ty).map_err(|_| {
            wf_unsupported(
                name,
                "could not determine the universe of the recursion \
                 parameter's type",
            )
        })?;

        // Open the return type: func_ty = (x : α) → ret.
        let ret_open = match func_ty.kind() {
            ExprKind::Pi(_, _, body) => body.instantiate(&Expr::fvar(first_fvar)),
            _ => {
                return Err(wf_unsupported(
                    name,
                    "the elaborated function type is not a Pi type",
                ));
            }
        };
        let v_level = self.infer_sort(&ret_open).map_err(|_| {
            wf_unsupported(name, "could not determine the universe of the return type")
        })?;

        // Motive: fun (x : α) => ret.
        let motive = Expr::lam(
            BinderInfo::Default,
            first_ty.clone(),
            ret_open.abstract_fvar(first_fvar),
        );

        // Relation and its well-foundedness witness (builtin-prelude
        // constructive foundation; no invImage / WellFoundedRelation).
        let rel = self.build_measure_rel(first_ty, measure_expr, first_fvar);
        let wf_proof =
            self.build_measure_wf_proof(first_ty, &u_level, &rel, measure_expr, first_fvar);

        // Open the body: func_body = fun (x : α) => body. (Opening — rather
        // than stripping the lambda and leaving a loose de Bruijn index —
        // keeps the parameter as `first_fvar`, which the decreasing
        // obligations and the final re-abstraction both key on.)
        let body_open = match func_body.kind() {
            ExprKind::Lam(_, _, body) => body.instantiate(&Expr::fvar(first_fvar)),
            _ => {
                return Err(wf_unsupported(
                    name,
                    "the elaborated function value is not a lambda",
                ));
            }
        };

        // Rewrite recursive calls `f arg` to `rec arg proof`, synthesizing a
        // decreasing proof per call site. FAIL CLOSED on any failure.
        let rec_fvar = self.fresh_fvar();
        let cfg = call_sites::RecCallRewrite {
            func_fvar,
            rec_fvar,
            param_fvar: first_fvar,
            measure_expr,
        };
        let transformed = self
            .transform_rec_calls_proved(&body_open, &cfg)
            .map_err(|reject| wf_unsupported(name, &reject.0))?;

        // Backstop: no self-reference may survive the rewrite. The rewriter
        // already guarantees this (it refuses shapes it cannot rewrite), but
        // this check keeps the fail-closed property independent of it.
        if encoding::contains_fvar(&transformed, func_fvar) {
            return Err(wf_unsupported(
                name,
                "a self-reference survived the call-site rewrite",
            ));
        }

        // rec : (y : α) → rel y x → C y
        let rec_param_ty = {
            let y_fvar = self.fresh_fvar();
            let rel_y_x = Expr::apps(rel.clone(), [Expr::fvar(y_fvar), Expr::fvar(first_fvar)]);
            let c_y = Expr::app(motive.clone(), Expr::fvar(y_fvar));
            let inner = Expr::arrow(rel_y_x, c_y);
            Expr::pi(
                BinderInfo::Default,
                first_ty.clone(),
                inner.abstract_fvar(y_fvar),
            )
        };

        // F := fun (x : α) (rec : …) => transformed
        let fix_body = {
            let with_rec = Expr::lam(
                BinderInfo::Default,
                rec_param_ty,
                transformed.abstract_fvar(rec_fvar),
            );
            Expr::lam(
                BinderInfo::Default,
                first_ty.clone(),
                with_rec.abstract_fvar(first_fvar),
            )
        };

        // WellFounded.fix.{u, v} α C rel hwf F
        let wf_fix = Expr::const_(Name::from_string("WellFounded.fix"), vec![u_level, v_level]);
        let result = Expr::apps(wf_fix, [first_ty.clone(), motive, rel, wf_proof, fix_body]);

        Ok((func_ty.clone(), result))
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
}
