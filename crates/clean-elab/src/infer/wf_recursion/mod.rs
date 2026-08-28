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
//! # Wider signatures, one recursion parameter (phase 2, 2026-08-22)
//!
//! `gcd` is the motivating case:
//!
//! ```lean
//! def gcd (a b : Nat) : Nat := if h : 0 < b then gcd b (a % b) else a
//! termination_by b
//! ```
//!
//! TWO parameters, but only ONE of them is the recursion parameter: the
//! measure is `b` and the decrease is `a % b < b`. Both stay single-parameter;
//! only the SIGNATURE is wider. The lowering therefore fixes on the measure's
//! parameter and threads the OTHER parameters through the MOTIVE:
//!
//! ```text
//! gcd = fun a b =>
//!   @WellFounded.fix α (fun x => Nat → Nat) rel hwf
//!     (fun x rec => fun a => dite (0 < x) (fun h => rec (a % x) prf x) (fun _ => a))
//!     b a
//! ```
//!
//! `C x = Π (others, with the recursion parameter := x) → ret`, so a
//! recursive call may change EVERY argument (gcd changes both) while the
//! obligation `Nat.lt (m arg) (m param)` stays exactly the one-parameter
//! obligation phase 1 already discharges.
//!
//! # A SUM measure over several parameters (phase 3, 2026-08-25)
//!
//! Phase 2's boundary was the MEASURE, and a two-branch **subtractive** Euclid
//! sits just past it:
//!
//! ```lean
//! def gcdSub (a b : Nat) : Nat :=
//!   if ha : a = 0 then b
//!   else if hb : b = 0 then a
//!   else if hge : a ≥ b then gcdSub (a - b) b else gcdSub a (b - a)
//! termination_by a + b
//! ```
//!
//! Neither parameter decreases — only `a + b` does. Such a measure is now
//! lowered by [`sum_measure`], on the observation that a multi-parameter
//! measure STILL induces a one-parameter well-founded relation: `Nat.lt` on
//! the measure's VALUE, with the parameters riding in the motive and tied to
//! the recursion variable by a hypothesis. No `PSigma` packing, no
//! lexicographic order, and the per-call-site obligation is still
//! `Nat.lt (m args) (m params)`. The shape was kernel-probed first —
//! `clean-kernel/tests/wf_sum_measure_kernel_probe.rs`.
//!
//! The gate is [`measure_shape::is_nat_sum`], a deliberate SCOPE limit rather
//! than a limit of the encoding (which is uniform in the measure): see that
//! module for why, and v7/D2 for why a measured boundary is never a design.
//!
//! # Limitations
//!
//! Current implementation supports:
//! - Single non-mutual definitions with any number of parameters, of which
//!   the measure names exactly ONE (the recursion parameter)
//! - A measure that is a SUM (`termination_by a + b`) over SEVERAL parameters
//! - Explicit `termination_by` with a `Nat`-valued measure expression
//! - Per-call-site decreasing proofs synthesized by the discharge cascade in
//!   [`decreasing`] (hypothesis lookup → `Nat.sub_lt` → `Nat.mod_lt` →
//!   `omega` → `simp_arith`), threaded through the rewrite in [`call_sites`]
//! - Mutual definitions via `PackMutual` encoding (see [`mutual`])
//!
//! Not yet supported (all FAIL CLOSED with a diagnostic naming
//! `termination_by` — never `sorry`, an axiom, or an unchecked declaration):
//! - A multi-parameter measure that is NOT a sum (lexicographic / packed)
//! - A recursion parameter whose TYPE depends on another parameter (the
//!   sole-parameter path only; the sum path does not reorder the telescope)
//! - Partially-applied recursive calls
//! - `decreasing_by` user tactic blocks (the default cascade still runs)
//! - Automatic measure inference (`GuessLex`)
//! - Non-Nat measures (custom `WellFoundedRelation` instances)
//! - Call sites whose decrease the cascade cannot discharge
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/`

pub(super) mod call_sites;
pub(crate) mod decreasing;
pub(super) mod encoding;
pub(crate) mod measure_params;
pub(crate) mod measure_shape;
pub(super) mod measure_wf;
pub(super) mod nat_rewrite;
pub(super) mod sub_elim;
pub(super) mod sum_measure;
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

/// Which of the two well-founded lowerings a definition takes.
///
/// Decided in `elab_wf_recursion_core`'s phase 2b from the ELABORATED measure
/// (real `FVar`s), never from a spelling. The routing hint in
/// `elab_decl_value` may disagree without consequence: it only chooses which
/// lowering is ATTEMPTED, and this is what the lowering actually believes.
enum WfShape {
    /// The measure names exactly one parameter, which becomes
    /// `WellFounded.fix`'s major premise (phases 1–2).
    SoleParameter(usize),
    /// The measure is a SUM mentioning several parameters; the fix runs on the
    /// measure's value and every parameter rides in the motive (phase 3, see
    /// [`sum_measure`]).
    SumOverParameters,
}

/// Spell the sum a refused multi-parameter measure could be restated as, e.g.
/// `a + b`. Used only inside the diagnostic, so a parameter without a source
/// name degrades to its position rather than failing.
fn sum_spelling(mentioned: &[usize], binders: &[clean_parser::SurfaceBinder]) -> String {
    mentioned
        .iter()
        .map(|index| {
            binders
                .get(*index)
                .map_or_else(|| format!("<parameter #{index}>"), |b| b.name.clone())
        })
        .collect::<Vec<_>>()
        .join(" + ")
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
        let (func_ty, ret_ty, func_body, func_fvar, binder_fvars) =
            self.elab_wf_pre_definition(name, binders, ty, val)?;

        // Phases 2-3 run with the binder locals still pushed (the measure and
        // the decreasing obligations reference them); clean up afterwards on
        // BOTH the success and the failure path (LIFO: forward decl, binders).
        let result = self.elab_wf_recursion_core(
            name,
            &func_ty,
            &ret_ty,
            &func_body,
            func_fvar,
            &binder_fvars,
            binders,
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
    #[allow(clippy::too_many_arguments)]
    fn elab_wf_recursion_core(
        &mut self,
        name: &str,
        func_ty: &Expr,
        ret_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        binders: &[clean_parser::SurfaceBinder],
        measure: &TerminationMeasure,
    ) -> Result<(Expr, Expr), ElabError> {
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

        // Phase 2b: WHICH shape is this? The measure decides.
        //
        //   ONE parameter   → it is the recursion parameter; it moves to the
        //                     front of the fix telescope and the others thread
        //                     through the motive (phases 1–2, unchanged).
        //   SEVERAL, a SUM  → the fix runs on the measure's VALUE and every
        //                     parameter rides in the motive (phase 3).
        //   SEVERAL, other  → lexicographic / packed: still refused, with the
        //                     sum form named as a way forward.
        //   NONE            → nothing can decrease; refused up front.
        //
        // A one-parameter definition keeps the phase-1 answer unconditionally
        // — including the degenerate `termination_by 5`, whose refusal stays
        // where it always was (an undischargeable decrease), not here.
        let shape = if binder_fvars.len() == 1 {
            WfShape::SoleParameter(0)
        } else {
            let mentioned: Vec<usize> = binder_fvars
                .iter()
                .enumerate()
                .filter(|(_, (fvar, _))| encoding::contains_fvar(&measure_expr, *fvar))
                .map(|(index, _)| index)
                .collect();
            let named = |index: usize| {
                binders
                    .get(index)
                    .map_or_else(|| format!("#{index}"), |b| format!("`{}`", b.name))
            };
            match mentioned.as_slice() {
                [only] => WfShape::SoleParameter(*only),
                [] => {
                    return Err(wf_unsupported(
                        name,
                        "the `termination_by` measure mentions none of the \
                         parameters, so nothing in it can decrease. Name the \
                         parameter the recursion shrinks, e.g. \
                         `termination_by <that parameter>`",
                    ));
                }
                _ if measure_shape::is_nat_sum(&measure_expr) => WfShape::SumOverParameters,
                many => {
                    let list: Vec<String> = many.iter().map(|i| named(*i)).collect();
                    return Err(wf_unsupported(
                        name,
                        &format!(
                            "the `termination_by` measure mentions {} \
                             parameters ({}) and is not a SUM. A SUM measure \
                             IS lowered — `termination_by {}` runs the \
                             recursion on the measure's value and threads \
                             every parameter through the motive — but a \
                             general lexicographic or packed measure is not. \
                             Ways forward: (1) restate the measure as a sum, \
                             e.g. `termination_by {}`, which is what a \
                             two-branch subtractive recursion needs; \
                             (2) restate it so it names ONE parameter — a \
                             wider SIGNATURE is fine, the other parameters \
                             are threaded through unchanged; (3) introduce an \
                             inner helper whose single parameter carries the \
                             decrease",
                            many.len(),
                            list.join(", "),
                            sum_spelling(many, binders),
                            sum_spelling(many, binders),
                        ),
                    ));
                }
            }
        };

        // Phase 3: build the `WellFounded.fix` definition value.
        match shape {
            WfShape::SoleParameter(param_index) => {
                // The recursion parameter moves to the FRONT of the telescope
                // (it becomes `WellFounded.fix`'s major premise, with every
                // other parameter re-bound inside the motive). That reordering
                // is only well-formed when its type does not depend on another
                // parameter. The sum path does NOT reorder, so this gate is
                // deliberately scoped to this arm.
                if binder_fvars.len() > 1 {
                    let (_, param_ty) = &binder_fvars[param_index];
                    for (index, (fvar, _)) in binder_fvars.iter().enumerate() {
                        if index != param_index && encoding::contains_fvar(param_ty, *fvar) {
                            return Err(wf_unsupported(
                                name,
                                "the recursion parameter's TYPE depends on \
                                 another parameter, so it cannot be moved to \
                                 the front of the telescope. Ways forward: \
                                 (1) reorder the parameters so the recursion \
                                 parameter's type is self-contained; \
                                 (2) recurse on a parameter whose type is \
                                 closed",
                            ));
                        }
                    }
                }
                self.build_wf_definition(
                    name,
                    func_ty,
                    ret_ty,
                    func_body,
                    func_fvar,
                    binder_fvars,
                    binders,
                    param_index,
                    &measure_expr,
                )
            }
            WfShape::SumOverParameters => self.build_wf_sum_definition(
                name,
                func_ty,
                ret_ty,
                func_body,
                func_fvar,
                binder_fvars,
                binders,
                &measure_expr,
            ),
        }
    }

    /// Elaborate the pre-definition: type, body, and forward declaration.
    ///
    /// Returns (type, ret_ty, body, func_fvar, binder_fvars) where:
    /// - type is the full Pi type
    /// - ret_ty is the return type, still OPEN over `binder_fvars` (the
    ///   multi-parameter motive is built from it, so it must not be
    ///   re-abstracted and re-opened)
    /// - body is the Lambda-abstracted value
    /// - func_fvar is the FVar used for recursive references
    /// - binder_fvars are the FVars for each parameter
    fn elab_wf_pre_definition(
        &mut self,
        name: &str,
        binders: &[clean_parser::SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
    ) -> Result<(Expr, Expr, Expr, FVarId, Vec<(FVarId, Expr)>), ElabError> {
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
        self.current_expected_type = Some(ret_ty.clone());

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

        Ok((full_ty, ret_ty, full_val, func_fvar, binder_fvars))
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
    /// For a WIDER signature `f (p₀ … pₙ₋₁) : β` whose measure names the
    /// single parameter `pᵢ`, the same term is built with `pᵢ` as the major
    /// premise and every OTHER parameter re-bound inside the motive:
    ///
    /// ```text
    /// fun p₀ … pₙ₋₁ =>
    ///   WellFounded.fix.{u, v} α
    ///     (fun x => Π (others)[pᵢ := x] → β[pᵢ := x])       -- motive C
    ///     rel hwf
    ///     (fun x rec => fun (others) => body[f args ↦ rec argᵢ prf args…])
    ///     pᵢ (others)
    /// ```
    ///
    /// The relation, the well-foundedness witness and every per-call-site
    /// obligation are unchanged one-parameter objects — only the motive and
    /// the argument threading widen. A one-parameter definition takes the
    /// same path and produces the byte-identical phase-1 term (no eta
    /// wrapper): see the `binder_fvars.len() == 1` early return below.
    ///
    /// Returns `(type, value)`. The kernel re-checks the value in full at
    /// registration; every decreasing proof was already strictly re-checked
    /// at synthesis time.
    #[allow(clippy::too_many_arguments)]
    fn build_wf_definition(
        &mut self,
        name: &str,
        func_ty: &Expr,
        ret_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        binders: &[clean_parser::SurfaceBinder],
        param_index: usize,
        measure_expr: &Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        use super::convert_binder_info;

        let arity = binder_fvars.len();
        let (param_fvar, param_ty) = &binder_fvars[param_index];
        let (param_fvar, param_ty) = (*param_fvar, param_ty.clone());
        let binder_info_at = |index: usize| {
            binders
                .get(index)
                .map_or(BinderInfo::Default, |b| convert_binder_info(b.info))
        };

        // Universe levels. Failing to determine one is a hard refusal:
        // defaulting to a made-up level parameter would produce a term the
        // kernel rejects with a level-mismatch message naming internals.
        let u_level = self.infer_sort(&param_ty).map_err(|_| {
            wf_unsupported(
                name,
                "could not determine the universe of the recursion \
                 parameter's type",
            )
        })?;

        // The motive's body: `Π (others) → ret`, with the others re-bound in
        // their ORIGINAL relative order and `ret` still open over `pᵢ`. With
        // one parameter this is exactly `ret`.
        let mut motive_body = ret_ty.clone();
        for index in (0..arity).rev() {
            if index == param_index {
                continue;
            }
            let (fvar, binder_ty) = &binder_fvars[index];
            motive_body = Expr::pi(
                binder_info_at(index),
                binder_ty.clone(),
                motive_body.abstract_fvar(*fvar),
            );
        }
        let v_level = self.infer_sort(&motive_body).map_err(|_| {
            wf_unsupported(name, "could not determine the universe of the return type")
        })?;

        // Motive: fun (x : α) => Π (others)[pᵢ := x] → ret[pᵢ := x].
        let motive = Expr::lam(
            BinderInfo::Default,
            param_ty.clone(),
            motive_body.abstract_fvar(param_fvar),
        );

        // Relation and its well-foundedness witness (builtin-prelude
        // constructive foundation; no invImage / WellFoundedRelation).
        let rel = self.build_measure_rel(&param_ty, measure_expr, param_fvar);
        let wf_proof =
            self.build_measure_wf_proof(&param_ty, &u_level, &rel, measure_expr, param_fvar);

        // Open the body: func_body = fun p₀ … pₙ₋₁ => body. (Opening — rather
        // than stripping the lambdas and leaving loose de Bruijn indices —
        // keeps each parameter as its own fvar, which the decreasing
        // obligations and the final re-abstraction both key on.)
        let mut body_open = func_body.clone();
        for (fvar, _) in binder_fvars {
            let ExprKind::Lam(_, _, inner) = body_open.kind() else {
                return Err(wf_unsupported(
                    name,
                    "the elaborated function value is not a lambda",
                ));
            };
            body_open = inner.instantiate(&Expr::fvar(*fvar));
        }

        // Rewrite recursive calls `f args` to `rec argᵢ proof args…`,
        // synthesizing a decreasing proof per call site. FAIL CLOSED on any
        // failure.
        let rec_fvar = self.fresh_fvar();
        let cfg = call_sites::RecCallRewrite {
            func_fvar,
            rec_fvar,
            arity,
            measure_expr,
            shape: call_sites::RecShape::SoleParameter {
                param_fvar,
                param_index,
            },
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
            let rel_y_x = Expr::apps(rel.clone(), [Expr::fvar(y_fvar), Expr::fvar(param_fvar)]);
            let c_y = Expr::app(motive.clone(), Expr::fvar(y_fvar));
            let inner = Expr::arrow(rel_y_x, c_y);
            Expr::pi(
                BinderInfo::Default,
                param_ty.clone(),
                inner.abstract_fvar(y_fvar),
            )
        };

        // F := fun (x : α) (rec : …) => fun (others) => transformed
        let fix_body = {
            let mut inner = transformed;
            for index in (0..arity).rev() {
                if index == param_index {
                    continue;
                }
                let (fvar, binder_ty) = &binder_fvars[index];
                inner = Expr::lam(
                    binder_info_at(index),
                    binder_ty.clone(),
                    inner.abstract_fvar(*fvar),
                );
            }
            let with_rec = Expr::lam(
                BinderInfo::Default,
                rec_param_ty,
                inner.abstract_fvar(rec_fvar),
            );
            Expr::lam(
                BinderInfo::Default,
                param_ty.clone(),
                with_rec.abstract_fvar(param_fvar),
            )
        };

        // WellFounded.fix.{u, v} α C rel hwf F
        let wf_fix = Expr::const_(Name::from_string("WellFounded.fix"), vec![u_level, v_level]);
        let fix_app = Expr::apps(wf_fix, [param_ty.clone(), motive, rel, wf_proof, fix_body]);

        // ONE parameter: the fix application IS the definition value, exactly
        // as phase 1 emitted it. Deliberately not eta-expanded — the term
        // shape is pinned by the superproject's recursion probes, and an
        // eta wrapper would be a silent change to a measured artifact.
        if arity == 1 {
            return Ok((func_ty.clone(), fix_app));
        }

        // Wider signature: fun p₀ … pₙ₋₁ => fix … pᵢ (others).
        let mut applied = Expr::app(fix_app, Expr::fvar(param_fvar));
        for (index, (fvar, _)) in binder_fvars.iter().enumerate() {
            if index != param_index {
                applied = Expr::app(applied, Expr::fvar(*fvar));
            }
        }
        let mut value = applied;
        for index in (0..arity).rev() {
            let (fvar, binder_ty) = &binder_fvars[index];
            value = Expr::lam(
                binder_info_at(index),
                binder_ty.clone(),
                value.abstract_fvar(*fvar),
            );
        }

        Ok((func_ty.clone(), value))
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
