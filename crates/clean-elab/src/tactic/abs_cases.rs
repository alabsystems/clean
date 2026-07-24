// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Absolute value case splitting tactic
//!
//! The `abs_cases` tactic splits on the sign of an expression, creating
//! two proof goals: one where the expression is non-negative and one
//! where it is negative.

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use crate::tactic::tc_app;
use crate::tactic::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

/// Configuration for abs_cases
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AbsCasesConfig {
    /// Name for the non-negative case hypothesis
    pub nonneg_name: String,
    /// Name for the negative case hypothesis
    pub neg_name: String,
}

impl Default for AbsCasesConfig {
    fn default() -> Self {
        AbsCasesConfig {
            nonneg_name: "h_nonneg".to_string(),
            neg_name: "h_neg".to_string(),
        }
    }
}

impl AbsCasesConfig {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_names(nonneg: &str, neg: &str) -> Self {
        AbsCasesConfig {
            nonneg_name: nonneg.to_string(),
            neg_name: neg.to_string(),
        }
    }
}

/// Tactic: abs_cases
///
/// Splits on the absolute value of an expression, creating two cases:
/// 1. When the expression is non-negative (x ≥ 0), where |x| = x
/// 2. When the expression is negative (x < 0), where |x| = -x
///
/// This is useful for proving properties about absolute values by
/// case analysis.
///
/// # Example
/// ```text
/// -- Goal: |x| ≥ 0
/// abs_cases x
/// -- Case 1: h_nonneg : x ≥ 0 ⊢ x ≥ 0
/// -- Case 2: h_neg : x < 0 ⊢ -x ≥ 0
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `var_name` identifies a numeric-typed variable (Int, Real, Rat, Float, Complex)
///   in the current goal's local context.
/// ENSURES: On `Ok(())`, the current goal is replaced by two sub-goals: one with
///   `h_nonneg : var ≥ 0` and one with `h_neg : ¬(var ≥ 0)` in their local contexts.
/// ENSURES: The proof term uses `Or.rec` over `Classical.em (var ≥ 0)`.
pub fn abs_cases(state: &mut ProofState, var_name: &str) -> TacticResult {
    abs_cases_with_config(state, var_name, AbsCasesConfig::new())
}

/// abs_cases with custom configuration
///
/// REQUIRES: `state.goals` is non-empty; `var_name` identifies a numeric-typed variable.
/// ENSURES: On `Ok(())`, two sub-goals are created with hypothesis names from `config`.
/// ENSURES: Returns `Err(InvalidTarget)` for non-numeric types; `Err(HypothesisNotFound)`
///   if the variable is missing.
pub fn abs_cases_with_config(
    state: &mut ProofState,
    var_name: &str,
    config: AbsCasesConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the variable in context
    let var_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == var_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(var_name.to_string()))?;

    // Check if the type is numeric (Int, Real, Rat, etc.)
    let is_numeric = is_numeric_type(&var_decl.ty);
    if !is_numeric {
        return Err(TacticError::InvalidTarget {
            tactic: "abs_cases".into(),
            detail: format!(
                "{var_name} has type {:?}, expected numeric type",
                var_decl.ty
            ),
        });
    }

    let var_expr = Expr::fvar(var_decl.fvar);
    let var_ty = var_decl.ty.clone();

    // Create the two cases using by_cases
    // Case 1: var ≥ 0
    let zero = make_zero_for_type(&var_ty, state);
    let ge_zero = make_ge_expr(&var_expr, &zero, &var_ty, state);

    // Split into two goals
    let original_target = goal.target.clone();
    let local_ctx = goal.local_ctx.clone();

    // ONE shared fvar for the hypothesis of BOTH branches (B103). The two
    // branch lambdas are PARALLEL binders — each is its own `λ h => ?meta`
    // directly under `Or.rec`, both at binder depth 1. The scope checker
    // (`close_fvars::assignment_scope_violation`) and `close_fvars` both use
    // the positional model `(n - base) < depth`, so a SECOND fresh fvar (at
    // offset 1) can never be legal under a depth-1 binder: minting two fvars
    // made the negative branch's meta capture an out-of-scope local
    // (`nested metavariable … captures out-of-scope local … at binder depth
    // 1`). Because the branches are disjoint scopes (a goal is solved before
    // the next), both `h` binders safely share one id — exactly the
    // `by_cases` / `split_ite` pattern (existential.rs / connective.rs).
    let hyp_fvar = state.fresh_fvar();
    let nonneg_fvar = hyp_fvar;
    let neg_fvar = hyp_fvar;

    // Case 1: x ≥ 0
    let mut case1_ctx = local_ctx.clone();
    case1_ctx.push(LocalDecl {
        fvar: nonneg_fvar,
        name: config.nonneg_name,
        ty: ge_zero.clone(),
        value: None,
    });

    // Case 2: ¬(x ≥ 0) — constructed as Pi(ge_zero, False) to match
    // Classical.em's structural output: Or P (P → False), NOT Or P (Not P).
    // Part of #2154: the App(Not, P) form caused a structural mismatch with
    // Classical.em, making the Or.rec proof ill-typed for close_goal.
    let false_const = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
    let not_ge_zero_ty = Expr::pi(
        clean_kernel::BinderInfo::Default,
        ge_zero.clone(),
        false_const,
    );
    let mut case2_ctx = local_ctx;
    case2_ctx.push(LocalDecl {
        fvar: neg_fvar,
        name: config.neg_name,
        ty: not_ge_zero_ty.clone(),
        value: None,
    });

    // Create fresh metas in the exact branch contexts.
    let case1_meta = state.fresh_meta_in_context(original_target.clone(), &case1_ctx);
    let case2_meta = state.fresh_meta_in_context(original_target.clone(), &case2_ctx);

    // Create the two new goals
    let case1_goal = Goal {
        meta_id: case1_meta,
        target: original_target.clone(),
        local_ctx: case1_ctx,
        tag: None,
    };

    let case2_goal = Goal {
        meta_id: case2_meta,
        target: original_target.clone(),
        local_ctx: case2_ctx,
        tag: None,
    };

    // Build proof: @Or.rec {a} {b} {motive} (λ h, ?m1) (λ h, ?m2) (Classical.em P)
    //
    // Or.rec : {a b : Prop} → {motive : Or a b → Sort u} →
    //          (a → motive (Or.inl ...)) → (b → motive (Or.inr ...)) →
    //          (t : Or a b) → motive t
    // Classical.em : (p : Prop) → p ∨ ¬p
    //
    // Uses Or.rec (not Or.elim, which doesn't exist in the kernel environment).
    // Or.rec is auto-generated when the Or inductive is registered via init_classical.
    // Part of #2154: migrated from Or.elim to Or.rec following wlog/existential pattern.
    let em_app = Expr::app(state.mk_const_str("Classical.em"), ge_zero.clone());
    let case1_meta_expr = Expr::fvar(MetaState::to_fvar(case1_meta));
    let case2_meta_expr = Expr::fvar(MetaState::to_fvar(case2_meta));

    // Or.rec has 0 universe params (Prop-valued inductive, elim-only-at-zero).
    let or_rec = Expr::const_(clean_kernel::name::Name::from_string("Or.rec"), vec![]);

    // Motive: λ _ : Or (x ≥ 0) ¬(x ≥ 0) => target
    let or_type = Expr::app(
        Expr::app(
            Expr::const_(clean_kernel::name::Name::from_string("Or"), vec![]),
            ge_zero.clone(),
        ),
        not_ge_zero_ty.clone(),
    );
    let motive = Expr::lam(
        clean_kernel::BinderInfo::Default,
        or_type,
        original_target.clone(),
    );

    // Branch bodies abstract the shared hypothesis fvar (mirrors `by_cases`):
    // when a branch meta's solution mentions its hypothesis, `close_fvars`
    // converts the shared id to BVar(0) under this binder.
    let branch_pos = Expr::lam(
        clean_kernel::BinderInfo::Default,
        ge_zero.clone(),
        case1_meta_expr.abstract_fvar(nonneg_fvar),
    );
    let branch_neg = Expr::lam(
        clean_kernel::BinderInfo::Default,
        not_ge_zero_ty.clone(),
        case2_meta_expr.abstract_fvar(neg_fvar),
    );

    // Or.rec {a} {b} {motive} branch_pos branch_neg em_p
    let proof = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(or_rec, ge_zero.clone()), not_ge_zero_ty),
                    motive,
                ),
                branch_pos,
            ),
            branch_neg,
        ),
        em_app,
    );

    // Part of #2154: checked close_goal type-checks the Or.rec proof.
    // Proof is @Or.rec {ge_zero} {¬ge_zero} {motive} (λ h, ?m1) (λ h, ?m2) (Classical.em ge_zero).
    // Requires env with Or.rec (init_classical), GE.ge (init_ge), instLEInt (init_int_ord).
    state.close_goal(&goal, proof)?;

    state.goals.push_front(case2_goal);
    state.goals.push_front(case1_goal);

    Ok(())
}

/// Check if a type is numeric (Int, Real, Rat, etc.)
///
/// REQUIRES: `ty` is a well-formed type expression.
/// ENSURES: Returns `true` only for `Const` expressions named Int, Real, Rat, Float, or Complex.
pub(crate) fn is_numeric_type(ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            matches!(s.as_str(), "Int" | "Real" | "Rat" | "Float" | "Complex")
        }
        _ => false,
    }
}

/// Create a zero constant for the given numeric type
///
/// REQUIRES: `ty` is a well-formed type expression.
/// ENSURES: For `Const(T, _)` types, returns `Const("{T}.zero")`; otherwise
///   returns `Const("OfNat.ofNat")` as a fallback.
pub(crate) fn make_zero_for_type(ty: &Expr, state: &mut ProofState) -> Expr {
    match ty.kind() {
        ExprKind::Const(name, _) => {
            let type_name = name.to_string();
            state.mk_const_str(&format!("{type_name}.zero"))
        }
        _ => state.mk_const_str("OfNat.ofNat"),
    }
}

/// Create a >= expression: `@GE.ge.{0} ty inst lhs rhs`
///
/// GE.ge takes an LE instance (GE is defined via LE).
/// Part of #2078: previously only produced `GE.ge lhs rhs` (missing type + instance).
/// Part of #2154: use Level::zero() instead of fresh param for GE.ge.{u},
/// since all supported numeric types (Int, Real, Rat) are Type 0.
/// Fresh params cause universe TypeMismatch in close_goal's infer_type.
///
/// REQUIRES: `lhs`/`rhs` are operand expressions; `ty` is their shared type.
/// ENSURES: Returns the fully-applied 4-arg form `GE.ge.{0} ty inst lhs rhs` where
///   `inst` is resolved via `rel_inst_for_type` for the actual type.
/// ENSURES: Type and instance arguments are always present (no missing implicit args).
pub(crate) fn make_ge_expr(lhs: &Expr, rhs: &Expr, ty: &Expr, _state: &mut ProofState) -> Expr {
    // GE.ge uses the LE instance — resolve from the actual type (Int, Real, etc.)
    let inst = tc_app::rel_inst_for_type(ty, "GE.ge");
    // GE.ge.{u} : {alpha : Type u} → [LE alpha] → alpha → alpha → Prop
    // All numeric types are Type 0, so u = 0.
    let ge_const = Expr::const_(
        clean_kernel::name::Name::from_string("GE.ge"),
        vec![clean_kernel::Level::zero()],
    );
    tc_app::mk_tc_rel(ge_const, ty.clone(), inst, lhs.clone(), rhs.clone())
}
