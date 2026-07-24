// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term construction for finite case-splitting tactics.
//!
//! Extracted from `finite_cases.rs` for file-size compliance.
//! SOUNDNESS FIX (#2232): These functions construct eliminator proof terms
//! linking original goal metas to sub-goal metas, preventing orphaned
//! metavariables.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError};
use super::interval_cases::make_equality_type;
use crate::unify::MetaState;

/// Construct the eliminator proof term for fin_cases.
///
/// - Bool: `@Bool.casesOn motive h ?m_false ?m_true`
/// - PUnit: `@PUnit.casesOn motive h ?m_unit`
/// - Other types (Fin n, etc.): `Or.rec {a} {b} {motive} (λ _. ?m₀) (λ _. ...) (Classical.em (h = v₀))`
///
/// # Contract
///
/// REQUIRES: `new_goals.len() == inhabitants.len()` for non-Bool/PUnit types
/// REQUIRES: `new_goals.len() == 2` for Bool, `== 1` for PUnit
/// REQUIRES: `hyp` is a local declaration in `goal.local_ctx`
/// ENSURES: On Ok, returns a proof term referencing meta-FVars from `new_goals`
/// ENSURES: The proof term, when type-checked, has type `goal.target`
pub(crate) fn build_fin_cases_proof(
    state: &mut ProofState,
    goal: &Goal,
    hyp: &LocalDecl,
    new_goals: &[Goal],
    inhabitants: &[Expr],
) -> Result<Expr, TacticError> {
    if let ExprKind::Const(name, _) = hyp.ty.kind() {
        let name_str = name.to_string();
        if name_str == "Bool" && new_goals.len() == 2 {
            return build_bool_caseson(state, goal, hyp, new_goals);
        }
        if (name_str == "Unit" || name_str == "unit" || name_str == "PUnit") && new_goals.len() == 1
        {
            return build_punit_caseson(state, goal, hyp, new_goals);
        }
    }
    // Fallback for all types (including Fin n): Or.elim chain
    build_or_elim_chain(
        state,
        &goal.target,
        hyp.fvar,
        &hyp.ty,
        new_goals,
        inhabitants,
        0,
    )
}

/// Build `@Bool.casesOn.{0} {motive} h ?m_false ?m_true`.
///
/// Bool.casesOn : {motive : Bool → Sort u}
///              → (t : Bool) → motive false → motive true → motive t
/// (Lean-faithful MajorAfterMotive ordering: major premise precedes minors)
///
/// REQUIRES: `new_goals.len() == 2` (one per Bool constructor)
/// REQUIRES: `hyp.ty` is `Bool`
/// ENSURES: On Ok, proof term applies `Bool.casesOn` with motive derived from `goal.target`
fn build_bool_caseson(
    _state: &mut ProofState,
    goal: &Goal,
    hyp: &LocalDecl,
    new_goals: &[Goal],
) -> Result<Expr, TacticError> {
    let motive = Expr::lam(
        BinderInfo::Default,
        hyp.ty.clone(),
        goal.target.abstract_fvar(hyp.fvar),
    );

    // Bool has 0 level params; casesOn adds 1 motive universe param.
    // fin_cases always eliminates into Prop (Sort 0), so motive universe = 0.
    // Using mk_const_str creates fresh Param levels that the kernel cannot
    // unify with concrete levels during type checking (universe params are rigid).
    let mut proof = Expr::const_(Name::from_string("Bool.casesOn"), vec![Level::zero()]);
    proof = Expr::app(proof, motive);

    // get_finite_inhabitants returns [true, false].
    // Bool.casesOn expects branches in constructor order: false (0), true (1).
    // SOUNDNESS FIX (#2232): map inhabitants to constructor order.
    let meta_false = Expr::fvar(MetaState::to_fvar(new_goals[1].meta_id));
    let meta_true = Expr::fvar(MetaState::to_fvar(new_goals[0].meta_id));

    // casesOn uses the Lean-faithful MajorAfterMotive ordering:
    // motive → major → minors. The major premise (the value being
    // case-split) comes right after the motive, before the minors.
    proof = Expr::app(proof, Expr::fvar(hyp.fvar));
    proof = Expr::app(proof, meta_false);
    proof = Expr::app(proof, meta_true);

    Ok(proof)
}

/// Build `@PUnit.casesOn.{0, u} {motive} h ?m_unit`.
///
/// PUnit.casesOn : {motive : PUnit → Sort u}
///               → (t : PUnit) → motive PUnit.unit → motive t
/// (Lean-faithful MajorAfterMotive ordering: major premise precedes minors)
///
/// REQUIRES: `new_goals.len() == 1` (PUnit has one constructor)
/// REQUIRES: `hyp.ty` is `PUnit` (or `Unit`/`unit`)
/// ENSURES: On Ok, proof term applies `PUnit.casesOn` with correct universe levels
fn build_punit_caseson(
    _state: &mut ProofState,
    goal: &Goal,
    hyp: &LocalDecl,
    new_goals: &[Goal],
) -> Result<Expr, TacticError> {
    let motive = Expr::lam(
        BinderInfo::Default,
        hyp.ty.clone(),
        goal.target.abstract_fvar(hyp.fvar),
    );

    // PUnit has 1 level param (u); casesOn adds 1 motive universe param.
    // Total: 2 levels = [motive_univ, punit_u].
    // fin_cases always eliminates into Prop (Sort 0), so motive universe = 0.
    // Extract PUnit's universe from the hypothesis type to preserve generality.
    let punit_u = if let ExprKind::Const(_, levels) = hyp.ty.kind() {
        levels.first().cloned().unwrap_or_else(Level::zero)
    } else {
        Level::zero()
    };
    let mut proof = Expr::const_(
        Name::from_string("PUnit.casesOn"),
        vec![Level::zero(), punit_u],
    );
    proof = Expr::app(proof, motive);
    // casesOn uses Lean-faithful MajorAfterMotive: motive → major → minors.
    proof = Expr::app(proof, Expr::fvar(hyp.fvar));
    proof = Expr::app(proof, Expr::fvar(MetaState::to_fvar(new_goals[0].meta_id)));

    Ok(proof)
}

/// Build a right-nested Or.rec chain with Classical.em.
///
/// `Or.rec {a} {b} {motive} (λ _. ?m₀) (λ _. Or.rec ... ?m_{n-1}) (Classical.em P₀)`
/// where Pₖ = `@Eq T h vₖ`.
///
/// Uses Or.rec (not Or.elim, which doesn't exist in the kernel environment).
/// Or.rec is auto-generated when the Or inductive is registered via init_classical.
/// Part of #2154: migrated from Or.elim to Or.rec following wlog/existential pattern.
///
/// The innermost branch uses the last meta directly (without Or.rec),
/// relying on the finite type's exhaustiveness.
///
/// # Contract
///
/// REQUIRES: `idx < new_goals.len()` and `values.len() >= new_goals.len()`
/// REQUIRES: `new_goals[idx].meta_id` is a valid unassigned metavariable
/// REQUIRES: `Classical.em` is available in `state.env()` (via `init_classical`)
/// ENSURES: On Ok, returns an `Or.rec` chain referencing all meta-FVars in `new_goals[idx..]`
/// ENSURES: Base case (`idx == new_goals.len() - 1`) returns the last meta-FVar directly
pub(crate) fn build_or_elim_chain(
    state: &mut ProofState,
    target: &Expr,
    hyp_fvar: FVarId,
    eq_type: &Expr,
    new_goals: &[Goal],
    values: &[Expr],
    idx: usize,
) -> Result<Expr, TacticError> {
    // Base case: last goal — use meta directly
    if idx >= new_goals.len() - 1 {
        return Ok(Expr::fvar(MetaState::to_fvar(new_goals[idx].meta_id)));
    }

    let eq_level = Level::succ(Level::zero());
    let prop = make_equality_type(eq_type, &Expr::fvar(hyp_fvar), &values[idx], eq_level);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let not_prop = Expr::pi(BinderInfo::Default, prop.clone(), false_const);

    let em = Expr::app(state.mk_const_str("Classical.em"), prop.clone());

    // True branch: λ (heq : h = vₖ). ?mₖ
    // Sub-goals preserve the original target for dependent cases (#2480),
    // so the meta type matches the constant motive — no transport needed.
    let true_branch = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::fvar(MetaState::to_fvar(new_goals[idx].meta_id)),
    );

    // False branch: λ (_ : ¬(h = vₖ)). <recurse>
    let rest = build_or_elim_chain(state, target, hyp_fvar, eq_type, new_goals, values, idx + 1)?;
    let false_branch = Expr::lam(BinderInfo::Default, not_prop.clone(), rest);

    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let or_type = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), prop.clone()),
        not_prop.clone(),
    );
    let motive = Expr::lam(BinderInfo::Default, or_type, target.clone());

    let proof = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(or_rec, prop), not_prop), motive),
                true_branch,
            ),
            false_branch,
        ),
        em,
    );

    Ok(proof)
}
