// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extensionality tactics
//!
//! This module provides tactics for proving equality via extensionality principles:
//! - `funext` - Function extensionality: proves `f = g` by showing `∀ x, f x = g x`
//! - `propext` - Propositional extensionality: proves `P = Q` by showing `P ↔ Q`
//! - `set_ext` - Set extensionality: proves `s = t` by showing `∀ x, x ∈ s ↔ x ∈ t`
//! - `quot_ext` - Quotient extensionality via induction principles

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::{apply, collect_consts, match_equality, Goal, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

// ============================================================================
// Function Extensionality
// ============================================================================

/// Apply function extensionality.
///
/// For a goal of the form `f = g` where `f g : A → B`,
/// changes the goal to `∀ x, f x = g x`.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, the current goal is an equality whose type is a `Pi`
///   (function) type; `var_name` names the introduced pointwise binder.
/// ENSURES: On `Ok(())`, the original equality goal is closed with a `funext`
///   proof and replaced by a pointwise equality subgoal.
/// ENSURES: On `Ok(())`, the generated subgoal reuses the original local context
///   and `intro` is applied to expose the fresh argument.
pub fn funext(state: &mut ProofState, var_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // Check if target is an equality
    let (ty, lhs, rhs, _levels) = match_equality(&target)?;

    // Check if the type is a function type
    let (binder_info, dom, cod) = match ty.kind() {
        ExprKind::Pi(bi, binder_type, body) => {
            (*bi, binder_type.as_ref().clone(), body.as_ref().clone())
        }
        _ => {
            return Err(TacticError::GoalMismatch(
                "funext: equality is not between functions".to_string(),
            ))
        }
    };

    // Infer the result type (codomain applied to the argument).
    //
    // FVar-id ↔ binder-depth discipline (#2204): the pointwise proof lands as
    // `funext … (fun x => <proof of f x = g x>)`, so the lambda that binds `x`
    // sits at binder depth 1 in the assembled term. For `close_fvars` to convert
    // `x` back to `BVar(0)` it must carry id `base + 0`, which is exactly the
    // value `next_fvar` holds *now* — the id the trailing `intro` will allocate.
    // Allocating a throwaway FVar here (used only to WHNF the codomain for
    // universe-level inference, never stored in the proof term) would bump
    // `next_fvar` and push `intro`'s `x` one past its binder depth, leaving it
    // unconvertible → `closed_proof()` fails closed → `ProofNotProduced`. So we
    // snapshot `next_fvar`, use the placeholder purely for inference, then
    // restore it so `intro` gets the depth-aligned id.
    let saved_next_fvar = state.next_fvar;
    let fvar_expr = Expr::fvar(state.fresh_fvar());
    let result_ty = state.whnf(&goal, &cod.clone().instantiate(&fvar_expr));

    // Compute universe levels for Eq and funext from the actual types.
    // Domain sort → u, codomain sort → v, so Eq.{v} and funext.{u, v}.
    let dom_sort = state.infer_type(&goal, &dom).ok();
    let result_sort = state.infer_type(&goal, &result_ty).ok();
    let (eq_expr, funext_expr) = match (&dom_sort, &result_sort) {
        (Some(ds), Some(rs)) => match (ds.kind(), rs.kind()) {
            (ExprKind::Sort(u), ExprKind::Sort(v)) => (
                Expr::const_(Name::from_string("Eq"), vec![v.clone()]),
                Expr::const_(Name::from_string("funext"), vec![u.clone(), v.clone()]),
            ),
            _ => (state.mk_const_str("Eq"), state.mk_const_str("funext")),
        },
        _ => (state.mk_const_str("Eq"), state.mk_const_str("funext")),
    };

    let x_bv = Expr::bvar(0);
    let new_lhs = Expr::app(lhs.clone(), x_bv.clone());
    let new_rhs = Expr::app(rhs.clone(), x_bv);
    let pointwise_eq = Expr::app(Expr::app(Expr::app(eq_expr, cod.clone()), new_lhs), new_rhs);
    let new_target = Expr::pi(binder_info, dom.clone(), pointwise_eq);

    let new_meta = state.fresh_meta(new_target.clone());

    // Build the proof term using funext:
    // funext : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
    //          (∀ x, f x = g x) → f = g
    //
    // Part of #2232: previously passed ty (full Pi type) as {α} instead of dom,
    // omitted {β} entirely, and used Type as the lambda domain instead of dom.
    let pointwise_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta)));

    // {β} : α → Sort v — wrap the Pi codomain in a lambda to make a function
    let beta = Expr::lam(binder_info, dom.clone(), cod);

    // Apply funext {α} {β} {f} {g} h — all 5 args (4 implicit + 1 explicit)
    let mut proof = funext_expr;
    proof = Expr::app(proof, dom.clone()); // {α} = domain type
    proof = Expr::app(proof, beta); // {β} = codomain function
    proof = Expr::app(proof, lhs.clone()); // {f}
    proof = Expr::app(proof, rhs.clone()); // {g}
    proof = Expr::app(proof, pointwise_meta); // h : ∀ x, f x = g x

    // Reify the pointwise continuation as its own Pi goal so close_goal checks
    // a direct metavariable argument instead of a binder-local lambda body.
    state.close_goal(&goal, proof)?;

    state.goals.push_front(Goal {
        meta_id: new_meta,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    });

    // Restore `next_fvar` to its pre-inference value so the `intro` below
    // allocates `x` at the id matching the binder depth of the assembled
    // `funext … (fun x => …)` term (see the snapshot above). The intervening
    // `metas.fresh` allocates a *metavariable* id (not an FVar), and
    // `close_goal` / `whnf` / `infer_type` only borrow `&self`, so no other
    // FVar was minted between the snapshot and here — restoring is sound and
    // keeps ids contiguous for `close_fvars`. Nested calls (e.g. `funext a b`)
    // stay aligned because each call restores to the `next_fvar` left by the
    // previous `intro`, so successive binders get `base, base+1, …`.
    state.next_fvar = saved_next_fvar;
    super::proof_term::intro(state, var_name)?;
    Ok(())
}

// ============================================================================
// Propositional Extensionality
// ============================================================================

/// Apply propositional extensionality.
///
/// For a goal of the form `P = Q` where `P Q : Prop`,
/// changes the goal to `P ↔ Q`.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, the current goal is an equality between propositions.
/// ENSURES: On `Ok(())`, the original goal is closed with `propext` and the new
///   front goal target is `Iff lhs rhs`.
/// ENSURES: On `Ok(())`, the generated goal preserves the original local context.
pub fn propext(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // Check if target is an equality of propositions
    let (ty, lhs, rhs, _levels) = match_equality(&target)?;

    // Check that the type is Prop (Sort(0))
    match ty.kind() {
        ExprKind::Sort(level) if level.is_zero() => {}
        _ => {
            return Err(TacticError::GoalMismatch(
                "propext: equality is not between propositions".to_string(),
            ))
        }
    }

    // Create new goal: P ↔ Q
    let iff_type = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lhs.clone()),
        rhs.clone(),
    );

    let new_meta = state.fresh_meta(iff_type.clone());
    let new_goal = Goal {
        meta_id: new_meta,
        target: iff_type,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    // Build proof term: `propext {a} {b} ?m` where `?m : a ↔ b` is the new goal.
    //
    // Clean's `propext` is the faithful `Iff`-shaped axiom
    // `{a b : Prop} → (a ↔ b) → a = b` (see
    // `clean-kernel/src/env/logic.rs::init_propext`), so it takes the `Iff` proof
    // directly. An earlier change (#2232) applied it to four arguments
    // `{a}{b}(a→b)(b→a)` by extracting `Iff.mp`/`Iff.mpr`; once `propext` was made
    // Iff-shaped, that fourth application landed on the already-`Eq`-typed result
    // and the kernel rejected it (`NotAFunction` on `a = b`).
    let meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta)));

    let mut proof = Expr::const_(Name::from_string("propext"), vec![]);
    proof = Expr::app(proof, lhs.clone()); // {a}
    proof = Expr::app(proof, rhs.clone()); // {b}
    proof = Expr::app(proof, meta_expr); // h : a ↔ b

    // The meta-FVar for the `a ↔ b` goal appears directly as `propext`'s argument.
    // Part of #2154 Tier 2 Wave 1: migrated to checked close_goal.
    state.close_goal(&goal, proof)?;

    state.goals.push_front(new_goal);
    Ok(())
}

// ============================================================================
// Set Extensionality
// ============================================================================

/// Set extensionality.
///
/// For a goal of the form `s = t` where `s t : Set α`,
/// changes the goal to `∀ x, x ∈ s ↔ x ∈ t`.
///
/// Part of #2232: rewrote proof construction. Previously referenced nonexistent
/// `Set.ext` constant, used metas.fresh instead of fresh_fvar for the x variable,
/// and had FVars in Pi body instead of bvar(0). Now composes funext + propext.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, the current goal is an equality between set/predicate
///   expressions with an inferable element type; `var_name` names the introduced
///   element binder.
/// ENSURES: On `Ok(())`, the original equality goal is closed with a
///   `funext`/`propext` proof and replaced by a membership-iff subgoal.
/// ENSURES: On `Ok(())`, the generated subgoal inherits the original local
///   context and `intro` is applied to expose the element argument.
pub fn set_ext(state: &mut ProofState, var_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // Check if target is an equality
    let (ty, lhs, rhs, _levels) = match_equality(&target)?;

    // Check if this is a Set type (Set α = α → Prop)
    // Sets are represented as functions to Prop
    let is_set_type = match ty.kind() {
        ExprKind::App(f, _) => {
            if let ExprKind::Const(name, _) = f.kind() {
                name == &Name::from_string("Set")
            } else {
                false
            }
        }
        ExprKind::Pi(_, _, ret) => {
            // α → Prop is represented as Pi type
            matches!(ret.kind(), ExprKind::Sort(l) if l.is_zero())
        }
        _ => false,
    };

    if !is_set_type {
        // Try to proceed anyway - the type might be definitionally equal to Set
    }

    // Extract the element type
    let elem_type = match ty.kind() {
        ExprKind::App(_, arg) => arg.as_ref().clone(),
        ExprKind::Pi(_, ty, _) => ty.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "set_ext: cannot determine element type".to_string(),
            ))
        }
    };

    // Build goal target: ∀ (x : α), Iff (s x) (t x) — using bvar(0) for bound var
    let x_bv = Expr::bvar(0);
    let mem_lhs_bv = Expr::app(lhs.clone(), x_bv.clone());
    let mem_rhs_bv = Expr::app(rhs.clone(), x_bv.clone());
    let iff_body = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), mem_lhs_bv),
        mem_rhs_bv,
    );
    let new_target = Expr::pi(BinderInfo::Default, elem_type.clone(), iff_body);

    // Create meta for the goal (type: ∀ x, Iff (s x) (t x))
    let new_meta = state.fresh_meta(new_target.clone());
    let meta_fvar = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta)));
    let new_goal = Goal {
        meta_id: new_meta,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    // Build composite proof: funext {α} {β} {s} {t} (λ (x : α), propext ... )
    //
    // Inside the lambda, x = bvar(0), and ?m applied to bvar(0) gives Iff (s x) (t x),
    // which `propext` turns into `s x = t x` directly.
    let x_in_lam = Expr::bvar(0);
    let s_x = Expr::app(lhs.clone(), x_in_lam.clone());
    let t_x = Expr::app(rhs.clone(), x_in_lam.clone());
    let meta_x = Expr::app(meta_fvar, x_in_lam); // ?m x : Iff (s x) (t x)

    // propext {s x} {t x} (?m x) : s x = t x
    //
    // Clean's `propext` is the faithful `Iff`-shaped axiom
    // `{a b : Prop} → (a ↔ b) → a = b` (see
    // `clean-kernel/src/env/logic.rs::init_propext`), so apply it to the `Iff`
    // proof `?m x` directly. Extracting `Iff.mp`/`Iff.mpr` and passing both (as
    // before) produced an ill-typed term — `NotAFunction` on `s x = t x` — because
    // the fourth application landed on the already-`Eq`-typed result.
    let mut propext_body = Expr::const_(Name::from_string("propext"), vec![]);
    propext_body = Expr::app(propext_body, s_x);
    propext_body = Expr::app(propext_body, t_x);
    propext_body = Expr::app(propext_body, meta_x);

    // λ (x : α), propext_body
    let h_fun = Expr::lam(BinderInfo::Default, elem_type.clone(), propext_body);

    // {β} : α → Sort v — constant function returning Prop
    let beta = Expr::lam(BinderInfo::Default, elem_type.clone(), Expr::prop());

    // funext {α} {β} {s} {t} h — all 5 args.
    // close_goal requires concrete universe instantiation here; fresh level
    // params on funext do not unify against the element sort during infer_type.
    let funext = state
        .infer_type(&goal, &elem_type)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(u) => Some(Expr::const_(
                Name::from_string("funext"),
                vec![u.clone(), Level::succ(Level::zero())],
            )),
            _ => None,
        })
        .unwrap_or_else(|| state.mk_const_str("funext"));
    let mut proof = funext;
    proof = Expr::app(proof, elem_type.clone()); // {α}
    proof = Expr::app(proof, beta); // {β} = λ _ => Prop
    proof = Expr::app(proof, lhs); // {f} = s
    proof = Expr::app(proof, rhs); // {g} = t
    proof = Expr::app(proof, h_fun); // h : λ x, s x = t x

    // The continuation meta already has the Pi type `∀ x, s x ↔ t x`, so the
    // lambda only applies the meta to its binder instead of embedding a binder-
    // dependent meta body. This is checkable through close_goal. (#2154)
    state.close_goal(&goal, proof)?;

    // Push the Pi goal; auto-intro to match expected behavior (set_ext introduces x)
    state.goals.push_front(new_goal);
    super::proof_term::intro(state, var_name)?;

    Ok(())
}

// ============================================================================
// Quotient Extensionality
// ============================================================================

/// Quotient extensionality (for quotient types).
///
/// For a goal involving quotient equality, introduces the lifting lemma.
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: On `Ok(())`, the current goal mentions `Quot`/`Quotient` and the
///   environment contains `Quot.ind`.
/// ENSURES: On `Ok(())`, delegates to [`apply`] with `Quot.ind`, leaving any
///   subgoals produced by `apply` at the front of the goal stack.
/// ENSURES: Returns `Err(GoalMismatch)` for non-quotient goals and
///   `Err(EnvironmentMissing)` when `Quot.ind` is unavailable.
pub fn quot_ext(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // Check if target involves Quotient
    let has_quotient = collect_consts(&target)
        .iter()
        .any(|n| n.to_string().contains("Quotient") || n.to_string().contains("Quot"));

    if !has_quotient {
        return Err(TacticError::GoalMismatch(
            "quot_ext: goal does not involve quotient types".to_string(),
        ));
    }

    // Try to apply Quotient.ind or Quot.ind
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::param(Name::from_string("u"))],
    );
    if state
        .env
        .get_const(&Name::from_string("Quot.ind"))
        .is_some()
    {
        // Apply Quot.ind
        apply(state, quot_ind)?;
        return Ok(());
    }

    Err(TacticError::EnvironmentMissing {
        constant: "Quot.ind".to_string(),
    })
}
