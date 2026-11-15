// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! choose tactic: extract witness from an existential hypothesis.

use super::names::local_name_matches;
use clean_parser::SurfaceName;

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

use super::super::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::util::{apply_predicate, try_extract_exists};

/// Configuration for choose tactic
#[derive(Debug, Clone, Default)]
pub struct ChooseConfig {
    /// Names to use for the witness and proof
    pub witness_name: Option<SurfaceName>,
    pub proof_name: Option<SurfaceName>,
}

impl ChooseConfig {
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_witness_name(mut self, name: &SurfaceName) -> Self {
        self.witness_name = Some(name.clone());
        self
    }

    #[must_use]
    pub fn with_proof_name(mut self, name: &SurfaceName) -> Self {
        self.proof_name = Some(name.clone());
        self
    }
}

/// choose tactic: extract witness from an existential hypothesis
///
/// Given a hypothesis `h : exists x, P x`, the `choose` tactic produces
/// a witness `x` and a proof `hx : P x`.
///
/// # Example
/// ```text
/// -- h : exists n : Nat, n > 0
/// choose n hn using h
/// -- Now have n : Nat and hn : n > 0
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a local hypothesis whose type is `Exists α p`
/// ENSURES: On Ok, the current goal is closed via `Exists.elim` and replaced by one continuation goal
/// ENSURES: On Ok, the continuation goal removes `hyp_name` and adds witness/proof locals named `witness_name` and `proof_name`
/// ENSURES: On Ok, the witness local has type `α` and the proof local has type `p witness`
/// ENSURES: On Err(HypothesisNotFound | GoalMismatch), the goal queue is not advanced
pub fn choose(
    state: &mut ProofState,
    hyp_name: &SurfaceName,
    witness_name: &SurfaceName,
    proof_name: &SurfaceName,
) -> TacticResult {
    for name in [hyp_name, witness_name, proof_name] {
        super::names::require_binding_name(name, "choose")?;
    }
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Extract all needed data from the goal first (before mutations)
    let (hyp_type, hyp_fvar, goal_target, goal_id, original_ctx, case_binders) = {
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?;

        // Find the hypothesis
        let hyp_idx = goal
            .local_ctx
            .iter()
            .rposition(|d| local_name_matches(&d.name, hyp_name))
            .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

        (
            goal.local_ctx[hyp_idx].ty.clone(),
            goal.local_ctx[hyp_idx].fvar,
            goal.target.clone(),
            goal.meta_id,
            goal.local_ctx.clone(),
            goal.case_binders.clone(),
        )
    };

    // Check if the hypothesis is an existential: exists x, P x
    // Exists is encoded as: Exists alpha (lambda x, P x) or Exists.{u} alpha P
    let Some((domain, predicate)) = try_extract_exists(&hyp_type) else {
        return Err(TacticError::GoalMismatch(format!(
            "choose: hypothesis '{hyp_name}' is not an existential (exists)"
        )));
    };

    // Create goal object for close_goal (needs original ctx before modification).
    // Part of #2154 Track 3 Option B: migrate from metas.assign bypass to checked
    // close_goal by supplying all implicit arguments to Exists.elim.
    // (Constructed before minting so the fvar ids below can derive from it.)
    let goal_for_close = Goal {
        case_binders: case_binders.clone(),
        meta_id: goal_id,
        target: goal_target.clone(),
        local_ctx: original_ctx.clone(),
        tag: None,
    };

    // GOAL-DERIVED minting (see existential.rs by_cases): both locals reach the
    // continuation subgoal's context and are bound by the two nested lambdas of
    // the `Exists.elim` continuation (witness at depth 1, proof at depth 2), so
    // they must carry ids `base` and `base + 1` of the destination meta's
    // positional window — the global cursor drifts past that window whenever
    // anything minted since the goal's meta was created.
    let (witness_fvar, proof_fvar) = {
        let base = state.goal_binder_base(&goal_for_close);
        state.next_fvar = state.next_fvar.max(base + 2);
        (FVarId::new(base), FVarId::new(base + 1))
    };

    // Create the witness local declaration
    let witness_decl = LocalDecl {
        binder_info: Default::default(),
        fvar: witness_fvar,
        name: witness_name.clone(),
        ty: domain.clone(),
        value: None,
    };

    // Apply the predicate to the witness to get the type of the proof
    let proof_type = apply_predicate(&predicate, Expr::fvar(witness_fvar));

    let proof_decl = LocalDecl {
        binder_info: Default::default(),
        fvar: proof_fvar,
        name: proof_name.clone(),
        ty: proof_type,
        value: None,
    };

    // Create the continuation goal FIRST so we can reference its meta in the proof term.
    // (Creating the fresh meta after building the proof term caused a circular
    // assignment: goal_id was assigned to a term containing fvar(goal_id).)
    let mut new_ctx = original_ctx;
    new_ctx.push(witness_decl);
    new_ctx.push(proof_decl);
    // Remove the original existential hypothesis
    new_ctx.retain(|d| d.fvar != hyp_fvar);

    let new_meta_id = state.fresh_meta_in_context(goal_target, &new_ctx);
    let new_goal = Goal {
        case_binders,
        meta_id: new_meta_id,
        target: goal_for_close.target.clone(),
        local_ctx: new_ctx,
        tag: None,
    };

    // Build the proof term using @Exists.elim with ALL implicit arguments supplied.
    // Exists.elim : {α : Sort u} → {p : α → Prop} → {b : Prop} →
    //               (∃ x, p x) → (∀ x, p x → b) → b
    // Supply {α}=domain, {p}=predicate, {b}=goal_target explicitly so that
    // close_goal's infer_type can process the proof term without implicit insertion.
    let cont_fvar = Expr::fvar(MetaState::to_fvar(new_meta_id));
    // Inner lambda binder type: p(x) where x is the outer lambda's bound variable.
    // In de Bruijn: App(p, BVar(0)) with BVar(0) referencing the outer binder.
    let pred_applied = Expr::app(predicate.clone(), Expr::bvar(0));
    let mut elim = Expr::const_(Name::from_string("Exists.elim"), vec![Level::Zero]);
    elim = Expr::app(elim, domain.clone()); // {α} : Sort 0
    elim = Expr::app(elim, predicate); // {p} : α → Prop
    elim = Expr::app(elim, goal_for_close.target.clone()); // {b} : Prop
    elim = Expr::app(elim, Expr::fvar(hyp_fvar)); // h : ∃ x, p x
    elim = Expr::app(
        elim,
        Expr::lam(
            BinderInfo::Default,
            domain,
            Expr::lam(BinderInfo::Default, pred_applied, cont_fvar),
        ),
    ); // continuation : ∀ x, p x → b

    // Close the goal with type-checked proof (bypass ratchet 3→2).
    state.close_goal(&goal_for_close, elim)?;

    // Push the continuation goal
    state.invalidate_tc_cache();
    state.goals.push_front(new_goal);

    Ok(())
}

/// Simple choose with default names
///
/// # Contract
///
/// REQUIRES: same as `choose`
/// ENSURES: Behaves like `choose(state, hyp_name, "{hyp_name}_witness", "{hyp_name}_spec")`
pub fn choose_simple(state: &mut ProofState, hyp_name: &SurfaceName) -> TacticResult {
    // Generate default names based on hypothesis name
    let witness_name = super::names::generated_suffix(hyp_name, "_witness");
    let proof_name = super::names::generated_suffix(hyp_name, "_spec");
    choose(state, hyp_name, &witness_name, &proof_name)
}
