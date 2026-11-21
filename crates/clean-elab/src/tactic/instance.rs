// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance tactics: letI, haveI, inferI
//!
//! These tactics introduce local typeclass instances that are available
//! for resolution within the current goal's scope.

use crate::instances::{extract_class_app, DEFAULT_PRIORITY};
use crate::tactic::{have_, let_, Goal, ProofState, TacticError, TacticResult};
use clean_kernel::{Expr, ExprKind, FVarId, Name};

impl ProofState {
    /// Synthesize `class_ty` the way Lean's `synthInstance` does inside the goal:
    /// the goal's class-typed locals are local instances, tried first at every
    /// sub-goal (a `∀`-typed local and a `DecidableEq` local included), and the
    /// file's instance state applies — an `attribute [-instance]` erasure,
    /// `local instance`s of an open section, `scoped instance`s of an open
    /// namespace.
    ///
    /// The optional namespace is open only while this query runs.
    /// ENSURES: on `Some(s)`, `s` mentions no unassigned metavariable.
    pub(super) fn synthesize_class_in_goal(
        &self,
        goal: &Goal,
        class_ty: &Expr,
        open_namespace: Option<&Name>,
    ) -> Option<Expr> {
        let scope = crate::infer::TacticInstanceScope {
            instances: self.instances.as_ref(),
            namespace_state: self.namespace_state(),
            visibility: self.instance_visibility.as_deref(),
            rigid_levels: self.metas.rigid_level_params_snapshot(),
            locals: self
                .meta_scope_for_context(&goal.local_ctx)
                .into_iter()
                .map(|(name, fvar, ty)| {
                    let ty = self.metas.instantiate(&ty);
                    (name, fvar, ty)
                })
                .collect(),
            next_fvar: self.next_fvar,
            level_mint: self.level_mint.clone(),
        };
        crate::ElabCtx::synthesize_in_tactic_scope(&self.env, &scope, class_ty, open_namespace)
    }
}

/// Introduce a transparent, goal-local definition and inline it in the final term.
/// Goal-scoped typeclass search already considers class-typed local declarations.
pub fn let_i(
    state: &mut ProofState,
    name: &clean_parser::SurfaceName,
    ty: Expr,
    value: Expr,
) -> TacticResult {
    super::have_let::let_binding(state, name, ty, Some(value), true)
}

/// Introduce a local instance hypothesis for the current goal.
///
/// `haveI` introduces a local instance hypothesis with a proof obligation.
/// It's like `have` but registers the result as an instance for typeclass
/// resolution.
///
/// # Example
/// ```text
/// -- Goal: some goal requiring Decidable P
/// haveI : Decidable P := by decide
/// -- Creates subgoal for Decidable P, then uses result as instance
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
///
/// REQUIRES: At least one goal exists in `state`.
/// ENSURES: On `Ok`, a proof obligation subgoal for `ty` is created via `have_`.
/// ENSURES: If `ty` is a typeclass application and an instance table exists,
///   the hypothesis fvar is registered as an instance for that class.
pub fn have_i(state: &mut ProofState, name: &clean_parser::SurfaceName, ty: Expr) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Extract class name for instance registration before ty is moved
    let class_info = extract_class_app(&ty);
    let ty_for_inst = ty.clone();

    // Capture the fvar ID that have_() will allocate for the local hypothesis.
    // have_()'s no-proof path mints GOAL-DERIVED (see existential.rs by_cases),
    // so predict the same id from the same goal — nothing mutates `state`
    // between here and the mint, so the prediction is exact. Predicting from
    // the raw cursor would desync whenever the cursor sits above the goal's
    // binder base.
    let inst_fvar = {
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
        FVarId::new(state.goal_binder_base(goal))
    };

    // haveI creates a new goal for the instance, then adds it to context
    have_(state, name, ty, None)?;

    // Register in instance table if available (#2233)
    if let Some((class_name, _)) = class_info {
        if let Some(instances) = state.instances.as_mut() {
            let inst_expr = Expr::from_kind(ExprKind::FVar(inst_fvar));
            instances.add_instance(
                name.name().clone(),
                class_name,
                inst_expr,
                ty_for_inst,
                DEFAULT_PRIORITY,
            );
        }
    }

    Ok(())
}

/// Introduce an instance using inference.
///
/// `inferI` attempts to synthesize an instance using typeclass resolution
/// and adds it to the local context.
///
/// # Example
/// ```text
/// -- In a context where Decidable P can be inferred
/// inferI (inst : Decidable P)
/// -- inst is now available
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if the instance cannot be inferred
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: An instance table must be present in `state.instances`.
/// ENSURES: On `Ok`, the resolved instance value is added to the local context
///   as a let-binding and registered in the instance table.
/// ENSURES: On `Err(InstanceSynthesisFailed)`, no matching instance was found.
pub fn infer_i(state: &mut ProofState, name: &clean_parser::SurfaceName, ty: Expr) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Extract class name for instance registration before ty is moved
    let class_info = extract_class_app(&ty);

    // Try instance resolution with type checking first, then simple lookup.
    // Fails with TacticError if no instance can be found — matching Lean 4
    // semantics where `inferInstance` is an error, not a silent sorry.
    let value = if state.instances.is_some() {
        // Primary: Use type-aware resolution with def-eq checking
        resolve_instance_tactic(state, &ty)
            // Fallback: Simple class name lookup
            .or_else(|| {
                state
                    .instances
                    .as_ref()
                    .and_then(|inst| resolve_instance_simple(inst, &ty))
            })
            .ok_or_else(|| TacticError::InstanceSynthesisFailed {
                class: "instance".into(),
                ty: crate::error_render::term(&ty),
            })?
    } else {
        // No instance table available — cannot resolve instances
        return Err(TacticError::InstanceSynthesisFailed {
            class: "instance".into(),
            ty: "no instance table available".into(),
        });
    };

    // Route the inferred value through the same proof-carrying let boundary as
    // `letI`; mutating the existing goal context would widen its immutable
    // metavariable scope after creation.
    let_(state, name, ty.clone(), Some(value.clone()))?;

    // Register resolved instance in instance table (#2233)
    if let Some((class_name, _)) = class_info {
        if let Some(instances) = state.instances.as_mut() {
            instances.add_instance(name.name().clone(), class_name, value, ty, DEFAULT_PRIORITY);
        }
    }

    Ok(())
}

/// Instance resolution for the tactic system.
///
/// Performs instance lookup with type argument matching using def-eq.
/// For full instance resolution with metavariable unification and
/// dependent instance resolution, use ElabCtx::resolve_instance.
///
/// # Strategy
/// 1. Extract class name and type arguments from goal
/// 2. Look up registered instances for the class
/// 3. For each instance (in priority order), check if instantiated type matches goal
/// 4. Return the first matching instance expression
fn resolve_instance_tactic(state: &ProofState, goal_ty: &Expr) -> Option<Expr> {
    let instances = state.instances.as_ref()?;
    let goal = state.goals.front()?;

    // Extract the class name and arguments from the goal type
    let (class_name, goal_args) = extract_class_app(goal_ty)?;

    // Look up registered instances for this class
    let registered_instances = instances.get_instances(&class_name);

    // Try each instance in priority order (highest first)
    for inst in registered_instances {
        // The instance type is the type of inst.expr when fully applied.
        // For concrete instances like `instAddNat : Add Nat`, the type is already
        // the class application and no additional application is needed.
        //
        // For polymorphic instances like `instAddList : {α} → Add (List α)`,
        // we need to instantiate the type parameters.

        // Extract class args from instance type
        let (inst_class, inst_args) = extract_class_app(&inst.type_)?;

        // Class names must match
        if inst_class != class_name {
            continue;
        }

        // For simple matching: if the instance has the same arity and
        // the arguments are definitionally equal, we have a match
        if inst_args.len() != goal_args.len() {
            continue;
        }

        // Check if instance arguments match goal arguments
        let mut matches = true;
        for (inst_arg, goal_arg) in inst_args.iter().zip(goal_args.iter()) {
            if !state.is_def_eq(goal, inst_arg, goal_arg) {
                matches = false;
                break;
            }
        }

        if matches {
            // Return the instance expression directly.
            // The instance expression should already be fully applied for concrete
            // instances. For polymorphic instances, the caller (or elaborator) will
            // need to handle universe level instantiation.
            return Some(inst.expr.clone());
        }
    }

    None
}

/// Simple instance resolution without type checking.
///
/// Fallback for when def-eq checking is not available.
/// Just returns the first instance for the class name.
fn resolve_instance_simple(
    instances: &crate::instances::InstanceTable,
    goal_ty: &Expr,
) -> Option<Expr> {
    let (class_name, _) = extract_class_app(goal_ty)?;
    let registered = instances.get_instances(&class_name);
    registered.first().map(|inst| inst.expr.clone())
}
