// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Goal closing, management, and proof state cloning operations.
use super::error::TacticError;
use super::{Goal, LocalDecl, ProofState};
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::sorry::{create_sorry_term_with_kind_at_level, SorryKind};
use clean_kernel::{Environment, Expr, ExprKind, Level};
use std::collections::HashSet;
use std::collections::VecDeque;

fn require_const(env: &Environment, constant: &str) -> Result<(), TacticError> {
    if env.get_const(&Name::from_string(constant)).is_some() {
        Ok(())
    } else {
        Err(TacticError::EnvironmentMissing {
            constant: constant.to_string(),
        })
    }
}

impl ProofState {
    /// Build a sorry term that is well-typed in the current goal context.
    ///
    /// Goal targets can mention elaborator or tactic locals that the
    /// environment-only kernel helper cannot see, so the tactic layer must
    /// infer `goal.target : Sort u` inside the active goal context and pass
    /// that universe level down explicitly.
    pub(crate) fn build_goal_sorry_term(
        &self,
        goal: &Goal,
        kind: SorryKind,
    ) -> Result<Expr, TacticError> {
        let target = self.metas.instantiate(&goal.target);
        let target_ty = self.infer_type(goal, &target)?;
        let target_sort = self.whnf(goal, &target_ty);
        let ExprKind::Sort(level) = target_sort.kind() else {
            return Err(TacticError::TypeCheckFailed(format!(
                "goal target must have a sort, got {target_sort:?}"
            )));
        };

        Ok(create_sorry_term_with_kind_at_level(
            self.env(),
            &target,
            kind,
            level.clone(),
        ))
    }

    /// Close the current goal with a type-checked proof term.
    ///
    /// This is the **safe default**: infers the proof's type, WHNF-normalizes
    /// both sides, and checks definitional equality against the goal target.
    /// Returns `Err` if the proof term is ill-typed or its type does not match
    /// the goal, so callers can fall through to a fallback (decide, sorry).
    ///
    /// For callers that have already validated the proof (e.g., via `unify()`
    /// or `is_def_eq()`), use `close_goal_unchecked` with a `// SAFETY:` comment
    /// explaining why the proof is known to be well-typed. (#2159, #2130)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty (at least one open goal)
    /// REQUIRES: `goal` is the current front goal in `self.goals`
    /// REQUIRES: `proof` is a well-typed expression in the current environment
    /// ENSURES: On Ok, the front goal is popped and its metavariable is assigned `proof`
    /// ENSURES: On Err(TypeMismatch), `proof`'s inferred type ≠ goal target; state unchanged
    /// ENSURES: On Err(TypeCheckFailed), meta assignment failed; state unchanged
    pub(crate) fn close_goal(&mut self, goal: &Goal, proof: Expr) -> Result<(), TacticError> {
        // Strict (infer_only=false) inference: validate App-argument types and
        // Lam/Pi domain sorts, matching what the kernel's add_decl does. The
        // lenient infer_type (infer_only=true) skips those checks and so accepts
        // ill-typed App args (e.g. @Eq.trans a a c (Eq.refl a) (Eq.refl b)) that
        // add_decl later rejects. Part of #38. infer_type_strict and is_def_eq
        // both instantiate metas internally.
        let inferred_ty = self.infer_type_strict(goal, &proof)?;

        // Normalize proof type through typeclass projections before comparing.
        // is_def_eq's lazy delta reduction cannot reduce multi-step chains like
        // @LE.le Nat instLENat a b → Nat.le a b (requires delta + beta + proj),
        // but full WHNF can. Without this, all arithmetic proof terms are rejected
        // and linarith/mathverse always fall through to trustedArith. Part of #2150.
        let proof_ty = self.whnf(goal, &inferred_ty);

        // Check that the inferred type matches the goal target
        let target = self.metas.instantiate(&goal.target);
        if !self.is_def_eq(goal, &proof_ty, &target) {
            return Err(TacticError::TypeMismatch {
                expected: format!("{target:?}"),
                actual: format!("{proof_ty:?}"),
            });
        }

        #[allow(deprecated)] // close_goal is the checked wrapper — it must call through
        self.close_goal_unchecked(proof)
    }

    /// Close the current goal with an **assembled recursor/eliminator** proof
    /// whose minor-premise arguments are still-open subgoal metavariables.
    ///
    /// This is the assembly-time variant for goal-transforming tactics
    /// (`induction`, `cases`) that build a `T.rec … minorᵢ … major` term where
    /// each `minorᵢ = fun fields ih => ?subgoalᵢ`. The subgoal metas are open at
    /// this point and their stored TARGET types reference the tactic's own
    /// binder FVars (the constructor fields / induction hypotheses). The kernel
    /// abstracts a lambda's binder via a *fresh* FVar, so the strict
    /// (`infer_only=false`) App-argument check would compare the recursor's
    /// expected motive-relative minor-premise type (BVar-bound) against the
    /// meta's stored type (still carrying the raw binder FVar) and reject the
    /// genuinely-valid term. See #38 for the full chain.
    ///
    /// The recursor application is therefore inferred **leniently**
    /// (`infer_only=true`, App-args not re-checked) here, but its def-eq against
    /// the goal target IS verified, so the result type is pinned. Soundness is
    /// not weakened: once the subgoal metas are solved, the fully-instantiated
    /// proof is re-checked **strictly** by `verify_tactic_proof` — the single
    /// enforcement point that all goal-transforming tactics flow through. A bug
    /// in the assembled spine fails there, never silently.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty and `goal` is the front goal
    /// REQUIRES: `proof` is a recursor/eliminator application whose open-meta
    ///   minor premises are re-validated by `verify_tactic_proof`
    /// ENSURES: On Ok, the front goal is popped and assigned `proof`
    /// ENSURES: On Err(TypeMismatch), `proof`'s lenient-inferred type is not
    ///   def-eq to the goal target; state unchanged
    pub(crate) fn close_goal_assembled(
        &mut self,
        goal: &Goal,
        proof: Expr,
    ) -> Result<(), TacticError> {
        // Lenient inference: the open-meta minor premises leak tactic binder
        // FVars through their stored types (#38). Strict App-arg checking is
        // deferred to verify_tactic_proof once the metas are solved.
        let inferred_ty = self.infer_type(goal, &proof)?;
        let proof_ty = self.whnf(goal, &inferred_ty);
        let target = self.metas.instantiate(&goal.target);
        if !self.is_def_eq(goal, &proof_ty, &target) {
            return Err(TacticError::TypeMismatch {
                expected: format!("{target:?}"),
                actual: format!("{proof_ty:?}"),
            });
        }
        #[allow(deprecated)]
        // checked: def-eq target match above + strict verify_tactic_proof later
        self.close_goal_unchecked(proof)
    }

    /// Close the current goal with a proof term **without type-checking**.
    ///
    /// # Safety (logical)
    ///
    /// The caller MUST ensure the proof term has the correct type for the
    /// current goal. Every call site must include a `// SAFETY:` comment
    /// explaining why the proof is known to be well-typed (e.g., validated
    /// by `unify()`, `is_def_eq()`, or trusted axiom). (#2159)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty
    /// REQUIRES: `proof` has the correct type for the current goal (caller-verified)
    /// ENSURES: On Ok, front goal's metavariable is assigned `proof` and goal is popped
    /// ENSURES: On Err(NoGoals), no goals exist; state unchanged
    /// ENSURES: On Err(TypeCheckFailed), meta assignment failed; state unchanged
    #[deprecated(note = "use close_goal (checked) instead — see #2154")]
    pub(crate) fn close_goal_unchecked(&mut self, proof: Expr) -> Result<(), TacticError> {
        let goal = self.goals.front().cloned().ok_or(TacticError::NoGoals)?;
        let goal_meta_id = goal.meta_id;
        let meta = self.metas.get(goal_meta_id).cloned().ok_or_else(|| {
            TacticError::TypeCheckFailed(format!(
                "active goal references undeclared metavariable {goal_meta_id:?}"
            ))
        })?;

        // A Goal is a focus/view of an immutable metavariable obligation.  It
        // may narrow or rename that obligation's visible context, but it must
        // never retarget it, add a new local, or silently retype an existing
        // local.  Enforce this at the raw-assignment boundary so even legacy
        // unchecked tactic paths cannot turn mutable Goal bookkeeping into
        // proof authority.
        let captured_target = self.metas.instantiate(&meta.ty);
        let focused_target = self.metas.instantiate(&goal.target);
        if captured_target != focused_target
            && !self.is_def_eq(&goal, &captured_target, &focused_target)
        {
            return Err(TacticError::TypeCheckFailed(format!(
                "active goal target is not definitionally equal to metavariable {goal_meta_id:?} type"
            )));
        }

        let exact_scope = self.meta_scope_for_context(&goal.local_ctx);
        for (_, fvar, ty) in &exact_scope {
            let Some((_, _, captured_ty)) = meta
                .locals
                .iter()
                .find(|(_, captured_fvar, _)| captured_fvar == fvar)
            else {
                return Err(TacticError::TypeCheckFailed(format!(
                    "active goal context widens metavariable {goal_meta_id:?} with local {fvar:?}"
                )));
            };
            let captured_ty = self.metas.instantiate(captured_ty);
            let focused_ty = self.metas.instantiate(ty);
            if captured_ty != focused_ty && !self.is_def_eq(&goal, &captured_ty, &focused_ty) {
                return Err(TacticError::TypeCheckFailed(format!(
                    "active goal retypes local {fvar:?} outside metavariable {goal_meta_id:?} creation scope"
                )));
            }
        }

        let allowed: HashSet<_> = meta.locals.iter().map(|(_, fvar, _)| *fvar).collect();
        // This assignment can sit below binders already captured by the
        // destination meta.  For example, the second `intro` closes a meta
        // whose scope already contains the first introduced FVar.  Binder
        // depth in this assignment fragment therefore starts one past the
        // destination's captured tactic locals, not always at the global base.
        let assignment_binder_base = allowed
            .iter()
            .map(|fvar| fvar.as_u64())
            .filter(|id| *id >= self.fvar_base && *id < self.next_fvar)
            .max()
            .map_or(self.fvar_base, |id| id.saturating_add(1));
        let instantiated_proof = self.metas.instantiate(&proof);
        if let Some(detail) = super::close_fvars::assignment_scope_violation(
            &instantiated_proof,
            &allowed,
            &self.metas,
            assignment_binder_base,
            self.next_fvar,
        ) {
            return Err(TacticError::TypeCheckFailed(format!(
                "metavariable {goal_meta_id:?} assignment violates its creation scope: {detail}"
            )));
        }

        if !self.metas.assign(goal_meta_id, proof) {
            return Err(TacticError::TypeCheckFailed(format!(
                "failed to assign proof to metavariable {:?}",
                goal_meta_id
            )));
        }
        self.pop_current_goal()?;
        Ok(())
    }

    /// Replace the current goal's target with a definitionally equal type.
    ///
    /// Mirrors Lean 4's `replaceTargetDefEq`: allocates a fresh metavariable
    /// for `new_target`, closes the old goal with the fresh meta expression
    /// (which is valid because `new_target` is def-eq to the old target), and
    /// pushes the new goal to the front. This keeps all goal replacement on
    /// one architectural path (old meta assigned → new goal active), avoiding
    /// in-place target mutation that can disconnect `MetaId(0)` from the proof
    /// chain.
    ///
    /// Part of #2477.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty
    /// REQUIRES: `new_target` is definitionally equal to the current goal target
    /// ENSURES: On Ok, the old goal's metavariable is assigned the fresh meta expression
    /// ENSURES: On Ok, a new goal with `new_target` is at the front of `self.goals`
    /// ENSURES: On Ok, `proof_term()` remains connected through `MetaId(0)`
    /// ENSURES: On Err(GoalMismatch), `new_target` is not def-eq; state unchanged
    pub(crate) fn replace_target_def_eq(&mut self, new_target: Expr) -> Result<(), TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();

        // Syntactic shortcut: if the target is unchanged, nothing to do
        if goal.target == new_target {
            return Ok(());
        }

        // Verify definitional equality
        if !self.is_def_eq(&goal, &goal.target, &new_target) {
            return Err(TacticError::GoalMismatch(
                "replace_target_def_eq: new target is not definitionally equal \
                 to current target"
                    .to_string(),
            ));
        }

        // Allocate a fresh metavariable for the new target
        let new_meta_id = self.fresh_meta(new_target.clone());
        let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));

        // Close the old goal with the fresh meta expression. close_goal
        // will infer the meta's type (new_target), WHNF-normalize, and
        // confirm it is def-eq to the old target. Part of #2154.
        self.close_goal(&goal, new_meta_expr)?;

        // Push the replacement goal to the front
        self.goals.push_front(Goal {
            meta_id: new_meta_id,
            target: new_target,
            local_ctx: goal.local_ctx,
            tag: goal.tag,
        });

        Ok(())
    }

    /// Replace the current goal's target using an equality proof.
    ///
    /// Mirrors Lean 4's `replaceTargetEq`: given `eq_proof : old_target = new_target`,
    /// builds `Eq.mpr eq_proof ?new` to close the old goal and pushes a new goal
    /// for `new_target`. This is used by tactics that produce equality proofs
    /// (e.g., `ring_nf`, `simp`, `conv`).
    ///
    /// Part of #2477.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty
    /// REQUIRES: `eq_proof` has type `@Eq (Sort u) old_target new_target`
    /// ENSURES: On Ok, the old goal is closed with `Eq.mpr eq_proof ?new_meta`
    /// ENSURES: On Ok, a new goal with `new_target` is at the front of `self.goals`
    /// ENSURES: On Ok, `proof_term()` remains connected through `MetaId(0)`
    pub(crate) fn replace_target_eq(
        &mut self,
        new_target: Expr,
        eq_proof: Expr,
    ) -> Result<(), TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let old_target = self.metas.instantiate(&goal.target);
        require_const(self.env(), "Eq.mpr")?;

        // Compute the universe level from the target's sort.
        // target : Sort u → Eq uses @Eq.{succ u}, Eq.mpr uses .{u}
        let sort_level = self
            .infer_type(&goal, &old_target)
            .ok()
            .and_then(|ty| match ty.kind() {
                ExprKind::Sort(level) => Some(level.clone()),
                _ => None,
            })
            .ok_or_else(|| {
                TacticError::TypeCheckFailed(
                    "replace_target_eq: cannot infer universe level of target type".into(),
                )
            })?;

        // Wave 97 (Gap 18): kernel-typecheck the supplied equality
        // proof BEFORE mutating the goal. The caller must provide a
        // term of type `@Eq.{succ u} (Sort u) old_target new_target`.
        // Without this check the goal would be silently corrupted by
        // an ill-typed witness (e.g. a proof of `P` masquerading as a
        // proof of `P = Q`). Use the goal-scoped `infer_type` so the
        // local context (fvars introduced by tactics) is in scope, then
        // use the goal-scoped `is_def_eq` for the comparison — both
        // routes through the kernel.
        let expected_eq_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Eq"),
                        vec![Level::succ(sort_level.clone())],
                    ),
                    Expr::sort(sort_level.clone()),
                ),
                old_target.clone(),
            ),
            new_target.clone(),
        );
        let inferred_proof_ty = self.infer_type(&goal, &eq_proof).map_err(|e| {
            TacticError::TypeCheckFailed(format!(
                "replace_target_eq: cannot infer type of equality proof: {e:?}"
            ))
        })?;
        if !self.is_def_eq(&goal, &inferred_proof_ty, &expected_eq_ty) {
            return Err(TacticError::TypeMismatch {
                expected: format!("{expected_eq_ty:?}"),
                actual: format!("{inferred_proof_ty:?}"),
            });
        }

        // Allocate a fresh metavariable for the new target
        let new_meta_id = self.fresh_meta(new_target.clone());
        let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));

        // Build Eq.mpr.{u} old_target new_target eq_proof ?new_meta
        let eq_mpr = Expr::const_(Name::from_string("Eq.mpr"), vec![sort_level]);
        let proof = Expr::app(
            Expr::app(
                Expr::app(Expr::app(eq_mpr, old_target), new_target.clone()),
                eq_proof,
            ),
            new_meta_expr,
        );

        // Close the old goal with the Eq.mpr proof term
        self.close_goal(&goal, proof)?;

        // Push the replacement goal to the front
        self.goals.push_front(Goal {
            meta_id: new_meta_id,
            target: new_target,
            local_ctx: goal.local_ctx,
            tag: goal.tag,
        });

        Ok(())
    }

    /// Remove and return the current goal.
    ///
    /// This helper centralizes empty-goal handling so tactic code does not
    /// panic on `remove(0)` when no goals are present.
    /// Invalidates the TypeChecker cache since the current goal changes.
    /// Part of #1671.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.goals` is non-empty
    /// ENSURES: On Ok, returns the former front goal; `self.goals.len()` decreases by 1
    /// ENSURES: On Ok, TypeChecker cache is invalidated
    /// ENSURES: On Err(NoGoals), `self.goals` was empty; state unchanged
    pub(crate) fn pop_current_goal(&mut self) -> Result<Goal, TacticError> {
        if self.goals.is_empty() {
            return Err(TacticError::NoGoals);
        }
        self.invalidate_tc_cache();
        Ok(self
            .goals
            .pop_front()
            .expect("invariant: checked non-empty above"))
    }

    /// Clear all goals (used when proof is complete).
    ///
    /// # Contract
    ///
    /// ENSURES: `self.goals.is_empty()` is true
    /// ENSURES: TypeChecker cache is invalidated
    pub fn clear_goals(&mut self) {
        self.invalidate_tc_cache();
        self.goals.clear();
    }

    /// Remove goals whose metavariables are already assigned (#1803).
    ///
    /// Lean 4's `getUnsolvedGoals` filters out goals with assigned mvars.
    /// When tactic A closes a shared metavariable, other goals referencing
    /// that meta may become transitively solved. Without pruning, these
    /// "phantom" goals remain in the list, causing false unsolved-goal
    /// errors or unnecessary sorry insertion.
    ///
    /// Call after each tactic application.
    ///
    /// # Contract
    ///
    /// ENSURES: All remaining goals have unassigned metavariables
    /// ENSURES: `self.goals.len()` <= previous `self.goals.len()`
    /// ENSURES: TypeChecker cache is invalidated only if goals were pruned
    pub fn prune_solved_goals(&mut self) {
        let before = self.goals.len();
        self.goals
            .retain(|goal| !self.metas.is_assigned(goal.meta_id));
        if self.goals.len() != before {
            self.invalidate_tc_cache();
        }
    }

    /// Create a new proof state with a specific goal (for tree-based search).
    ///
    /// This clones the environment and meta state, but sets a fresh goal list.
    ///
    /// # Contract
    ///
    /// REQUIRES: `goal.meta_id` is a valid metavariable ID
    /// ENSURES: Returned state has exactly one goal (the provided `goal`)
    /// ENSURES: Returned state shares environment and instance data with `self`
    /// ENSURES: `goal.meta_id` exists in the returned state's MetaState
    /// ENSURES: `next_fvar` >= max FVar ID in the goal's local context
    pub fn clone_with_goal(&self, goal: Goal) -> Self {
        let goal_meta_id = goal.meta_id;
        // #close_fvars (double `<;>` with `intro`): the floor for `next_fvar`
        // must avoid colliding with FVars ALREADY in this goal's local_ctx, but
        // it must NOT add an unconditional +1 when the context is empty. A
        // parallel-branch combinator (`<;>`/all_goals) resets `self.next_fvar` to
        // a shared per-branch base before cloning each sibling goal, precisely so
        // every branch's first `intro` allocates the SAME id and maps to the same
        // BVar at the same binder depth. If an empty-context goal still bumped
        // `next_fvar` to `0 + 1 = 1`, that first `intro` would get id 1 while its
        // lambda sits at binder depth 1 — `close_fvars`' `(n - base) < depth`
        // check then fails (`1 < 1` is false) and the FVar is left unconverted
        // (an ID-to-binder gap → the close_fvars panic on a valid
        // `constructor <;> intro h <;> trivial`). Only raise the floor above the
        // caller-supplied `self.next_fvar` when the context genuinely contains a
        // higher FVar id. (The old `.unwrap_or(0) + 1` defeated the very
        // per-branch reset it was meant to cooperate with — see #2533.)
        let ctx_floor = goal
            .local_ctx
            .iter()
            .map(|d| d.fvar.as_u64() + 1)
            .max()
            .unwrap_or(0);
        let next_fvar = ctx_floor.max(self.next_fvar);
        let mut metas = self.metas.clone();
        // Ensure the goal's meta exists in the cloned MetaState. Search tree
        // clones may pass goals with meta IDs created in a temporary state.
        // Without this, fresh() can reuse the goal's ID, causing circular
        // assignments that the occurs check rightly rejects. Part of #2199.
        let exact_scope = self.meta_scope_for_context(&goal.local_ctx);
        metas.ensure_meta_with_locals(goal.meta_id, goal.target.clone(), exact_scope.clone());
        if let Some(meta) = metas.get(goal.meta_id) {
            let captured_target = self.metas.instantiate(&meta.ty);
            let focused_target = self.metas.instantiate(&goal.target);
            assert!(
                captured_target == focused_target
                    || self.is_def_eq(&goal, &captured_target, &focused_target),
                "focused goal target must be definitionally equal to its metavariable type"
            );
            // A focused goal may have narrowed its visible context (`clear`) or
            // renamed a declaration since the metavariable was created.  Both
            // are authority-preserving: every still-visible FVar must retain a
            // compatible type, while surplus creation-scope locals remain a
            // safe immutable superset.  A new FVar or incompatible retyping is
            // a genuine scope widening and must fail closed.
            let scope_is_compatible_subset = exact_scope.iter().all(|(_, fvar, ty)| {
                meta.locals
                    .iter()
                    .find(|(_, captured_fvar, _)| captured_fvar == fvar)
                    .is_some_and(|(_, _, captured_ty)| {
                        let captured_ty = self.metas.instantiate(captured_ty);
                        let goal_ty = self.metas.instantiate(ty);
                        captured_ty == goal_ty || self.is_def_eq(&goal, &captured_ty, &goal_ty)
                    })
            });
            assert!(
                scope_is_compatible_subset,
                "focused goal context must be a type-compatible subset of its metavariable scope"
            );
        }
        ProofState {
            env: self.env.clone(),
            goals: VecDeque::from([goal]),
            metas,
            root_meta_id: goal_meta_id,
            next_fvar,
            instances: self.instances.clone(),
            universe_params: self.universe_params.clone(),
            next_universe: self.next_universe,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: self.elab_locals.clone(),
            fvar_base: self.fvar_base,
            trust_ledger: self.trust_ledger,
            conv_nav: None,
            conv_focus_witness: None,
            conv_focus_tree: None,
            conv_congr_cursor: None,
            options: self.options.clone(),
            namespace_state: self.namespace_state.clone(),
        }
    }

    /// Create a nested proof state with a fresh root metavariable.
    ///
    /// Unlike `ProofState::new`, this reuses the parent's metavariable context
    /// so the nested goal gets a non-colliding root meta. This is required for
    /// phase-3d sub-proof-states (`have`, `conv`) that later merge assignments
    /// back into the parent.
    pub(crate) fn clone_with_fresh_goal_target(&self, target: Expr) -> Self {
        let local_ctx = self
            .current_goal()
            .map(|goal| goal.local_ctx.clone())
            .unwrap_or_default();
        self.clone_with_fresh_goal_target_in_context(target, &local_ctx)
    }

    /// Create a nested proof state whose root metavariable is stamped with an
    /// explicitly supplied goal context.
    ///
    /// Scratch proof builders can operate on a goal other than the parent's
    /// current front goal.  They must use this boundary instead of minting in
    /// the front context and overwriting `Goal.local_ctx` afterward.
    pub(crate) fn clone_with_fresh_goal_target_in_context(
        &self,
        target: Expr,
        local_ctx: &[LocalDecl],
    ) -> Self {
        let local_ctx = local_ctx.to_vec();
        let goal_fvar_floor = local_ctx
            .iter()
            .map(|decl| decl.fvar.as_u64().saturating_add(1))
            .max()
            .unwrap_or(0);
        let mut metas = self.metas.clone();
        let scope = self.meta_scope_for_context(&local_ctx);
        let root_meta_id = metas.fresh_with_locals(target.clone(), scope);
        ProofState {
            env: self.env.clone(),
            goals: VecDeque::from([Goal {
                meta_id: root_meta_id,
                target,
                local_ctx,
                tag: None,
            }]),
            metas,
            root_meta_id,
            next_fvar: self.next_fvar.max(goal_fvar_floor),
            instances: self.instances.clone(),
            universe_params: self.universe_params.clone(),
            next_universe: self.next_universe,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: self.elab_locals.clone(),
            fvar_base: self.fvar_base,
            trust_ledger: self.trust_ledger,
            conv_nav: None,
            conv_focus_witness: None,
            conv_focus_tree: None,
            conv_congr_cursor: None,
            options: self.options.clone(),
            namespace_state: self.namespace_state.clone(),
        }
    }

    /// Merge metavariable state from a focused sub-proof-state back into this one.
    ///
    /// Used by `all_goals`, `any_goals`, and `seq_focus` to propagate
    /// metavariable assignments from individual goal processing back to
    /// the parent state (#1802).
    ///
    /// # Contract
    ///
    /// REQUIRES: `focused` was created from `self` via `clone_with_goal`
    /// ENSURES: All meta assignments in `focused` are merged into `self`
    /// ENSURES: `self.next_fvar` >= `focused.next_fvar` (monotonically increasing)
    pub fn merge_meta_state(&mut self, focused: &ProofState) {
        self.metas.merge_from(&focused.metas);
        self.next_fvar = self.next_fvar.max(focused.next_fvar);
        self.trust_ledger.adopt_branch(&focused.trust_ledger);
    }
}

const _: fn(&ProofState, Expr) -> ProofState = ProofState::clone_with_fresh_goal_target;
