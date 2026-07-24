// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AND-OR tree search engine with backtracking for aesop.

use crate::stack_safe;
use crate::tactic::{Goal, ProofState, ProofTrustLedger, TacticError, TacticResult};
use crate::unify::MetaState;

use super::aesop::{aesop_normalize, aesop_safe_rules, aesop_try_close, AesopConfig};
use super::aesop_rules::aesop_get_candidates;
use super::goal_queue::GoalQueue;
use super::types::{
    AesopSearchState, GoalId, GoalState, NodeState, Percent, RappId, RuleAttempt, SearchTree,
};

// =============================================================================
// AND-OR Tree Propagation
// =============================================================================

/// Propagate provenness upward from a proven goal
///
/// When a goal is proven:
/// 1. Mark the goal as proven
/// 2. Check if the parent rapp now has all subgoals proven
/// 3. If so, mark the parent rapp as proven and the grandparent goal
/// 4. Continue recursively upward
///
/// REQUIRES: `goal_id` identifies a goal already stored in `tree` when callers expect propagation to update the tree.
/// REQUIRES: If `by_rapp` is `Some(rapp_id)`, that rapp represents the rule application that just proved `goal_id`.
/// ENSURES: `goal_id` is marked proven in `tree` (`ProvenByNormalization` for `None`, `ProvenByRuleApplication(rapp_id)` for `Some(rapp_id)`).
/// ENSURES: Any ancestor rapp whose child goals are all proven is marked `NodeState::Proven`.
/// ENSURES: Any ancestor goal reached through a newly proven rapp is recursively marked `GoalState::ProvenByRuleApplication`.
fn propagate_proven(tree: &mut SearchTree, goal_id: GoalId, by_rapp: Option<RappId>) {
    stack_safe(|| {
        // Mark goal as proven
        if let Some(goal) = tree.get_goal_mut(goal_id) {
            goal.state = match by_rapp {
                Some(rapp_id) => GoalState::ProvenByRuleApplication(rapp_id),
                None => GoalState::ProvenByNormalization,
            };
        }

        // Get parent rapp (if any)
        let parent_rapp_id = match tree.get_goal(goal_id) {
            Some(goal) => goal.parent,
            None => return,
        };

        let parent_rapp_id = match parent_rapp_id {
            Some(id) => id,
            None => return, // Root goal, we're done
        };

        // Check if all siblings are proven (parent rapp is AND node)
        let all_subgoals_proven = {
            if let Some(rapp) = tree.get_rapp(parent_rapp_id) {
                rapp.children.iter().all(|g| {
                    tree.get_goal(*g)
                        .map(|goal| goal.state.is_proven())
                        .unwrap_or(false)
                })
            } else {
                false
            }
        };

        if all_subgoals_proven {
            // Mark parent rapp as proven
            if let Some(rapp) = tree.get_rapp_mut(parent_rapp_id) {
                rapp.state = NodeState::Proven;
            }

            // Get grandparent goal
            let grandparent_goal_id = tree
                .get_rapp(parent_rapp_id)
                .map(|rapp| rapp.parent)
                .unwrap_or(GoalId(0));

            // Mark grandparent goal as proven by this rapp
            if let Some(grandparent) = tree.get_goal_mut(grandparent_goal_id) {
                grandparent.state = GoalState::ProvenByRuleApplication(parent_rapp_id);
            }

            // Continue propagating upward
            propagate_proven(tree, grandparent_goal_id, Some(parent_rapp_id));
        }
    })
}

/// Mark a goal as unprovable and propagate upward
///
/// When a goal becomes unprovable:
/// 1. Mark the goal as unprovable
/// 2. Mark the parent rapp as unprovable (AND semantics: one failure = total failure)
/// 3. Check if all rapps of grandparent are now unprovable
/// 4. If so, mark grandparent as unprovable and continue
///
/// REQUIRES: `goal_id` identifies a goal already stored in `tree` when callers expect propagation to update the tree.
/// ENSURES: `goal_id` is marked `GoalState::Unprovable`.
/// ENSURES: If `goal_id` has a parent rapp, that rapp is marked `NodeState::Unprovable`.
/// ENSURES: Any ancestor goal whose child rapps are all unprovable is recursively marked `GoalState::Unprovable`.
fn mark_unprovable(tree: &mut SearchTree, goal_id: GoalId) {
    stack_safe(|| {
        // Mark goal as unprovable
        if let Some(goal) = tree.get_goal_mut(goal_id) {
            goal.state = GoalState::Unprovable;
        }

        // Get parent rapp
        let parent_rapp_id = match tree.get_goal(goal_id) {
            Some(goal) => goal.parent,
            None => return,
        };

        let parent_rapp_id = match parent_rapp_id {
            Some(id) => id,
            None => return, // Root goal unprovable
        };

        // Mark parent rapp as unprovable (AND node: one child failed)
        if let Some(rapp) = tree.get_rapp_mut(parent_rapp_id) {
            rapp.state = NodeState::Unprovable;
        }

        // Get grandparent goal
        let grandparent_goal_id = match tree.get_rapp(parent_rapp_id) {
            Some(rapp) => rapp.parent,
            None => return,
        };

        // Check if all rapps of grandparent are now unprovable (OR node)
        let all_rapps_unprovable = {
            if let Some(grandparent) = tree.get_goal(grandparent_goal_id) {
                !grandparent.children.is_empty()
                    && grandparent.children.iter().all(|r| {
                        tree.get_rapp(*r)
                            .map(|rapp| rapp.state == NodeState::Unprovable)
                            .unwrap_or(false)
                    })
            } else {
                false
            }
        };

        if all_rapps_unprovable {
            // Grandparent goal is OR node with all children failed = goal failed
            mark_unprovable(tree, grandparent_goal_id);
        }
    })
}

/// Merge proof artifacts from a proven cloned branch back into the main state.
///
/// `aesop_search_tree` explores goals in cloned `ProofState`s. When one branch
/// closes a goal, the parent state must inherit the branch's proof-term meta
/// assignments, trust ledger, and FVar watermark before the clone is dropped.
fn merge_proven_branch(
    state: &mut ProofState,
    metas: Box<MetaState>,
    trust_ledger: ProofTrustLedger,
    next_fvar: u64,
) {
    state.metas.merge_from(metas.as_ref());
    state.trust_ledger.adopt_branch(&trust_ledger);
    state.next_fvar = state.next_fvar.max(next_fvar);
}

// =============================================================================
// Tree-Based Aesop Search (with backtracking)
// =============================================================================

/// Tree-based aesop search with proper AND-OR backtracking
///
/// This replaces the linear first-match strategy with a complete search
/// that explores all branches and backtracks when a path fails.
/// REQUIRES: `state` has a current goal when callers expect search to begin.
/// REQUIRES: `config.max_depth` and `config.max_goals` bound the intended search effort for this run.
/// ENSURES: On `Ok(())`, the root goal was proven and `state.clear_goals()` has been applied.
/// ENSURES: On `Err(SearchExhausted { .. })`, the root goal remained unproven after exhausting active branches or the configured iteration budget.
/// ENSURES: Failed searches may still consume fresh metavariables in `state` while registering explored subgoals.
pub(super) fn aesop_search_tree(state: &mut ProofState, config: &AesopConfig) -> TacticResult {
    // Get the initial goal
    let root_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Initialize the search state (wraps tree + diagnostics)
    let mut search_state = AesopSearchState::new(root_goal.clone());
    let root_id = search_state.tree().root();

    // Initialize the goal queue with the configured strategy
    let mut queue = GoalQueue::with_strategy(config.strategy);
    queue.push(root_id, Percent::hundred(), 0, 0);

    // Use the explicit max_iterations config field
    let max_iterations = config.max_iterations;

    for _ in 0..max_iterations {
        // Get next active goal to expand
        let Some(goal_id) = queue.pop_active_goal(search_state.tree()) else {
            // No more goals to expand
            break;
        };

        search_state.tree_mut().next_iteration();
        search_state.iteration_count += 1;

        // Get goal data
        let goal_data = match search_state.tree().get_goal(goal_id) {
            Some(g) => g.clone(),
            None => continue,
        };

        // Check depth limit
        if goal_data.depth > config.max_depth {
            continue;
        }

        // Update last expanded
        let iteration = search_state.tree().iteration();
        if let Some(g) = search_state.tree_mut().get_goal_mut(goal_id) {
            g.last_expanded_in_iteration = iteration;
        }

        // Try to prove this goal
        let result = try_prove_goal_in_tree(
            state,
            &mut search_state,
            &mut queue,
            goal_id,
            &goal_data.goal,
            config,
        );

        match result {
            ProveResult::Proven {
                metas,
                trust_ledger,
                next_fvar,
            } => {
                merge_proven_branch(state, metas, trust_ledger, next_fvar);
                // Goal was closed - propagate
                propagate_proven(search_state.tree_mut(), goal_id, None);
            }
            ProveResult::NewSubgoals => {
                // New subgoals were added - continue search
            }
            ProveResult::NoCandidates => {
                // No rules apply - mark as unprovable if no children
                if search_state
                    .tree()
                    .get_goal(goal_id)
                    .map(|g| g.children.is_empty())
                    .unwrap_or(true)
                {
                    mark_unprovable(search_state.tree_mut(), goal_id);
                }
            }
        }

        // Check if root is proven
        if search_state.tree().is_root_proven() {
            // Success - all goals closed
            state.clear_goals();
            return Ok(());
        }

        // Check if root is unprovable
        if search_state.tree().is_root_unprovable() {
            return Err(TacticError::SearchExhausted {
                tactic: "aesop".into(),
                detail: format!(
                    "no proof found after {} iterations ({} rule attempts)",
                    search_state.iteration_count(),
                    search_state.total_attempts(),
                ),
            });
        }
    }

    // Check final state
    if search_state.tree().is_root_proven() {
        state.clear_goals();
        Ok(())
    } else {
        Err(TacticError::SearchExhausted {
            tactic: "aesop".into(),
            detail: format!(
                "search exhausted after {} iterations ({} rule attempts)",
                search_state.iteration_count(),
                search_state.total_attempts(),
            ),
        })
    }
}

/// Result of trying to prove a goal
enum ProveResult {
    /// Goal was proven (closed directly). Carries the cloned meta state,
    /// trust ledger, and next_fvar watermark so the caller can merge
    /// proof-term assignments into the main state. Without this merge,
    /// proof-term metavariable assignments made in the cloned sub-state
    /// are lost when the clone is dropped. (#2533)
    ///
    /// `next_fvar` must also be merged: cloned sub-states allocate FVars
    /// (e.g., from `intro`) starting at the parent's `next_fvar`. Without
    /// bumping the parent's `next_fvar`, `closed_proof()` won't close
    /// these clone-allocated FVars, causing `verify_tactic_proof` to fail
    /// with `UnknownFVar`. (#2533 elab_tactic integration)
    Proven {
        metas: Box<MetaState>,
        trust_ledger: ProofTrustLedger,
        next_fvar: u64,
    },
    /// New subgoals were created
    NewSubgoals,
    /// No candidates apply
    NoCandidates,
}

/// Try to prove a goal in the search tree
/// REQUIRES: `goal_id` identifies the active tree node whose stored goal matches `goal`.
/// REQUIRES: `search_state` and `queue` belong to the same in-flight search run.
/// ENSURES: Returns `ProveResult::Proven` only when safe rules, normalization/closing, or one candidate application closes `goal_id`.
/// ENSURES: Returns `ProveResult::NewSubgoals` only when at least one successful candidate created a child rapp and enqueued remapped subgoals.
/// ENSURES: Returns `ProveResult::NoCandidates` when no candidate closed the goal or produced queued subgoals.
/// ENSURES: Any subgoals registered in the tree are remapped onto fresh metavariables allocated from `state.metas`.
/// ENSURES: All candidate attempts are recorded in `search_state.rule_attempts`.
fn try_prove_goal_in_tree(
    state: &mut ProofState,
    search_state: &mut AesopSearchState,
    queue: &mut GoalQueue,
    goal_id: GoalId,
    goal: &Goal,
    config: &AesopConfig,
) -> ProveResult {
    // Create a temporary proof state for this goal
    let mut temp_state = state.clone_with_goal(goal.clone());

    // Phase 1: Try safe rules (these always make progress)
    if aesop_safe_rules(&mut temp_state, config, 0).is_ok() && temp_state.goals().is_empty() {
        search_state.record_attempt(
            goal_id,
            RuleAttempt {
                rule_name: "safe_rules".into(),
                success: true,
                subgoals_produced: 0,
            },
        );
        return ProveResult::Proven {
            next_fvar: temp_state.next_fvar,
            metas: Box::new(temp_state.metas),
            trust_ledger: temp_state.trust_ledger,
        };
    }

    // Phase 2: Try normalization
    if config.use_simp {
        let _ = aesop_normalize(&mut temp_state);
    }

    if temp_state.goals().is_empty() {
        search_state.record_attempt(
            goal_id,
            RuleAttempt {
                rule_name: "normalization".into(),
                success: true,
                subgoals_produced: 0,
            },
        );
        return ProveResult::Proven {
            next_fvar: temp_state.next_fvar,
            metas: Box::new(temp_state.metas),
            trust_ledger: temp_state.trust_ledger,
        };
    }

    // Phase 3: Try to close directly
    if aesop_try_close(&mut temp_state).is_ok() {
        search_state.record_attempt(
            goal_id,
            RuleAttempt {
                rule_name: "try_close".into(),
                success: true,
                subgoals_produced: 0,
            },
        );
        return ProveResult::Proven {
            next_fvar: temp_state.next_fvar,
            metas: Box::new(temp_state.metas),
            trust_ledger: temp_state.trust_ledger,
        };
    }

    // Phase 4: Get candidates and create child rapps for each
    let candidates = aesop_get_candidates(&mut temp_state, config);

    if candidates.is_empty() {
        return ProveResult::NoCandidates;
    }

    let mut created_any = false;

    // Capture the processed goal after safe rules - candidates reference hypotheses
    // that may have been introduced during safe rule application (e.g., intro).
    let processed_goal = temp_state.current_goal().cloned();

    let tree = &mut search_state.tree;
    for (cand_idx, candidate) in candidates.iter().enumerate() {
        // Create a fresh state for this candidate using the PROCESSED goal
        // (after safe rules), not the original goal. Candidates may reference
        // hypotheses that were added by intro or other safe rules.
        let mut cand_state = match &processed_goal {
            Some(g) => state.clone_with_goal(g.clone()),
            None => continue, // No goal after safe rules - skip candidates
        };

        let rule_label = format!("candidate_{cand_idx}");

        // Try applying the candidate
        if (candidate.apply)(&mut cand_state).is_ok() {
            let num_subgoals = cand_state.goals().len();
            let rapp_id = tree.add_rapp(goal_id);

            // Check if this closed all goals
            if cand_state.goals().is_empty() {
                // Rapp proved the goal with no subgoals
                if let Some(rapp) = tree.get_rapp_mut(rapp_id) {
                    rapp.state = NodeState::Proven;
                }
                propagate_proven(tree, goal_id, Some(rapp_id));
                search_state
                    .rule_attempts
                    .entry(goal_id)
                    .or_default()
                    .push(RuleAttempt {
                        rule_name: rule_label,
                        success: true,
                        subgoals_produced: 0,
                    });
                return ProveResult::Proven {
                    next_fvar: cand_state.next_fvar,
                    metas: Box::new(cand_state.metas),
                    trust_ledger: cand_state.trust_ledger,
                };
            }

            // Record successful application that produced subgoals
            search_state
                .rule_attempts
                .entry(goal_id)
                .or_default()
                .push(RuleAttempt {
                    rule_name: rule_label,
                    success: true,
                    subgoals_produced: num_subgoals,
                });

            // Add subgoals to tree and queue.
            // Each subgoal's meta_id comes from cand_state (a clone), so we
            // register a fresh meta in the main state to ensure
            // try_prove_goal_in_tree can close these goals later.
            for subgoal in cand_state.goals() {
                let fresh_meta =
                    state.fresh_meta_in_context(subgoal.target.clone(), &subgoal.local_ctx);
                let remapped_subgoal = Goal {
                    meta_id: fresh_meta,
                    target: subgoal.target.clone(),
                    local_ctx: subgoal.local_ctx.clone(),
                    tag: None,
                };
                let priority = Percent::from_f64(candidate.priority as f64 / 100.0);
                let subgoal_id = tree.add_goal(rapp_id, remapped_subgoal);
                let iteration = tree.iteration();
                queue.push(subgoal_id, priority, 0, iteration);
            }

            created_any = true;
        } else {
            // Record failed application
            search_state
                .rule_attempts
                .entry(goal_id)
                .or_default()
                .push(RuleAttempt {
                    rule_name: rule_label,
                    success: false,
                    subgoals_produced: 0,
                });
        }
    }

    if created_any {
        ProveResult::NewSubgoals
    } else {
        ProveResult::NoCandidates
    }
}

#[cfg(test)]
mod tests;
