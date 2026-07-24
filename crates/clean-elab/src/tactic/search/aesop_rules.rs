// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aesop rule candidate generation and builder support.

use crate::tactic::{apply, cases, left_, right_, use_single, Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{AesopRuleBuilder, AesopRulePhase, Expr, ExprKind, Level};

use super::aesop::{AesopCandidate, AesopConfig};
use super::aesop_builders::{
    apply_destruct_rule, apply_forward_rule, apply_tactic_rule, apply_unfold_rule,
    enumerate_witnesses, extract_exists_witness_type,
};
use super::simple::can_apply_to_produce;

/// Create an AesopCandidate from a registered rule
///
/// Returns None if the rule cannot be applied to the current target.
/// REQUIRES: `goal` and `target` come from the active proof state described by `state`.
/// ENSURES: `Apply` and legacy `Constructors` rules return `Some` only when `can_apply_to_produce` can target `goal`.
/// ENSURES: `Tactic`, `Forward`, `Destruct`, and `Unfold` builders return deferred closures without mutating `state`.
fn make_rule_candidate(
    state: &ProofState,
    goal: &Goal,
    rule_name: &Name,
    builder: AesopRuleBuilder,
    target: &Expr,
    priority: i32,
) -> Option<AesopCandidate> {
    // Tactic builder doesn't need a constant - it just dispatches to a named tactic
    if matches!(builder, AesopRuleBuilder::Tactic) {
        let tactic_name = rule_name.clone();
        let tactic_priority = priority.saturating_sub(15);
        return Some(AesopCandidate {
            priority: tactic_priority,
            apply: Box::new(move |s| apply_tactic_rule(s, &tactic_name)),
        });
    }

    // Get the constant for this rule (required for other builder types)
    let constant = state.env().get_const(rule_name)?;

    // Create instance with fresh levels
    let levels: Vec<Level> = constant
        .level_params
        .iter()
        .enumerate()
        .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
        .collect();

    let const_type = if levels.is_empty() {
        constant.type_.clone()
    } else {
        let subst: Vec<(Name, Level)> = constant
            .level_params
            .iter()
            .cloned()
            .zip(levels.iter().cloned())
            .collect();
        constant.type_.instantiate_level_params(&subst)
    };

    // Check applicability based on builder type
    match builder {
        AesopRuleBuilder::Apply => {
            // Check if this constant can be applied to produce the target type
            if can_apply_to_produce(state, goal, &const_type, target, 5).is_some() {
                let name = rule_name.clone();
                let lvls = levels.clone();
                Some(AesopCandidate {
                    priority,
                    apply: Box::new(move |s| apply(s, Expr::const_(name.clone(), lvls.clone()))),
                })
            } else {
                None
            }
        }
        AesopRuleBuilder::Constructors => {
            // Constructors builder with builder_args is handled specially in aesop_get_candidates.
            // It registers a type T, and when the goal is of type T, all constructors of T
            // are generated as candidates.
            //
            // For rules without builder_args (legacy/explicit constructor registration),
            // treat like apply: check if this constructor can produce the target.
            if can_apply_to_produce(state, goal, &const_type, target, 5).is_some() {
                let name = rule_name.clone();
                let lvls = levels.clone();
                Some(AesopCandidate {
                    priority,
                    apply: Box::new(move |s| apply(s, Expr::const_(name.clone(), lvls.clone()))),
                })
            } else {
                None
            }
        }
        AesopRuleBuilder::Simp => {
            // Simp rules are handled via simp tactic, not direct application
            // For now, don't generate a direct candidate (simp is called separately)
            None
        }
        AesopRuleBuilder::Cases => {
            // Cases rules need a hypothesis to destruct
            // This requires more context - skip for now
            None
        }
        AesopRuleBuilder::Forward => {
            // Forward rules add hypotheses to context rather than closing goals
            // They work differently from apply rules:
            // - Check if rule's arguments can be matched from local context
            // - If so, add conclusion as new hypothesis
            let name = rule_name.clone();
            let rule_ty = const_type.clone();
            let lvls = levels.clone();

            // Forward rules have lower priority than apply rules since
            // they don't close the goal, just enrich the context
            let forward_priority = priority.saturating_sub(20);

            Some(AesopCandidate {
                priority: forward_priority,
                apply: Box::new(move |s| apply_forward_rule(s, &name, &rule_ty, &lvls)),
            })
        }
        AesopRuleBuilder::Destruct => {
            // Destruct rules are like forward rules but clear the matched hypothesis
            // This prevents infinite loops and keeps the context clean
            let name = rule_name.clone();
            let rule_ty = const_type.clone();
            let lvls = levels.clone();

            // Destruct rules have same priority as forward rules
            let destruct_priority = priority.saturating_sub(20);

            Some(AesopCandidate {
                priority: destruct_priority,
                apply: Box::new(move |s| apply_destruct_rule(s, &name, &rule_ty, &lvls)),
            })
        }
        AesopRuleBuilder::Unfold => {
            // Unfold rules replace a definition with its body in the goal
            let name = rule_name.clone();
            let env_clone = state.env().clone();

            // Unfold rules work best during normalization phase
            // Give them moderate priority
            let unfold_priority = priority.saturating_sub(10);

            Some(AesopCandidate {
                priority: unfold_priority,
                apply: Box::new(move |s| apply_unfold_rule(s, &name, &env_clone)),
            })
        }
        AesopRuleBuilder::Tactic => {
            // Handled at the start of the function (doesn't require constant lookup)
            unreachable!("Tactic builder handled at function start")
        }
    }
}

/// Get candidate tactics for backtracking search
/// REQUIRES: If a current goal exists, its target and local context are well-formed in `state`.
/// ENSURES: Returns an empty vector when `state` has no current goal.
/// ENSURES: Returned candidates are sorted in descending priority order.
/// ENSURES: Candidates may include witness, rule, hypothesis, environment, `cases`, and constructor applications permitted by the current goal and config.
pub(super) fn aesop_get_candidates(
    state: &mut ProofState,
    config: &AesopConfig,
) -> Vec<AesopCandidate> {
    let mut candidates = Vec::new();

    let Some(goal) = state.current_goal() else {
        return candidates;
    };

    let target = goal.target.clone();
    let target_head = target.get_app_fn();
    let local_ctx = goal.local_ctx.clone();

    // Candidate: left/right for Or
    if let ExprKind::Const(name, _) = target_head.kind() {
        if name.to_string() == "Or" {
            candidates.push(AesopCandidate {
                priority: 50,
                apply: Box::new(left_),
            });
            candidates.push(AesopCandidate {
                priority: 50,
                apply: Box::new(right_),
            });
        }

        // Candidate: existsi for Exists with intelligent witness enumeration
        if name.to_string() == "Exists" {
            // Extract the witness type from the existential
            if let Some(witness_type) = extract_exists_witness_type(&target) {
                // Enumerate candidate witnesses for this type
                let witnesses = enumerate_witnesses(state, goal, &witness_type, &local_ctx);

                // Add a candidate for each witness (higher priority for earlier witnesses)
                for (i, witness) in witnesses.into_iter().enumerate() {
                    let priority = 35 - (i as i32).min(10); // Range from 35 to 25
                    candidates.push(AesopCandidate {
                        priority,
                        apply: Box::new(move |s| use_single(s, witness.clone())),
                    });
                }
            }
        }
    }

    // Extract head constants for indexed lookup
    let target_head_name = match target_head.kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    };

    let hyp_heads: Vec<Name> = local_ctx
        .iter()
        .filter_map(|d| match d.ty.get_app_fn().kind() {
            ExprKind::Const(name, _) => Some(name.clone()),
            _ => None,
        })
        .collect();

    // Get rule set with potential priority overrides
    // If rule_sets is non-empty, use combined rule sets with effective_priority
    // Otherwise use the default rule set directly
    let rule_set = if config.rule_sets.is_empty() {
        state.env().get_aesop_rule_set().clone()
    } else {
        state.env().get_combined_rule_sets(&config.rule_sets)
    };

    // Helper to compute priority considering phase and effective priority
    let compute_priority = |rule: &clean_kernel::AesopRule| -> i32 {
        // Use effective_priority to account for any rule set overrides
        let effective = rule_set.effective_priority(rule);
        match rule.phase {
            AesopRulePhase::Safe => 85,
            AesopRulePhase::Unsafe => 20 + (effective as i32 * 40 / 100),
            AesopRulePhase::Norm => 90, // Norm rules have highest priority
        }
    };

    // Candidate: registered aesop rules using indexed lookup
    // First get target-indexed rules (matching goal conclusion)
    if let Some(head) = &target_head_name {
        for rule in state.env().get_rules_for_target(head) {
            let priority = compute_priority(rule);
            if let Some(cand) =
                make_rule_candidate(state, goal, &rule.name, rule.builder, &target, priority)
            {
                candidates.push(cand);
            }
        }
    }

    // Get hyps-indexed rules (matching hypothesis types)
    for rule in state.env().get_rules_for_hyps(&hyp_heads) {
        let priority = compute_priority(rule);
        if let Some(cand) =
            make_rule_candidate(state, goal, &rule.name, rule.builder, &target, priority)
        {
            candidates.push(cand);
        }
    }

    // Fallback: Also check all safe/unsafe rules (backward compatibility)
    // This ensures rules registered before indexing was added still work
    // Use rule_set to apply effective_priority for overrides
    for rule in &rule_set.safe_rules {
        if let Some(cand) = make_rule_candidate(state, goal, &rule.name, rule.builder, &target, 85)
        {
            candidates.push(cand);
        }
    }

    for rule in &rule_set.unsafe_rules {
        let priority = 20 + (rule_set.effective_priority(rule) as i32 * 40 / 100);
        if let Some(cand) =
            make_rule_candidate(state, goal, &rule.name, rule.builder, &target, priority)
        {
            candidates.push(cand);
        }
    }

    // Norm rules - normalization rules like unfold, simp
    // These should have highest priority as they simplify the goal
    for rule in &rule_set.norm_rules {
        let priority = 90; // Norm rules have highest priority
        if let Some(cand) =
            make_rule_candidate(state, goal, &rule.name, rule.builder, &target, priority)
        {
            candidates.push(cand);
        }
    }

    // Candidate: apply local hypotheses
    for decl in &local_ctx {
        let decl_fvar = decl.fvar;
        let decl_ty = decl.ty.clone();

        // Check if it's a function that can be applied
        if let Some(args) = can_apply_to_produce(state, goal, &decl_ty, &target, 5) {
            if !args.is_empty() {
                candidates.push(AesopCandidate {
                    priority: 80,
                    apply: Box::new(move |s| apply(s, Expr::fvar(decl_fvar))),
                });
            }
        }
    }

    // Candidate: apply lemmas from environment (limited to avoid explosion)
    // Only consider constants whose type is a function (has at least one Pi/arrow),
    // to avoid zero-argument constructors (Nat.zero, True, etc.) trivially
    // closing goals and bypassing registered aesop rule filtering.
    // Also skip Sort-level targets (Prop/Type) since any type inhabiting the
    // sort would match, which is too aggressive.
    if !matches!(target_head.kind(), ExprKind::Sort(_)) {
        let mut const_count = 0;
        for constant in state.env().constants() {
            if const_count > 20 {
                break;
            }

            // Skip constants whose type is not a function — they are zero-arg
            // constructors or axioms that would trivially close goals
            if !matches!(constant.type_.kind(), ExprKind::Pi(..)) {
                continue;
            }

            let levels: Vec<Level> = constant
                .level_params
                .iter()
                .enumerate()
                .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
                .collect();

            let const_type = if levels.is_empty() {
                constant.type_.clone()
            } else {
                let subst: Vec<(Name, Level)> = constant
                    .level_params
                    .iter()
                    .cloned()
                    .zip(levels.iter().cloned())
                    .collect();
                constant.type_.instantiate_level_params(&subst)
            };

            if let Some(_args) = can_apply_to_produce(state, goal, &const_type, &target, 5) {
                let const_name = constant.name.clone();
                let const_levels = levels.clone();

                candidates.push(AesopCandidate {
                    priority: 40,
                    apply: Box::new(move |s| {
                        apply(s, Expr::const_(const_name.clone(), const_levels.clone()))
                    }),
                });
                const_count += 1;
            }
        }
    }

    // Candidate: cases on hypotheses with inductive types
    // Preserve existing heuristics, but allow extending the set via
    // `@[aesop ... cases <Type>]` rules.
    let mut cases_type_priorities: std::collections::HashMap<Name, i32> =
        std::collections::HashMap::new();
    for ty in ["And", "Or", "Exists", "Sum"] {
        cases_type_priorities.insert(Name::from_string(ty), 70);
    }

    // Add types from registered safe `cases` rules
    for rule in state.env().get_aesop_safe_rules() {
        if rule.builder == AesopRuleBuilder::Cases {
            for ty in &rule.builder_args {
                if state.env().get_inductive(ty).is_some() {
                    cases_type_priorities
                        .entry(ty.clone())
                        .and_modify(|p| *p = (*p).max(70))
                        .or_insert(70);
                }
            }
        }
    }

    // Add types from registered unsafe `cases` rules
    for rule in state.env().get_aesop_unsafe_rules() {
        if rule.builder == AesopRuleBuilder::Cases {
            // Convert rule priority (0-100) to candidate priority (roughly 20-60 range)
            let priority = 20 + (rule.priority as i32 * 40 / 100);
            for ty in &rule.builder_args {
                if state.env().get_inductive(ty).is_some() {
                    cases_type_priorities
                        .entry(ty.clone())
                        .and_modify(|p| *p = (*p).max(priority))
                        .or_insert(priority);
                }
            }
        }
    }

    for decl in &local_ctx {
        let decl_ty_head = decl.ty.get_app_fn();
        if let ExprKind::Const(name, _) = decl_ty_head.kind() {
            if let Some(priority) = cases_type_priorities.get(name) {
                let hyp_name = decl.name.clone();
                candidates.push(AesopCandidate {
                    priority: *priority,
                    apply: Box::new(move |s| cases(s, &hyp_name)),
                });
            }
        }
    }

    // Candidate: constructors builder - try all constructors for matching target type
    // When `@[aesop safe constructors T]` is registered, and goal is of type `T`,
    // generate candidates for each constructor of T.
    let mut constructors_type_priorities: std::collections::HashMap<Name, i32> =
        std::collections::HashMap::new();

    // Add types from registered safe `constructors` rules
    for rule in state.env().get_aesop_safe_rules() {
        if rule.builder == AesopRuleBuilder::Constructors {
            for ty in &rule.builder_args {
                if state.env().get_inductive(ty).is_some() {
                    constructors_type_priorities
                        .entry(ty.clone())
                        .and_modify(|p| *p = (*p).max(75))
                        .or_insert(75);
                }
            }
        }
    }

    // Add types from registered unsafe `constructors` rules
    for rule in state.env().get_aesop_unsafe_rules() {
        if rule.builder == AesopRuleBuilder::Constructors {
            // Convert rule priority (0-100) to candidate priority (roughly 20-60 range)
            let priority = 20 + (rule.priority as i32 * 40 / 100);
            for ty in &rule.builder_args {
                if state.env().get_inductive(ty).is_some() {
                    constructors_type_priorities
                        .entry(ty.clone())
                        .and_modify(|p| *p = (*p).max(priority))
                        .or_insert(priority);
                }
            }
        }
    }

    // Check if target type matches any registered constructors type
    if let ExprKind::Const(target_type_name, _) = target_head.kind() {
        if let Some(priority) = constructors_type_priorities.get(target_type_name) {
            // Get the inductive type info
            if let Some(ind_val) = state.env().get_inductive(target_type_name) {
                // Generate a candidate for each constructor
                for ctor_name in &ind_val.constructor_names {
                    if let Some(ctor_val) = state.env().get_constructor(ctor_name) {
                        let ctor_name_clone = ctor_name.clone();
                        // Create fresh level params for the constructor
                        let levels: Vec<Level> = ctor_val
                            .level_params
                            .iter()
                            .enumerate()
                            .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
                            .collect();
                        let lvls = levels.clone();
                        candidates.push(AesopCandidate {
                            priority: *priority,
                            apply: Box::new(move |s| {
                                apply(s, Expr::const_(ctor_name_clone.clone(), lvls.clone()))
                            }),
                        });
                    }
                }
            }
        }
    }

    // Sort by priority (higher first)
    candidates.sort_by_key(|b| std::cmp::Reverse(b.priority));

    candidates
}
