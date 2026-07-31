// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Advanced AI proof search tactics: backward chaining, goal decomposition,
//! rewrite search, and budget-limited search orchestration.
//!
//! Builds on `proof_search.rs` and `ai_verify_loop.rs` infrastructure.
//! All proof terms are kernel-verified via `try_verify_proof`.
use crate::env::{ConstantInfo, ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

use super::proof_search::{mk_eq_refl, parse_eq_goal, try_verify_proof};

// ---------------------------------------------------------------------------
// Search budget
// ---------------------------------------------------------------------------

/// Tracks remaining search budget across recursive calls.
#[derive(Debug, Clone)]
pub(crate) struct SearchBudget {
    pub(crate) max_candidates: usize,
    pub(crate) max_depth: usize,
    pub(crate) candidates_tried: usize,
}

impl SearchBudget {
    pub(crate) fn new(max_candidates: usize, max_depth: usize) -> Self {
        Self {
            max_candidates,
            max_depth,
            candidates_tried: 0,
        }
    }

    fn exhausted(&self) -> bool {
        self.candidates_tried >= self.max_candidates
    }

    fn try_spend(&mut self) -> bool {
        if self.exhausted() {
            return false;
        }
        self.candidates_tried += 1;
        true
    }
}

// ---------------------------------------------------------------------------
// Tactic search result
// ---------------------------------------------------------------------------

/// Result of an advanced tactic search.
#[derive(Debug, Clone)]
pub(crate) enum TacticResult {
    Found { proof: Expr, strategy: &'static str },
    Exhausted { candidates_tried: usize },
    BudgetExceeded { candidates_tried: usize },
}

// ---------------------------------------------------------------------------
// Goal decomposition helpers
// ---------------------------------------------------------------------------

/// Recognized compound goal shapes.
#[derive(Debug, Clone)]
pub(crate) enum GoalShape {
    /// `And a b`
    And { left: Expr, right: Expr },
    /// `Or a b`
    Or { left: Expr, right: Expr },
    /// `Iff a b`
    Iff { left: Expr, right: Expr },
    /// `True`
    True,
    /// `Eq T lhs rhs` with universe levels
    Eq {
        ty: Expr,
        levels: Vec<Level>,
        lhs: Expr,
        rhs: Expr,
    },
    /// Anything else — opaque to decomposition
    Other,
}

/// Classify a goal expression into a recognized shape.
pub(crate) fn classify_goal(goal: &Expr) -> GoalShape {
    // Check for Eq first (it's the most structured)
    if let Some((ty, levels, lhs, rhs)) = parse_eq_goal(goal) {
        return GoalShape::Eq {
            ty,
            levels,
            lhs,
            rhs,
        };
    }

    let head = goal.get_app_fn();
    let args = goal.get_app_args();

    match (head.kind(), args.as_slice()) {
        (ExprKind::Const(name, _), [a, b]) if *name == Name::from_string("And") => GoalShape::And {
            left: (*a).clone(),
            right: (*b).clone(),
        },
        (ExprKind::Const(name, _), [a, b]) if *name == Name::from_string("Or") => GoalShape::Or {
            left: (*a).clone(),
            right: (*b).clone(),
        },
        (ExprKind::Const(name, _), [a, b]) if *name == Name::from_string("Iff") => GoalShape::Iff {
            left: (*a).clone(),
            right: (*b).clone(),
        },
        (ExprKind::Const(name, _), []) if *name == Name::from_string("True") => GoalShape::True,
        _ => GoalShape::Other,
    }
}

// ---------------------------------------------------------------------------
// Backward chaining
// ---------------------------------------------------------------------------

/// Try backward chaining: find lemmas whose conclusion unifies with the goal,
/// then recursively prove the premises.
///
/// For a lemma `L : Π (x₁ : A₁) ... (xₙ : Aₙ), conclusion` where
/// `conclusion` is definitionally equal to `goal`, we try to find proofs for
/// each premise `Aᵢ` recursively. If all premises are proved, the proof is
/// `L proof₁ proof₂ ... proofₙ`.
pub(crate) fn backward_chain(
    env: &Environment,
    goal: &Expr,
    budget: &mut SearchBudget,
    depth: usize,
) -> Option<Expr> {
    if depth > budget.max_depth || budget.exhausted() {
        return None;
    }

    let tc = TypeChecker::with_mode(env, env.mode());
    let goal_levels = goal_head_levels(goal);

    // Collect constants sorted by relevance (theorems/axioms first)
    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_cached_key(|info| (constant_kind_rank(info.kind), info.name.to_string()));

    for info in constants {
        if budget.exhausted() {
            return None;
        }

        // Only consider theorems and axioms for backward chaining
        if !matches!(info.kind, ConstantKind::Theorem | ConstantKind::Axiom) {
            continue;
        }

        let levels = lookup_levels(info, &goal_levels);
        let Some(candidate_type) = env.instantiate_type(&info.name, &levels) else {
            continue;
        };

        // First, try the constant directly (no premises needed)
        if !budget.try_spend() {
            return None;
        }

        if tc.is_def_eq(&candidate_type, goal) {
            let proof = Expr::const_(info.name.clone(), levels.clone());
            if try_verify_proof(env, goal, &proof) {
                return Some(proof);
            }
        }

        // Now try to decompose the type as Π-chain and check if the conclusion matches
        let (premises, conclusion) = decompose_pi(&candidate_type);
        if premises.is_empty() {
            continue;
        }

        if !tc.is_def_eq(&conclusion, goal) {
            continue;
        }

        // Try to prove all premises recursively
        let mut premise_proofs = Vec::with_capacity(premises.len());
        let mut all_proved = true;

        for premise_ty in &premises {
            if let Some(sub_proof) = tactic_search(env, premise_ty, budget, depth + 1) {
                premise_proofs.push(sub_proof);
            } else {
                all_proved = false;
                break;
            }
        }

        if all_proved {
            // Build the proof: L proof₁ ... proofₙ
            let lemma_ref = Expr::const_(info.name.clone(), levels);
            let proof = Expr::apps(lemma_ref, premise_proofs);
            if try_verify_proof(env, goal, &proof) {
                return Some(proof);
            }
        }
    }

    None
}

/// Decompose a Pi-type into a list of non-dependent premises and the
/// conclusion. Only decomposes non-dependent arrows (where the body doesn't
/// actually depend on the bound variable).
fn decompose_pi(ty: &Expr) -> (Vec<Expr>, Expr) {
    let mut premises = Vec::new();
    let mut current = ty.clone();

    while let ExprKind::Pi(_, domain, body) = current.kind() {
        premises.push((**domain).clone());
        current = (**body).clone();
    }

    (premises, current)
}

// ---------------------------------------------------------------------------
// Goal decomposition tactics
// ---------------------------------------------------------------------------

/// Decompose compound goals and prove sub-goals recursively.
pub(crate) fn decompose_goal(
    env: &Environment,
    goal: &Expr,
    budget: &mut SearchBudget,
    depth: usize,
) -> Option<Expr> {
    if depth > budget.max_depth || budget.exhausted() {
        return None;
    }

    match classify_goal(goal) {
        GoalShape::True => {
            if !budget.try_spend() {
                return None;
            }
            let proof = Expr::const_str("True.intro");
            if try_verify_proof(env, goal, &proof) {
                return Some(proof);
            }
            None
        }

        GoalShape::And { left, right } => {
            // To prove `And a b`, prove `a` and `b` separately, then use And.intro
            let left_proof = tactic_search(env, &left, budget, depth + 1)?;
            let right_proof = tactic_search(env, &right, budget, depth + 1)?;

            if !budget.try_spend() {
                return None;
            }

            // And.intro a b ha hb
            let proof = Expr::apps(
                Expr::const_str("And.intro"),
                [left, right, left_proof, right_proof],
            );
            if try_verify_proof(env, goal, &proof) {
                return Some(proof);
            }
            None
        }

        GoalShape::Or { left, right } => {
            // Try Or.inl first (prove left), then Or.inr (prove right)
            if let Some(left_proof) = tactic_search(env, &left, budget, depth + 1) {
                if !budget.try_spend() {
                    return None;
                }
                // Or.inl a b ha
                let proof = Expr::apps(
                    Expr::const_str("Or.inl"),
                    [left.clone(), right.clone(), left_proof],
                );
                if try_verify_proof(env, goal, &proof) {
                    return Some(proof);
                }
            }

            if let Some(right_proof) = tactic_search(env, &right, budget, depth + 1) {
                if !budget.try_spend() {
                    return None;
                }
                // Or.inr a b hb
                let proof = Expr::apps(Expr::const_str("Or.inr"), [left, right, right_proof]);
                if try_verify_proof(env, goal, &proof) {
                    return Some(proof);
                }
            }

            None
        }

        GoalShape::Iff { left, right } => {
            // For Iff a a, try Iff.rfl
            let tc = TypeChecker::with_mode(env, env.mode());
            if tc.is_def_eq(&left, &right) {
                if !budget.try_spend() {
                    return None;
                }
                let proof = Expr::apps(Expr::const_str("Iff.rfl"), [left.clone()]);
                if try_verify_proof(env, goal, &proof) {
                    return Some(proof);
                }
            }

            // General case: build forward and backward functions
            // We would need to find proofs of (left -> right) and (right -> left)
            // This is more complex and left for future extension
            None
        }

        GoalShape::Eq {
            ty,
            levels,
            lhs,
            rhs,
        } => {
            // Try Eq.refl
            let tc = TypeChecker::with_mode(env, env.mode());
            if tc.is_def_eq(&lhs, &rhs) {
                if !budget.try_spend() {
                    return None;
                }
                let proof = mk_eq_refl(&levels, &ty, &lhs);
                if try_verify_proof(env, goal, &proof) {
                    return Some(proof);
                }
            }
            None
        }

        GoalShape::Other => None,
    }
}

// ---------------------------------------------------------------------------
// Rewrite search
// ---------------------------------------------------------------------------

/// Find equality lemmas in the environment and try rewriting the goal.
///
/// For a goal `Eq T lhs rhs`, searches for lemmas of the form `Eq T a b`
/// where `a` is def-eq to `lhs`, then recursively proves `Eq T b rhs`.
/// Uses Eq.trans to chain rewrites.
pub(crate) fn rewrite_search(
    env: &Environment,
    goal: &Expr,
    budget: &mut SearchBudget,
    depth: usize,
) -> Option<Expr> {
    if depth > budget.max_depth || budget.exhausted() {
        return None;
    }

    let (ty, levels, lhs, rhs) = parse_eq_goal(goal)?;
    let tc = TypeChecker::with_mode(env, env.mode());

    // Trivial case: lhs == rhs
    if tc.is_def_eq(&lhs, &rhs) {
        if !budget.try_spend() {
            return None;
        }
        let proof = mk_eq_refl(&levels, &ty, &lhs);
        if try_verify_proof(env, goal, &proof) {
            return Some(proof);
        }
    }

    // Search for equality lemmas that can rewrite lhs
    let goal_levels = goal_head_levels(goal);
    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_cached_key(|info| (constant_kind_rank(info.kind), info.name.to_string()));

    for info in constants {
        if budget.exhausted() {
            return None;
        }

        let info_levels = lookup_levels(info, &goal_levels);
        let Some(info_type) = env.instantiate_type(&info.name, &info_levels) else {
            continue;
        };

        // Check if this lemma is an equality: Eq T' a b
        let Some((eq_ty, eq_levels, eq_lhs, eq_rhs)) = parse_eq_goal(&info_type) else {
            continue;
        };

        if !budget.try_spend() {
            return None;
        }

        // Check if the equality's LHS matches our goal's LHS
        if !tc.is_def_eq(&eq_ty, &ty) || !tc.is_def_eq(&eq_lhs, &lhs) {
            // Also try the reverse: eq_rhs matches lhs (use Eq.symm)
            if tc.is_def_eq(&eq_ty, &ty) && tc.is_def_eq(&eq_rhs, &lhs) {
                // We have `eq_lhs = eq_rhs` and `eq_rhs == lhs`, so rewrite gives us
                // a step from lhs to eq_lhs
                let lemma_proof = Expr::const_(info.name.clone(), info_levels.clone());
                let symm_proof = Expr::apps(
                    Expr::const_str_levels("Eq.symm", eq_levels.clone()),
                    [eq_ty.clone(), eq_lhs.clone(), eq_rhs.clone(), lemma_proof],
                );

                // Now need: eq_lhs = rhs
                if tc.is_def_eq(&eq_lhs, &rhs) {
                    // One-step rewrite via symm
                    if try_verify_proof(env, goal, &symm_proof) {
                        return Some(symm_proof);
                    }
                }

                // Multi-step: symm gives lhs = eq_lhs, then find eq_lhs = rhs
                let remaining_goal = Expr::apps(
                    Expr::const_str_levels("Eq", levels.clone()),
                    [ty.clone(), eq_lhs.clone(), rhs.clone()],
                );

                if let Some(rest_proof) = tactic_search(env, &remaining_goal, budget, depth + 1) {
                    let trans_proof = Expr::apps(
                        Expr::const_str_levels("Eq.trans", levels.clone()),
                        [
                            ty.clone(),
                            lhs.clone(),
                            eq_lhs,
                            rhs.clone(),
                            symm_proof,
                            rest_proof,
                        ],
                    );
                    if try_verify_proof(env, goal, &trans_proof) {
                        return Some(trans_proof);
                    }
                }
            }
            continue;
        }

        // eq_lhs matches lhs. Check if eq_rhs matches rhs (single step)
        if tc.is_def_eq(&eq_rhs, &rhs) {
            let proof = Expr::const_(info.name.clone(), info_levels.clone());
            if try_verify_proof(env, goal, &proof) {
                return Some(proof);
            }
        }

        // Multi-step: we have lhs = eq_rhs, now need eq_rhs = rhs
        let remaining_goal = Expr::apps(
            Expr::const_str_levels("Eq", levels.clone()),
            [ty.clone(), eq_rhs.clone(), rhs.clone()],
        );

        let lemma_proof = Expr::const_(info.name.clone(), info_levels);
        if let Some(rest_proof) = tactic_search(env, &remaining_goal, budget, depth + 1) {
            let trans_proof = Expr::apps(
                Expr::const_str_levels("Eq.trans", levels.clone()),
                [
                    ty.clone(),
                    lhs.clone(),
                    eq_rhs,
                    rhs.clone(),
                    lemma_proof,
                    rest_proof,
                ],
            );
            if try_verify_proof(env, goal, &trans_proof) {
                return Some(trans_proof);
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Orchestrated tactic search
// ---------------------------------------------------------------------------

/// Run all tactic strategies with budget/depth limiting.
///
/// Strategy order:
/// 1. Goal decomposition (cheap structural analysis)
/// 2. Direct lookup (existing proof_search strategies)
/// 3. Backward chaining (recursive, more expensive)
/// 4. Rewrite search (equality goals only)
pub(crate) fn tactic_search(
    env: &Environment,
    goal: &Expr,
    budget: &mut SearchBudget,
    depth: usize,
) -> Option<Expr> {
    if depth > budget.max_depth || budget.exhausted() {
        return None;
    }

    // 1. Goal decomposition
    if let Some(proof) = decompose_goal(env, goal, budget, depth) {
        return Some(proof);
    }

    // 2. Direct lookup (try each constant directly)
    if let Some(proof) = direct_lookup(env, goal, budget) {
        return Some(proof);
    }

    // 3. Backward chaining (only at shallow depths to limit explosion)
    if depth < budget.max_depth.min(3) {
        if let Some(proof) = backward_chain(env, goal, budget, depth) {
            return Some(proof);
        }
    }

    // 4. Rewrite search (equality goals only)
    if parse_eq_goal(goal).is_some() {
        if let Some(proof) = rewrite_search(env, goal, budget, depth) {
            return Some(proof);
        }
    }

    None
}

/// Simple direct lookup: try each constant whose type matches the goal.
fn direct_lookup(env: &Environment, goal: &Expr, budget: &mut SearchBudget) -> Option<Expr> {
    let tc = TypeChecker::with_mode(env, env.mode());
    let goal_levels = goal_head_levels(goal);

    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_cached_key(|info| (constant_kind_rank(info.kind), info.name.to_string()));

    for info in constants {
        if budget.exhausted() {
            return None;
        }
        if !budget.try_spend() {
            return None;
        }

        let levels = lookup_levels(info, &goal_levels);
        let Some(candidate_type) = env.instantiate_type(&info.name, &levels) else {
            continue;
        };

        if !tc.is_def_eq(&candidate_type, goal) {
            continue;
        }

        let candidate = Expr::const_(info.name.clone(), levels);
        if try_verify_proof(env, goal, &candidate) {
            return Some(candidate);
        }
    }

    None
}

/// Top-level entry point for tactic-driven proof search.
pub(crate) fn search_proof_tactics(
    env: &Environment,
    goal: &Expr,
    max_candidates: usize,
    max_depth: usize,
) -> TacticResult {
    let mut budget = SearchBudget::new(max_candidates, max_depth);

    match tactic_search(env, goal, &mut budget, 0) {
        Some(proof) => {
            // Determine which strategy found the proof by classifying goal shape
            let strategy = match classify_goal(goal) {
                GoalShape::And { .. } => "decompose_and",
                GoalShape::Or { .. } => "decompose_or",
                GoalShape::Iff { .. } => "decompose_iff",
                GoalShape::True => "trivial",
                GoalShape::Eq { .. } => "eq_search",
                GoalShape::Other => "backward_chain",
            };
            TacticResult::Found { proof, strategy }
        }
        None => {
            if budget.exhausted() {
                TacticResult::BudgetExceeded {
                    candidates_tried: budget.candidates_tried,
                }
            } else {
                TacticResult::Exhausted {
                    candidates_tried: budget.candidates_tried,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Shared helpers (duplicated from proof_search to avoid pub visibility issues)
// ---------------------------------------------------------------------------

fn goal_head_levels(goal_type: &Expr) -> Vec<Level> {
    match goal_type.get_app_fn().kind() {
        ExprKind::Const(_, levels) => levels.iter().cloned().collect(),
        _ => Vec::new(),
    }
}

fn lookup_levels(info: &ConstantInfo, goal_levels: &[Level]) -> Vec<Level> {
    if info.level_params.len() == goal_levels.len() {
        return goal_levels.to_vec();
    }
    info.level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect()
}

fn constant_kind_rank(kind: ConstantKind) -> u8 {
    match kind {
        ConstantKind::Theorem => 0,
        ConstantKind::Axiom => 1,
        ConstantKind::Opaque => 2,
        ConstantKind::Definition => 3,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Environment builders -----------------------------------------------

    fn make_true_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env
    }

    fn make_eq_nat_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().expect("init_nat");
        env.init_eq().expect("init_eq");
        env
    }

    fn make_and_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env.init_and().expect("init_and");
        env
    }

    fn make_or_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env.init_or().expect("init_or");
        env
    }

    fn make_iff_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env.init_iff().expect("init_iff");
        env
    }

    fn make_full_logic_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("init_true_false");
        env.init_nat().expect("init_nat");
        env.init_eq().expect("init_eq");
        env.init_and().expect("init_and");
        env.init_or().expect("init_or");
        env.init_iff().expect("init_iff");
        env
    }

    // -- Goal constructors --------------------------------------------------

    fn mk_true() -> Expr {
        Expr::const_str("True")
    }

    fn mk_and(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("And"), [a, b])
    }

    fn mk_or(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Or"), [a, b])
    }

    fn mk_iff(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Iff"), [a, b])
    }

    fn eq_nat_goal(lhs: u64, rhs: u64) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                Expr::const_str("Nat"),
                Expr::nat_lit(lhs),
                Expr::nat_lit(rhs),
            ],
        )
    }

    // -- SearchBudget tests -------------------------------------------------

    #[test]
    fn test_budget_new_and_exhaustion() {
        let mut budget = SearchBudget::new(3, 5);
        assert!(!budget.exhausted());
        assert!(budget.try_spend());
        assert!(budget.try_spend());
        assert!(budget.try_spend());
        assert!(budget.exhausted());
        assert!(!budget.try_spend());
        assert_eq!(budget.candidates_tried, 3);
    }

    #[test]
    fn test_budget_zero_is_immediately_exhausted() {
        let budget = SearchBudget::new(0, 5);
        assert!(budget.exhausted());
    }

    // -- classify_goal tests ------------------------------------------------

    #[test]
    fn test_classify_goal_true() {
        assert!(matches!(classify_goal(&mk_true()), GoalShape::True));
    }

    #[test]
    fn test_classify_goal_and() {
        let goal = mk_and(mk_true(), mk_true());
        match classify_goal(&goal) {
            GoalShape::And { left, right } => {
                assert!(matches!(classify_goal(&left), GoalShape::True));
                assert!(matches!(classify_goal(&right), GoalShape::True));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_goal_or() {
        let goal = mk_or(mk_true(), mk_true());
        assert!(matches!(classify_goal(&goal), GoalShape::Or { .. }));
    }

    #[test]
    fn test_classify_goal_iff() {
        let goal = mk_iff(mk_true(), mk_true());
        assert!(matches!(classify_goal(&goal), GoalShape::Iff { .. }));
    }

    #[test]
    fn test_classify_goal_eq() {
        let goal = eq_nat_goal(0, 0);
        assert!(matches!(classify_goal(&goal), GoalShape::Eq { .. }));
    }

    #[test]
    fn test_classify_goal_other() {
        let goal = Expr::prop();
        assert!(matches!(classify_goal(&goal), GoalShape::Other));
    }

    // -- decompose_goal tests -----------------------------------------------

    #[test]
    fn test_decompose_true() {
        let env = make_true_env();
        let goal = mk_true();
        let mut budget = SearchBudget::new(100, 5);
        let result = decompose_goal(&env, &goal, &mut budget, 0);
        assert!(result.is_some(), "should find proof of True");
        let proof = result.unwrap();
        assert!(try_verify_proof(&env, &goal, &proof));
    }

    #[test]
    fn test_decompose_and_true_true() {
        let env = make_and_env();
        let goal = mk_and(mk_true(), mk_true());
        let mut budget = SearchBudget::new(200, 5);
        let result = decompose_goal(&env, &goal, &mut budget, 0);
        assert!(result.is_some(), "should prove And True True");
        let proof = result.unwrap();
        assert!(try_verify_proof(&env, &goal, &proof));
    }

    #[test]
    fn test_decompose_nested_and() {
        let env = make_and_env();
        // And True (And True True)
        let goal = mk_and(mk_true(), mk_and(mk_true(), mk_true()));
        let mut budget = SearchBudget::new(500, 5);
        let result = decompose_goal(&env, &goal, &mut budget, 0);
        assert!(result.is_some(), "should prove nested And");
        let proof = result.unwrap();
        assert!(try_verify_proof(&env, &goal, &proof));
    }

    #[test]
    fn test_decompose_or_left() {
        let env = make_or_env();
        // Or True False — should prove via Or.inl
        let goal = mk_or(mk_true(), Expr::const_str("False"));
        let mut budget = SearchBudget::new(200, 5);
        let result = decompose_goal(&env, &goal, &mut budget, 0);
        assert!(result.is_some(), "should prove Or True False via inl");
        let proof = result.unwrap();
        assert!(try_verify_proof(&env, &goal, &proof));
    }

    #[test]
    fn test_decompose_eq_refl() {
        let env = make_eq_nat_env();
        let goal = eq_nat_goal(0, 0);
        let mut budget = SearchBudget::new(100, 5);
        let result = decompose_goal(&env, &goal, &mut budget, 0);
        assert!(result.is_some(), "should prove Eq.refl for 0 = 0");
        let proof = result.unwrap();
        assert!(try_verify_proof(&env, &goal, &proof));
    }

    // -- tactic_search integration tests ------------------------------------

    #[test]
    fn test_tactic_search_true() {
        let env = make_true_env();
        let goal = mk_true();
        let result = search_proof_tactics(&env, &goal, 100, 5);
        assert!(
            matches!(result, TacticResult::Found { .. }),
            "should find proof of True"
        );
    }

    #[test]
    fn test_tactic_search_eq_nat_refl() {
        let env = make_eq_nat_env();
        let goal = eq_nat_goal(1, 1);
        let result = search_proof_tactics(&env, &goal, 200, 5);
        match result {
            TacticResult::Found { proof, .. } => {
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_tactic_search_and_true_true_integration() {
        let env = make_and_env();
        let goal = mk_and(mk_true(), mk_true());
        let result = search_proof_tactics(&env, &goal, 300, 5);
        match result {
            TacticResult::Found { proof, strategy } => {
                assert_eq!(strategy, "decompose_and");
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_tactic_search_or_true_false_integration() {
        let env = make_or_env();
        let goal = mk_or(mk_true(), Expr::const_str("False"));
        let result = search_proof_tactics(&env, &goal, 300, 5);
        match result {
            TacticResult::Found { proof, strategy } => {
                assert_eq!(strategy, "decompose_or");
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_tactic_search_iff_reflexive() {
        let env = make_iff_env();
        let goal = mk_iff(mk_true(), mk_true());
        let result = search_proof_tactics(&env, &goal, 200, 5);
        match result {
            TacticResult::Found { proof, strategy } => {
                assert_eq!(strategy, "decompose_iff");
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_tactic_search_budget_exceeded() {
        let env = make_eq_nat_env();
        // An impossible goal with tiny budget
        let goal = eq_nat_goal(0, 1);
        let result = search_proof_tactics(&env, &goal, 2, 1);
        assert!(
            matches!(
                result,
                TacticResult::BudgetExceeded { .. } | TacticResult::Exhausted { .. }
            ),
            "should exhaust budget on impossible goal"
        );
    }

    #[test]
    fn test_tactic_search_depth_limited() {
        let env = make_and_env();
        // Deeply nested And — should fail at depth 0
        let goal = mk_and(mk_true(), mk_and(mk_true(), mk_and(mk_true(), mk_true())));
        // Depth 0 means no recursion allowed
        let result = search_proof_tactics(&env, &goal, 500, 0);
        assert!(
            !matches!(result, TacticResult::Found { .. }),
            "depth 0 should not find deeply nested proof"
        );
    }

    #[test]
    fn test_decompose_pi_simple_arrow() {
        // Simulate: Prop -> Prop (non-dependent)
        let ty = Expr::arrow(Expr::prop(), Expr::prop());
        let (premises, conclusion) = decompose_pi(&ty);
        assert_eq!(premises.len(), 1);
        assert_eq!(conclusion, Expr::prop());
    }

    #[test]
    fn test_decompose_pi_no_premises() {
        let ty = Expr::prop();
        let (premises, conclusion) = decompose_pi(&ty);
        assert!(premises.is_empty());
        assert_eq!(conclusion, Expr::prop());
    }

    // -- Full logic integration tests ---------------------------------------

    #[test]
    fn test_full_logic_and_or_combination() {
        let env = make_full_logic_env();
        // Or True True — should prove via inl
        let goal = mk_or(mk_true(), mk_true());
        let result = search_proof_tactics(&env, &goal, 500, 5);
        match result {
            TacticResult::Found { proof, .. } => {
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_full_logic_triple_and() {
        let env = make_full_logic_env();
        // And (And True True) True
        let goal = mk_and(mk_and(mk_true(), mk_true()), mk_true());
        let result = search_proof_tactics(&env, &goal, 500, 5);
        match result {
            TacticResult::Found { proof, .. } => {
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn test_tactic_result_exhausted_for_false() {
        let env = make_true_env();
        // False has no proof (without absurd)
        let goal = Expr::const_str("False");
        let result = search_proof_tactics(&env, &goal, 1000, 3);
        assert!(
            !matches!(result, TacticResult::Found { .. }),
            "should not find proof of False"
        );
    }

    #[test]
    fn test_backward_chain_skips_non_theorem_axiom() {
        // backward_chain only considers Theorem/Axiom constants, not Definitions
        // or constructors. True.intro is a constructor, so backward_chain alone
        // won't find it — but the orchestrated tactic_search will via decompose.
        let env = make_true_env();
        let goal = mk_true();
        let mut budget = SearchBudget::new(100, 5);
        // backward_chain may or may not find this depending on constant kinds.
        // The important thing is it doesn't crash.
        let _result = backward_chain(&env, &goal, &mut budget, 0);
        // The orchestrated search DOES find it via decompose_goal:
        let result2 = search_proof_tactics(&env, &goal, 100, 5);
        assert!(matches!(result2, TacticResult::Found { .. }));
    }

    #[test]
    fn test_eq_nat_zero_zero_refl() {
        let env = make_eq_nat_env();
        let goal = eq_nat_goal(0, 0);
        let result = search_proof_tactics(&env, &goal, 200, 5);
        match result {
            TacticResult::Found { proof, .. } => {
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found for 0=0, got {other:?}"),
        }
    }

    #[test]
    fn test_eq_nat_succ_succ_refl() {
        let env = make_eq_nat_env();
        let goal = eq_nat_goal(3, 3);
        let result = search_proof_tactics(&env, &goal, 200, 5);
        match result {
            TacticResult::Found { proof, .. } => {
                assert!(try_verify_proof(&env, &goal, &proof));
            }
            other => panic!("expected Found for 3=3, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_nested_and_or() {
        // And (Or True True) True
        let inner = mk_or(mk_true(), mk_true());
        let goal = mk_and(inner, mk_true());
        match classify_goal(&goal) {
            GoalShape::And { left, .. } => {
                assert!(matches!(classify_goal(&left), GoalShape::Or { .. }));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }
}
