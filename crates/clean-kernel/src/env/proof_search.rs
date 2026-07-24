// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operational proof search for kernel goals.
//!
//! This module performs small generate-and-test proof search by constructing
//! candidate proof terms and checking them with the kernel type checker. It is
//! distinct from `verified_proof_search`, which registers a correctness
//! formalization of proof search inside the environment.

use crate::env::{ConstantInfo, ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

#[derive(Debug, Clone)]
pub enum ProofSearchResult {
    Found {
        proof: Expr,
        strategy: &'static str,
    },
    Exhausted {
        candidates_tried: usize,
    },
    BudgetExceeded {
        candidates_tried: usize,
        budget: usize,
    },
}

pub fn search_proof(env: &Environment, goal_type: &Expr, budget: usize) -> ProofSearchResult {
    let tc = TypeChecker::with_mode(env, env.mode());
    let mut candidates_tried = 0usize;

    if let Some((ty, levels, lhs, rhs)) = parse_eq_goal(goal_type) {
        if candidates_tried >= budget {
            return ProofSearchResult::BudgetExceeded {
                candidates_tried,
                budget,
            };
        }
        candidates_tried += 1;

        if tc.is_def_eq(&lhs, &rhs) {
            let proof = mk_eq_refl(&levels, &ty, &lhs);
            if try_verify_proof(env, goal_type, &proof) {
                return ProofSearchResult::Found {
                    proof,
                    strategy: "refl",
                };
            }
        }
    }

    if goal_is_prop(&tc, goal_type) {
        if candidates_tried >= budget {
            return ProofSearchResult::BudgetExceeded {
                candidates_tried,
                budget,
            };
        }
        candidates_tried += 1;

        let proof = Expr::const_str("True.intro");
        if try_verify_proof(env, goal_type, &proof) {
            return ProofSearchResult::Found {
                proof,
                strategy: "trivial_prop",
            };
        }
    }

    let goal_levels = goal_head_levels(goal_type);
    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_cached_key(|info| (constant_kind_rank(info.kind), info.name.to_string()));

    for info in constants {
        if candidates_tried >= budget {
            return ProofSearchResult::BudgetExceeded {
                candidates_tried,
                budget,
            };
        }
        candidates_tried += 1;

        let levels = lookup_levels(info, &goal_levels);
        let Some(candidate_type) = env.instantiate_type(&info.name, &levels) else {
            continue;
        };
        if !tc.is_def_eq(&candidate_type, goal_type) {
            continue;
        }

        let candidate = Expr::const_(info.name.clone(), levels);
        if try_verify_proof(env, goal_type, &candidate) {
            return ProofSearchResult::Found {
                proof: candidate,
                strategy: "lookup",
            };
        }
    }

    ProofSearchResult::Exhausted { candidates_tried }
}

pub fn try_verify_proof(env: &Environment, goal_type: &Expr, candidate: &Expr) -> bool {
    let tc = TypeChecker::with_mode(env, env.mode());
    let Ok(candidate_type) = tc.infer_type(candidate) else {
        return false;
    };
    tc.is_def_eq(&candidate_type, goal_type)
}

pub(crate) fn parse_eq_goal(expr: &Expr) -> Option<(Expr, Vec<Level>, Expr, Expr)> {
    let args = expr.get_app_args();
    match (expr.get_app_fn().kind(), args.as_slice()) {
        (ExprKind::Const(name, levels), [ty, lhs, rhs]) if *name == Name::from_string("Eq") => {
            Some((
                (*ty).clone(),
                levels.iter().cloned().collect(),
                (*lhs).clone(),
                (*rhs).clone(),
            ))
        }
        _ => None,
    }
}

pub(crate) fn mk_eq_refl(levels: &[Level], ty: &Expr, a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.refl", levels.to_vec()),
        [ty.clone(), a.clone()],
    )
}

fn goal_is_prop(tc: &TypeChecker<'_>, goal_type: &Expr) -> bool {
    let Ok(goal_sort) = tc.infer_type(goal_type) else {
        return false;
    };
    tc.is_def_eq(&goal_sort, &Expr::prop())
}

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
