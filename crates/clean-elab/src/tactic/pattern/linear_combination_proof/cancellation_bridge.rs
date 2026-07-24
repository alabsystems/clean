// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cancellation bridge for linear combination proof reconstruction.

use clean_kernel::name::Name;
use clean_kernel::tc::whnf_proof::EqProofBuilder;
use clean_kernel::{Expr, ExprKind};

use super::super::super::core::{Goal, ProofState};
use super::super::util::try_extract_eq;
use super::expr_builders::{carrier_name, make_add_app, make_eq_type};
use super::{prove_eq_by_ring_nf, try_close_with_proof, EqAcc};

/// Connect the combined equality to the goal via a shared additive witness.
pub(super) fn try_with_cancellation_bridge(
    state: &ProofState,
    goal: &Goal,
    acc: &EqAcc,
) -> Option<Expr> {
    let target = state.metas.instantiate(&goal.target);
    let (goal_lhs, goal_rhs) = try_extract_eq(&target)?;

    for witness in find_shared_additive_witnesses(&acc.alpha, &acc.lhs, &acc.rhs) {
        let Some(goal_lhs_plus_witness) = make_add_app(&acc.alpha, &goal_lhs, &witness) else {
            continue;
        };
        let Some(goal_rhs_plus_witness) = make_add_app(&acc.alpha, &goal_rhs, &witness) else {
            continue;
        };

        let Some(left_proof) = prove_eq_by_ring_nf(
            state,
            goal,
            make_eq_type(&acc.alpha, &goal_lhs_plus_witness, &acc.lhs, &acc.u),
        ) else {
            continue;
        };
        let Some(right_proof) = prove_eq_by_ring_nf(
            state,
            goal,
            make_eq_type(&acc.alpha, &acc.rhs, &goal_rhs_plus_witness, &acc.u),
        ) else {
            continue;
        };

        let bridged_eq = EqProofBuilder::mk_eq_trans(
            acc.u.clone(),
            acc.alpha.clone(),
            goal_lhs_plus_witness.clone(),
            acc.lhs.clone(),
            goal_rhs_plus_witness.clone(),
            left_proof,
            EqProofBuilder::mk_eq_trans(
                acc.u.clone(),
                acc.alpha.clone(),
                acc.lhs.clone(),
                acc.rhs.clone(),
                goal_rhs_plus_witness.clone(),
                acc.proof.clone(),
                right_proof,
            ),
        );

        if let Some(proof) = cancel_shared_additive_witness(
            state,
            goal,
            &acc.alpha,
            goal_lhs.clone(),
            goal_rhs.clone(),
            witness,
            bridged_eq,
        ) {
            return Some(proof);
        }
    }

    None
}

fn find_shared_additive_witnesses(alpha: &Expr, lhs: &Expr, rhs: &Expr) -> Vec<Expr> {
    let mut lhs_candidates = Vec::new();
    collect_additive_candidates(alpha, lhs, &mut lhs_candidates);

    let mut rhs_candidates = Vec::new();
    collect_additive_candidates(alpha, rhs, &mut rhs_candidates);

    let mut witnesses = Vec::new();
    for candidate in lhs_candidates {
        if rhs_candidates.contains(&candidate) && !witnesses.contains(&candidate) {
            witnesses.push(candidate);
        }
    }
    witnesses
}

fn collect_additive_candidates(alpha: &Expr, expr: &Expr, candidates: &mut Vec<Expr>) {
    if !candidates.contains(expr) {
        candidates.push(expr.clone());
    }

    if let Some((lhs, rhs)) = split_add_app(alpha, expr) {
        collect_additive_candidates(alpha, &lhs, candidates);
        collect_additive_candidates(alpha, &rhs, candidates);
    }
}

fn split_add_app(alpha: &Expr, expr: &Expr) -> Option<(Expr, Expr)> {
    let add_name = add_op_name(alpha)?;
    let args = expr.get_app_args();
    if args.len() != 2 {
        return None;
    }
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) if name.to_string() == add_name => {
            Some(((*args[0]).clone(), (*args[1]).clone()))
        }
        _ => None,
    }
}

fn add_op_name(alpha: &Expr) -> Option<&'static str> {
    match carrier_name(alpha)? {
        "Nat" => Some("Nat.add"),
        "Int" => Some("Int.add"),
        "Rat" => Some("Rat.add"),
        "Real" => Some("Real.add"),
        _ => None,
    }
}

fn cancel_shared_additive_witness(
    state: &ProofState,
    goal: &Goal,
    alpha: &Expr,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let proof = match carrier_name(alpha)? {
        "Nat" => apply_nat_add_right_cancel(state, goal_lhs, goal_rhs, witness, bridged_eq)?,
        "Int" => apply_int_add_right_cancel(state, goal_lhs, goal_rhs, witness, bridged_eq)?,
        "Rat" => apply_rat_add_right_cancel(state, goal_lhs, goal_rhs, witness, bridged_eq)?,
        "Real" => apply_real_add_right_cancel(state, goal_lhs, goal_rhs, witness, bridged_eq)?,
        _ => return None,
    };

    if try_close_with_proof(state, goal, &proof).is_ok() {
        Some(proof)
    } else {
        None
    }
}

fn apply_nat_add_right_cancel(
    state: &ProofState,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let theorem = Name::from_string("Nat.add_right_cancel");
    state.env().get_const(&theorem)?;
    Some(Expr::apps(
        Expr::const_(theorem, vec![]),
        [goal_lhs, witness, goal_rhs, bridged_eq],
    ))
}

fn apply_int_add_right_cancel(
    state: &ProofState,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let theorem = Name::from_string("Int.add_right_cancel");
    state.env().get_const(&theorem)?;
    Some(Expr::apps(
        Expr::const_(theorem, vec![]),
        [goal_lhs, witness, goal_rhs, bridged_eq],
    ))
}

fn apply_rat_add_right_cancel(
    state: &ProofState,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let theorem = Name::from_string("Rat.add_right_cancel");
    state.env().get_const(&theorem)?;
    Some(Expr::apps(
        Expr::const_(theorem, vec![]),
        [goal_lhs, witness, goal_rhs, bridged_eq],
    ))
}

fn apply_real_add_right_cancel(
    state: &ProofState,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let theorem = Name::from_string("Real.add_right_cancel");
    state.env().get_const(&theorem)?;
    Some(Expr::apps(
        Expr::const_(theorem, vec![]),
        [goal_lhs, witness, goal_rhs, bridged_eq],
    ))
}
