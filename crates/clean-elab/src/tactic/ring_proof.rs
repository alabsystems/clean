// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ring axiom proof building for multi-step compositions (#2442).

use super::ring_proof_surface::{
    assoc_name, comm_name, identity_entries_for, is_identity_expr, resolve_concrete_op,
    zero_const_name,
};
use super::simp::{mk_congr_arg, mk_congr_fun, mk_eq_refl_expr, mk_eq_symm_expr, mk_eq_trans_expr};
use super::{Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

const RING_PROOF_MAX_DEPTH: u8 = 3;

/// Try to build a proof of `lhs = rhs` using multi-step ring axiom compositions.
///
/// REQUIRES: `lhs` and `rhs` are the left and right sides of an equality goal.
/// ENSURES: Returns `Some(proof)` where `proof : lhs = rhs` when found
///   within depth bound. Returns `None` when no proof exists.
pub(crate) fn try_build_ring_axiom_proof(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    try_build_ring_eq_proof(state, goal, lhs, rhs, RING_PROOF_MAX_DEPTH)
}

fn try_build_ring_eq_proof(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
    depth: u8,
) -> Option<Expr> {
    if state.is_def_eq(goal, lhs, rhs) {
        return mk_eq_refl_expr(state, goal, lhs);
    }
    if depth == 0 {
        return None;
    }
    if let Some(proof) = try_single_ring_axiom(state, goal, lhs, rhs) {
        return Some(proof);
    }
    if let Some(proof) = try_single_ring_axiom(state, goal, rhs, lhs) {
        return mk_eq_symm_expr(state, goal, &proof);
    }
    if let Some(proof) = try_identity_axiom(state, goal, lhs, rhs) {
        return Some(proof);
    }
    if let Some(proof) = try_identity_axiom(state, goal, rhs, lhs) {
        return mk_eq_symm_expr(state, goal, &proof);
    }
    if let Some(proof) = try_congr_ring_op(state, goal, lhs, rhs, depth - 1) {
        return Some(proof);
    }
    if let Some(proof) = try_ring_transitivity(state, goal, lhs, rhs, depth - 1) {
        return Some(proof);
    }
    None
}

fn try_single_ring_axiom(state: &ProofState, goal: &Goal, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let lhs_head = lhs.get_app_fn();
    let rhs_head = rhs.get_app_fn();
    let lhs_args = lhs.get_app_args();
    let rhs_args = rhs.get_app_args();
    let lhs_name = match (lhs_head.kind(), rhs_head.kind()) {
        (ExprKind::Const(ln, _), ExprKind::Const(rn, _)) if ln == rn => ln.to_string(),
        _ => return None,
    };

    if lhs_args.len() < 2 || rhs_args.len() < 2 {
        return None;
    }

    let l = lhs_args.len();
    let r = rhs_args.len();
    let (a_lhs, b_lhs) = (lhs_args[l - 2], lhs_args[l - 1]);
    let (a_rhs, b_rhs) = (rhs_args[r - 2], rhs_args[r - 1]);

    // Resolve typeclass heads (HAdd.hAdd, ...) to concrete carrier ops
    // (Nat.add, ...) for surface-table lookups. Keep the raw `lhs_name` for
    // structural inner-head comparisons. Part of #3368.
    let resolved = resolve_concrete_op(&lhs_name, &lhs_args).unwrap_or_else(|| lhs_name.clone());

    if state.is_def_eq(goal, a_lhs, b_rhs) && state.is_def_eq(goal, b_lhs, a_rhs) {
        if let Some(comm) = comm_name(&resolved) {
            if state.env().get_const(&Name::from_string(comm)).is_some() {
                return Some(Expr::apps(
                    Expr::const_(Name::from_string(comm), vec![]),
                    [a_lhs.clone(), b_lhs.clone()],
                ));
            }
        }
    }

    try_assoc_match(state, goal, lhs, rhs, &lhs_name, &resolved)
}

fn try_assoc_match(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
    op_name: &str,
    resolved_op: &str,
) -> Option<Expr> {
    let lhs_args = lhs.get_app_args();
    let rhs_args = rhs.get_app_args();
    let l = lhs_args.len();
    let r = rhs_args.len();
    let (inner_lhs, c_lhs) = (lhs_args[l - 2], lhs_args[l - 1]);
    let (a_rhs, inner_rhs) = (rhs_args[r - 2], rhs_args[r - 1]);

    let inner_lhs_head = inner_lhs.get_app_fn();
    let inner_rhs_head = inner_rhs.get_app_fn();

    match (inner_lhs_head.kind(), inner_rhs_head.kind()) {
        (ExprKind::Const(ln, _), ExprKind::Const(rn, _))
            if ln.to_string() == op_name && rn.to_string() == op_name => {}
        _ => return None,
    }

    let il_args = inner_lhs.get_app_args();
    let ir_args = inner_rhs.get_app_args();
    if il_args.len() < 2 || ir_args.len() < 2 {
        return None;
    }

    let il = il_args.len();
    let ir = ir_args.len();
    let (a, b_inner) = (il_args[il - 2], il_args[il - 1]);
    let (b_rhs_inner, c_rhs) = (ir_args[ir - 2], ir_args[ir - 1]);

    if !state.is_def_eq(goal, a, a_rhs)
        || !state.is_def_eq(goal, b_inner, b_rhs_inner)
        || !state.is_def_eq(goal, c_lhs, c_rhs)
    {
        return None;
    }

    if let Some(assoc) = assoc_name(resolved_op) {
        if state.env().get_const(&Name::from_string(assoc)).is_some() {
            return Some(Expr::apps(
                Expr::const_(Name::from_string(assoc), vec![]),
                [a.clone(), b_inner.clone(), c_lhs.clone()],
            ));
        }
    }
    None
}

fn try_identity_axiom(state: &ProofState, goal: &Goal, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let head = lhs.get_app_fn();
    let args = lhs.get_app_args();
    let op_name = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        _ => return None,
    };
    if args.len() < 2 {
        return None;
    }
    let n = args.len();
    let (a, b) = (args[n - 2], args[n - 1]);
    // Resolve typeclass heads to concrete carrier ops for the lemma table and
    // the annihilator constant. Identity-element recognition stays on the raw
    // op (generic recognizer covers all carriers). Part of #3368.
    let resolved = resolve_concrete_op(&op_name, &args).unwrap_or_else(|| op_name.clone());
    for entry in identity_entries_for(&op_name, &args) {
        if state
            .env()
            .get_const(&Name::from_string(entry.lemma))
            .is_none()
        {
            continue;
        }
        let (id_arg, other) = if entry.id_on_right { (b, a) } else { (a, b) };
        if !is_identity_expr(id_arg, &op_name, entry.kind) {
            continue;
        }
        let expected = if entry.annihilator {
            Expr::const_(Name::from_string(zero_const_name(&resolved)?), vec![])
        } else {
            other.clone()
        };
        if state.is_def_eq(goal, rhs, &expected) {
            return Some(Expr::app(
                Expr::const_(Name::from_string(entry.lemma), vec![]),
                other.clone(),
            ));
        }
    }
    None
}

fn try_congr_ring_op(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
    depth: u8,
) -> Option<Expr> {
    let lhs_head = lhs.get_app_fn();
    let rhs_head = rhs.get_app_fn();
    let lhs_args = lhs.get_app_args();
    let rhs_args = rhs.get_app_args();

    match (lhs_head.kind(), rhs_head.kind()) {
        (ExprKind::Const(ln, _), ExprKind::Const(rn, _)) if ln == rn => {}
        _ => return None,
    }
    if lhs_args.len() != rhs_args.len() || lhs_args.len() < 2 {
        return None;
    }

    let n = lhs_args.len();
    for i in 0..n - 2 {
        if !state.is_def_eq(goal, lhs_args[i], rhs_args[i]) {
            return None;
        }
    }

    let (a_l, b_l) = (lhs_args[n - 2], lhs_args[n - 1]);
    let (a_r, b_r) = (rhs_args[n - 2], rhs_args[n - 1]);

    // Case 1: last arg differs
    if state.is_def_eq(goal, a_l, a_r) {
        if let Some(h_b) = try_build_ring_eq_proof(state, goal, b_l, b_r, depth) {
            let f_args: Vec<Expr> = lhs_args[..n - 1].iter().map(|e| (*e).clone()).collect();
            let f = Expr::apps_ref(lhs_head.clone(), &f_args);
            return mk_congr_arg(state, goal, &f, b_l, b_r, &h_b);
        }
    }

    // Case 2: penultimate arg differs
    if state.is_def_eq(goal, b_l, b_r) {
        if let Some(h_a) = try_build_ring_eq_proof(state, goal, a_l, a_r, depth) {
            let hf_args: Vec<Expr> = lhs_args[..n - 2].iter().map(|e| (*e).clone()).collect();
            let head_fn = Expr::apps_ref(lhs_head.clone(), &hf_args);
            if let Some(h_f) = mk_congr_arg(state, goal, &head_fn, a_l, a_r, &h_a) {
                let f_old_args: Vec<Expr> =
                    lhs_args[..n - 1].iter().map(|e| (*e).clone()).collect();
                let f_new_args: Vec<Expr> =
                    rhs_args[..n - 1].iter().map(|e| (*e).clone()).collect();
                let f_old = Expr::apps_ref(lhs_head.clone(), &f_old_args);
                let f_new = Expr::apps_ref(rhs_head.clone(), &f_new_args);
                return mk_congr_fun(state, goal, &f_old, &f_new, b_l, &h_f);
            }
        }
    }
    None
}

struct AxiomRewrite {
    result: Expr,
    proof: Expr,
}

fn try_single_axiom_rewrite(state: &ProofState, _goal: &Goal, expr: &Expr) -> Option<AxiomRewrite> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let op_name = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        _ => return None,
    };
    if args.len() < 2 {
        return None;
    }
    let n = args.len();
    let (a, b) = (args[n - 2], args[n - 1]);

    // Resolve typeclass heads to concrete carrier ops for surface lookups; keep
    // raw `op_name` for the structural inner-head comparison. Part of #3368.
    let resolved = resolve_concrete_op(&op_name, &args).unwrap_or_else(|| op_name.clone());

    if let Some(comm) = comm_name(&resolved) {
        if state.env().get_const(&Name::from_string(comm)).is_some() {
            let mut result_args: Vec<Expr> = args.iter().map(|e| (*e).clone()).collect();
            result_args[n - 2] = b.clone();
            result_args[n - 1] = a.clone();
            return Some(AxiomRewrite {
                result: Expr::apps_ref(head.clone(), &result_args),
                proof: Expr::apps(
                    Expr::const_(Name::from_string(comm), vec![]),
                    [a.clone(), b.clone()],
                ),
            });
        }
    }

    // Assoc: op (op a' b') c → op a' (op b' c)
    let inner = a;
    let inner_head = inner.get_app_fn();
    if let ExprKind::Const(inner_n, _) = inner_head.kind() {
        if inner_n.to_string() == op_name {
            let inner_args = inner.get_app_args();
            if inner_args.len() >= 2 {
                let in_n = inner_args.len();
                let (a_inner, b_inner, c) = (inner_args[in_n - 2], inner_args[in_n - 1], b);
                if let Some(assoc) = assoc_name(&resolved) {
                    if state.env().get_const(&Name::from_string(assoc)).is_some() {
                        let mut bc_args: Vec<Expr> =
                            inner_args.iter().map(|e| (*e).clone()).collect();
                        bc_args[in_n - 2] = b_inner.clone();
                        bc_args[in_n - 1] = c.clone();
                        let bc = Expr::apps_ref(inner_head.clone(), &bc_args);
                        let mut result_args: Vec<Expr> =
                            args.iter().map(|e| (*e).clone()).collect();
                        result_args[n - 2] = a_inner.clone();
                        result_args[n - 1] = bc;
                        return Some(AxiomRewrite {
                            result: Expr::apps_ref(head.clone(), &result_args),
                            proof: Expr::apps(
                                Expr::const_(Name::from_string(assoc), vec![]),
                                [a_inner.clone(), b_inner.clone(), c.clone()],
                            ),
                        });
                    }
                }
            }
        }
    }

    try_identity_rewrite(state, a, b, &op_name, &resolved, &args)
}

fn try_identity_rewrite(
    state: &ProofState,
    a: &Expr,
    b: &Expr,
    op_name: &str,
    resolved_op: &str,
    args: &[&Expr],
) -> Option<AxiomRewrite> {
    for entry in identity_entries_for(op_name, args) {
        if state
            .env()
            .get_const(&Name::from_string(entry.lemma))
            .is_none()
        {
            continue;
        }
        let (id_arg, other) = if entry.id_on_right { (b, a) } else { (a, b) };
        if !is_identity_expr(id_arg, op_name, entry.kind) {
            continue;
        }
        let result = if entry.annihilator {
            Expr::const_(Name::from_string(zero_const_name(resolved_op)?), vec![])
        } else {
            other.clone()
        };
        let proof = Expr::app(
            Expr::const_(Name::from_string(entry.lemma), vec![]),
            other.clone(),
        );
        return Some(AxiomRewrite { result, proof });
    }
    None
}

fn try_ring_transitivity(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    target: &Expr,
    depth: u8,
) -> Option<Expr> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let op_name = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        _ => return None,
    };
    if args.len() < 2 {
        return None;
    }
    let n = args.len();
    if let Some(proof) = try_comm_step(state, goal, head, &args, &op_name, target, depth) {
        return Some(proof);
    }
    if let Some(proof) = try_assoc_step(state, goal, head, &args, &op_name, target, depth) {
        return Some(proof);
    }
    if let Some(proof) = try_congr_sub_step(state, goal, head, &args, n - 2, target, depth) {
        return Some(proof);
    }
    if let Some(proof) = try_congr_sub_step(state, goal, head, &args, n - 1, target, depth) {
        return Some(proof);
    }
    None
}

fn try_comm_step(
    state: &ProofState,
    goal: &Goal,
    head: &Expr,
    args: &[&Expr],
    op_name: &str,
    target: &Expr,
    depth: u8,
) -> Option<Expr> {
    let n = args.len();
    let (a, b) = (args[n - 2], args[n - 1]);
    let resolved = resolve_concrete_op(op_name, args).unwrap_or_else(|| op_name.to_string());
    if let Some(comm) = comm_name(&resolved) {
        if state.env().get_const(&Name::from_string(comm)).is_some() {
            let mut mid_args: Vec<Expr> = args.iter().map(|e| (*e).clone()).collect();
            mid_args[n - 2] = b.clone();
            mid_args[n - 1] = a.clone();
            let mid = Expr::apps_ref(head.clone(), &mid_args);
            let step_proof = Expr::apps(
                Expr::const_(Name::from_string(comm), vec![]),
                [a.clone(), b.clone()],
            );
            let rest = try_build_ring_eq_proof(state, goal, &mid, target, depth)?;
            return mk_eq_trans_expr(state, goal, &step_proof, &rest);
        }
    }
    None
}

fn try_assoc_step(
    state: &ProofState,
    goal: &Goal,
    head: &Expr,
    args: &[&Expr],
    op_name: &str,
    target: &Expr,
    depth: u8,
) -> Option<Expr> {
    let n = args.len();
    let inner = args[n - 2];
    let c = args[n - 1];
    let inner_head = inner.get_app_fn();
    match inner_head.kind() {
        ExprKind::Const(name, _) if name.to_string() == op_name => {}
        _ => return None,
    }

    let inner_args = inner.get_app_args();
    if inner_args.len() < 2 {
        return None;
    }
    let in_n = inner_args.len();
    let (a_inner, b_inner) = (inner_args[in_n - 2], inner_args[in_n - 1]);

    let resolved = resolve_concrete_op(op_name, args).unwrap_or_else(|| op_name.to_string());
    if let Some(assoc) = assoc_name(&resolved) {
        if state.env().get_const(&Name::from_string(assoc)).is_some() {
            let mut bc_args: Vec<Expr> = inner_args.iter().map(|e| (*e).clone()).collect();
            bc_args[in_n - 2] = b_inner.clone();
            bc_args[in_n - 1] = c.clone();
            let bc = Expr::apps_ref(inner_head.clone(), &bc_args);
            let mut mid_args: Vec<Expr> = args.iter().map(|e| (*e).clone()).collect();
            mid_args[n - 2] = a_inner.clone();
            mid_args[n - 1] = bc;
            let mid = Expr::apps_ref(head.clone(), &mid_args);
            let step_proof = Expr::apps(
                Expr::const_(Name::from_string(assoc), vec![]),
                [a_inner.clone(), b_inner.clone(), c.clone()],
            );
            let rest = try_build_ring_eq_proof(state, goal, &mid, target, depth)?;
            return mk_eq_trans_expr(state, goal, &step_proof, &rest);
        }
    }
    None
}

fn try_congr_sub_step(
    state: &ProofState,
    goal: &Goal,
    head: &Expr,
    args: &[&Expr],
    sub_idx: usize,
    target: &Expr,
    depth: u8,
) -> Option<Expr> {
    let sub = args[sub_idx];
    let rewrite = try_single_axiom_rewrite(state, goal, sub)?;

    let mut mid_args: Vec<Expr> = args.iter().map(|e| (*e).clone()).collect();
    mid_args[sub_idx] = rewrite.result.clone();
    let mid = Expr::apps_ref(head.clone(), &mid_args);

    let n = args.len();
    let congr_proof = if sub_idx == n - 1 {
        let f_args: Vec<Expr> = args[..n - 1].iter().map(|e| (*e).clone()).collect();
        let f = Expr::apps_ref(head.clone(), &f_args);
        mk_congr_arg(state, goal, &f, sub, &rewrite.result, &rewrite.proof)?
    } else {
        let head_fn_args: Vec<Expr> = args[..n - 2].iter().map(|e| (*e).clone()).collect();
        let head_fn = Expr::apps_ref(head.clone(), &head_fn_args);
        let h_f = mk_congr_arg(state, goal, &head_fn, sub, &rewrite.result, &rewrite.proof)?;
        let f_old_args: Vec<Expr> = args[..n - 1].iter().map(|e| (*e).clone()).collect();
        let f_old = Expr::apps_ref(head.clone(), &f_old_args);
        let mut f_new_args = f_old_args.clone();
        f_new_args[sub_idx] = rewrite.result;
        let f_new = Expr::apps_ref(head.clone(), &f_new_args);
        mk_congr_fun(state, goal, &f_old, &f_new, args[n - 1], &h_f)?
    };

    let rest = try_build_ring_eq_proof(state, goal, &mid, target, depth)?;
    mk_eq_trans_expr(state, goal, &congr_proof, &rest)
}
