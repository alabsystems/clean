// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Single-step ring-axiom rewriting and transitivity chaining (#2442).
//!
//! Split out of `ring_proof.rs`: this half owns the *step* machinery — apply
//! one commutativity / associativity / identity axiom to a subterm, then chain
//! the remainder through `super::ring_proof::try_build_ring_eq_proof`. The
//! parent module owns the *whole-equality* strategies that drive it.

use super::ring_proof::try_build_ring_eq_proof;
use super::ring_proof_surface::{
    assoc_name, comm_name, identity_entries_for, is_identity_expr, resolve_concrete_op,
    zero_const_name,
};
use super::simp::{mk_congr_arg, mk_congr_fun, mk_eq_trans_expr};
use super::{Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

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

pub(super) fn try_ring_transitivity(
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
