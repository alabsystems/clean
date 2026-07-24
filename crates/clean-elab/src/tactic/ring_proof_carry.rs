// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying ring normalization (#2501). Builds proofs during normalization.
//!
//! Sort/reorder proof construction is in [`ring_proof_sort`].

use super::ring_proof_sort::merge_sorted_chains;
use super::ring_proof_surface::{
    distribution_entry, identity_entries, is_identity_expr, neg_neg_name, resolve_concrete_binop,
    sub_eq_add_neg_name, sub_to_add_op, sub_to_neg_op, zero_const_name, DistributionEntry,
};
use super::simp::{mk_congr_arg, mk_congr_fun, mk_eq_refl_expr, mk_eq_symm_expr, mk_eq_trans_expr};
use super::{Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

pub(crate) struct RingRewriteResult {
    pub expr: Expr,
    pub proof: Option<Expr>,
}

pub(crate) fn ring_normalize_with_proof(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Option<RingRewriteResult> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if matches!(
                s.as_str(),
                "Nat.add"
                    | "Nat.mul"
                    | "Int.add"
                    | "Int.mul"
                    | "Rat.add"
                    | "Rat.mul"
                    | "HAdd.hAdd"
                    | "HMul.hMul"
            ) && args.len() >= 2
            {
                return normalize_binop(state, goal, expr, &s);
            }
            // Subtraction: rewrite a - b to a + (-b) via sub_eq_add_neg. Part of #3368.
            if matches!(s.as_str(), "Int.sub" | "HSub.hSub") && args.len() >= 2 {
                return normalize_sub(state, goal, expr, &s);
            }
            // Negation: normalize inner and handle double negation. Part of #3368.
            if matches!(s.as_str(), "Int.neg" | "Neg.neg") && !args.is_empty() {
                return normalize_neg(state, goal, expr, &s);
            }
            Some(atom_result(expr))
        }
        _ => Some(atom_result(expr)),
    }
}

fn atom_result(expr: &Expr) -> RingRewriteResult {
    RingRewriteResult {
        expr: expr.clone(),
        proof: None,
    }
}

fn normalize_binop(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    op_name: &str,
) -> Option<RingRewriteResult> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let n = args.len();
    let (a, b) = (args[n - 2], args[n - 1]);
    let a_r = ring_normalize_with_proof(state, goal, a)?;
    let b_r = ring_normalize_with_proof(state, goal, b)?;

    // Resolve typeclass heads (HAdd.hAdd / HMul.hMul / HSub.hSub) to a concrete
    // carrier operator (Nat.add / ...) for surface-lemma lookups AND for the
    // structural NF building below. Concrete carrier operators take exactly two
    // args (empty prefix); the rebuilt concrete-headed chains are definitionally
    // equal to the original typeclass-headed forms, so the proof-carrying chain
    // type-checks at `close_goal` (which WHNF-normalizes before is_def_eq).
    // For already-concrete heads this is a no-op. Part of #3368.
    let (struct_op, struct_head, struct_prefix): (String, Expr, Vec<Expr>) =
        match resolve_concrete_binop(op_name, &args) {
            Some((rop, rhead)) => (rop, rhead, Vec::new()),
            None => (
                op_name.to_string(),
                head.clone(),
                args[..n - 2].iter().map(|e| (*e).clone()).collect(),
            ),
        };

    if let Some(r) = try_identity_elim(state, goal, expr, &a_r, &b_r, op_name) {
        return Some(r);
    }

    // Distribution: a * (b + c) or (a + b) * c.
    if let Some(r) = try_distribute(state, goal, expr, &a_r, &b_r, &struct_op) {
        return Some(r);
    }

    let congr = build_child_congr(state, goal, head, &args, &a_r, &b_r)?;

    let a_terms = collect_op_terms(&a_r.expr, &struct_op);
    let b_terms = collect_op_terms(&b_r.expr, &struct_op);

    let (merged, merge_proof) = merge_sorted_chains(
        state,
        goal,
        &a_r.expr,
        &b_r.expr,
        &a_terms,
        &b_terms,
        &struct_op,
        &struct_head,
        &struct_prefix,
    )?;

    let total_proof = chain_optional(state, goal, congr.proof, merge_proof);
    Some(RingRewriteResult {
        expr: merged,
        proof: total_proof,
    })
}

/// Normalize subtraction by rewriting `a - b` to `a + (-b)` via the
/// `sub_eq_add_neg` lemma, then recursing on the addition.
///
/// Part of #3368.
fn normalize_sub(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    op_name: &str,
) -> Option<RingRewriteResult> {
    let lemma_name = sub_eq_add_neg_name(op_name)?;
    let add_op = sub_to_add_op(op_name)?;
    let neg_op = sub_to_neg_op(op_name)?;

    // Check that the lemma exists in the environment
    state.env().get_const(&Name::from_string(lemma_name))?;

    let args = expr.get_app_args();
    let n = args.len();
    let (a, b) = (args[n - 2], args[n - 1]);

    // Build the rewritten expression: add(a, neg(b))
    let neg_b = Expr::app(Expr::const_(Name::from_string(neg_op), vec![]), b.clone());
    let rewritten = Expr::app(
        Expr::app(Expr::const_(Name::from_string(add_op), vec![]), a.clone()),
        neg_b,
    );

    // Build proof: sub_eq_add_neg a b
    let sub_proof = Expr::apps(
        Expr::const_(Name::from_string(lemma_name), vec![]),
        [a.clone(), b.clone()],
    );

    // Normalize the rewritten addition recursively
    let add_r = ring_normalize_with_proof(state, goal, &rewritten)?;
    let total_proof = chain_optional(state, goal, Some(sub_proof), add_r.proof);
    Some(RingRewriteResult {
        expr: add_r.expr,
        proof: total_proof,
    })
}

/// Normalize negation: recurse into the inner expression, then handle
/// double negation elimination via `neg_neg`.
///
/// Part of #3368.
fn normalize_neg(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    op_name: &str,
) -> Option<RingRewriteResult> {
    let args = expr.get_app_args();
    let inner = args[args.len() - 1];
    let head = expr.get_app_fn();

    // Normalize the inner expression first
    let inner_r = ring_normalize_with_proof(state, goal, inner)?;

    // Build congruence proof if inner changed: neg(inner) = neg(inner_r.expr)
    let congr_proof = if let Some(ref inner_pf) = inner_r.proof {
        // Build: congrArg neg inner inner_r.expr inner_pf
        let neg_fn = {
            let prefix: Vec<Expr> = args[..args.len() - 1]
                .iter()
                .map(|e| (*e).clone())
                .collect();
            Expr::apps_ref(head.clone(), &prefix)
        };
        mk_congr_arg(state, goal, &neg_fn, inner, &inner_r.expr, inner_pf)
    } else {
        None
    };

    // Check for double negation: neg(neg(x)) = x
    let inner_head = inner_r.expr.get_app_fn();
    if let ExprKind::Const(inner_name, _) = inner_head.kind() {
        if inner_name.to_string() == op_name {
            if let Some(neg_neg) = neg_neg_name(op_name) {
                if state.env().get_const(&Name::from_string(neg_neg)).is_some() {
                    let inner_inner_args = inner_r.expr.get_app_args();
                    if !inner_inner_args.is_empty() {
                        let x = inner_inner_args[inner_inner_args.len() - 1];
                        // neg_neg x : neg(neg(x)) = x
                        let neg_neg_proof =
                            Expr::app(Expr::const_(Name::from_string(neg_neg), vec![]), x.clone());
                        let total = chain_optional(state, goal, congr_proof, Some(neg_neg_proof));
                        return Some(RingRewriteResult {
                            expr: x.clone(),
                            proof: total,
                        });
                    }
                }
            }
        }
    }

    // No double negation — return neg(normalized_inner)
    let result_expr = {
        let mut result_args: Vec<Expr> = args[..args.len() - 1]
            .iter()
            .map(|e| (*e).clone())
            .collect();
        result_args.push(inner_r.expr);
        Expr::apps_ref(head.clone(), &result_args)
    };
    Some(RingRewriteResult {
        expr: result_expr,
        proof: congr_proof,
    })
}

fn try_identity_elim(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    a_r: &RingRewriteResult,
    b_r: &RingRewriteResult,
    op_name: &str,
) -> Option<RingRewriteResult> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let n = args.len();

    for entry in identity_entries(op_name) {
        if state
            .env()
            .get_const(&Name::from_string(entry.lemma))
            .is_none()
        {
            continue;
        }
        let (id_side, other_side) = if entry.id_on_right {
            (&b_r, &a_r)
        } else {
            (&a_r, &b_r)
        };
        if !is_identity_expr(&id_side.expr, op_name, entry.kind) {
            continue;
        }
        let orig_other = if entry.id_on_right {
            args[n - 2]
        } else {
            args[n - 1]
        };
        let result_expr = if entry.annihilator {
            Expr::const_(Name::from_string(zero_const_name(op_name)?), vec![])
        } else {
            other_side.expr.clone()
        };

        let congr = build_child_congr(state, goal, head, &args, a_r, b_r);
        let identity_proof = Expr::app(
            Expr::const_(Name::from_string(entry.lemma), vec![]),
            other_side.expr.clone(),
        );
        let total = if let Some(c) = congr {
            chain_optional(state, goal, c.proof, Some(identity_proof))
        } else {
            if other_side.proof.is_some() {
                return None;
            }
            let orig_id_arg = if entry.id_on_right {
                args[n - 1]
            } else {
                args[n - 2]
            };
            if !is_identity_expr(orig_id_arg, op_name, entry.kind) {
                continue;
            }
            Some(Expr::app(
                Expr::const_(Name::from_string(entry.lemma), vec![]),
                orig_other.clone(),
            ))
        };

        // For annihilator: total proves original_expr = 0 (complete).
        // For non-annihilator: total proves original_expr = other_side.expr
        // via congruence (handling child normalization) + identity lemma.
        // The child normalization proof is already incorporated in the
        // congruence step, so chaining with other_side.proof would be
        // ill-typed (the endpoints don't match). Part of #2442.
        let final_proof = total;

        return Some(RingRewriteResult {
            expr: result_expr,
            proof: final_proof,
        });
    }
    None
}

/// Try to distribute multiplication over addition.
///
/// Handles `Nat.mul(a, Nat.add(x, y))` via `Nat.left_distrib` and
/// `Nat.mul(Nat.add(x, y), b)` via `Nat.right_distrib`.
fn try_distribute(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    a_r: &RingRewriteResult,
    b_r: &RingRewriteResult,
    op_name: &str,
) -> Option<RingRewriteResult> {
    let distrib = distribution_entry(op_name)?;

    if is_binop(&b_r.expr, distrib.sum_op) {
        return try_left_distrib(state, goal, expr, a_r, b_r, op_name, distrib);
    }
    if is_binop(&a_r.expr, distrib.sum_op) {
        return try_right_distrib(state, goal, expr, a_r, b_r, op_name, distrib);
    }
    None
}

fn is_binop(expr: &Expr, op_name: &str) -> bool {
    let head = expr.get_app_fn();
    matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == op_name)
        && expr.get_app_args().len() >= 2
}

fn mk_binop_expr(op_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(op_name), vec![]), lhs),
        rhs,
    )
}

fn try_left_distrib(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    a_r: &RingRewriteResult,
    b_r: &RingRewriteResult,
    op_name: &str,
    distrib: DistributionEntry,
) -> Option<RingRewriteResult> {
    state
        .env()
        .get_const(&Name::from_string(distrib.left_distrib))?;

    let b_args = b_r.expr.get_app_args();
    if b_args.len() < 2 {
        return None;
    }
    let bn = b_args.len();
    let (x, y) = (b_args[bn - 2].clone(), b_args[bn - 1].clone());

    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let congr = build_child_congr(state, goal, head, &args, a_r, b_r)?;

    // Nat.left_distrib a_r.expr x y : a_r * (x + y) = a_r*x + a_r*y
    let distrib_proof = Expr::apps(
        Expr::const_(Name::from_string(distrib.left_distrib), vec![]),
        [a_r.expr.clone(), x.clone(), y.clone()],
    );

    let prod1 = mk_binop_expr(op_name, a_r.expr.clone(), x);
    let prod2 = mk_binop_expr(op_name, a_r.expr.clone(), y);
    let sum = mk_binop_expr(distrib.sum_op, prod1, prod2);

    // Normalize the distributed sum (recurse for sub-products and sorting)
    let sum_r = ring_normalize_with_proof(state, goal, &sum)?;

    let congr_then_distrib = chain_optional(state, goal, congr.proof, Some(distrib_proof));
    let total = chain_optional(state, goal, congr_then_distrib, sum_r.proof);
    Some(RingRewriteResult {
        expr: sum_r.expr,
        proof: total,
    })
}

fn try_right_distrib(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    a_r: &RingRewriteResult,
    b_r: &RingRewriteResult,
    op_name: &str,
    distrib: DistributionEntry,
) -> Option<RingRewriteResult> {
    state
        .env()
        .get_const(&Name::from_string(distrib.right_distrib))?;

    let a_args = a_r.expr.get_app_args();
    if a_args.len() < 2 {
        return None;
    }
    let an = a_args.len();
    let (x, y) = (a_args[an - 2].clone(), a_args[an - 1].clone());

    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    let congr = build_child_congr(state, goal, head, &args, a_r, b_r)?;

    // Nat.right_distrib x y b_r.expr : (x + y) * b_r = x*b_r + y*b_r
    let distrib_proof = Expr::apps(
        Expr::const_(Name::from_string(distrib.right_distrib), vec![]),
        [x.clone(), y.clone(), b_r.expr.clone()],
    );

    let prod1 = mk_binop_expr(op_name, x, b_r.expr.clone());
    let prod2 = mk_binop_expr(op_name, y, b_r.expr.clone());
    let sum = mk_binop_expr(distrib.sum_op, prod1, prod2);

    // Normalize the distributed sum (recurse for sub-products and sorting)
    let sum_r = ring_normalize_with_proof(state, goal, &sum)?;

    let congr_then_distrib = chain_optional(state, goal, congr.proof, Some(distrib_proof));
    let total = chain_optional(state, goal, congr_then_distrib, sum_r.proof);
    Some(RingRewriteResult {
        expr: sum_r.expr,
        proof: total,
    })
}

struct CongrResult {
    proof: Option<Expr>,
}

fn build_child_congr(
    state: &ProofState,
    goal: &Goal,
    head: &Expr,
    args: &[&Expr],
    a_r: &RingRewriteResult,
    b_r: &RingRewriteResult,
) -> Option<CongrResult> {
    let n = args.len();

    if a_r.proof.is_none() && b_r.proof.is_none() {
        return Some(CongrResult { proof: None });
    }

    let (a_orig, b_orig) = (args[n - 2], args[n - 1]);
    let mut proof: Option<Expr> = None;

    if let Some(ref a_pf) = a_r.proof {
        let hf_args: Vec<Expr> = args[..n - 2].iter().map(|e| (*e).clone()).collect();
        let head_fn = Expr::apps_ref(head.clone(), &hf_args);
        let h_f = mk_congr_arg(state, goal, &head_fn, a_orig, &a_r.expr, a_pf)?;
        let f_old_args: Vec<Expr> = args[..n - 1].iter().map(|e| (*e).clone()).collect();
        let mut f_new_args = f_old_args.clone();
        f_new_args[n - 2] = a_r.expr.clone();
        let f_old = Expr::apps_ref(head.clone(), &f_old_args);
        let f_new = Expr::apps_ref(head.clone(), &f_new_args);
        proof = Some(mk_congr_fun(state, goal, &f_old, &f_new, b_orig, &h_f)?);
    }

    if let Some(ref b_pf) = b_r.proof {
        let mut f_args: Vec<Expr> = args[..n - 1].iter().map(|e| (*e).clone()).collect();
        if a_r.proof.is_some() {
            f_args[n - 2] = a_r.expr.clone();
        }
        let f = Expr::apps_ref(head.clone(), &f_args);
        let h_b = mk_congr_arg(state, goal, &f, b_orig, &b_r.expr, b_pf)?;
        proof = chain_optional(state, goal, proof, Some(h_b));
    }

    Some(CongrResult { proof })
}

pub(super) fn collect_op_terms(expr: &Expr, op_name: &str) -> Vec<Expr> {
    let head = expr.get_app_fn();
    let is_op = matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == op_name);
    if !is_op {
        return vec![expr.clone()];
    }
    let args = expr.get_app_args();
    if args.len() < 2 {
        return vec![expr.clone()];
    }
    let n = args.len();
    let mut terms = collect_op_terms(args[n - 2], op_name);
    terms.push(args[n - 1].clone());
    terms
}

pub(super) fn chain_optional(
    state: &ProofState,
    goal: &Goal,
    p1: Option<Expr>,
    p2: Option<Expr>,
) -> Option<Expr> {
    match (p1, p2) {
        (None, None) => None,
        (Some(p), None) | (None, Some(p)) => Some(p),
        (Some(a), Some(b)) => mk_eq_trans_expr(state, goal, &a, &b),
    }
}

pub(crate) fn combine_side_proofs(
    state: &ProofState,
    goal: &Goal,
    lhs_r: &RingRewriteResult,
    rhs_r: &RingRewriteResult,
) -> Option<Expr> {
    match (&lhs_r.proof, &rhs_r.proof) {
        (None, None) => mk_eq_refl_expr(state, goal, &lhs_r.expr),
        (Some(lp), None) => Some(lp.clone()),
        (None, Some(rp)) => mk_eq_symm_expr(state, goal, rp),
        (Some(lp), Some(rp)) => {
            let rp_symm = mk_eq_symm_expr(state, goal, rp)?;
            mk_eq_trans_expr(state, goal, lp, &rp_symm)
        }
    }
}
