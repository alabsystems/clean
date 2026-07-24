// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sort/reorder proof construction for proof-carrying ring normalization.
//!
//! Provides merge, flatten, and bubble-sort with proof terms for ring chains.
//! Used by [`ring_proof_carry`] during normalization.

use super::ring_helpers::ring_normalize;
use super::ring_proof_carry::chain_optional;
use super::ring_proof_fuse::{fuse_like_terms, FuseCtx};
use super::ring_proof_surface::{assoc_name, coeff_merge_entry, comm_name};
use super::simp::{mk_congr_arg, mk_congr_fun, mk_eq_symm_expr, mk_eq_trans_expr};
use super::{Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

pub(super) fn build_op_chain(head: &Expr, prefix: &[Expr], terms: &[Expr]) -> Expr {
    assert!(!terms.is_empty());
    if terms.len() == 1 {
        return terms[0].clone();
    }
    let mut result = terms[0].clone();
    for t in &terms[1..] {
        let mut args = prefix.to_vec();
        args.push(result);
        args.push(t.clone());
        result = Expr::apps_ref(head.clone(), &args);
    }
    result
}

/// Merge context for chain operations, reducing argument count.
struct MergeCtx<'a> {
    state: &'a ProofState,
    goal: &'a Goal,
    op_name: &'a str,
    head: &'a Expr,
    prefix: &'a [Expr],
}

pub(super) fn merge_sorted_chains(
    state: &ProofState,
    goal: &Goal,
    a_expr: &Expr,
    b_expr: &Expr,
    a_terms: &[Expr],
    b_terms: &[Expr],
    op_name: &str,
    head: &Expr,
    prefix: &[Expr],
) -> Option<(Expr, Option<Expr>)> {
    let ctx = MergeCtx {
        state,
        goal,
        op_name,
        head,
        prefix,
    };
    let all_terms: Vec<Expr> = a_terms.iter().chain(b_terms.iter()).cloned().collect();
    if all_terms.len() <= 1 {
        return Some((all_terms.into_iter().next()?, None));
    }

    let flat = build_op_chain(head, prefix, &all_terms);

    let current_expr = {
        let mut args = prefix.to_vec();
        args.push(a_expr.clone());
        args.push(b_expr.clone());
        Expr::apps_ref(head.clone(), &args)
    };
    let flatten_proof = build_flatten_proof(state, goal, &current_expr, &flat);

    let mut sorted_terms = all_terms;
    let sort_proof = bubble_sort_chain(&ctx, &flat, &mut sorted_terms);

    let sorted = build_op_chain(head, prefix, &sorted_terms);
    let sort_total = chain_optional(state, goal, flatten_proof, sort_proof);

    // Coefficient-merge pass (#ring-coeff-merge): fuse runs of def-eq-identical
    // adjacent monomials (e.g. `a*b + a*b → 2*(a*b)`) with a kernel-valid
    // proof. Only applies to addition operators (the `coeff_merge_entry`
    // surface); multiplication chains are returned unchanged. On any
    // unsupported run the fuser returns `None` and we keep the sorted chain
    // (no coefficient merge), so the caller fails-closed rather than faking.
    if coeff_merge_entry(op_name).is_some() && sorted_terms.len() >= 2 {
        let fuse_ctx = FuseCtx {
            state,
            goal,
            add_op: op_name,
            head,
            prefix,
        };
        if let Some((mut fused_terms, fuse_proof)) = fuse_like_terms(&fuse_ctx, &sorted_terms) {
            if fused_terms.len() != sorted_terms.len() {
                // Fusion can change a monomial's canonical key (e.g. `a*b`
                // becomes the literal-led `(2*a)*b`, which sorts before
                // `a*a`), so re-sort to land in the same canonical order as
                // the syntactic normal form. Both sides run identical
                // fuse+resort logic, so their proof-carry forms agree and
                // `combine_side_proofs` can chain them.
                let fused_chain = build_op_chain(head, prefix, &fused_terms);
                let resort_proof = bubble_sort_chain(&ctx, &fused_chain, &mut fused_terms);
                let fused = build_op_chain(head, prefix, &fused_terms);
                let merge_total = chain_optional(state, goal, sort_total, fuse_proof);
                let total = chain_optional(state, goal, merge_total, resort_proof);
                return Some((fused, total));
            }
        }
    }

    Some((sorted, sort_total))
}

fn build_flatten_proof(state: &ProofState, goal: &Goal, from: &Expr, to: &Expr) -> Option<Expr> {
    if state.is_def_eq(goal, from, to) {
        return None;
    }
    flatten_right_assoc(state, goal, from, to)
}

fn flatten_right_assoc(state: &ProofState, goal: &Goal, from: &Expr, to: &Expr) -> Option<Expr> {
    if state.is_def_eq(goal, from, to) {
        return super::simp::mk_eq_refl_expr(state, goal, from);
    }
    let head = from.get_app_fn();
    let args = from.get_app_args();
    let n = args.len();
    if n < 2 {
        return None;
    }
    let (lhs, rhs) = (args[n - 2], args[n - 1]);

    let rhs_head = rhs.get_app_fn();
    let is_same_op = matches!((head.kind(), rhs_head.kind()),
        (ExprKind::Const(h, _), ExprKind::Const(r, _)) if h == r);
    if !is_same_op {
        return None;
    }

    let rhs_args = rhs.get_app_args();
    if rhs_args.len() < 2 {
        return None;
    }
    let rn = rhs_args.len();
    let (b, c) = (rhs_args[rn - 2], rhs_args[rn - 1]);

    let op_str = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        _ => return None,
    };
    let assoc_name = assoc_name(&op_str)?;
    state.env().get_const(&Name::from_string(assoc_name))?;

    let assoc_proof = Expr::apps(
        Expr::const_(Name::from_string(assoc_name), vec![]),
        [lhs.clone(), b.clone(), c.clone()],
    );
    let step = mk_eq_symm_expr(state, goal, &assoc_proof)?;

    let mut inner_args: Vec<Expr> = args[..n - 2].iter().map(|e| (*e).clone()).collect();
    inner_args.push(lhs.clone());
    inner_args.push(b.clone());
    let inner = Expr::apps_ref(head.clone(), &inner_args);
    let mut mid_args: Vec<Expr> = args[..n - 2].iter().map(|e| (*e).clone()).collect();
    mid_args.push(inner);
    mid_args.push(c.clone());
    let mid = Expr::apps_ref(head.clone(), &mid_args);

    let rest = flatten_right_assoc(state, goal, &mid, to);
    chain_optional(state, goal, Some(step), rest)
}

fn bubble_sort_chain(ctx: &MergeCtx<'_>, chain: &Expr, terms: &mut [Expr]) -> Option<Expr> {
    let n = terms.len();
    if n <= 1 {
        return None;
    }
    let mut proof: Option<Expr> = None;
    let mut _current = chain.clone();
    for _ in 0..n {
        let mut swapped = false;
        for j in (1..n).rev() {
            let lc = ring_normalize(&terms[j - 1]);
            let rc = ring_normalize(&terms[j]);
            if lc > rc {
                let swap_pf = swap_at_position(ctx, terms, j)?;
                terms.swap(j - 1, j);
                _current = build_op_chain(ctx.head, ctx.prefix, terms);
                proof = chain_optional(ctx.state, ctx.goal, proof, Some(swap_pf));
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
    }
    proof
}

fn swap_at_position(ctx: &MergeCtx<'_>, terms: &[Expr], j: usize) -> Option<Expr> {
    let n = terms.len();
    if n == 2 && j == 1 {
        return comm_proof(ctx.state, ctx.op_name, &terms[0], &terms[1]);
    }

    if j == n - 1 {
        let inner_prefix = build_op_chain(ctx.head, ctx.prefix, &terms[..n - 2]);
        swap_last_two(ctx, &inner_prefix, &terms[n - 2], &terms[n - 1])
    } else {
        let inner_terms = terms[..j + 1].to_vec();
        let inner_proof = swap_at_position(ctx, &inner_terms, j)?;

        let mut lifted = inner_proof;
        for k in (j + 1)..n {
            let head_fn = Expr::apps_ref(ctx.head.clone(), ctx.prefix);
            let old_inner = build_op_chain(ctx.head, ctx.prefix, &terms[..k]);
            let mut swapped_prefix_terms: Vec<Expr> = terms[..k].to_vec();
            swapped_prefix_terms.swap(j - 1, j);
            let new_inner = build_op_chain(ctx.head, ctx.prefix, &swapped_prefix_terms);
            let h_f = mk_congr_arg(
                ctx.state, ctx.goal, &head_fn, &old_inner, &new_inner, &lifted,
            )?;
            let f_old = {
                let mut a = ctx.prefix.to_vec();
                a.push(old_inner);
                Expr::apps_ref(ctx.head.clone(), &a)
            };
            let f_new = {
                let mut a = ctx.prefix.to_vec();
                a.push(new_inner);
                Expr::apps_ref(ctx.head.clone(), &a)
            };
            lifted = mk_congr_fun(ctx.state, ctx.goal, &f_old, &f_new, &terms[k], &h_f)?;
        }
        Some(lifted)
    }
}

fn swap_last_two(ctx: &MergeCtx<'_>, inner_prefix: &Expr, a: &Expr, b: &Expr) -> Option<Expr> {
    let assoc_name = assoc_name(ctx.op_name)?;
    let comm_name = comm_name(ctx.op_name)?;
    ctx.state.env().get_const(&Name::from_string(assoc_name))?;
    ctx.state.env().get_const(&Name::from_string(comm_name))?;

    let step1 = Expr::apps(
        Expr::const_(Name::from_string(assoc_name), vec![]),
        [inner_prefix.clone(), a.clone(), b.clone()],
    );

    let ab = {
        let mut args = ctx.prefix.to_vec();
        args.push(a.clone());
        args.push(b.clone());
        Expr::apps_ref(ctx.head.clone(), &args)
    };
    let comm = Expr::apps(
        Expr::const_(Name::from_string(comm_name), vec![]),
        [a.clone(), b.clone()],
    );
    let prefix_fn = {
        let mut args = ctx.prefix.to_vec();
        args.push(inner_prefix.clone());
        Expr::apps_ref(ctx.head.clone(), &args)
    };
    let ba = {
        let mut args = ctx.prefix.to_vec();
        args.push(b.clone());
        args.push(a.clone());
        Expr::apps_ref(ctx.head.clone(), &args)
    };
    let step2 = mk_congr_arg(ctx.state, ctx.goal, &prefix_fn, &ab, &ba, &comm)?;

    let step3_raw = Expr::apps(
        Expr::const_(Name::from_string(assoc_name), vec![]),
        [inner_prefix.clone(), b.clone(), a.clone()],
    );
    let step3 = mk_eq_symm_expr(ctx.state, ctx.goal, &step3_raw)?;

    let p12 = mk_eq_trans_expr(ctx.state, ctx.goal, &step1, &step2)?;
    mk_eq_trans_expr(ctx.state, ctx.goal, &p12, &step3)
}

fn comm_proof(state: &ProofState, op_name: &str, a: &Expr, b: &Expr) -> Option<Expr> {
    let comm_name = comm_name(op_name)?;
    state.env().get_const(&Name::from_string(comm_name))?;
    Some(Expr::apps(
        Expr::const_(Name::from_string(comm_name), vec![]),
        [a.clone(), b.clone()],
    ))
}
