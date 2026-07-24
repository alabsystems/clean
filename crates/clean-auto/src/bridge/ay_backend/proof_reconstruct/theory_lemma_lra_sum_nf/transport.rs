// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::super::expr_builders;
use super::super::expr_builders_arith::CmpOp;
use super::super::theory_lemma_lra_additive::{
    mk_int_add, mk_int_add_assoc, mk_int_add_comm, mk_int_zero_add,
};
use super::{
    exprs_syntactically_equal, is_zero_literal, mk_cmp_prop, mk_int_eq_refl, mk_int_eq_symm,
    mk_int_eq_trans, mk_int_literal, mk_int_to_int_type, mk_int_to_prop_type, mk_int_ty, IntAddNf,
    IntCloseShape,
};

pub(super) fn normalize_cmp_proof(
    op: CmpOp,
    lhs_original: &Expr,
    rhs_original: &Expr,
    shape: &IntCloseShape,
    proof: &Expr,
) -> Option<Expr> {
    let lhs_eq =
        normalize_sum_to_close_expr(lhs_original, &shape.lhs_prefix_terms(), &shape.shared)?;
    let rhs_eq =
        normalize_sum_to_close_expr(rhs_original, &shape.rhs_prefix_terms(), &shape.shared)?;
    Some(transport_cmp_proof(
        op,
        (lhs_original, rhs_original),
        (&shape.lhs_expr(), &shape.rhs_expr()),
        (&lhs_eq, &rhs_eq),
        proof,
    ))
}

fn mk_int_add_apply_eq(
    lhs_from: &Expr,
    lhs_to: &Expr,
    rhs_from: &Expr,
    rhs_to: &Expr,
    lhs_eq: &Expr,
    rhs_eq: &Expr,
) -> Expr {
    let int_ty = mk_int_ty();
    let int_to_int = mk_int_to_int_type();
    let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
    let partial_eq = expr_builders::mk_congr_arg(
        &expr_builders::infer_universe_level(&int_ty),
        &expr_builders::infer_universe_level(&int_to_int),
        &int_ty,
        &int_to_int,
        lhs_from,
        lhs_to,
        &int_add,
        lhs_eq,
    );

    expr_builders::mk_congr(
        &expr_builders::infer_universe_level(&int_ty),
        &expr_builders::infer_universe_level(&int_ty),
        &int_ty,
        &int_ty,
        &Expr::app(int_add.clone(), lhs_from.clone()),
        &Expr::app(int_add, lhs_to.clone()),
        rhs_from,
        rhs_to,
        &partial_eq,
        rhs_eq,
    )
}

fn mk_cmp_apply_eq(
    op: CmpOp,
    lhs_from: &Expr,
    lhs_to: &Expr,
    rhs_from: &Expr,
    rhs_to: &Expr,
    lhs_eq: &Expr,
    rhs_eq: &Expr,
) -> Expr {
    let int_ty = mk_int_ty();
    let int_to_prop = mk_int_to_prop_type();
    let prop = Expr::sort(Level::zero());
    let rel = Expr::const_(
        Name::from_string(match op {
            CmpOp::Le => "Int.le",
            CmpOp::Lt => "Int.lt",
        }),
        vec![],
    );
    let partial_eq = expr_builders::mk_congr_arg(
        &expr_builders::infer_universe_level(&int_ty),
        &expr_builders::infer_universe_level(&int_to_prop),
        &int_ty,
        &int_to_prop,
        lhs_from,
        lhs_to,
        &rel,
        lhs_eq,
    );

    expr_builders::mk_congr(
        &expr_builders::infer_universe_level(&int_ty),
        &expr_builders::infer_universe_level(&prop),
        &int_ty,
        &prop,
        &Expr::app(rel.clone(), lhs_from.clone()),
        &Expr::app(rel, lhs_to.clone()),
        rhs_from,
        rhs_to,
        &partial_eq,
        rhs_eq,
    )
}

fn transport_cmp_proof(
    op: CmpOp,
    original: (&Expr, &Expr),
    close: (&Expr, &Expr),
    eqs: (&Expr, &Expr),
    proof: &Expr,
) -> Expr {
    let (lhs_original, rhs_original) = original;
    let (lhs_close, rhs_close) = close;
    let (lhs_eq, rhs_eq) = eqs;
    let original_prop = mk_cmp_prop(op, lhs_original, rhs_original);
    let close_prop = mk_cmp_prop(op, lhs_close, rhs_close);
    let prop_eq = mk_cmp_apply_eq(
        op,
        lhs_original,
        lhs_close,
        rhs_original,
        rhs_close,
        lhs_eq,
        rhs_eq,
    );
    let prop_sort = Expr::sort(Level::zero());
    let prop_eq_symm = expr_builders::mk_eq_symm(&prop_sort, &original_prop, &close_prop, &prop_eq);
    expr_builders::mk_eq_mpr(
        &Level::zero(),
        &close_prop,
        &original_prop,
        &prop_eq_symm,
        proof,
    )
}

fn flatten_add_terms(expr: &Expr) -> Vec<Expr> {
    let mut terms = Vec::new();
    flatten_add_terms_into(expr, &mut terms);
    terms
}

fn flatten_add_terms_into(expr: &Expr, terms: &mut Vec<Expr>) {
    crate::bridge::stack_safe(|| {
        let expr = expr.strip_mdata();
        if let Some((a, b)) = IntAddNf::as_flatten_add(expr) {
            flatten_add_terms_into(a, terms);
            flatten_add_terms_into(b, terms);
        } else {
            terms.push(expr.clone());
        }
    })
}

pub(super) fn build_right_assoc_expr(terms: &[Expr]) -> Expr {
    if terms.is_empty() {
        return mk_int_literal(0);
    }

    let mut result = terms.last().expect("invariant: terms non-empty").clone();
    for term in terms.iter().rev().skip(1) {
        result = mk_int_add(term, &result);
    }
    result
}

fn prove_append_right_assoc(left_terms: &[Expr], right_terms: &[Expr]) -> Option<Expr> {
    crate::bridge::stack_safe(|| {
        if left_terms.is_empty() || right_terms.is_empty() {
            return None;
        }
        if left_terms.len() == 1 {
            let target_terms = left_terms
                .iter()
                .cloned()
                .chain(right_terms.iter().cloned())
                .collect::<Vec<_>>();
            return Some(mk_int_eq_refl(&build_right_assoc_expr(&target_terms)));
        }

        let head = &left_terms[0];
        let left_tail_terms = &left_terms[1..];
        let left_tail_expr = build_right_assoc_expr(left_tail_terms);
        let right_expr = build_right_assoc_expr(right_terms);
        let target_tail_terms = left_tail_terms
            .iter()
            .cloned()
            .chain(right_terms.iter().cloned())
            .collect::<Vec<_>>();
        let target_tail_expr = build_right_assoc_expr(&target_tail_terms);
        let lhs = mk_int_add(&build_right_assoc_expr(left_terms), &right_expr);
        let mid = mk_int_add(head, &mk_int_add(&left_tail_expr, &right_expr));
        let target = mk_int_add(head, &target_tail_expr);
        let step1 = mk_int_add_assoc(head, &left_tail_expr, &right_expr);
        let tail_eq = prove_append_right_assoc(left_tail_terms, right_terms)?;
        let step2 = mk_int_add_apply_eq(
            head,
            head,
            &mk_int_add(&left_tail_expr, &right_expr),
            &target_tail_expr,
            &mk_int_eq_refl(head),
            &tail_eq,
        );
        Some(mk_int_eq_trans(&lhs, &mid, &target, &step1, &step2))
    })
}

fn prove_expr_equals_right_assoc(expr: &Expr) -> Option<Expr> {
    crate::bridge::stack_safe(|| {
        let expr = expr.strip_mdata();
        let (lhs, rhs, raw_expr, raw_intro) =
            if let Some((lhs, rhs)) = IntAddNf::as_raw_int_add(expr) {
                (lhs, rhs, expr.clone(), None)
            } else if let Some((lhs, rhs)) = IntAddNf::as_alias_int_add(expr) {
                let raw_expr = mk_int_add(lhs, rhs);
                let raw_intro = mk_int_eq_refl(&raw_expr);
                (lhs, rhs, raw_expr, Some(raw_intro))
            } else {
                return Some(mk_int_eq_refl(expr));
            };

        let lhs_eq = prove_expr_equals_right_assoc(lhs)?;
        let rhs_eq = prove_expr_equals_right_assoc(rhs)?;
        let lhs_terms = flatten_add_terms(lhs);
        let rhs_terms = flatten_add_terms(rhs);
        let lhs_norm = build_right_assoc_expr(&lhs_terms);
        let rhs_norm = build_right_assoc_expr(&rhs_terms);
        let mid = mk_int_add(&lhs_norm, &rhs_norm);
        let target_terms = lhs_terms
            .iter()
            .cloned()
            .chain(rhs_terms.iter().cloned())
            .collect::<Vec<_>>();
        let target = build_right_assoc_expr(&target_terms);
        let step1 = mk_int_add_apply_eq(lhs, &lhs_norm, rhs, &rhs_norm, &lhs_eq, &rhs_eq);
        let step2 = prove_append_right_assoc(&lhs_terms, &rhs_terms)?;
        let step1 = if let Some(raw_intro) = raw_intro {
            mk_int_eq_trans(expr, &raw_expr, &mid, &raw_intro, &step1)
        } else {
            step1
        };
        Some(mk_int_eq_trans(expr, &mid, &target, &step1, &step2))
    })
}

fn prove_adjacent_swap(terms: &[Expr], swap_idx: usize) -> Option<Expr> {
    crate::bridge::stack_safe(|| {
        if terms.len() < 2 || swap_idx + 1 >= terms.len() {
            return None;
        }

        if swap_idx > 0 {
            let head = &terms[0];
            let tail_eq = prove_adjacent_swap(&terms[1..], swap_idx - 1)?;
            let tail_from = build_right_assoc_expr(&terms[1..]);
            let mut swapped_tail = terms[1..].to_vec();
            swapped_tail.swap(swap_idx - 1, swap_idx);
            let tail_to = build_right_assoc_expr(&swapped_tail);
            return Some(mk_int_add_apply_eq(
                head,
                head,
                &tail_from,
                &tail_to,
                &mk_int_eq_refl(head),
                &tail_eq,
            ));
        }

        let a = &terms[0];
        let b = &terms[1];
        if terms.len() == 2 {
            return Some(mk_int_add_comm(a, b));
        }

        let tail = build_right_assoc_expr(&terms[2..]);
        let lhs = build_right_assoc_expr(terms);
        let a_plus_b = mk_int_add(a, b);
        let b_plus_a = mk_int_add(b, a);
        let mid1 = mk_int_add(&a_plus_b, &tail);
        let mid2 = mk_int_add(&b_plus_a, &tail);
        let target_terms = [b.clone(), a.clone()]
            .into_iter()
            .chain(terms[2..].iter().cloned())
            .collect::<Vec<_>>();
        let target = build_right_assoc_expr(&target_terms);
        let step1 = mk_int_eq_symm(&mid1, &lhs, &mk_int_add_assoc(a, b, &tail));
        let step2 = mk_int_add_apply_eq(
            &a_plus_b,
            &b_plus_a,
            &tail,
            &tail,
            &mk_int_add_comm(a, b),
            &mk_int_eq_refl(&tail),
        );
        let step3 = mk_int_add_assoc(b, a, &tail);
        let step12 = mk_int_eq_trans(&lhs, &mid1, &mid2, &step1, &step2);
        Some(mk_int_eq_trans(&lhs, &mid2, &target, &step12, &step3))
    })
}

fn prove_reorder_right_assoc(current_terms: &[Expr], target_terms: &[Expr]) -> Option<Expr> {
    if current_terms.len() != target_terms.len() {
        return None;
    }
    if current_terms == target_terms {
        return Some(mk_int_eq_refl(&build_right_assoc_expr(current_terms)));
    }

    let start = build_right_assoc_expr(current_terms);
    let mut proof = mk_int_eq_refl(&start);
    let mut current_expr = start.clone();
    let mut terms = current_terms.to_vec();

    for idx in 0..target_terms.len() {
        if exprs_syntactically_equal(&terms[idx], &target_terms[idx]) {
            continue;
        }
        let mut swap_pos = terms[idx + 1..]
            .iter()
            .position(|term| exprs_syntactically_equal(term, &target_terms[idx]))
            .map(|offset| idx + 1 + offset)?;

        while swap_pos > idx {
            let swap_eq = prove_adjacent_swap(&terms, swap_pos - 1)?;
            let mut swapped_terms = terms.clone();
            swapped_terms.swap(swap_pos - 1, swap_pos);
            let swapped_expr = build_right_assoc_expr(&swapped_terms);
            proof = mk_int_eq_trans(&start, &current_expr, &swapped_expr, &proof, &swap_eq);
            current_expr = swapped_expr;
            terms = swapped_terms;
            swap_pos -= 1;
        }
    }

    if terms == target_terms {
        Some(proof)
    } else {
        None
    }
}

fn prove_group_suffix(prefix_terms: &[Expr], shared_terms: &[Expr]) -> Option<Expr> {
    crate::bridge::stack_safe(|| {
        if prefix_terms.is_empty() || shared_terms.is_empty() {
            return None;
        }
        if prefix_terms.len() == 1 {
            let target_terms = prefix_terms
                .iter()
                .cloned()
                .chain(shared_terms.iter().cloned())
                .collect::<Vec<_>>();
            return Some(mk_int_eq_refl(&build_right_assoc_expr(&target_terms)));
        }

        let head = &prefix_terms[0];
        let tail_prefix_terms = &prefix_terms[1..];
        let shared_expr = build_right_assoc_expr(shared_terms);
        let full_target_terms = prefix_terms
            .iter()
            .cloned()
            .chain(shared_terms.iter().cloned())
            .collect::<Vec<_>>();
        let full_target_expr = build_right_assoc_expr(&full_target_terms);
        let tail_target_terms = tail_prefix_terms
            .iter()
            .cloned()
            .chain(shared_terms.iter().cloned())
            .collect::<Vec<_>>();
        let tail_target_expr = build_right_assoc_expr(&tail_target_terms);
        let tail_grouped_expr =
            mk_int_add(&build_right_assoc_expr(tail_prefix_terms), &shared_expr);
        let mid = mk_int_add(head, &tail_grouped_expr);
        let target = mk_int_add(&build_right_assoc_expr(prefix_terms), &shared_expr);
        let tail_eq = prove_group_suffix(tail_prefix_terms, shared_terms)?;
        let step1 = mk_int_add_apply_eq(
            head,
            head,
            &tail_target_expr,
            &tail_grouped_expr,
            &mk_int_eq_refl(head),
            &tail_eq,
        );
        let step2 = mk_int_eq_symm(
            &target,
            &mid,
            &mk_int_add_assoc(
                head,
                &build_right_assoc_expr(tail_prefix_terms),
                &shared_expr,
            ),
        );
        Some(mk_int_eq_trans(
            &full_target_expr,
            &mid,
            &target,
            &step1,
            &step2,
        ))
    })
}

fn normalize_sum_to_close_expr(
    original: &Expr,
    prefix_terms: &[Expr],
    shared_terms: &[Expr],
) -> Option<Expr> {
    let zero = mk_int_literal(0);
    let mut target_terms = if prefix_terms.is_empty() && !shared_terms.is_empty() {
        vec![zero.clone()]
    } else {
        Vec::new()
    };
    target_terms.extend(prefix_terms.iter().cloned());
    target_terms.extend(shared_terms.iter().cloned());

    if target_terms.is_empty() {
        target_terms.push(zero);
    }

    let mut proof = prove_expr_equals_right_assoc(original)?;
    let source_terms = flatten_add_terms(original);
    let source_right = build_right_assoc_expr(&source_terms);
    let mut current_expr = source_right.clone();
    let mut current_terms = source_terms;

    if target_terms.len() == current_terms.len() + 1 && is_zero_literal(&target_terms[0]) {
        let zero_added = mk_int_add(&target_terms[0], &current_expr);
        let zero_intro =
            mk_int_eq_symm(&zero_added, &current_expr, &mk_int_zero_add(&current_expr));
        proof = mk_int_eq_trans(original, &current_expr, &zero_added, &proof, &zero_intro);
        current_terms.insert(0, target_terms[0].clone());
        current_expr = zero_added;
    }

    if current_terms.len() != target_terms.len() {
        return None;
    }
    if current_terms != target_terms {
        let reorder_eq = prove_reorder_right_assoc(&current_terms, &target_terms)?;
        let reordered_expr = build_right_assoc_expr(&target_terms);
        proof = mk_int_eq_trans(
            original,
            &current_expr,
            &reordered_expr,
            &proof,
            &reorder_eq,
        );
        current_expr = reordered_expr;
    }

    if shared_terms.is_empty() || prefix_terms.len() <= 1 {
        return Some(proof);
    }

    let grouped = mk_int_add(
        &build_right_assoc_expr(prefix_terms),
        &build_right_assoc_expr(shared_terms),
    );
    let regroup_eq = prove_group_suffix(prefix_terms, shared_terms)?;
    Some(mk_int_eq_trans(
        original,
        &current_expr,
        &grouped,
        &proof,
        &regroup_eq,
    ))
}
