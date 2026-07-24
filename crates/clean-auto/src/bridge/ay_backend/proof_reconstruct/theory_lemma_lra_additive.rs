// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additive combination proof builders for LRA Farkas reconstruction.
//!
//! Builds kernel Expr terms for `{Int,Real}.add_le_add_left/right` and
//! `{Int,Real}.add_lt_add_left/right` used by the N-bound additive combination
//! path in `theory_lemma_lra.rs`.

use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use crate::arith_proof::ArithSort;

/// Build `@Int.add_le_add_left a b h c`.
///
/// Type: `Int.le a b → ∀ c : Int, Int.le (Int.add c a) (Int.add c b)`
pub(super) fn mk_int_add_le_add_left(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Int.add_le_add_left", a, b, h, c)
}

/// Build `@Int.add_le_add_right a b h c`.
///
/// Type: `Int.le a b → ∀ c : Int, Int.le (Int.add a c) (Int.add b c)`
pub(super) fn mk_int_add_le_add_right(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Int.add_le_add_right", a, b, h, c)
}

/// Build `@Int.add_lt_add_left a b h c`.
///
/// Type: `Int.lt a b → ∀ c : Int, Int.lt (Int.add c a) (Int.add c b)`
pub(super) fn mk_int_add_lt_add_left(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Int.add_lt_add_left", a, b, h, c)
}

/// Build `@Int.add_lt_add_right a b h c`.
///
/// Type: `Int.lt a b → ∀ c : Int, Int.lt (Int.add a c) (Int.add b c)`
pub(super) fn mk_int_add_lt_add_right(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Int.add_lt_add_right", a, b, h, c)
}

/// Dispatch `add_X_add_left` based on the bound's comparison op.
pub(super) fn mk_int_add_cmp_add_left(op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    match op {
        CmpOp::Le => mk_int_add_le_add_left(a, b, h, c),
        CmpOp::Lt => mk_int_add_lt_add_left(a, b, h, c),
    }
}

/// Dispatch `add_X_add_right` based on the accumulated comparison op.
pub(super) fn mk_int_add_cmp_add_right(op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    match op {
        CmpOp::Le => mk_int_add_le_add_right(a, b, h, c),
        CmpOp::Lt => mk_int_add_lt_add_right(a, b, h, c),
    }
}

/// Build `@Int.add a b` (raw Int.add, not HAdd.hAdd).
pub(super) fn mk_int_add(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@Int.add_assoc a b c`.
///
/// Type: `Eq (Int.add (Int.add a b) c) (Int.add a (Int.add b c))`
pub(super) fn mk_int_add_assoc(a: &Expr, b: &Expr, c: &Expr) -> Expr {
    mk_3arg("Int.add_assoc", a, b, c)
}

/// Build `@Int.add_comm a b`.
///
/// Type: `Eq (Int.add a b) (Int.add b a)`
pub(super) fn mk_int_add_comm(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `@Int.zero_add a`.
///
/// Type: `Eq (Int.add (Int.ofNat 0) a) a`
pub(super) fn mk_int_zero_add(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.zero_add"), vec![]),
        a.clone(),
    )
}

// =========================================================================
// Real additive builders
// =========================================================================

/// Build `@Real.add_le_add_left a b h c`.
fn mk_real_add_le_add_left(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Real.add_le_add_left", a, b, h, c)
}

/// Build `@Real.add_le_add_right a b h c`.
fn mk_real_add_le_add_right(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Real.add_le_add_right", a, b, h, c)
}

/// Build `@Real.add_lt_add_left a b h c`.
fn mk_real_add_lt_add_left(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Real.add_lt_add_left", a, b, h, c)
}

/// Build `@Real.add_lt_add_right a b h c`.
fn mk_real_add_lt_add_right(a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    mk_4arg("Real.add_lt_add_right", a, b, h, c)
}

/// Dispatch `add_X_add_left` for Real based on the bound's comparison op.
fn mk_real_add_cmp_add_left(op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    match op {
        CmpOp::Le => mk_real_add_le_add_left(a, b, h, c),
        CmpOp::Lt => mk_real_add_lt_add_left(a, b, h, c),
    }
}

/// Dispatch `add_X_add_right` for Real based on the accumulated comparison op.
fn mk_real_add_cmp_add_right(op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    match op {
        CmpOp::Le => mk_real_add_le_add_right(a, b, h, c),
        CmpOp::Lt => mk_real_add_lt_add_right(a, b, h, c),
    }
}

/// Build `@Real.add a b` (raw Real.add).
fn mk_real_add(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

// =========================================================================
// Sort-dispatched wrappers
// =========================================================================

/// Sort-dispatched `add_cmp_add_left`: Int or Real.
pub(super) fn mk_add_cmp_add_left(
    sort: &Sort,
    op: CmpOp,
    a: &Expr,
    b: &Expr,
    h: &Expr,
    c: &Expr,
) -> Option<Expr> {
    match sort {
        Sort::Int => Some(mk_int_add_cmp_add_left(op, a, b, h, c)),
        Sort::Real => Some(mk_real_add_cmp_add_left(op, a, b, h, c)),
        _ => None,
    }
}

/// Sort-dispatched `add_cmp_add_right`: Int or Real.
pub(super) fn mk_add_cmp_add_right(
    sort: &Sort,
    op: CmpOp,
    a: &Expr,
    b: &Expr,
    h: &Expr,
    c: &Expr,
) -> Option<Expr> {
    match sort {
        Sort::Int => Some(mk_int_add_cmp_add_right(op, a, b, h, c)),
        Sort::Real => Some(mk_real_add_cmp_add_right(op, a, b, h, c)),
        _ => None,
    }
}

/// Sort-dispatched transitivity chain step.
///
/// Delegates to the shared `arith_proof::mk_chain_step` via `ay_sort_to_arith` (#2910).
pub(super) fn mk_chain_step(
    sort: &Sort,
    left_op: CmpOp,
    right_op: CmpOp,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    h1: &Expr,
    h2: &Expr,
) -> Option<Expr> {
    let arith = match sort {
        Sort::Int => ArithSort::Int,
        Sort::Real => ArithSort::Real,
        _ => return None,
    };
    Some(crate::arith_proof::mk_chain_step(
        arith, a, b, c, left_op, right_op, h1, h2,
    ))
}

/// Sort-dispatched `add(a, b)`.
pub(super) fn mk_sort_add(sort: &Sort, a: &Expr, b: &Expr) -> Option<Expr> {
    match sort {
        Sort::Int => Some(mk_int_add(a, b)),
        Sort::Real => Some(mk_real_add(a, b)),
        _ => None,
    }
}

/// Build a 4-argument application: `@Lemma a b h c`.
fn mk_4arg(lemma: &str, a: &Expr, b: &Expr, h: &Expr, c: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string(lemma), vec![]), a.clone()),
                b.clone(),
            ),
            h.clone(),
        ),
        c.clone(),
    )
}

/// Build a 3-argument application: `@Lemma a b c`.
fn mk_3arg(lemma: &str, a: &Expr, b: &Expr, c: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(lemma), vec![]), a.clone()),
            b.clone(),
        ),
        c.clone(),
    )
}

// =========================================================================
// Scaled-bound accumulator for weighted Farkas replay (Part of #2581)
// =========================================================================

/// Proof of a (possibly scaled) bound: `lhs op rhs`.
///
/// After scaling a hypothesis `a op b` by integer coefficient `k`, this carries
/// `(k*a, k*b, op, proof_of_ka_op_kb)` where `k*a` is the repeated-addition
/// expression `a + a + ... + a` (k times).
pub(super) struct SortCmpAcc {
    pub(super) lhs: Expr,
    pub(super) rhs: Expr,
    pub(super) op: CmpOp,
    pub(super) proof: Expr,
}

/// Scale a single hypothesis by a positive integer coefficient via repeated
/// addition.
///
/// For coefficient 1, returns the hypothesis directly.
/// For coefficient k > 1, builds `k*a op k*b` by repeatedly combining
/// `h : a op b` with the accumulator using `add_cmp_add_right` (for the
/// accumulated side) and `add_cmp_add_left` (for the hypothesis), joined
/// by a transitivity chain step.
///
/// Requires: `coeff >= 1`, sort is Int or Real.
pub(super) fn scale_bound(
    sort: &Sort,
    op: CmpOp,
    lhs: &Expr,
    rhs: &Expr,
    hyp: &Expr,
    coeff: u64,
) -> Option<SortCmpAcc> {
    if coeff == 0 {
        return None;
    }

    let mk_add = |a: &Expr, b: &Expr| -> Option<Expr> { mk_sort_add(sort, a, b) };
    let mk_acl = |o: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Option<Expr> {
        mk_add_cmp_add_left(sort, o, a, b, h, c)
    };
    let mk_acr = |o: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Option<Expr> {
        mk_add_cmp_add_right(sort, o, a, b, h, c)
    };
    let mk_cs = |lo: CmpOp,
                 ro: CmpOp,
                 a: &Expr,
                 b: &Expr,
                 c: &Expr,
                 h1: &Expr,
                 h2: &Expr|
     -> Option<Expr> { mk_chain_step(sort, lo, ro, a, b, c, h1, h2) };

    if coeff == 1 {
        return Some(SortCmpAcc {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            op,
            proof: hyp.clone(),
        });
    }

    // k=2: combine h with itself
    // step1 = add_cmp_add_left(a, b, h, a) → a+a op a+b
    // step2 = add_cmp_add_right(a, b, h, b) → a+b op b+b
    // chain: a+a op a+b, a+b op b+b
    // result: a+a op b+b = 2a op 2b
    let step1 = mk_acl(op, lhs, rhs, hyp, lhs)?;
    let step2 = mk_acr(op, lhs, rhs, hyp, rhs)?;
    let acc_lhs = mk_add(lhs, lhs)?;
    let sum_mid = mk_add(lhs, rhs)?;
    let acc_rhs = mk_add(rhs, rhs)?;
    let acc_op = expr_builders_arith::combine_ops(op, op);
    let acc_proof = mk_cs(op, op, &acc_lhs, &sum_mid, &acc_rhs, &step1, &step2)?;

    let mut acc = SortCmpAcc {
        lhs: acc_lhs,
        rhs: acc_rhs,
        op: acc_op,
        proof: acc_proof,
    };

    // k=3..coeff: keep adding h
    for _ in 2..coeff {
        let step_a = mk_acr(acc.op, &acc.lhs, &acc.rhs, &acc.proof, lhs)?;
        let step_b = mk_acl(op, lhs, rhs, hyp, &acc.rhs)?;
        let new_lhs = mk_add(&acc.lhs, lhs)?;
        let mid = mk_add(&acc.rhs, lhs)?;
        let new_rhs = mk_add(&acc.rhs, rhs)?;
        let new_proof = mk_cs(acc.op, op, &new_lhs, &mid, &new_rhs, &step_a, &step_b)?;
        acc = SortCmpAcc {
            lhs: new_lhs,
            rhs: new_rhs,
            op: expr_builders_arith::combine_ops(acc.op, op),
            proof: new_proof,
        };
    }

    Some(acc)
}

/// Combine N scaled bound accumulators into a single additive proof.
///
/// Uses the same pairwise combination pattern as the unweighted additive path:
/// `add_cmp_add_right` for the accumulated side, `add_cmp_add_left` for the
/// new bound, joined by a transitivity chain step.
///
/// Requires: `accs.len() >= 2`, all same sort.
pub(super) fn combine_scaled_bounds(sort: &Sort, accs: &mut [SortCmpAcc]) -> Option<SortCmpAcc> {
    if accs.len() < 2 {
        return None;
    }

    let mk_add = |a: &Expr, b: &Expr| -> Option<Expr> { mk_sort_add(sort, a, b) };
    let mk_acl = |o: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Option<Expr> {
        mk_add_cmp_add_left(sort, o, a, b, h, c)
    };
    let mk_acr = |o: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Option<Expr> {
        mk_add_cmp_add_right(sort, o, a, b, h, c)
    };
    let mk_cs = |lo: CmpOp,
                 ro: CmpOp,
                 a: &Expr,
                 b: &Expr,
                 c: &Expr,
                 h1: &Expr,
                 h2: &Expr|
     -> Option<Expr> { mk_chain_step(sort, lo, ro, a, b, c, h1, h2) };

    // Base case: combine first two accumulators
    let b1 = &accs[1];
    let b0 = &accs[0];
    let step1 = mk_acl(b0.op, &b0.lhs, &b0.rhs, &b0.proof, &b1.lhs)?;
    let step2 = mk_acr(b1.op, &b1.lhs, &b1.rhs, &b1.proof, &b0.rhs)?;
    let combined_lhs = mk_add(&b1.lhs, &b0.lhs)?;
    let sum_mid = mk_add(&b1.lhs, &b0.rhs)?;
    let combined_rhs = mk_add(&b1.rhs, &b0.rhs)?;
    let combined_op = expr_builders_arith::combine_ops(b0.op, b1.op);
    let combined_proof = mk_cs(
        b0.op,
        b1.op,
        &combined_lhs,
        &sum_mid,
        &combined_rhs,
        &step1,
        &step2,
    )?;

    let mut acc = SortCmpAcc {
        lhs: combined_lhs,
        rhs: combined_rhs,
        op: combined_op,
        proof: combined_proof,
    };

    // Iterate for remaining accumulators
    for bound in accs.iter().skip(2) {
        let step_a = mk_acr(acc.op, &acc.lhs, &acc.rhs, &acc.proof, &bound.lhs)?;
        let step_b = mk_acl(bound.op, &bound.lhs, &bound.rhs, &bound.proof, &acc.rhs)?;
        let new_lhs = mk_add(&acc.lhs, &bound.lhs)?;
        let mid = mk_add(&acc.rhs, &bound.lhs)?;
        let new_rhs = mk_add(&acc.rhs, &bound.rhs)?;
        let new_proof = mk_cs(acc.op, bound.op, &new_lhs, &mid, &new_rhs, &step_a, &step_b)?;
        acc = SortCmpAcc {
            lhs: new_lhs,
            rhs: new_rhs,
            op: expr_builders_arith::combine_ops(acc.op, bound.op),
            proof: new_proof,
        };
    }

    Some(acc)
}
