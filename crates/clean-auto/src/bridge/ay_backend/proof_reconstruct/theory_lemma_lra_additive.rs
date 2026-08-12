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
/// `(k*a, k*b, op, proof_of_ka_op_kb)` where `k*a` is an addition tree with
/// `k` occurrences of `a`.
#[derive(Clone)]
pub(super) struct SortCmpAcc {
    pub(super) lhs: Expr,
    pub(super) rhs: Expr,
    pub(super) op: CmpOp,
    pub(super) proof: Expr,
}

/// Combine two authenticated comparison accumulators by addition.
///
/// Given `a0 op0 b0` and `a1 op1 b1`, constructs a kernel proof of
/// `(a1 + a0) combine(op0, op1) (b1 + b0)`. Keeping this operation in one
/// helper makes both coefficient scaling and N-bound accumulation use the
/// same checked proof shape.
fn combine_two_scaled_bounds(
    sort: &Sort,
    first: &SortCmpAcc,
    second: &SortCmpAcc,
) -> Option<SortCmpAcc> {
    let step1 = mk_add_cmp_add_left(
        sort,
        first.op,
        &first.lhs,
        &first.rhs,
        &first.proof,
        &second.lhs,
    )?;
    let step2 = mk_add_cmp_add_right(
        sort,
        second.op,
        &second.lhs,
        &second.rhs,
        &second.proof,
        &first.rhs,
    )?;
    let combined_lhs = mk_sort_add(sort, &second.lhs, &first.lhs)?;
    let sum_mid = mk_sort_add(sort, &second.lhs, &first.rhs)?;
    let combined_rhs = mk_sort_add(sort, &second.rhs, &first.rhs)?;
    let combined_op = expr_builders_arith::combine_ops(first.op, second.op);
    let combined_proof = mk_chain_step(
        sort,
        first.op,
        second.op,
        &combined_lhs,
        &sum_mid,
        &combined_rhs,
        &step1,
        &step2,
    )?;

    Some(SortCmpAcc {
        lhs: combined_lhs,
        rhs: combined_rhs,
        op: combined_op,
        proof: combined_proof,
    })
}

/// Scale a single hypothesis by a positive integer coefficient with a binary
/// addition chain.
///
/// For coefficient 1, returns the hypothesis directly. For coefficient
/// `k > 1`, repeated doubling builds authenticated powers of two and the set
/// bits of `k` are combined with [`combine_two_scaled_bounds`]. The resulting
/// arithmetic expression still contains exactly `k` copies of each endpoint,
/// while its proof depth is logarithmic rather than linear in `k`.
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

    let base = SortCmpAcc {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
        op,
        proof: hyp.clone(),
    };

    let mut remaining = coeff;
    let mut power = base;
    let mut result: Option<SortCmpAcc> = None;
    while remaining != 0 {
        if remaining & 1 == 1 {
            result = Some(match result {
                Some(acc) => combine_two_scaled_bounds(sort, &acc, &power)?,
                None => power.clone(),
            });
        }
        remaining >>= 1;
        if remaining != 0 {
            power = combine_two_scaled_bounds(sort, &power, &power)?;
        }
    }

    result
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

    let mut acc = combine_two_scaled_bounds(sort, &accs[0], &accs[1])?;

    // Iterate for remaining accumulators
    for bound in accs.iter().skip(2) {
        // The helper returns `second + first`; reverse the arguments here to
        // preserve the established left-associated `acc + bound` endpoint
        // shape consumed by symbolic normal-form closeout.
        acc = combine_two_scaled_bounds(sort, bound, &acc)?;
    }

    Some(acc)
}
