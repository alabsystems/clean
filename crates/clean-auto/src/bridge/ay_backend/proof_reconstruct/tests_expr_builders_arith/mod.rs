// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused arithmetic expr-builder scenario families under
//! `tests::tests_expr_builders_arith`.

pub(super) use super::super::expr_builders_arith::{
    combine_ops, extract_concrete_int_from_expr, is_concrete_violation_by_expr,
    mk_int_concrete_false, mk_lt_irrefl_false, CmpOp,
};
pub(super) use super::super::theory_lemma_lra_additive::{
    combine_scaled_bounds, mk_int_add, scale_bound, SortCmpAcc,
};
pub(super) use super::super::theory_lemma_lra_sum_nf::{
    build_close_shape, try_close_int_additive_nf, IntAddNf,
};
pub(super) use super::{Expr, ExprKind, Name, Sort};

mod support;

mod combine_scaled_bounds;
mod concrete_false;
mod concrete_int;
mod scale_bound;

use support::expr_contains_const;

fn mk_var_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_int_ofnat_expr(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_int_negsucc_expr(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}
