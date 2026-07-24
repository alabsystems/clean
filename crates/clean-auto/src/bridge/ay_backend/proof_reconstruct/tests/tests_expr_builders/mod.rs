// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused expr-builder scenario families under `tests::tests_expr_builders`.

pub(super) use super::super::expr_builders::{
    infer_universe_level, mk_add, mk_eq, mk_ite_checked, mk_le, mk_lt, mk_mul, mk_neg,
    sort_to_lean_type,
};
pub(super) use super::super::expr_builders_arith::{
    combine_ops, mk_chain_step_for_sort, mk_int_concrete_false, mk_lt_irrefl_false,
    mk_real_concrete_false, mk_real_ofint_concrete_false, CmpOp,
};
pub(super) use super::super::expr_builders_real_downcast::downcast_real_hyp_to_int;
pub(super) use super::{
    Expr, ExprKind, FVarId, Level, Name, ReconstructionContext, Sort, TermStore, VariableMapping,
};

mod support;

mod concrete_false;
mod instance_and_chain;
mod sort_and_ite;

use support::expr_contains_const;
