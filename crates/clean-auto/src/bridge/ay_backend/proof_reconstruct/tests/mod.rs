// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof reconstruction translation and smoke tests split by scenario family.

pub(super) use super::expr_builders::{mk_and, mk_eq, mk_not, sort_to_lean_type};
pub(super) use super::tests_support::{bool_var, translation_context};
pub(super) use super::trace::ProofTrace;
pub(super) use super::{
    attempt_reconstruction, ReconstructionContext, ReconstructionError, VariableMapping,
};
pub(super) use ay::Sort;
pub(super) use ay_core::{Proof, TermStore};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{Expr, ExprKind, FVarId, Level};

mod assume;
mod core;
mod farkas_certificate;
mod quantifiers;
mod stack_safe;
mod tests_expr_builders;
#[path = "../tests_expr_builders_arith/mod.rs"]
mod tests_expr_builders_arith;
#[path = "../tests_expr_builders_arith_typecheck.rs"]
mod tests_expr_builders_arith_typecheck;
#[path = "../tests_perf.rs"]
mod tests_perf;
#[path = "../tests_real_downcast_normalize.rs"]
mod tests_real_downcast_normalize;
#[path = "../tests_scale_bound_boundary.rs"]
mod tests_scale_bound_boundary;
mod trace_rooting;
mod translate_term_inner;
