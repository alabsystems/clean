// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test-only helper re-exports for tactic submodule tests.

pub(crate) use super::super::abs_cases::is_numeric_type;
pub(crate) use super::super::ac_rfl::{ac_exprs_equal, ac_normalize, get_ac_op_name, ACExpr};
pub(crate) use super::super::algebra::{AbelTerm, GroupTerm};
pub(crate) use super::super::arith_field_simp::extract_denominators;
pub(crate) use super::super::arith_linarith::{
    fourier_motzkin_check, fourier_motzkin_check_certified,
};
pub(crate) use super::super::arith_linarith_proof::{build_add_le_add_proof, build_scaled_proof};
pub(crate) use super::super::arith_mathverse_parse::{
    expr_to_linear, expr_to_mathverse_constraint, extract_constant, extract_single_var,
    match_hmod_app,
};
pub(crate) use super::super::arith_nlinarith::{
    is_zero_expr, nlinarith_exprs_equal, try_compute_linear_product,
};
pub(crate) use super::super::arith_push_neg::{make_not, push_neg_expr};
pub(crate) use super::super::calc::make_calc_rel;
pub(crate) use super::super::cc::CCState;
pub(crate) use super::super::debug::beta_reduce_all;
pub(crate) use super::super::decide_eq::{decidable_type_check, eval_to_nat, match_decidable_eq};
pub(crate) use super::super::finite_cases::{
    get_finite_inhabitants, make_nat_literal, substitute_fvar,
};
pub(crate) use super::super::gcongr::{
    make_ineq_goal, match_add, match_inequality, match_mul, IneqRel,
};
pub(crate) use super::super::hypothesis::collect_fvars;
pub(crate) use super::super::interval_cases::{make_equality_type, make_int_literal};
pub(crate) use super::super::library_search::{
    calculate_type_similarity, count_pis, expr_depth, extract_head_name,
};
pub(crate) use super::super::nat_expr_eval::eval_nat_expr;
pub(crate) use super::super::omega_tactic::{
    extract_certified_mathverse_constraints, mathverse_check_certified, negate_mathverse_constraint,
};
pub(crate) use super::super::pattern::{
    apply_predicate, count_foralls, extract_binary_args, extract_class_name, find_first_type,
    generate_fresh_hyp_name, get_app_head, infer_simple_type, is_binary_app, is_continuity_goal,
    is_dite_const, is_false_prop, is_ite_const, is_measurability_goal, is_true_prop, make_relation,
    occurs_bvar_dsimp, rename_hypothesis, shift_bvars_dsimp, split_pattern_args,
    try_extract_exists, try_infer_expr_type,
};
pub(crate) use super::super::polynomial::gcd_u64;
pub(crate) use super::super::ring_helpers::{
    make_add, make_mul, make_neg, make_pow, ring_expr_to_expr, ring_flatten_add, ring_flatten_mul,
    ring_normalize, RingExpr,
};
pub(crate) use super::super::search::{can_apply_to_produce, types_unify};
pub(crate) use super::super::simp::{
    beta_reduce, collect_simp_lemmas, contains_bvar, eta_reduce, is_trivial_equality,
    is_true_const, shift_expr,
};
pub(crate) use super::super::tauto::fresh_hyp_name;
pub(crate) use super::super::term_close::count_placeholders;
pub(crate) use super::super::unfold::substitute_const;
pub(crate) use super::super::wlog::{normalize_numerals, push_negations_in_expr};
