// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for type checker (part 2)
//
// Test modules are split by category for maintainability.
use super::*;
use crate::expr::{BinderInfo, FVarId};
use crate::name::Name;

mod support;

mod cases_on;
mod convert_fvar_cert;
mod defeq_literals;
mod hetero_projection_value;
mod inductive_field_types;
mod inductive_validation;
mod iota_extras;
mod iota_field_boundary;
mod iota_ih_order;
mod iota_indexed_recursive;
mod iota_pi_motive_fin_sum;
mod iota_recursive;
mod iota_reflexive;
mod iota_structural;
mod lift_expr;
mod local_context;
mod mutual_inductive;
mod nat_bignum_parity;
mod nat_reduction;
mod no_confusion;
mod no_confusion_fallback2_tests;
mod no_confusion_fallback_tests;
mod no_confusion_proof_tests;
mod no_confusion_reduce;
mod no_confusion_sort_levels;
mod no_confusion_v430_fidelity;
mod no_confusion_value_check;
mod no_confusion_value_tests;
mod order_diamond_chain;
mod ordering_projection_value;
mod perf_cache_proofs;
mod perf_complexity_tests;
mod perf_delta_scaling;
mod performance_proofs;
mod proof_cov_batch;
mod proof_cov_cache_reuse;
mod proof_cov_defeq;
mod proof_cov_inference;
mod proof_cov_iota;
mod proof_cov_literals;
mod proof_cov_reduction;
mod proof_cov_whnf;
mod proof_irrelevance;
mod rec_on;
mod recursor;
mod recursor_rhs_types;
mod reduce_cache;
mod soundness_nested_arg;
mod stack_safe_proofs;
mod structure_eta;
mod tc_parity_checks;
mod tc_regression_beta_delta;
mod tc_regression_nat_combined;
mod tc_regression_structural;
mod tc_regression_typeclass_unfold;
mod tests_lean4_parity;
