// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for SMT bridge
use super::*;

#[path = "test_helpers.rs"]
pub(super) mod test_helpers;
use test_helpers::{make_eq, setup_env};

#[path = "tests_arith_chain.rs"]
mod tests_arith_chain;
#[path = "tests_arith_int.rs"]
mod tests_arith_int;
#[path = "tests_arith_reconstruction.rs"]
mod tests_arith_reconstruction;
#[path = "tests_arith_typecheck.rs"]
mod tests_arith_typecheck;
#[path = "tests_array.rs"]
mod tests_array;
#[path = "tests_cross_validation.rs"]
mod tests_cross_validation;
#[path = "tests_disjunction.rs"]
mod tests_disjunction;
#[path = "tests_ematching.rs"]
mod tests_ematching;
#[path = "tests_gamma_crown_ay_discharge.rs"]
mod tests_gamma_crown_ay_discharge;
#[path = "tests_goal_premise.rs"]
mod tests_goal_premise;
#[path = "tests_hypothesis_stack_safety.rs"]
pub(crate) mod tests_hypothesis_stack_safety;
#[path = "tests_kernel_validate.rs"]
mod tests_kernel_validate;
#[path = "tests_kernel_validate_exists.rs"]
mod tests_kernel_validate_exists;
#[path = "tests_kernel_validate_exists_unkeyable.rs"]
mod tests_kernel_validate_exists_unkeyable;
#[path = "tests_proof_recon_equality.rs"]
mod tests_proof_recon_equality;
#[path = "tests_proof_reconstruction.rs"]
mod tests_proof_reconstruction;
#[path = "tests_prop_classical_split.rs"]
mod tests_prop_classical_split;
#[path = "tests_prop_compound_typecheck.rs"]
mod tests_prop_compound_typecheck;
#[path = "tests_prop_eq_multihop.rs"]
mod tests_prop_eq_multihop;
#[path = "tests_prop_eq_rewrite.rs"]
mod tests_prop_eq_rewrite;
#[path = "tests_prop_eq_trans.rs"]
mod tests_prop_eq_trans;
#[path = "tests_prop_fallback.rs"]
mod tests_prop_fallback;
#[path = "tests_prop_helper_paths.rs"]
mod tests_prop_helper_paths;
#[path = "tests_prop_iff.rs"]
mod tests_prop_iff;
#[path = "tests_prop_phase3.rs"]
mod tests_prop_phase3;
#[path = "tests_prop_phase3_typecheck.rs"]
mod tests_prop_phase3_typecheck;
#[path = "tests_prop_phase3b.rs"]
mod tests_prop_phase3b;
#[path = "tests_prop_reconstruction.rs"]
mod tests_prop_reconstruction;
#[path = "tests_prop_surface.rs"]
mod tests_prop_surface;
#[path = "tests_prove_basic.rs"]
mod tests_prove_basic;
#[path = "tests_quantifier_regression.rs"]
mod tests_quantifier_regression;
#[path = "tests_rat_ay_proof.rs"]
mod tests_rat_ay_proof;
#[path = "tests_regression.rs"]
mod tests_regression;
#[path = "tests_scoring_quantifier.rs"]
mod tests_scoring_quantifier;
#[path = "tests_skolem.rs"]
mod tests_skolem;
#[path = "tests_stack_safety.rs"]
mod tests_stack_safety;
#[path = "tests_total_priority.rs"]
mod tests_total_priority;
#[path = "tests_trail_guidance.rs"]
mod tests_trail_guidance;
#[path = "tests_trail_payload.rs"]
mod tests_trail_payload;
#[path = "tests_trigger.rs"]
mod tests_trigger;

#[path = "tests_lossy_guard.rs"]
mod tests_lossy_guard;
#[path = "tests_root/classify_edges.rs"]
mod tests_root_classify_edges;
#[path = "tests_root/logical_form.rs"]
mod tests_root_logical_form;
#[path = "tests_root/stats.rs"]
mod tests_root_stats;
#[path = "tests_root/support.rs"]
mod tests_root_support;
#[path = "tests_root/term_translation.rs"]
mod tests_root_term_translation;
#[path = "tests_root/witness.rs"]
mod tests_root_witness;

#[path = "tests_instantiate.rs"]
mod tests_instantiate;
#[path = "tests_proof_translation_contract.rs"]
mod tests_proof_translation_contract;
#[path = "tests_prop_exists.rs"]
mod tests_prop_exists;

use tests_root_support::{collect_hypothesis_ids, congr_func_name};
