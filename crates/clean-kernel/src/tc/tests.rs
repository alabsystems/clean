// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for type checker
//
// Test modules are split by category for maintainability.
use super::*;

pub(crate) mod helpers;

mod args_failure_cache;
mod basics;
mod batch_cache;
mod bignat;
mod cache;
mod cert_abstract;
mod cert_infer;
mod cert_rebind;
mod certified;
mod cubical;
mod cubical_cert_hcomp_cap;
mod cubical_coe;
mod cubical_glue;
mod cubical_groupoid;
mod cubical_hcomp_ctor;
mod cubical_hcomp_universe;
mod cubical_hfill;
mod cubical_hlevels;
mod cubical_int;
mod cubical_isequiv;
mod cubical_j;
mod cubical_paths;
mod cubical_pi1;
mod defeq;
mod delta_reduction;
mod directed;
mod dite_proof_irrel_ws9;
mod eq_trans_regression;
mod errors;
mod eta;
mod heartbeat;
mod higher_order_pi;
mod infer_type_recursion_guard;
mod let_zeta;
mod micro;
mod mutation;
mod projection;
mod projection_scaling;
mod proof_cov;
mod proof_irrelevance;
mod proof_irrelevance_edge;
mod quotient;
mod recursor;
mod scaling;
mod struct_eta;
mod struct_eta_advanced;
mod trust_kernel_certified;
mod whnf;
mod whnf_bare_binop_defer;
mod whnf_proof;
mod whnf_proof_coverage;
mod zfc;
