// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry-absence verification tests for tactic soundness.
//!
//! These tests verify that tactics produce genuine proof terms, not sorry-based
//! fallbacks. Three global counters are monitored:
//!
//! - `sorry_count()`: increments on `create_sorry_term()` — incomplete proofs
//! - `arith_proof_count()`: increments on `create_trusted_arith_term()` — trustedArith fallback
//! - `ay_proof_count()`: increments on `create_trusted_ay_term()` — trustedAy fallback
//!
//! Tests assert that NONE of these counters increase when running tactics on
//! provable goals, unless the test explicitly documents a known trusted-axiom
//! dependency. Without monitoring all three counters, a tactic can silently
//! redirect sorry fallbacks to trustedArith/trustedAy, causing sorry_count tests
//! to pass while no kernel-checkable proofs are produced.
//!
//! Filed as part of #1144 enforcement gap analysis.

use super::*;
use crate::tactic::{arith_proof_count, ay_proof_count};
use clean_kernel::env::Declaration;
use clean_kernel::sorry::sorry_count;
use serial_test::serial;

mod aesop;
mod arith;
mod decide;
mod mathverse;
mod simp;
mod support;

use support::{
    assert_all_counters_zero_on_failure, setup_env_with_simp_add_lemma, setup_linarith_transitivity,
};
