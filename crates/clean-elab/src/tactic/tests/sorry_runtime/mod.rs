// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime sorry frequency metric (#2160 T1).
//!
//! While the static sorry ratchet (`sorry_census.rs`) counts *call sites* via
//! `sorry_baseline.json`, this module measures how often sorry actually fires
//! at *runtime* across a representative tactic workload.
//!
//! The workload exercises 9 goal/tactic combinations:
//! - W1-W6: Arithmetic tactics (linarith, mathverse, nlinarith) — expected 0 sorry post-Phase 3
//! - W7: Instance resolution without a typeclass table — expected 0 sorry (fails closed)
//! - W8: Intentional `sorry` tactic — always 1
//! - W9: Direct `create_sorry_term` (structural sorry) — always 1
//!
//! The ratchet constant `RUNTIME_SORRY_RATCHET` is defined locally in the
//! ratchet test. Tighten it downward as tactic improvements eliminate sorry.

use super::*;
use clean_kernel::sorry::{
    create_sorry_term, enable_sorry_location_tracking, reset_sorry_counter, reset_sorry_locations,
    sorry_count, sorry_locations,
};
use serial_test::serial;

mod deny_all;
mod ratchet;
mod reporting;
mod workloads;

use reporting::format_sorry_locations;
use workloads::{
    workload_instance_no_table, workload_linarith_basic, workload_linarith_le_trans,
    workload_linarith_scaled, workload_mathverse_linear, workload_mathverse_parity,
    workload_nlinarith, workload_sorry_tactic, workload_structural_sorry,
};
