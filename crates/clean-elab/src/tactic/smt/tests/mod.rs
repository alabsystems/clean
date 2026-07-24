// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[cfg(not(feature = "ay-smt"))]
pub(super) use super::bridge_reconstruction;
#[cfg(feature = "ay-smt")]
pub(super) use super::SmtSolver;
pub(super) use super::{
    assert_no_sorry, ay_reconstruction_failure_count, ay_types, bridge_validation,
    record_ay_reconstruction_failure, record_ay_reconstruction_success,
    reset_ay_reconstruction_failure_counter, reset_sorry_counter, AyConfig, SmtVerifyPolicy,
};
pub(super) use crate::tactic::smt_translate::SmtSort;
pub(super) use crate::tactic::tc_app::nat_le_tc;
pub(super) use crate::tactic::ProofState;
#[cfg(not(feature = "ay-smt"))]
pub(super) use clean_kernel::env::Declaration;
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::sorry::{
    create_sorry_term, local_ay_reconstruction_success_count,
    reset_local_ay_reconstruction_success_counter,
};
pub(super) use clean_kernel::{Environment, Expr};

mod config;
mod counters;
mod decide;
mod recovery;
#[cfg(feature = "ay-smt")]
mod solver_observability;
mod validation;
