// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof reconstruction tests for equality reasoning.

pub(super) use super::super::*;
pub(super) use super::test_helpers::{make_eq, setup_env};
pub(super) use super::{collect_hypothesis_ids, congr_func_name};
pub(super) use clean_kernel::env::Declaration;

#[path = "tests_proof_recon_equality/basics.rs"]
mod basics;
#[path = "tests_proof_recon_equality/chains.rs"]
mod chains;
#[path = "tests_proof_recon_equality/congruence.rs"]
mod congruence;
#[path = "tests_proof_recon_equality/nary.rs"]
mod nary;
