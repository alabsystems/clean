// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for propositional proof reconstruction (#2442 Phases 2-3).

pub(super) use super::super::*;
pub(super) use crate::proof::ProofStep;
pub(super) use clean_kernel::env::Declaration;
pub(super) use ntest::timeout;

#[path = "tests_prop_reconstruction/classical_forms.rs"]
mod classical_forms;
#[path = "tests_prop_reconstruction/direct.rs"]
mod direct;
#[path = "tests_prop_reconstruction/errors.rs"]
mod errors;
#[path = "tests_prop_reconstruction/proof_search.rs"]
mod proof_search;
#[path = "tests_prop_reconstruction/recursive.rs"]
mod recursive;
#[path = "tests_prop_reconstruction/support.rs"]
mod support;

use support::*;
