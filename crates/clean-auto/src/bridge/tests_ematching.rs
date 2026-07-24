// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-matching and trigger extraction coverage.

pub(super) use super::super::*;
pub(super) use super::test_helpers::{make_eq, setup_env};

#[path = "tests_ematching/dedup.rs"]
mod dedup;
#[path = "tests_ematching/instantiation.rs"]
mod instantiation;
#[path = "tests_ematching/substitution.rs"]
mod substitution;
#[path = "tests_ematching/trigger_extraction.rs"]
mod trigger_extraction;
