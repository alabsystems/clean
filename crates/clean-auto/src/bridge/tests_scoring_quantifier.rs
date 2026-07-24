// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier scoring and prefix-analysis coverage.

pub(super) use super::super::*;
pub(super) use super::{make_eq, setup_env};
// Goal-premise tests share this fixture helper with the priority leaf.
pub(super) use priority::make_pending_forall;

#[path = "tests_scoring_quantifier/prefix_analysis.rs"]
mod prefix_analysis;
#[path = "tests_scoring_quantifier/priority.rs"]
mod priority;
#[path = "tests_scoring_quantifier/trigger_scoring.rs"]
mod trigger_scoring;
