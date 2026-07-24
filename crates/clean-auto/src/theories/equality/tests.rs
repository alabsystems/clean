// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "tests_backtrack.rs"]
mod tests_backtrack;
#[path = "tests_core.rs"]
mod tests_core;
#[path = "tests_deductions.rs"]
mod tests_deductions;
#[path = "tests_explanations.rs"]
mod tests_explanations;
#[path = "tests_proof.rs"]
mod tests_proof;
#[path = "tests_reset.rs"]
mod tests_reset;

use super::*;
use crate::cdcl::Lit;
use crate::egraph::Symbol;
use crate::proof::ProofForest;
use crate::smt::{SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};
