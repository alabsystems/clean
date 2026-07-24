// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Advanced tactic tests, split by tactic family.
//!
//! Previously a single 6000+ line file; now organized into focused modules.
//!
//! Related test files (split earlier):
//! - conv.rs: conv tactic tests
//! - library_search.rs: library search tests
//! - propositional.rs: contrapose, push_neg, tauto tests
//! - search_tactics.rs: exact?, apply?, suggest, aesop, hint tests

use super::*;

mod support;

mod algebraic_reasoning;
mod algebraic_reasoning_ext;
mod arith_frontend;
mod calc_trans_chain;
mod equality_conversion;
mod instance_misc;
mod instance_misc_ext;
mod instance_misc_helpers;
mod new_tactics;
mod proof_term_soundness;
mod tactic_state;
