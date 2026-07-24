// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-type soundness tests for linarith proof construction.
//!
//! Split from `linarith_proof_type.rs` as part of #3004.

use super::*;

use self::support::{expr_contains_const, make_int_le_tc, make_real_le_tc, mk_rel};

mod support;

mod chain_closeout;
mod scaling;
mod term_soundness;
mod verify_proof;
