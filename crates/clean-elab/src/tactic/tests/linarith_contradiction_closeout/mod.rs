// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linarith contradiction-closeout regressions.
//!
//! Split from `linarith_contradiction_closeout.rs` as part of #3004.

use super::*;

use self::support::{
    expr_contains_const, make_int_le_tc, make_real_le_tc, make_real_ofint, make_real_ofnat,
};

mod support;

mod mathverse_int;
mod real_concrete;
mod real_symbolic;
