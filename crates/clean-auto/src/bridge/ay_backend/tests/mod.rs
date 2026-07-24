// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Ay SMT backend.

pub(super) use super::*;
pub(super) use ay::Sort;
pub(super) use clean_kernel::expr::BigNat;
pub(super) use clean_kernel::{Expr, FVarId};
pub(super) use num_bigint::BigInt;

mod core;
mod profiles;
mod proof_backend;
mod runtime_helpers;
mod support;
mod translation_guards;
mod triggers;
