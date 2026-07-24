// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge-local re-exports of the shared arithmetic proof builders.
//!
//! The implementation lives in [`crate::arith_proof`]. This module provides
//! backward-compatible paths for existing bridge consumers (#2905).

pub(crate) use crate::arith_proof::{
    combine_ops, detect_sort, mk_chain_step, mk_le_antisymm, mk_le_of_lt, mk_le_refl,
    mk_lt_irrefl_false, mk_nat_ground_le, mk_nat_ground_lt, ArithSort, CmpOp,
};
