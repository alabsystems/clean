// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — BatchVerifier and VerificationArena.
//!
//! Covers:
//! - `BatchVerifier` methods: stream_check, stream_valid, find_first_valid,
//!   find_first_valid_parallel, count_valid, valid_indices
//! - `VerificationArena` full API: push, push_many, verify_all, get_result, get_expr,
//!   get_type, is_valid, valid_pairs, valid_indices, stats, clear

use super::*;

mod batch_verifier;
mod fixtures;
mod verification_arena;
