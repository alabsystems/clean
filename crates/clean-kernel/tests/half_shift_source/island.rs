// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The Trust-only island of `tests/half_shift_source.rs`, loaded only under
//! `cfg(clean_trust_islands)`.

#[path = "../half_shift_source.lean"]
clean mod half_shift_proof;
