// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Trust checks these universal source proofs during compilation when the
//! build sets `cfg(clean_trust_islands)`, the switch that also loads the
//! kernel model islands (`src/model_islands.rs`). Stock rustc cannot parse a
//! `clean mod`, so the island lives in a file only that cfg loads: Clean's own
//! source stays compilable with no Trust-only feature load-bearing. One way
//! to run it: `targo --unverified rustc --locked -p clean-kernel --test
//! half_shift_source -- --cfg clean_trust_islands`. This target has no Rust
//! test functions and grants no Rust implementation proof claim.

#[cfg(clean_trust_islands)]
#[path = "half_shift_source/island.rs"]
mod island;
