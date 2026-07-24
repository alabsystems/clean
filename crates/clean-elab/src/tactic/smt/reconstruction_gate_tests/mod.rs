// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reconstruction-gate test module.
//!
//! Split from a flat `reconstruction_gate_tests.rs` into lane-specific leaves:
//! - `support`: shared env/proof builders used across all lanes
//! - `wrap`: refutation-wrapping coverage (`ay_refutation`)
//! - `acceptance`: candidate acceptance and trust-accounting ratchets
//! - `exists`: Exists-placeholder closure and solver-backed integration

mod support;

mod acceptance;
mod exists;
mod wrap;
