// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel soundness gate — dedicated integration test binary.
//!
//! Structured gate that verifies clean kernel soundness by comparing
//! accept/reject behavior against a checked-in Lean 4 corpus.
//!
//! Mirrors the ay soundness gate pattern:
//! - `accept.rs`: files clean must accept without trust (Lean 4 accepts them)
//! - `reject.rs`: files clean must reject (Lean 4 rejects them)
//! - `ledger.rs`: fail-closed regression ledger linking issues to gate tests
//! - `common.rs`: shared gate verdict types and runner helpers
//!
//! Run: `cargo test -p clean-elab --test soundness_gate`
//!
//! Issue: #2134
//! Design: designs/2026-03-11-2134-structured-kernel-soundness-gate.md

mod common;

mod accept;
mod baseline;
mod corpus;
mod ledger;
mod reject;
