// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Crate-level test-support utilities for production-source scanning.
//!
//! Provides shared helpers for ratchet tests and hygiene gates that need to
//! walk Rust source files and distinguish production code from test code.

pub(crate) mod source_scan;
