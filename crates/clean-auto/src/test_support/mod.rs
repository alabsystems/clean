// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Crate-level test-support utilities for `clean-auto`'s source-reading
//! ratchets. Test-only: gated `#[cfg(test)]` at the `lib.rs` declaration.

pub(crate) mod source_scan;
