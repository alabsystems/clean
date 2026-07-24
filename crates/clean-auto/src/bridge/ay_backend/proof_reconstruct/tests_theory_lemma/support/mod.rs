// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test fixture helpers for theory-lemma proof reconstruction tests.
//!
//! Organized into three sub-modules with distinct import contracts:
//!
//! - `boundary`: Fake-constant helpers for trust-boundary / semantic-validation
//!   failure tests. Only boundary test modules should import from here.
//! - `semantic`: Semantically honest helpers for success-path fixtures. Uses
//!   native ay constants and raw comparison builders.
//! - `kernel`: Kernel environment bootstrap and type-check assertion helpers.

pub(super) mod boundary;
pub(super) mod kernel;
pub(super) mod semantic;
