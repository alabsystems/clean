// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evidence formats and source provenance checks that do not need a Clean kernel.

#![forbid(unsafe_code)]

pub mod digest;
pub mod envelope;
pub mod source_scan;
pub mod trustcore;
