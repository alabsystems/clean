// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! QBF certificate and strategy verification helpers.
//!
//! The QBF lane backs the `invalid_qbf_strategy` false control
//! (`clean_mathverse::false_control_suite::FalseControlId::InvalidQbfStrategy`):
//! a deliberately broken Skolem strategy must be REJECTED, so every check in
//! [`strategy`] is fail-closed by construction.

pub mod strategy;
