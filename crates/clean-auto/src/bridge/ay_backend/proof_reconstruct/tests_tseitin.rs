// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tseitin clausification rule handlers grouped by rule family.
//!
//! Tseitin rules are premise-free tautology clauses emitted during ay's
//! Boolean clausification. Each clause encodes a direction of the equivalence
//! `v ↔ phi` where `v` is the Tseitin variable for sub-formula `phi`.
//!
//! Part of #302.

pub(super) use super::{attempt_reconstruction, VariableMapping};
pub(super) use ay::Sort;
pub(super) use ay_core::{Proof, TermStore};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};

mod and_neg;
mod and_pos;
mod or_neg;
mod or_pos;
mod support;
