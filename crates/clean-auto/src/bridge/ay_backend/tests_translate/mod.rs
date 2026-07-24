// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation-specific tests for the Ay SMT backend.
//!
//! Tests for expression translation semantics: Nat arithmetic (monus, div-by-zero),
//! FVar application handling (uninterpreted functions, congruence).
//! Split from tests.rs for file size (#2249).

pub(super) use super::*;
pub(super) use ay::Sort;
pub(super) use clean_kernel::FVarId;

mod domain_sorts;
mod fvar_apps;
mod mdata;
mod nat_semantics;
mod quantifier_like;
mod real_constructors;
mod solve_outcomes;
mod string_literals;
mod support;
mod typeclass_ops;
