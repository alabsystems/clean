// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end arithmetic proof reconstruction tests that close through the
//! kernel TypeChecker.
//!
//! Split into sub-modules by test category:
//! - `chain`: cyclic and transitivity chain closers
//! - `mixed_ge_le`: raw `>=`/`<`/`>=` chain normalization coverage
//! - `normalization`: raw `>` / `>=` operator normalization
//! - `farkas_coeff`: Farkas coefficient pruning and symbolic-tail handling

pub(super) use super::tests_e2e::assert_proof_type_checks_to_false;
pub(super) use super::{attempt_reconstruction, ReconstructionResult, VariableMapping};
pub(super) use ay::Sort;
pub(super) use ay_core::{FarkasAnnotation, Proof, Symbol, TermStore, TheoryLemmaKind};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, FVarId, Level, LocalContext,
};

mod support;

mod additive;
mod chain;
mod farkas_coeff;
mod mixed_ge_le;
mod normalization;
mod pcay_milestone1;
