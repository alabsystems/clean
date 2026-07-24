// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end LRA Farkas proof reconstruction tests with kernel TypeChecker
//! validation.
//!
//! Split into shared support plus Int-only scenario families:
//! - `support`: environment/bootstrap helpers and shared e2e assertions
//! - `int_chain`: transitivity-chain closeout coverage
//! - `int_additive`: additive and symbolic additive closeout coverage
//! - `int_additive_nf`: additive normal-form cancellation coverage

pub(super) use super::{attempt_reconstruction, VariableMapping};
pub(super) use ay::Sort;
pub(super) use ay_core::{FarkasAnnotation, Proof, TermStore};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, Level};

mod support;

mod int_additive;
mod int_additive_nf;
mod int_chain;

pub(super) use support::{
    mk_env_for_lra, mk_env_for_real_lra, mk_int_add_expr, mk_int_ofnat, mk_le_int, mk_le_real,
    mk_lt_real, mk_real_add_expr, mk_real_int_const_expr, mk_real_ofint_expr, mk_real_ofnat,
};
