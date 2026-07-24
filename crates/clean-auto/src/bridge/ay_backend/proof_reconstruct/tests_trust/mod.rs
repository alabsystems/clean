// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Trust step handling in ay proof reconstruction.
//!
//! Trust steps are emitted by ay's SAT proof manager when resolution hint
//! reconstruction fails. Instead of cascading failures to downstream steps,
//! the reconstruction pipeline synthesizes `trustedAy` sub-terms for Trust
//! step clauses, allowing the remaining proof to be kernel-verified.
//!
//! Part of #302.

pub(super) use super::{attempt_reconstruction, VariableMapping};
pub(super) use crate::bridge::ay_backend::{ResidualTrustSource, ResidualTrustSummary};
pub(super) use ay::Sort;
pub(super) use ay_core::{AletheRule, Proof, TermStore, TheoryLemmaKind};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{Expr, ExprKind, FVarId, Level};

mod fallback;
mod support;
mod surface;
mod typecheck;

use support::{
    assert_composed_proof_type_checks_to_false, count_trusted_ay_in_expr, mk_env_with_test_prop,
    mk_p_hypothesis, mk_trust_single_literal,
};
