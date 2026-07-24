// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct unit tests for the Classical.em case-split combinator.
//!
//! Part of #2891: provide direct test coverage for `em_combinator.rs`,
//! which previously had zero direct tests and only indirect e2e coverage.

pub(super) use std::cell::Cell;

pub(super) use ay_core::{ProofId, TermId, TermStore};
pub(super) use clean_kernel::name::Name;
pub(super) use clean_kernel::{Expr, ExprKind};

pub(super) use super::em_combinator::EmSplitItem;
pub(super) use super::tests_support::{register_bool_var, translation_context};
pub(super) use super::{ReconstructionContext, ReconstructionError, VariableMapping};
pub(super) use crate::bridge::disjunction;

/// Translate every literal in a clause into kernel expressions.
pub(super) fn translated_props(
    ctx: &mut ReconstructionContext<'_>,
    clause: &[TermId],
) -> Vec<Expr> {
    clause
        .iter()
        .map(|&lit| {
            ctx.translate_term(lit)
                .expect("em_combinator test literals should translate")
        })
        .collect()
}

#[path = "tests_em_combinator_edge_cases.rs"]
mod edge_cases;
#[path = "tests_em_combinator_errors.rs"]
mod errors;
#[path = "tests_em_combinator_structure.rs"]
mod structure;
