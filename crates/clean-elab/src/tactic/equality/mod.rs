// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality-focused tactics and helpers.
//!
//! This module contains tactics that manipulate equality goals and hypotheses,
//! along with helper routines for matching and rewriting equalities.
//!
//! Split into sub-modules for maintainability (#307):
//! - `expr_utils`: Pure expression helpers (match_equality, contains_expr, etc.)
//! - `rewrite`: Rewrite tactics (rewrite, rewrite_at, rewrite_ltr, rewrite_rtl)
//! - `structural`: Structural equality tactics (symm, trans, calc_trans)
//! - `subst`: Substitution tactics (subst, subst_vars) — split from structural.rs

mod expr_utils;
mod rewrite;
mod structural;
mod subst;

pub(crate) use expr_utils::{
    abstract_over, contains_expr, find_defeq_subterm_with, match_equality, replace_expr,
    rewrite_candidate_summaries,
};
pub use rewrite::{
    resolve_env_rewrite_parts, rewrite, rewrite_at, rewrite_at_with_proof, rewrite_ltr,
    rewrite_rtl, rewrite_with_proof,
};
#[cfg(test)]
pub(crate) use rewrite::{rewrite_chain, RewriteDirection, RewriteRule};
pub use structural::{calc_trans, symm, trans};
pub use subst::{subst, subst_vars};
