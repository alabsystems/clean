// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Search Tactics (exact?, apply?, suggest, aesop)
//!
//! This module provides proof search tactics that explore the proof space
//! to find applicable lemmas or suggest tactics.
//!
//! # AND-OR Tree Search
//!
//! The aesop tactic implements AND-OR tree search with backtracking:
//! - Goals are OR nodes (any child rapp proving the goal succeeds)
//! - Rule applications (rapps) are AND nodes (all subgoals must be proven)
//!
//! This architecture enables proper backtracking when unsafe rules fail,
//! which is required for Mathlib compatibility.

mod aesop;
mod aesop_builders;
mod aesop_rules;
mod aesop_search;
mod goal_queue;
mod simple;
mod suggest;
mod types;

pub use aesop::{aesop, aesop_with_config, AesopConfig, AesopRule, AesopRuleKind};
pub use simple::{apply_search, exact_search, rewrite_search, SearchResult};
pub(crate) use simple::{can_apply_to_produce, types_unify};
pub use suggest::{
    apply_search_and_apply, exact_search_and_apply, hint, rewrite_search_and_apply, suggest,
    TacticSuggestion,
};
#[cfg(test)]
pub use types::AesopStrategy;
pub use types::{AesopSearchState, RuleAttempt};
