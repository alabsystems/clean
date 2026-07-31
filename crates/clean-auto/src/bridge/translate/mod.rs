// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term translation between kernel expressions and SMT solver terms.
//!
//! Provides bidirectional translation: kernel `Expr` -> SMT `TermId` via
//! `translate_term`, and negated assertion of classified propositions via
//! `translate_negated_classified`.

// AY decommission debt: see the ay_backend note in bridge/mod.rs.
#[allow(dead_code)]
mod inductive_to_dt;
mod keys;
mod negated_goal;
mod term_lowering;
mod witness_registry;

pub(super) use keys::collect_app_args;
pub(crate) use keys::ExprKey;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod tests_unreachable;
