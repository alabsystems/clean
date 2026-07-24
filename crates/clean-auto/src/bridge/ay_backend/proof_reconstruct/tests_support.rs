// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test fixture helpers for proof-reconstruct direct suites.
//!
//! Consolidates translation-context setup and Bool variable registration
//! that was duplicated across tests/, tests_em_combinator, tests_trace,
//! tests_trace_rooting, and tests_resolution modules.

use super::{ReconstructionContext, VariableMapping};
use ay::Sort;
use ay_core::{TermId, TermStore};
use clean_kernel::{Expr, FVarId};

/// Create a translation-only context backed by the term store.
pub(super) fn translation_context<'a>(
    terms: &'a TermStore,
    map: &'a VariableMapping,
) -> ReconstructionContext<'a> {
    ReconstructionContext::new(terms, map, 0)
}

/// Create a Bool variable in the term store.
pub(super) fn bool_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

/// Register a Bool variable in both the term store and variable mapping.
pub(super) fn register_bool_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> TermId {
    let tid = terms.mk_var(name, Sort::Bool);
    map.register_var(name, Expr::fvar(FVarId::new(id)), Expr::prop());
    tid
}

/// Register a Bool variable with hypothesis registration (for resolution tests).
///
/// Extends `register_bool_var` by also calling `register_hypothesis`, which
/// is needed for resolution proof reconstruction that looks up hypothesis FVars.
pub(super) fn register_bool_hypothesis_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> TermId {
    let tid = register_bool_var(terms, map, name, id);
    map.register_hypothesis(
        name,
        FVarId::new(id),
        Expr::fvar(FVarId::new(id)),
        Expr::prop(),
    );
    tid
}
