// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared proptest strategies for generating CNF formulas, clauses, and
//! DRAT-style proof steps. Used by all sibling modules in
//! `fuzz_tests_proptest`.

use crate::sat_verify::cdcl::proof_logging::ProofStep;
use proptest::collection::vec;
use proptest::prelude::*;

/// Generate a single non-zero DIMACS literal over `1..=num_vars`.
pub(super) fn lit_strategy(num_vars: u32) -> impl Strategy<Value = i32> {
    (1..=num_vars as i32, any::<bool>()).prop_map(|(v, sign)| if sign { v } else { -v })
}

/// Generate a clause of 0..=max_len literals over `1..=num_vars`, deduplicated.
pub(super) fn clause_strategy(num_vars: u32, max_len: usize) -> impl Strategy<Value = Vec<i32>> {
    vec(lit_strategy(num_vars), 0..=max_len).prop_map(|lits| {
        let mut seen = std::collections::BTreeSet::new();
        let mut out = Vec::with_capacity(lits.len());
        for l in lits {
            if !seen.contains(&-l) && seen.insert(l) {
                out.push(l);
            }
        }
        out
    })
}

/// Generate a CNF formula: 0..=max_clauses clauses over `1..=num_vars`.
pub(super) fn cnf_strategy(
    num_vars: u32,
    max_clauses: usize,
    max_clause_len: usize,
) -> impl Strategy<Value = Vec<Vec<i32>>> {
    vec(clause_strategy(num_vars, max_clause_len), 0..=max_clauses)
}

/// Generate a random DRAT step (Add or Delete) over the given variable bound.
pub(super) fn drat_step_strategy(
    num_vars: u32,
    max_len: usize,
) -> impl Strategy<Value = ProofStep> {
    prop_oneof![
        clause_strategy(num_vars, max_len).prop_map(ProofStep::Add),
        clause_strategy(num_vars, max_len).prop_map(ProofStep::Delete),
    ]
}
