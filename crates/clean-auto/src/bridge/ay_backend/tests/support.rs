// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for ay_backend tests.

use super::*;

/// A backend holding the pigeonhole problem with `holes + 1` pigeons and
/// `holes` holes: propositional, UNSAT, and refutable only by a search whose
/// conflict count grows exponentially with `holes` (no resolution refutation
/// is shorter), so a small `:rlimit` or a tiny `:timeout` stops it undecided.
pub(super) fn pigeonhole_proof_backend(config: AyBackendConfig, holes: usize) -> AyProofBackend {
    let mut backend = AyProofBackend::with_config(config);
    let sits: Vec<Vec<String>> = (0..=holes)
        .map(|pigeon| {
            (0..holes)
                .map(|hole| backend.fresh_bool(&format!("p{pigeon}h{hole}")))
                .collect()
        })
        .collect();
    for pigeon in &sits {
        backend.assert_formula(&format!("(or {})", pigeon.join(" ")));
    }
    // Hole by hole, every pair of pigeons in pigeon order.
    let in_hole = (0..holes).map(|hole| {
        sits.iter()
            .map(|pigeon| pigeon[hole].as_str())
            .collect::<Vec<_>>()
    });
    for sitters in in_hole {
        for (index, first) in sitters.iter().enumerate() {
            for second in &sitters[index + 1..] {
                backend.assert_formula(&format!("(or (not {first}) (not {second}))"));
            }
        }
    }
    backend
}

pub(super) fn build_unsat_proof_backend(config: AyBackendConfig) -> AyProofBackend {
    let mut backend = AyProofBackend::with_config(config);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {} 0)", x));
    backend.assert_formula(&format!("(< {} 0)", x));
    backend
}
