// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Opt-in, total restoring division with checked agreement to the unchanged
//! raw subtraction evaluator. Zero returns the dividend in BOTH projections.
//! Positive divisors use a universally sufficient depth bound and the existing
//! guarded restoring driver, never the bounded 4200 wrapper. This is a migration
//! foundation, not a replacement of default arithmetic, a kernel reducer, or
//! model/native admission.

use super::{preflight, register_rows_and_check, verify_root, AGREEMENT_ROOTS};
use crate::spec::{SpecError, Specification};

#[path = "total_division_sources.rs"]
mod sources;

#[cfg(test)]
#[path = "total_division_tests.rs"]
mod tests;

const ROOTS: &[&str] = &[
    "ir_nat_div_total_agrees_v1",
    "ir_nat_rem_total_agrees_v1",
    "ir_nat_rem_total_positive_bound_v1",
    "ir_nat_rem_positive_bound_v1",
];

fn rows() -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    // Ordinary ByteV1 omits the LZD stage. Reuse this exact checked comparison
    // proof from its existing source owner, without registering that stage.
    // Its only non-primitive dependencies are the existing walk and checked
    // Bool absurdity prerequisite already carried by the positive package.
    std::iter::once((
        "ir_nat_ltb_succ_walk",
        super::super::eval_ir_lzd_fresh::ltb_succ_walk_source(),
    ))
    .chain(sources::UNCONDITIONAL.iter().chain(sources::TOTAL).copied())
}

#[cfg(test)]
pub(super) fn source_for_probe(name: &str) -> Option<&'static str> {
    sources::UNCONDITIONAL
        .iter()
        .find_map(|(key, source)| (*key == name).then_some(*source))
}

fn install_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    preflight(spec, rows.clone())?;
    // The existing checked package is an actual prerequisite, not a set of
    // names that can confer authority on an axiom or unchecked substitute.
    for root in AGREEMENT_ROOTS {
        verify_root(spec, root)?;
    }
    let mut candidate = spec.clone();
    register_rows_and_check(&mut candidate, rows, ROOTS)?;
    *spec = candidate;
    Ok(())
}

impl Specification {
    /// Atomically install the total restoring facade and all-Nat agreement into
    /// an owner carrying the existing checked positive-division package. Raw
    /// division, default vocabularies, caches, and checker policies stay fixed.
    ///
    /// # Errors
    /// Collision, missing/uncertified substrate, declaration or rooted refusal.
    pub(crate) fn install_eval_ir_total_restoring_division_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_transactionally(self, rows())
    }
}
