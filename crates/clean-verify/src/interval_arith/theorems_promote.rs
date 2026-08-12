// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dynamic proof-status computation for the 20 interval arithmetic theorems.
//!
//! The registration-time statuses in [`super::theorems::all_proof_statuses`]
//! are hardcoded placeholders; the **true** kernel-verified status comes from
//! the promote pipeline. This module exposes that pipeline as a single call
//! ([`compute_proof_statuses_dynamically`]) plus the id → spec-name mapping
//! ([`spec_name_for`]).
//!
//! Part of #3362 Acceptance Criterion #2.

use crate::proofs::promote::PromotionError;
use crate::spec::SpecError;

// Only `compute_proof_statuses_dynamically` uses these, and it is gated on
// `any(test, feature = "test-utils")` because it needs
// `Specification::new_interval_arith_test_spec`. Gate the imports identically
// so a plain build does not carry them unused.
#[cfg(any(test, feature = "test-utils"))]
use crate::proofs::promote::promote_single;
#[cfg(any(test, feature = "test-utils"))]
use crate::proofs::ProofLibrary;
#[cfg(any(test, feature = "test-utils"))]
use crate::spec::{ProofStatus, Specification};

/// Errors that can surface when computing dynamic proof statuses.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DynamicStatusError {
    /// Building the interval arithmetic test spec failed.
    #[error("failed to build interval arith spec: {0}")]
    Spec(#[from] SpecError),
    /// The T0x id has no matching spec definition name.
    #[error("no spec definition mapping for theorem id `{0}`")]
    UnknownTheoremId(String),
    /// Running `promote_single` against the spec failed.
    #[error("promote_single failed for `{spec_name}` ({id}): {error}")]
    PromoteFailed {
        /// Theorem id (`T01`..`T20`).
        id: String,
        /// Canonical spec definition name.
        spec_name: String,
        /// Underlying promotion error.
        error: PromotionError,
    },
}

/// Map a theorem id (e.g. `"T01"`) to its canonical spec definition name
/// (e.g. `"ia_t01_add_containment"`) used in
/// [`Specification::new_interval_arith_test_spec`].
#[must_use]
pub fn spec_name_for(id: &str) -> Option<&'static str> {
    match id {
        "T01" => Some("ia_t01_add_containment"),
        "T02" => Some("ia_t02_sub_containment"),
        "T03" => Some("ia_t03_neg_containment"),
        "T04" => Some("ia_t04_mul_containment"),
        "T05" => Some("ia_t05_div_containment"),
        "T06" => Some("ia_t06_abs_containment"),
        "T07" => Some("ia_t07_pow_containment"),
        "T08" => Some("ia_t08_sqrt_containment"),
        "T09" => Some("ia_t09_intersection_containment"),
        "T10" => Some("ia_t10_hull_containment"),
        "T11" => Some("ia_t11_subset_transitivity"),
        "T12" => Some("ia_t12_containment_transitivity"),
        "T13" => Some("ia_t13_point_interval"),
        "T14" => Some("ia_t14_contains_reflexive"),
        "T15" => Some("ia_t15_add_width"),
        "T16" => Some("ia_t16_sub_width"),
        "T17" => Some("ia_t17_neg_width"),
        "T18" => Some("ia_t18_add_commutativity"),
        "T19" => Some("ia_t19_mul_commutativity"),
        "T20" => Some("ia_t20_add_associativity"),
        _ => None,
    }
}

/// Compute each T0x's `ProofStatus` **dynamically** via the kernel promote
/// pipeline, rather than reading hardcoded `TXX_PROOF_STATUS` constants.
///
/// For every theorem this builds a fresh interval-arith spec, fetches the
/// matching proof term from the `ProofLibrary`, type-checks it through the
/// kernel via `promote_single`, and returns the observed status together with
/// the (hopefully empty) axiom dependency set.
///
/// Returns a tuple-per-theorem vector in T01..T20 order. The status field is
/// what the kernel actually accepted — if any proof fails elaboration or
/// type-checking, that T0x will stay `DerivedPending`.
///
/// # Errors
/// Returns [`DynamicStatusError`] if the interval-arith spec fails to build,
/// a theorem id has no spec-name mapping, or `promote_single` fails.
///
/// Part of #3362 Acceptance Criterion #2: `ProofStatus` computed dynamically
/// from kernel verification, not hardcoded.
///
/// Gated behind `cfg(any(test, feature = "test-utils"))` to match
/// [`Specification::new_interval_arith_test_spec`], which lives under the
/// same cfg. Without this gate the default-feature build of `clean-verify`
/// fails with `E0599` on the helper call below. See #3477.
#[cfg(any(test, feature = "test-utils"))]
pub fn compute_proof_statuses_dynamically(
) -> Result<Vec<(&'static str, &'static str, ProofStatus, Vec<String>)>, DynamicStatusError> {
    let mut spec = Specification::new_interval_arith_test_spec()?;
    let library = ProofLibrary::new();

    let registration = super::theorems::all_proof_statuses();
    let mut out = Vec::with_capacity(registration.len());
    for (id, desc, _pre_status) in registration {
        let spec_name = spec_name_for(id)
            .ok_or_else(|| DynamicStatusError::UnknownTheoremId((*id).to_string()))?;
        let attempt = promote_single(&mut spec, &library, spec_name).map_err(|error| {
            DynamicStatusError::PromoteFailed {
                id: (*id).to_string(),
                spec_name: (*spec_name).to_string(),
                error,
            }
        })?;
        let mut deps: Vec<String> = attempt.axiom_deps.into_iter().collect();
        deps.sort();
        out.push((id, desc, attempt.new_status, deps));
    }
    Ok(out)
}
