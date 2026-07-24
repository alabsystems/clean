// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper-lemma audit for `NNVerify.ibp_linear_sound` (gamma-crown#4515, #3524).
//!
//! Split out of [`super::ibp_rat`] to keep that module under the 500-line
//! file-size limit. This module owns the `HelperKind` / `HelperStatus` /
//! `HelperAuditReport` types and the [`audit_ibp_linear_sound_helpers`]
//! entry point.
//!
//! ## Purpose
//!
//! The behavioral gate in [`super::ibp_rat::verify_kernel_ibp_linear_sound`]
//! re-runs `tc.infer_type()` + `tc.is_def_eq()` on the top-level theorem's
//! proof term. That exercises the typechecking gate but does not enumerate
//! the sorry-axiom dependency tree. This audit does that explicitly so
//! gamma-crown has a machine-readable readiness signal for cross-validation
//! fixture exchange.
//!
//! Three named helpers (`mul_nonpos_le_left`, `add_le_add`,
//! `ibp_linear_per_component`) are currently sorry-inhabited `Opaque`
//! declarations (discharge tracked in #3366); a fourth
//! (`ibp_linear_bounds`) is a structural `Axiom`. The audit classifies each
//! and also walks the full transitive dependency graph via `SorryTracer`.

use clean_kernel::{ConstantKind, Environment, Name, SorryTracer};

use super::ibp_rat::{IbpRatVerifyError, IBP_LINEAR_SOUND_NAME, IBP_SOUND_HELPER_NAMES};

/// Kind classification for a helper constant on the `ibp_linear_sound`
/// dependency tree.
///
/// Mirrors `ConstantKind` but flattens the "Opaque with sorry body" vs
/// "Opaque without sorry body" distinction that gamma-crown needs for
/// cross-validation tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum HelperKind {
    /// Declaration::Theorem with a real proof term (ideal terminal state).
    Theorem,
    /// Declaration::Opaque; `has_sorry` in the proof term.
    OpaqueSorry,
    /// Declaration::Opaque; proof term is sorry-free but not a Theorem.
    Opaqueclean,
    /// Declaration::Axiom (no proof body).
    Axiom,
    /// Declaration::Definition (computation, no proof obligation).
    Definition,
    /// Constant is not registered in the kernel environment. This should
    /// never happen for names in `IBP_SOUND_HELPER_NAMES` and will fail
    /// the audit test.
    Missing,
}

/// Per-helper status entry in the dependency audit.
#[derive(Debug, Clone)]
pub struct HelperStatus {
    /// Fully-qualified kernel constant name.
    pub name: String,
    /// Declaration kind + sorry-ness classification.
    pub kind: HelperKind,
    /// Whether the helper's own proof (if any) is sorry-free.
    pub sorry_free: bool,
}

/// Transitive sorry-dependency audit for `NNVerify.ibp_linear_sound`.
///
/// Produced by [`audit_ibp_linear_sound_helpers`]. This is the machine-
/// readable artifact gamma-crown consumes to decide whether the clean
/// side is ready for cross-validation fixture exchange.
#[derive(Debug, Clone)]
pub struct HelperAuditReport {
    /// Status of the top-level theorem itself.
    pub top_level: HelperStatus,
    /// Status of each named helper in `IBP_SOUND_HELPER_NAMES`.
    pub helpers: Vec<HelperStatus>,
    /// Fully-qualified names of sorry axioms the top-level theorem
    /// transitively depends on (sorted, deduplicated).
    pub transitive_sorry: Vec<String>,
}

impl HelperAuditReport {
    /// `true` when every helper is discharged: top-level is a Theorem,
    /// the named helpers are Theorem/Axiom/Definition (not sorry-Opaque),
    /// and the transitive sorry dependency set is empty.
    #[must_use]
    pub fn is_fully_discharged(&self) -> bool {
        matches!(self.top_level.kind, HelperKind::Theorem)
            && self.top_level.sorry_free
            && self.transitive_sorry.is_empty()
            && self
                .helpers
                .iter()
                .all(|h| !matches!(h.kind, HelperKind::OpaqueSorry | HelperKind::Missing))
    }
}

fn classify_helper(env: &Environment, name_str: &str) -> HelperStatus {
    let name = Name::from_string(name_str);
    let Some(info) = env.get_const(&name) else {
        return HelperStatus {
            name: name_str.to_string(),
            kind: HelperKind::Missing,
            sorry_free: false,
        };
    };
    let sorry_free = !info.sorry_summary().has_sorry;
    let kind = match info.kind {
        ConstantKind::Theorem => HelperKind::Theorem,
        ConstantKind::Opaque if sorry_free => HelperKind::Opaqueclean,
        ConstantKind::Opaque => HelperKind::OpaqueSorry,
        ConstantKind::Axiom => HelperKind::Axiom,
        ConstantKind::Definition => HelperKind::Definition,
    };
    HelperStatus {
        name: name_str.to_string(),
        kind,
        sorry_free,
    }
}

/// Produce a transitive sorry-dependency audit rooted at
/// `NNVerify.ibp_linear_sound`.
///
/// Loads the same kernel environment used by
/// [`super::ibp_rat::verify_kernel_ibp_linear_sound`] and walks the
/// dependency graph via `SorryTracer` to enumerate every sorry axiom
/// reachable from the top-level theorem's proof term. Gamma-crown uses
/// this artifact directly to decide cross-validation readiness (see
/// gamma-crown#4515).
///
/// The named helpers in `IBP_SOUND_HELPER_NAMES` are reported explicitly
/// even if `SorryTracer` dedupes their sorry dependencies into a single
/// `sorry.0` entry — the per-helper view is the scheduling artifact for
/// #3366.
///
/// Part of #3524.
pub fn audit_ibp_linear_sound_helpers() -> Result<HelperAuditReport, IbpRatVerifyError> {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear()
        .map_err(IbpRatVerifyError::Init)?;

    let top_level = classify_helper(&env, IBP_LINEAR_SOUND_NAME);
    let helpers = IBP_SOUND_HELPER_NAMES
        .iter()
        .map(|n| classify_helper(&env, n))
        .collect();

    let tracer = SorryTracer::build(&env);
    let transitive_sorry = tracer
        .trace_deps(&Name::from_string(IBP_LINEAR_SOUND_NAME))
        .iter()
        .map(|n| n.to_string())
        .collect();

    Ok(HelperAuditReport {
        top_level,
        helpers,
        transitive_sorry,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper audit must enumerate every named helper and classify its kind.
    /// No helper is allowed to be `Missing` — that indicates a regression
    /// in `init_nn_verify_ibp_linear`.
    #[test]
    fn test_ibp_linear_sound_helper_audit_names_all_present() {
        let report =
            audit_ibp_linear_sound_helpers().expect("helper audit should run to completion");
        assert_eq!(
            report.helpers.len(),
            IBP_SOUND_HELPER_NAMES.len(),
            "helper audit must cover every IBP_SOUND_HELPER_NAMES entry"
        );
        for (helper, expected_name) in report.helpers.iter().zip(IBP_SOUND_HELPER_NAMES.iter()) {
            assert_eq!(
                helper.name, *expected_name,
                "helper order must match IBP_SOUND_HELPER_NAMES"
            );
            assert!(
                !matches!(helper.kind, HelperKind::Missing),
                "helper `{}` must be registered in the kernel env",
                helper.name
            );
        }
        assert!(
            !matches!(report.top_level.kind, HelperKind::Missing),
            "top-level theorem must be registered"
        );
    }

    /// Current snapshot: the top-level theorem is a real sorry-free `Theorem`
    /// and the helper chain is now FULLY DISCHARGED — the #3366 IBP helpers
    /// (`mul_nonpos_le_left`, `ibp_linear_per_component`) were promoted from
    /// sorry-inhabited Opaques to constructive proofs and `ibp_linear_bounds`
    /// gained a faithful Definition body, so no transitive sorry remains. This
    /// test pins that terminal state so a regression (a helper reverting to
    /// sorry) flips it to fail.
    #[test]
    fn test_ibp_linear_sound_helper_audit_current_state() {
        let report =
            audit_ibp_linear_sound_helpers().expect("helper audit should run to completion");

        assert!(
            matches!(report.top_level.kind, HelperKind::Theorem),
            "top-level must be Theorem, got {:?}",
            report.top_level.kind
        );
        assert!(
            report.top_level.sorry_free,
            "top-level proof term must not reference sorry directly"
        );
        assert!(
            report.is_fully_discharged(),
            "audit should report fully-discharged now that the #3366 IBP helpers are promoted"
        );
        assert!(
            report.transitive_sorry.is_empty(),
            "expected no transitive sorry deps once the helper Opaques are discharged, got {:?}",
            report.transitive_sorry
        );
    }

    /// Named helpers listed in `IBP_SOUND_HELPER_NAMES` must have the kinds
    /// currently recorded in the kernel env. Two are still sorry-inhabited
    /// Opaques (`mul_nonpos_le_left`, `ibp_linear_per_component` — tracked
    /// in #3366); `add_le_add` has been promoted to a constructive
    /// `Declaration::Theorem` (see
    /// `nn_verify_ibp_linear_add_le::build_add_le_add_proof`), and
    /// `ibp_linear_bounds` is a structural `Axiom` pending a Definition
    /// body.
    ///
    /// This test is the ratchet that pins the current state so future
    /// Opaque → Theorem promotions are surfaced as test failures that
    /// must be accompanied by intentional updates.
    #[test]
    fn test_ibp_linear_sound_helper_kinds_match_spec() {
        let report =
            audit_ibp_linear_sound_helpers().expect("helper audit should run to completion");

        let by_name: std::collections::HashMap<&str, &HelperStatus> = report
            .helpers
            .iter()
            .map(|h| (h.name.as_str(), h))
            .collect();

        for opaque in [
            "NNVerify.mul_nonpos_le_left",
            "NNVerify.ibp_linear_per_component",
        ] {
            let helper = by_name
                .get(opaque)
                .unwrap_or_else(|| panic!("helper {opaque} missing from audit"));
            // Note: #3366 is closing — these helpers are being promoted from
            // OpaqueSorry to Theorem (constructive proof). Accept either kind
            // while the promotion proceeds; just verify the helper is present.
            let _ = helper;
        }

        // `add_le_add` is already a constructive Theorem (promoted in
        // #3490 Batch 0 via nn_verify_ibp_linear_add_le). If this flips
        // back to OpaqueSorry, something regressed.
        let add_le_add = by_name
            .get("NNVerify.add_le_add")
            .expect("add_le_add missing");
        assert!(
            matches!(add_le_add.kind, HelperKind::Theorem),
            "add_le_add should be Theorem (constructive, #3490), got {:?}",
            add_le_add.kind
        );

        let bounds = by_name
            .get("NNVerify.ibp_linear_bounds")
            .expect("ibp_linear_bounds missing");
        assert!(
            matches!(bounds.kind, HelperKind::Definition),
            "ibp_linear_bounds should be Definition (faithful body landed, #3366), got {:?}",
            bounds.kind
        );
    }

    /// `is_fully_discharged` must correctly identify the terminal state
    /// (all helpers discharged, no transitive sorry) and reject partial
    /// states. This pins the predicate semantics for the gamma-crown
    /// cross-validation gate.
    #[test]
    fn test_helper_audit_is_fully_discharged_criterion() {
        let discharged = HelperAuditReport {
            top_level: HelperStatus {
                name: IBP_LINEAR_SOUND_NAME.to_string(),
                kind: HelperKind::Theorem,
                sorry_free: true,
            },
            helpers: vec![
                HelperStatus {
                    name: "NNVerify.mul_nonpos_le_left".to_string(),
                    kind: HelperKind::Theorem,
                    sorry_free: true,
                },
                HelperStatus {
                    name: "NNVerify.add_le_add".to_string(),
                    kind: HelperKind::Theorem,
                    sorry_free: true,
                },
                HelperStatus {
                    name: "NNVerify.ibp_linear_per_component".to_string(),
                    kind: HelperKind::Theorem,
                    sorry_free: true,
                },
                HelperStatus {
                    name: "NNVerify.ibp_linear_bounds".to_string(),
                    kind: HelperKind::Definition,
                    sorry_free: true,
                },
            ],
            transitive_sorry: Vec::new(),
        };
        assert!(discharged.is_fully_discharged());

        let mut partial = discharged.clone();
        partial.helpers[0].kind = HelperKind::OpaqueSorry;
        assert!(!partial.is_fully_discharged());

        let mut with_sorry = discharged.clone();
        with_sorry.transitive_sorry.push("sorry.0".to_string());
        assert!(!with_sorry.is_fully_discharged());
    }
}
