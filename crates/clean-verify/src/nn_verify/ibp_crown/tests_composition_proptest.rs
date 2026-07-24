// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for certificate verification and edit chain composition.
//!
//! Verifies mathematical invariants from neural_surgery:
//! - Sound certificates always pass verification
//! - Overly conservative (wider) bounds remain sound
//! - Certificates with bounds tighter than Lipschitz-derived are unsound
//! - Edit chain monotonicity: adding edits never narrows bounds
//! - Empty chain preserves original bounds
//! - Edit chain undo correctness within floating-point tolerance

use proptest::prelude::*;

use crate::neural_surgery::RankOneUpdate;
use crate::neural_surgery::{BoundPropagationSpec, LipschitzBound, OutputBound};
use crate::neural_surgery::{CertificateSpec, CertificateVerdict, EditCertificate};
use crate::neural_surgery::{EditChainSpec, EditSequence};

/// Strategy for a valid OutputBound with lower <= upper in [-10, 10].
fn output_bound_strategy() -> impl Strategy<Value = OutputBound> {
    (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(a, b)| {
        let lo = a.min(b);
        let hi = a.max(b);
        OutputBound::new(lo, hi)
    })
}

/// Strategy for a LipschitzBound with constant in [0.01, 10].
fn lipschitz_bound_strategy() -> impl Strategy<Value = LipschitzBound> {
    (0.01f64..10.0).prop_map(LipschitzBound::new)
}

/// Strategy for a small RankOneUpdate (2x2).
fn rank_one_update_strategy() -> impl Strategy<Value = RankOneUpdate> {
    (
        prop::collection::vec(-5.0f64..5.0, 2..=2),
        prop::collection::vec(-5.0f64..5.0, 2..=2),
    )
        .prop_map(|(u, v)| RankOneUpdate::new(u, v))
}

/// Strategy for a small RankOneUpdate with configurable dimension.
fn rank_one_update_dim_strategy(rows: usize, cols: usize) -> impl Strategy<Value = RankOneUpdate> {
    (
        prop::collection::vec(-5.0f64..5.0, rows..=rows),
        prop::collection::vec(-5.0f64..5.0, cols..=cols),
    )
        .prop_map(|(u, v)| RankOneUpdate::new(u, v))
}

/// Build a sound certificate: claimed bounds are exactly the Lipschitz-derived bounds.
fn make_sound_certificate(
    edit: RankOneUpdate,
    pre_bounds: OutputBound,
    lip: LipschitzBound,
) -> EditCertificate {
    let spec = BoundPropagationSpec::new();
    let delta = edit.frobenius_norm();
    let required = spec.propagate_bound(&pre_bounds, &lip, delta);
    EditCertificate {
        edit,
        pre_edit_bounds: pre_bounds,
        lipschitz: lip,
        claimed_post_edit_bounds: required,
    }
}

/// Build an overly conservative certificate: claimed bounds are wider than required.
fn make_conservative_certificate(
    edit: RankOneUpdate,
    pre_bounds: OutputBound,
    lip: LipschitzBound,
    extra_slack: f64,
) -> EditCertificate {
    let spec = BoundPropagationSpec::new();
    let delta = edit.frobenius_norm();
    let required = spec.propagate_bound(&pre_bounds, &lip, delta);
    EditCertificate {
        edit,
        pre_edit_bounds: pre_bounds,
        lipschitz: lip,
        claimed_post_edit_bounds: OutputBound::new(
            required.lower - extra_slack,
            required.upper + extra_slack,
        ),
    }
}

// ---------------------------------------------------------------------------
// Certificate soundness properties
// ---------------------------------------------------------------------------

proptest! {
    /// Exactly matching Lipschitz-derived bounds are always Sound.
    #[test]
    fn test_exact_certificate_is_sound(
        edit in rank_one_update_strategy(),
        pre_bounds in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
    ) {
        let cert = make_sound_certificate(edit, pre_bounds, lip);
        let spec = CertificateSpec::new();
        let verdict = spec.verify_certificate(&cert);
        prop_assert_eq!(
            verdict,
            CertificateVerdict::Sound,
            "exact Lipschitz-derived certificate should be Sound",
        );
    }

    /// Conservative (wider) certificates are also Sound.
    #[test]
    fn test_conservative_certificate_is_sound(
        edit in rank_one_update_strategy(),
        pre_bounds in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
        extra_slack in 0.01f64..10.0,
    ) {
        let cert = make_conservative_certificate(edit, pre_bounds, lip, extra_slack);
        let spec = CertificateSpec::new();
        let verdict = spec.verify_certificate(&cert);
        prop_assert_eq!(
            verdict,
            CertificateVerdict::Sound,
            "conservative certificate should be Sound",
        );
    }

    /// Certificates with bounds narrower than pre-edit are always Unsound
    /// (when the edit has non-zero norm, the required bounds widen).
    #[test]
    fn test_too_tight_certificate_is_unsound(
        pre_bounds in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
        u_val in 0.1f64..5.0,
        v_val in 0.1f64..5.0,
    ) {
        // Non-zero edit so Lipschitz slack is > 0
        let edit = RankOneUpdate::new(vec![u_val, 0.0], vec![0.0, v_val]);
        let cert = EditCertificate {
            edit,
            pre_edit_bounds: pre_bounds,
            lipschitz: lip,
            // Claimed bounds equal pre-edit bounds = too tight
            claimed_post_edit_bounds: pre_bounds,
        };
        let spec = CertificateSpec::new();
        let verdict = spec.verify_certificate(&cert);
        prop_assert_eq!(
            verdict,
            CertificateVerdict::Unsound,
            "too-tight certificate should be Unsound",
        );
    }

    /// Sound certificates pass the conservative check.
    #[test]
    fn test_sound_certificate_is_conservative(
        edit in rank_one_update_strategy(),
        pre_bounds in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
    ) {
        let cert = make_sound_certificate(edit, pre_bounds, lip);
        let spec = CertificateSpec::new();
        spec.verify_sound_is_conservative(&cert)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }

    /// Zero-edit certificate: sound iff claimed bounds contain pre-edit bounds.
    #[test]
    fn test_zero_edit_certificate_containing_is_sound(
        pre_bounds in output_bound_strategy(),
        extra in 0.0f64..5.0,
    ) {
        let spec = CertificateSpec::new();
        let claimed = OutputBound::new(
            pre_bounds.lower - extra,
            pre_bounds.upper + extra,
        );
        let verdict = spec
            .verify_zero_edit_certificate(&pre_bounds, &claimed)
            .expect("zero edit check should succeed");
        prop_assert_eq!(verdict, CertificateVerdict::Sound);
    }
}

// ---------------------------------------------------------------------------
// Bound propagation properties
// ---------------------------------------------------------------------------

proptest! {
    /// Propagated bounds are always at least as wide as original.
    #[test]
    fn test_propagated_bounds_widen(
        original in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
        delta in 0.0f64..10.0,
    ) {
        let spec = BoundPropagationSpec::new();
        let propagated = spec.propagate_bound(&original, &lip, delta);
        prop_assert!(
            propagated.width() >= original.width() - f64::EPSILON,
            "propagated width {} < original width {}",
            propagated.width(),
            original.width(),
        );
    }

    /// Zero perturbation preserves bounds.
    #[test]
    fn test_zero_perturbation_preserves(
        original in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
    ) {
        let spec = BoundPropagationSpec::new();
        spec.verify_zero_preserves_bounds(&original, &lip)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }

    /// Monotonicity: larger delta => wider bounds.
    #[test]
    fn test_bound_degradation_monotonic(
        original in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
        d1 in 0.0f64..5.0,
        d2 in 0.0f64..5.0,
    ) {
        let (delta1, delta2) = if d1 <= d2 { (d1, d2) } else { (d2, d1) };
        let spec = BoundPropagationSpec::new();
        spec.verify_monotonicity(&original, &lip, delta1, delta2)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }
}

// ---------------------------------------------------------------------------
// Edit chain composition properties
// ---------------------------------------------------------------------------

proptest! {
    /// Empty chain preserves original bounds.
    #[test]
    fn test_empty_chain_preserves_bounds(
        original in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
    ) {
        let spec = EditChainSpec::new();
        spec.verify_empty_chain_preserves(&original, &lip)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }

    /// Adding an edit to a chain never narrows the propagated bounds.
    #[test]
    fn test_chain_monotonicity(
        original in output_bound_strategy(),
        lip in lipschitz_bound_strategy(),
        edit1 in rank_one_update_dim_strategy(2, 2),
        edit2 in rank_one_update_dim_strategy(2, 2),
        extra_edit in rank_one_update_dim_strategy(2, 2),
    ) {
        let spec = EditChainSpec::new();
        let mut chain = EditSequence::new();
        chain.push(edit1);
        chain.push(edit2);

        spec.verify_chain_monotonicity(&original, &lip, &chain, &extra_edit)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }

    /// Chain of N edits: total perturbation norm >= each individual norm.
    #[test]
    fn test_chain_total_norm_triangle_inequality(
        edits in prop::collection::vec(rank_one_update_dim_strategy(2, 2), 1..=5),
    ) {
        let mut chain = EditSequence::new();
        for edit in &edits {
            chain.push(edit.clone());
        }
        let total = chain.total_perturbation_norm();
        for (i, edit) in edits.iter().enumerate() {
            prop_assert!(
                total >= edit.frobenius_norm() - f64::EPSILON,
                "total norm {} < individual norm[{i}] {}",
                total,
                edit.frobenius_norm(),
            );
        }
    }

    /// Chain propagated width equals original_width + 2*L*sum(||dW_i||).
    #[test]
    fn test_chain_propagated_width_formula(
        original in output_bound_strategy(),
        lip_c in 0.01f64..10.0,
        edits in prop::collection::vec(rank_one_update_dim_strategy(2, 2), 1..=4),
    ) {
        let lip = LipschitzBound::new(lip_c);
        let spec = EditChainSpec::new();
        let mut chain = EditSequence::new();
        for edit in &edits {
            chain.push(edit.clone());
        }
        let propagated = spec.propagate_chain_bounds(&original, &lip, &chain);
        let expected_width = original.width() + 2.0 * lip_c * chain.total_perturbation_norm();
        let tol = f64::EPSILON * expected_width.max(1.0) * 100.0;
        prop_assert!(
            (propagated.width() - expected_width).abs() < tol,
            "propagated width {} != expected {}",
            propagated.width(),
            expected_width,
        );
    }

    /// Undo correctness: apply then undo a chain of edits recovers W
    /// within floating-point tolerance.
    #[test]
    fn test_chain_undo_correctness(
        w_entries in prop::collection::vec(-10.0f64..10.0, 4..=4),
        edits in prop::collection::vec(rank_one_update_dim_strategy(2, 2), 1..=3),
    ) {
        let w = vec![
            vec![w_entries[0], w_entries[1]],
            vec![w_entries[2], w_entries[3]],
        ];
        let spec = EditChainSpec::new();
        let mut chain = EditSequence::new();
        for edit in &edits {
            chain.push(edit.clone());
        }
        spec.verify_undo_correctness(&w, &chain)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }

    /// Order independence: forward vs reverse application produces
    /// the same result within floating-point tolerance.
    #[test]
    fn test_chain_order_independence(
        w_entries in prop::collection::vec(-10.0f64..10.0, 4..=4),
        edits in prop::collection::vec(rank_one_update_dim_strategy(2, 2), 2..=4),
    ) {
        let w = vec![
            vec![w_entries[0], w_entries[1]],
            vec![w_entries[2], w_entries[3]],
        ];
        let spec = EditChainSpec::new();
        let mut chain = EditSequence::new();
        for edit in &edits {
            chain.push(edit.clone());
        }
        spec.verify_order_independence(&w, &chain)
            .map_err(|e| TestCaseError::Fail(format!("{e}").into()))?;
    }
}
