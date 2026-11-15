// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_mc_modes_and_option_combinations_match_actual_original() {
    for mode in [McMode::BoundedModelCheck, McMode::Chc, McMode::Pdr] {
        for bits in 0..16 {
            let mut r = mc();
            r.mode = mode;
            r.options.bmc.unwind_limit = if bits & 1 == 0 { 0 } else { u32::MAX };
            r.options.chc.pdr.enabled = bits & 2 != 0;
            r.options.chc.emit_horn_clauses = bits & 4 != 0;
            r.options.chc.pdr.max_frames = if bits & 8 == 0 { Some(0) } else { None };
            observed(&Input::Mc(r));
        }
    }
}
#[test]
fn pdr_preserves_enabled_then_emit_then_frame_error_order() {
    let (rows, _, _) = observed(&bad());
    assert_eq!(rows.len(), 3);
    assert!(matches!(
        rows[0],
        E::InvalidTrustMcChcOptions {
            field: "chc.pdr.enabled",
            ..
        }
    ));
    assert!(matches!(
        rows[1],
        E::InvalidTrustMcChcOptions {
            field: "chc.emit_horn_clauses",
            ..
        }
    ));
    assert!(matches!(
        rows[2],
        E::InvalidTrustMcChcOptions {
            field: "chc.pdr.max_frames",
            ..
        }
    ));
}
#[test]
fn bmc_ignores_invalid_chc_and_chc_ignores_disabled_pdr() {
    let mut r = mc();
    r.options.chc.pdr.enabled = false;
    r.options.chc.emit_horn_clauses = false;
    r.options.chc.pdr.max_frames = Some(0);
    r.options.bmc.unwind_limit = 1;
    r.mode = McMode::BoundedModelCheck;
    assert!(observed(&Input::Mc(r.clone())).0.is_empty());
    r.mode = McMode::Chc;
    let rows = observed(&Input::Mc(r)).0;
    assert_eq!(rows.len(), 2);
}
#[test]
fn nonzero_frame_and_unwind_extremes_are_unchanged() {
    for value in [1, 17, u32::MAX] {
        let mut r = mc();
        r.mode = McMode::Pdr;
        r.options.chc.pdr.enabled = true;
        r.options.chc.emit_horn_clauses = true;
        r.options.chc.pdr.max_frames = Some(value);
        r.options.bmc.unwind_limit = value;
        assert!(observed(&Input::Mc(r)).0.is_empty());
    }
}
#[test]
fn all_wp_modes_and_option_extremes_match_actual_original() {
    for mode in [
        WpMode::WeakestPrecondition,
        WpMode::StrongestPostcondition,
        WpMode::Abduction,
    ] {
        for emit in [false, true] {
            for limit in [0, 1, u32::MAX] {
                let mut r = wp();
                r.mode = mode;
                r.options.emit_verification_conditions = emit;
                r.options.max_abduced_preconditions = limit;
                r.provenance.replay_context.atoms.clear();
                observed(&Input::Wp(r));
            }
        }
    }
}
#[test]
fn strongest_postcondition_needs_both_independent_roles() {
    for assumption in [false, true] {
        for assertion in [false, true] {
            let mut r = wp();
            r.mode = WpMode::StrongestPostcondition;
            r.options.emit_verification_conditions = true;
            r.provenance.replay_context.atoms.clear();
            if assumption {
                r.provenance
                    .replay_context
                    .atoms
                    .push(atom(NativeReplayAtomKind::Assumption, false));
            }
            if assertion {
                r.provenance
                    .replay_context
                    .atoms
                    .push(atom(NativeReplayAtomKind::Assertion, true));
            }
            let rows = observed(&Input::Wp(r)).0;
            assert_eq!(rows.is_empty(), assumption && assertion);
        }
    }
}
#[test]
fn unsited_assertion_and_sited_assumption_do_not_replace_sited_assertion() {
    let mut r = wp();
    r.mode = WpMode::StrongestPostcondition;
    r.options.emit_verification_conditions = true;
    r.provenance.replay_context.atoms = vec![
        atom(NativeReplayAtomKind::Assumption, true),
        atom(NativeReplayAtomKind::Assertion, false),
    ];
    assert!(matches!(
        observed(&Input::Wp(r)).0.as_slice(),
        [E::MissingTrustWpStrongestPostconditionContext(_)]
    ));
}
#[test]
fn physical_last_role_matches_and_duplicate_ids_remain_exact() {
    let mut r = wp();
    r.mode = WpMode::StrongestPostcondition;
    r.options.emit_verification_conditions = true;
    r.provenance.replay_context.atoms = vec![atom(NativeReplayAtomKind::Assertion, false); 31];
    r.provenance
        .replay_context
        .atoms
        .push(atom(NativeReplayAtomKind::Assumption, false));
    r.provenance
        .replay_context
        .atoms
        .push(atom(NativeReplayAtomKind::Assertion, true));
    assert!(observed(&Input::Wp(r)).0.is_empty());
}
#[test]
fn irrelevant_formula_digest_and_span_are_not_validated_by_mode_leaf() {
    let mut r = wp();
    r.mode = WpMode::StrongestPostcondition;
    r.options.emit_verification_conditions = true;
    r.provenance.replay_context.atoms = vec![
        atom(NativeReplayAtomKind::Assumption, false),
        atom(NativeReplayAtomKind::Assertion, true),
    ];
    let (_, a, end) = observed(&Input::Wp(r.clone()));
    r.provenance.replay_context.atoms[0].formula =
        ProofFormula::smtlib2("x".repeat(8192), "not a sort");
    r.provenance.replay_context.atoms[0].payload_digest = ProofDigest::sha256([9; 32]);
    let (_, b, end_b) = observed(&Input::Wp(r));
    assert_eq!(&a.events[..end], &b.events[..end_b]);
}
#[test]
fn wp_context_error_precedes_emit_option_error() {
    let (rows, _, _) = observed(&bad_wp());
    assert!(matches!(
        rows.as_slice(),
        [
            E::MissingTrustWpStrongestPostconditionContext(_),
            E::InvalidTrustWpOptions {
                field: "emit_verification_conditions",
                ..
            }
        ]
    ));
}
#[test]
fn abduction_limit_is_not_applied_to_other_modes() {
    for mode in [WpMode::WeakestPrecondition, WpMode::Abduction] {
        let mut r = wp();
        r.mode = mode;
        r.options.emit_verification_conditions = true;
        r.options.max_abduced_preconditions = 0;
        assert_eq!(
            observed(&Input::Wp(r)).0.is_empty(),
            mode != WpMode::Abduction
        );
    }
}
#[test]
fn all_diagnostics_boolean_combinations_and_counter_limits_match_original() {
    for bits in 0..8 {
        for max in [0, 1, u32::MAX] {
            let mut p = NativeDiagnosticsPolicy::default();
            p.include_source_spans = bits & 1 != 0;
            p.include_lineage = bits & 2 != 0;
            p.emit_counterexamples = bits & 4 != 0;
            p.max_counterexamples = max;
            observed(&Input::Diagnostics(NativeRequestId::new(u32::MAX), p));
        }
    }
}
#[test]
fn diagnostics_use_actual_original_request_id_and_exact_error_order() {
    let (rows, _, _) = observed(&bad_diagnostics());
    assert_eq!(
        rows,
        vec![
            E::InvalidDiagnosticsPolicy {
                request: NativeRequestId::new(u32::MAX),
                field: "include_source_spans"
            },
            E::InvalidDiagnosticsPolicy {
                request: NativeRequestId::new(u32::MAX),
                field: "include_lineage"
            },
            E::InvalidDiagnosticsPolicy {
                request: NativeRequestId::new(u32::MAX),
                field: "max_counterexamples"
            }
        ]
    );
}
#[test]
fn disabled_counterexamples_preserve_zero_limit_exception() {
    let mut p = NativeDiagnosticsPolicy::default();
    p.emit_counterexamples = false;
    p.max_counterexamples = 0;
    assert!(
        observed(&Input::Diagnostics(NativeRequestId::new(0), p))
            .0
            .is_empty()
    );
}
