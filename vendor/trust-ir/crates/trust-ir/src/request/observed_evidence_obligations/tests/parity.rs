// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn unsorted_duplicate_ids_produce_two_unique_ascending_difference_groups() {
    let (r, e) = fixture();
    let (rows, _, _) = observed(&r, &e);
    let request = r.id();
    assert_eq!(
        rows,
        [1, 2, 5, 9, 3, 8]
            .into_iter()
            .map(|id| E::EvidenceObligationMismatch {
                request,
                obligation: ProofId::new(id)
            })
            .collect::<Vec<_>>()
    );
}
#[test]
fn reordered_repeated_equal_memberships_are_exact_empty_success() {
    assert!(
        observed(&request(&[8, 2, 2, 0, 8]), &evidence(&[0, 8, 2, 8, 8, 2]))
            .0
            .is_empty()
    );
}
#[test]
fn each_one_sided_difference_is_unique_sorted_and_complete() {
    for (r, e) in [
        (request(&[9, 2, 9, 1]), evidence(&[])),
        (request(&[]), evidence(&[9, 2, 9, 1])),
    ] {
        let (rows, _, _) = observed(&r, &e);
        assert_eq!(rows.len(), 3);
    }
}
#[test]
fn all_three_actual_request_getters_preserve_the_same_semantics() {
    let mut requests = crate::request::tests::native_bundle().requests;
    assert_eq!(requests.len(), 3);
    for r in &mut requests {
        set_requested(r, &[9, 7, 7, 0]);
        observed(r, &evidence(&[8, 7, 7, 0]));
    }
}
#[test]
fn empty_both_sides_is_success_without_an_authority_token() {
    assert!(observed(&request(&[]), &evidence(&[])).0.is_empty());
}
#[test]
fn error_request_id_remains_actual_request_even_when_evidence_id_differs() {
    let r = request(&[1]);
    let e = evidence(&[2]);
    assert_ne!(r.id(), e.request());
    let (rows, _, _) = observed(&r, &e);
    assert!(
        rows.iter()
            .all(|row| matches!(row,E::EvidenceObligationMismatch{request,..} if *request==r.id()))
    );
}
#[test]
fn whole_returned_diagnostics_outlive_both_original_inputs() {
    let (r, e) = fixture();
    let expected = ordinary(&r, &e);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.obligation_errors_observed(&r, &mut s, site()).unwrap();
    drop(r);
    drop(e);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn full_width_boundary_ids_keep_unsigned_order_in_each_group() {
    let r = request(&[u32::MAX, 0, 1]);
    let e = evidence(&[u32::MAX - 1, 1]);
    let (rows, _, _) = observed(&r, &e);
    assert_eq!(
        rows,
        vec![
            E::EvidenceObligationMismatch {
                request: r.id(),
                obligation: ProofId::new(0)
            },
            E::EvidenceObligationMismatch {
                request: r.id(),
                obligation: ProofId::new(u32::MAX)
            },
            E::EvidenceObligationMismatch {
                request: r.id(),
                obligation: ProofId::new(u32::MAX - 1)
            }
        ]
    );
}
