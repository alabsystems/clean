// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn complete_spare_string_capacity_is_accounted_after_first_stop() {
    let capacity = label().capacity();
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let e = E::RustReferenceAsPermissionBorrow { location: label() };
    assert_eq!(
        e.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|p| p.copy_bytes == capacity)
            .count(),
        1
    );
}
#[test]
fn full_outer_batch_capacity_is_released_after_nested_rows() {
    let mut rows = Vec::with_capacity(139);
    rows.extend(all());
    let capacity = rows.capacity();
    let baseline = capture(rows);
    let last = baseline
        .events
        .iter()
        .rposition(|p| p.copy_bytes == capacity * size_of::<E>())
        .unwrap();
    let nested = baseline
        .events
        .iter()
        .rposition(|p| p.copy_bytes == 8193)
        .unwrap();
    assert!(last > nested);
}
#[test]
fn each_nested_lineage_prover_remains_charged_after_cancellation() {
    let baseline = capture(vec![E::Lineage(lineage())]);
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    assert_eq!(
        run(vec![E::Lineage(lineage())], &mut observer),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        4
    );
    assert_eq!(
        &observer.events[..],
        &baseline.events[..baseline.events.len() - 1]
    );
}
#[test]
fn both_formula_labels_are_retired_even_when_first_label_refuses() {
    let baseline = capture(sites());
    let cut = baseline
        .events
        .iter()
        .position(|p| p.copy_bytes == 8193)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(cut),
        ..Observer::default()
    };
    assert_eq!(
        run(sites(), &mut observer),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        4
    );
}
#[test]
fn producer_other_and_import_name_are_distinct_owned_fields() {
    let e = E::BundleImportLanguageUncovered {
        import: crate::value::ImportId::new(2),
        name: label(),
        producer: Some(Producer::Other(label())),
        source_languages: BTreeSet::new(),
    };
    let observed = capture(vec![e]);
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        2
    );
}
#[test]
fn copy_function_rows_drain_including_their_spare_allocation() {
    let mut ids = Vec::with_capacity(257);
    ids.extend((0..110).map(FuncId::new));
    let cap = ids.capacity();
    let e = E::BundleLanguageUncovered {
        producer: None,
        functions: ids,
        source_languages: BTreeSet::new(),
    };
    let observed = capture(vec![e]);
    assert!(
        observed
            .events
            .iter()
            .any(|p| p.copy_bytes == cap * size_of::<FuncId>())
    );
}
#[test]
fn allocated_empty_language_root_is_not_treated_as_absent_storage() {
    let mut set = languages();
    while set.pop_first().is_some() {}
    let observed = capture(vec![E::BundlePrimaryLanguageUncovered {
        primary: NativeSourceLanguage::Rust,
        source_languages: set,
    }]);
    assert!(
        observed
            .events
            .iter()
            .any(|p| p.work == 6 * (11 + 12 + 8) + 4)
    );
}
#[test]
fn every_fixed_producer_variant_and_none_has_a_closed_disposal_path() {
    let mut rows = Vec::new();
    for producer in [
        None,
        Some(Producer::TRust),
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
    ] {
        rows.push(E::BundleLanguageUncovered {
            producer,
            functions: vec![],
            source_languages: BTreeSet::new(),
        });
    }
    let observed = capture(rows);
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|p| p.copy_bytes == 8193)
            .count(),
        0
    );
}
