// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn plain_and_full_actual_encodable_raw_writer_have_no_refusals_or_hash_work() {
    for m in [Module::new(""), module()] {
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn all_actual_reachable_classes_preserve_original_rank_and_full_diagnostics() {
    let m = all();
    assert_eq!(
        run(&m).0,
        vec![
            BinaryProjectionError::InlinedScopeChainUnencodable {
                function: 17,
                scope: 1
            },
            BinaryProjectionError::CompletenessClaimUnencodable,
            BinaryProjectionError::SignatureAbiUnencodable {
                signature: 0,
                detail: "ABI identity exceeds wire byte limit".into()
            },
            BinaryProjectionError::ProducerInternalType
        ]
    );
}
#[test]
fn only_first_physical_scope_occurrence_is_retained_not_smallest_function_id() {
    let mut m = all();
    let mut next = m.functions[0].clone();
    next.id = FuncId::new(1);
    m.functions.push(next);
    let out = run(&m).0;
    assert!(matches!(
        out[0],
        BinaryProjectionError::InlinedScopeChainUnencodable {
            function: 17,
            scope: 1
        }
    ));
    m.functions.swap(0, 1);
    assert!(matches!(
        run(&m).0[0],
        BinaryProjectionError::InlinedScopeChainUnencodable {
            function: 1,
            scope: 1
        }
    ));
}
#[test]
fn first_invalid_signature_row_detail_is_kept_even_if_later_reason_differs() {
    let mut m = all();
    let mut second = m.func_types[0].clone();
    second.abi.as_mut().unwrap().frontend.name.clear();
    second.abi.as_mut().unwrap().target.features = vec![String::new(); 65_536];
    m.func_types.push(second);
    assert!(
        matches!(&run(&m).0[2],BinaryProjectionError::SignatureAbiUnencodable{signature:0,detail}if detail=="ABI identity exceeds wire byte limit")
    );
    m.func_types.swap(0, 1);
    assert!(
        matches!(&run(&m).0[2],BinaryProjectionError::SignatureAbiUnencodable{signature:0,detail}if detail=="ABI record count exceeds wire node limit")
    );
}
#[test]
fn nested_internal_types_across_distinct_real_writer_carriers_keep_one_class() {
    let mut m = module();
    m.types
        .push(Ty::Ref(Box::new(Ty::Tuple(vec![Ty::Error, Ty::Error]))));
    m.func_types[0].returns.push(Ty::Error);
    m.globals[0].ty = Ty::Error;
    assert_eq!(run(&m).0, vec![BinaryProjectionError::ProducerInternalType]);
}
#[test]
fn canonical_escaped_abi_byte_limit_is_reported_and_later_type_class_still_visited() {
    let mut m = module();
    let mut a = abi();
    a.frontend.name = "\0".repeat((1 << 20) / 2);
    m.func_types[0].abi = Some(a);
    m.types.push(Ty::Error);
    assert_eq!(
        run(&m).0,
        vec![
            BinaryProjectionError::SignatureAbiUnencodable {
                signature: 0,
                detail: "ABI text exceeds byte limit".into()
            },
            BinaryProjectionError::ProducerInternalType
        ]
    );
}
#[test]
fn valid_typed_abi_uses_real_encoding_checks_without_creating_a_refusal() {
    let mut m = module();
    m.func_types[0].abi = Some(abi());
    assert!(run(&m).0.is_empty());
}
#[test]
#[cfg(target_pointer_width = "64")]
fn actual_direct_sink_all_six_classes_match_unchanged_checksink_and_first_wins() {
    let mut o = Observer::default();
    let rows = direct(&mut o).unwrap();
    assert_eq!(rows, ordinary_feed());
    assert_eq!(rows.len(), 6);
    assert!(matches!(
        &rows[0],
        BinaryProjectionError::ConstructAheadOfWireTag {
            construct: "FIRST",
            site: Some(WireNodeSite { index: 99, .. })
        }
    ));
    assert!(matches!(
        &rows[5],
        BinaryProjectionError::CountExceedsFormat {
            what: "FIRST count",
            ..
        }
    ));
}
#[test]
#[cfg(target_pointer_width = "64")]
fn actual_count_boundary_keeps_exact_v64_length_and_no_oversized_allocation() {
    for n in [u32::MAX as usize, u32::MAX as usize + 1] {
        let mut old = CheckSink::default();
        write_count(&mut old, "count", n);
        let expected_len = old.len;
        let expected: Vec<_> = old.first.into_iter().flatten().collect();
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut h = Refusals::default();
        let rows = {
            let mut out = Output::checker(&mut s, site(), &mut h).unwrap();
            observed_write_count(&mut out, "count", n).unwrap();
            assert_eq!(out.count().unwrap(), expected_len);
            out.take_refusals().unwrap()
        };
        assert_eq!(rows, expected);
        retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
    }
}
#[test]
fn raw_debug_paths_and_long_unicode_names_are_observed_without_identity_projection() {
    let mut m = module();
    m.files = vec!["raw λ\0尾".repeat(900)];
    let (_, large, _) = run(&m);
    m.files = vec![String::new()];
    let (_, empty, _) = run(&m);
    assert!(large.bytes > empty.bytes);
    assert!(large.work > empty.work);
}
#[test]
fn collection_never_converts_an_unencodable_module_into_a_checked_digest() {
    let m = all();
    assert!(!run(&m).0.is_empty());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        m.checked_stable_digest_observed(&mut s, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert_eq!(
        m.stable_digest_observed(&mut s, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
}
#[test]
fn returned_owned_signature_diagnostic_outlives_the_complete_source_module() {
    let m = all();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
    drop(m);
    assert!(
        matches!(&rows[2],BinaryProjectionError::SignatureAbiUnencodable{detail,..}if detail=="ABI identity exceeds wire byte limit")
    );
    retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
}

#[test]
fn malformed_storage_geometry_has_its_own_class_after_all_legacy_refusals() {
    let mut m = all();
    let previous = run(&m).0;
    let invalid = crate::StorageLayout::new(79, 8);
    m.types.push(Ty::Storage(invalid));
    m.types.push(Ty::Storage(crate::StorageLayout::new(80, 0)));
    let mut expected = previous;
    expected.push(BinaryProjectionError::InvalidStorageGeometry(invalid));
    assert_eq!(run(&m).0, expected);
    let mut valid = Module::new("valid-storage-geometry");
    valid
        .types
        .push(Ty::Storage(crate::StorageLayout::new(80, 8)));
    assert!(run(&valid).0.is_empty());
}
