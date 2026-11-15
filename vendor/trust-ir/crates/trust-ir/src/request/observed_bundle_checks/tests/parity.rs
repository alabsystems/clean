// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_three_permission_shapes_keep_full_physical_order_and_duplicate_ids() {
    let b = fixture();
    let (rows, _, _) = observed(&b, Rule::Reference);
    assert_eq!(rows.len(), 18);
    assert!(
        matches!(&rows[0],E::RustReferenceAsPermissionBorrow{location} if location.ends_with("bb4294967295 #0"))
    );
    assert!(
        matches!(&rows[1],E::RustReferenceAsPermissionBorrow{location} if location.ends_with("bb4294967295 #2"))
    );
}
#[test]
fn raw_quotes_nul_unicode_and_long_function_labels_are_not_normalized() {
    let b = fixture();
    let (rows, _, _) = observed(&b, Rule::Reference);
    assert!(
        matches!(&rows[0],E::RustReferenceAsPermissionBorrow{location} if location==&format!("function '{}' bb{} #0",b.module.functions[0].name,u32::MAX))
    );
}
#[test]
fn every_other_producer_and_unstamped_function_skips_without_input_fallback() {
    for p in [
        None,
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("long".repeat(5000))),
    ] {
        let mut b = fixture();
        for f in &mut b.module.functions {
            f.producer = p.clone();
        }
        assert!(observed(&b, Rule::Reference).0.is_empty());
    }
}
#[test]
fn rust_stamp_applies_even_without_rustmir_input() {
    let mut b = fixture();
    b.input = NativeAdapterInput::TrustIrModule;
    assert_eq!(observed(&b, Rule::Reference).0.len(), 18);
}
#[test]
fn empty_module_and_nonpermission_nodes_are_exact_empty_successes() {
    let mut b = fixture();
    b.module.functions.clear();
    assert!(observed(&b, Rule::Reference).0.is_empty());
    b = fixture();
    for f in &mut b.module.functions {
        for block in &mut f.blocks {
            block.body.retain(|n| !n.inst.uses_borrow_permissions());
        }
    }
    assert!(observed(&b, Rule::Reference).0.is_empty());
}
#[test]
fn missing_source_then_missing_target_remain_two_distinct_ordered_errors() {
    let b = fixture();
    let (rows, _, _) = observed(&b, Rule::Lineage);
    assert_eq!(
        rows,
        vec![
            E::SourceDigestNotInLineage(digest(1)),
            E::TrustIrDigestNotInLineage(digest(2))
        ]
    );
}
#[test]
fn source_and_target_may_match_different_duplicate_physical_nodes() {
    let mut b = fixture();
    b.lineage.nodes[2].source_module = digest(1);
    b.lineage.nodes[0].target_module = digest(2);
    assert!(observed(&b, Rule::Lineage).0.is_empty());
}
#[test]
fn no_source_input_does_not_read_provenance_source_digest() {
    let mut b = fixture();
    b.input = NativeAdapterInput::TrustIrModule;
    b.provenance.source_digest = Some(digest(1));
    assert_eq!(
        observed(&b, Rule::Lineage).0,
        vec![E::TrustIrDigestNotInLineage(digest(2))]
    );
}
#[test]
fn any_membership_short_circuits_before_later_irrelevant_rows() {
    let mut early = fixture();
    early.lineage.nodes[0].source_module = digest(1);
    early.lineage.nodes[0].target_module = digest(2);
    let mut late = fixture();
    late.lineage.nodes[2].source_module = digest(1);
    late.lineage.nodes[2].target_module = digest(2);
    let (_, a, na) = observed(&early, Rule::Lineage);
    let (_, b, nb) = observed(&late, Rule::Lineage);
    assert!(a.events[..na].len() < b.events[..nb].len());
}
#[test]
fn owned_locations_survive_complete_original_bundle_disposal() {
    let b = fixture();
    let expected = ordinary(&b, Rule::Reference);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .reference_spelling_errors_observed(&mut s, site())
        .unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
