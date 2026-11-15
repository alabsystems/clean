// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn array_and_aggregate_spellings_share_original_exact_child_classes() {
    let root = array(vec![
        array(vec![Constant::Int(1), Constant::Int(2)]),
        Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
    ]);
    assert_eq!(run(&root).0, 1);
}
#[test]
fn raw_bytes_alias_integer_lists_but_utf8_identity_is_not_erased() {
    let root = array(vec![
        bytes(&[1, 2]),
        array(vec![Constant::Int(1), Constant::Int(2)]),
    ]);
    assert_eq!(run(&root).0, 1);
    let root = array(vec![
        Constant::Bytes {
            data: vec![1, 2],
            utf8: true,
        },
        array(vec![Constant::Int(1), Constant::Int(2)]),
    ]);
    assert_eq!(run(&root).0, 0);
}
#[test]
fn empty_raw_bytes_array_and_aggregate_are_originally_one_list_class() {
    let root = array(vec![bytes(&[]), array(vec![]), Constant::Aggregate(vec![])]);
    assert_eq!(run(&root).0, 1);
}
#[test]
fn floats_use_exact_bits_including_equal_nan_payload_and_opposite_zero() {
    let nan = f64::from_bits(0x7ff8000000000042);
    assert_eq!(
        run(&array(vec![Constant::Float(nan), Constant::Float(nan)])).0,
        1
    );
    assert_eq!(
        run(&array(vec![Constant::Float(-0.0), Constant::Float(0.0)])).0,
        0
    );
    assert_eq!(
        run(&array(vec![
            Constant::Float(nan),
            Constant::Float(f64::from_bits(nan.to_bits() + 1))
        ]))
        .0,
        0
    );
}
#[test]
fn malformed_numeric_carrier_data_is_not_normalized_into_another_class() {
    assert_eq!(run(&array(vec![Constant::Int(0), Constant::U128(0)])).0, 0);
    assert_eq!(
        run(&array(vec![
            Constant::U128(u128::MAX),
            Constant::U128(u128::MAX)
        ]))
        .0,
        1
    );
}
#[test]
fn ordered_record_labels_and_normalized_child_classes_both_determine_equality() {
    assert_eq!(run(&sample()).0, 2);
    let a = Constant::Record(vec![
        ("a".into(), Constant::Int(1)),
        ("b".into(), Constant::Int(2)),
    ]);
    let b = Constant::Record(vec![
        ("b".into(), Constant::Int(1)),
        ("a".into(), Constant::Int(2)),
    ]);
    assert_eq!(run(&array(vec![a, b])).0, 0);
}
#[test]
fn closure_target_and_each_ordered_capture_class_are_part_of_the_key() {
    let a = Constant::Closure {
        func: FuncId::new(1),
        captures: vec![Constant::Int(1)],
    };
    let mut b = a.clone();
    if let Constant::Closure { func, .. } = &mut b {
        *func = FuncId::new(2);
    }
    assert_eq!(run(&array(vec![a.clone(), b])).0, 0);
    assert_eq!(run(&array(vec![a.clone(), a])).0, 1);
}
#[test]
fn splat_length_is_exact_data_and_never_identified_with_an_expanded_list() {
    let a = Constant::Splat {
        elem: Box::new(Constant::Int(1)),
        len: 2,
    };
    let b = Constant::Splat {
        elem: Box::new(Constant::Int(1)),
        len: u64::MAX,
    };
    assert_eq!(run(&array(vec![a.clone(), b])).0, 0);
    let root = array(vec![a, array(vec![Constant::Int(1), Constant::Int(1)])]);
    assert_eq!(run(&root).0, 1);
}
#[test]
fn sequence_set_vector_and_array_container_tags_remain_distinct() {
    for child in [
        Constant::Sequence(vec![Constant::Int(1)]),
        Constant::Set(vec![Constant::Int(1)]),
        Constant::Vector(vec![Constant::Int(1)]),
    ] {
        assert_eq!(run(&array(vec![child.clone(), child])).0, 1);
    }
    assert_eq!(
        run(&array(vec![
            Constant::Sequence(vec![]),
            Constant::Set(vec![]),
            Constant::Vector(vec![])
        ]))
        .0,
        0
    );
}
#[test]
fn phantom_uninit_bool_and_symbols_preserve_exact_original_leaf_distinctions() {
    for leaf in [
        Constant::PhantomData,
        Constant::Uninit,
        Constant::Bool(false),
        Constant::symbol_addr_with_addend("é🦀", i64::MIN),
    ] {
        assert_eq!(run(&array(vec![leaf.clone(), leaf])).0, 1);
    }
    assert_eq!(
        run(&array(vec![Constant::PhantomData, Constant::Uninit])).0,
        0
    );
}
#[test]
fn childless_root_early_return_does_not_expand_or_scan_leaf_payload() {
    for root in [
        bytes(&[1, 1]),
        Constant::symbol_addr("é".repeat(1000)),
        Constant::Int(1),
        Constant::PhantomData,
        Constant::Uninit,
    ] {
        assert_eq!(run(&root).0, 0);
    }
}
#[test]
fn actual_deep_and_wide_stored_trees_have_no_new_count_or_depth_cutoff() {
    let mut root = array(vec![Constant::Int(1); 17]);
    for _ in 0..16 {
        root = Constant::Sequence(vec![root]);
    }
    assert_eq!(run(&root).0, 1);
}
#[test]
fn whole_uniform_inventory_includes_each_nested_list_node_not_only_the_root() {
    let root = array(vec![
        array(vec![Constant::Int(1), Constant::Int(1)]),
        array(vec![Constant::Int(1), Constant::Int(1)]),
    ]);
    assert_eq!(run(&root).0, 3);
}
#[test]
fn membership_uses_only_actual_borrowed_source_node_addresses() {
    let root = array(vec![Constant::Int(1), Constant::Int(1)]);
    let external = root.clone();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    assert!(table.contains_observed(&root, &mut s, site()).unwrap());
    assert!(!table.contains_observed(&external, &mut s, site()).unwrap());
    table.retire_observed(&mut s, site()).unwrap();
}
