// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn all_fat_kinds_and_thin_refined_missing_inputs_match_the_actual_original_rule() {
    let mut cases = vec![
        None,
        Some(Ty::Ptr),
        Some(Ty::U32),
        Some(Ty::Ref(Box::new(Ty::I32))),
        Some(Ty::Refine(TyId::new(0), PredId::new(1))),
        Some(Ty::Tuple(vec![Ty::U32; 100])),
    ];
    cases.extend(
        [
            FatPtrKind::Str,
            FatPtrKind::Slice(TyId::new(u32::MAX)),
            FatPtrKind::TraitObject { trait_id: u32::MAX },
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
        ]
        .into_iter()
        .map(|kind| Some(Ty::FatPtr(kind))),
    );
    for input in cases {
        let expected = borrow_result_ty(input.as_ref());
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let actual = borrow_result_ty_observed(input.as_ref(), &mut session, site()).unwrap();
        assert_eq!(actual, expected);
        actual.retire_observed(&mut session, site()).unwrap();
        assert!(session.first_refusal().is_none());
    }
}
#[test]
fn reverse_stored_chains_ignore_provisional_known_types_and_publish_sorted_results() {
    let mut f = chain(7);
    let mut late = Block::new(BlockId::new(3));
    late.body = f.blocks[0].body.split_off(4);
    f.blocks.insert(0, late);
    let rows = parity(&f, &known());
    assert_eq!(rows, (1..=7).map(|id| (v(id), fat())).collect::<Vec<_>>());
    f.blocks.reverse();
    assert_eq!(parity(&f, &known()), rows);
}
#[test]
fn last_borrow_duplicate_wins_only_first_result_counts_and_other_defs_do_not_erase_it() {
    let mut multiple = borrow(3, 0, false);
    multiple.results.push(v(99));
    let mut f = function(vec![
        borrow(1, 0, false),
        borrow(2, 1, true),
        InstrNode::new(Inst::Undef { ty: Ty::U32 }).with_result(v(1)),
        multiple,
        InstrNode::new(Inst::BorrowMut { ptr: v(0) }),
    ]);
    assert_eq!(
        parity(&f, &known()),
        vec![(v(1), fat()), (v(2), fat()), (v(3), fat())]
    );
    f.blocks[0].body.push(borrow(1, 77, true));
    assert_eq!(
        parity(&f, &known()),
        vec![(v(1), Ty::Ptr), (v(2), Ty::Ptr), (v(3), fat())]
    );
}
#[test]
fn self_and_mutual_cycles_absent_roots_and_refined_fat_stay_provisional_ptr() {
    let f = function(vec![
        borrow(1, 1, false),
        borrow(2, 3, true),
        borrow(3, 2, false),
        borrow(4, 99, false),
        borrow(5, 0, false),
        borrow(6, u32::MAX, false),
    ]);
    let known = vec![
        (0, Ty::Refine(TyId::new(2), PredId::new(3))),
        (1, fat()),
        (2, fat()),
        (u32::MAX, fat()),
    ];
    assert_eq!(
        parity(&f, &known),
        vec![
            (v(1), Ty::Ptr),
            (v(2), Ty::Ptr),
            (v(3), Ty::Ptr),
            (v(4), Ty::Ptr),
            (v(5), Ty::Ptr),
            (v(6), fat())
        ]
    );
}
#[test]
fn concrete_known_rows_use_exact_last_match_semantics_without_a_uniqueness_grant() {
    let f = chain(3);
    assert!(
        parity(&f, &[(0, fat()), (0, Ty::Ptr)])
            .iter()
            .all(|(_, ty)| *ty == Ty::Ptr)
    );
    assert!(
        parity(&f, &[(0, Ty::Ptr), (0, fat())])
            .iter()
            .all(|(_, ty)| *ty == fat())
    );
}
#[test]
fn empty_nodes_and_sparse_maximum_value_ids_match_original_without_logical_extent() {
    let empty = function(vec![
        InstrNode::new(Inst::NullPtr),
        InstrNode::new(Inst::Borrow { ptr: v(0) }),
    ]);
    assert!(parity(&empty, &known()).is_empty());
    let f = function(vec![
        borrow(u32::MAX, 0, false),
        borrow(400_000_000, u32::MAX, true),
    ]);
    assert_eq!(
        parity(&f, &known()),
        vec![(v(400_000_000), fat()), (v(u32::MAX), fat())]
    );
}
#[test]
fn irrelevant_deep_thin_known_payloads_are_neither_cloned_nor_walked() {
    let f = chain(2);
    let (_, thin) = observed(&f, &[(0, Ty::Ptr)]);
    let (_, deep) = observed(
        &f,
        &[(0, Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U32; 20_000]))))],
    );
    assert_eq!(thin.events, deep.events);
    assert_eq!(thin.work, deep.work);
    assert_eq!(thin.bytes, deep.bytes);
}
