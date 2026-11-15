// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn module_lookup_prefers_matching_index_then_first_physical_fallback() {
    let (mut a, ta, mut b, tb) = structure_pair();
    a.structs.push(strukt(3, "wrong duplicate", Ty::Bool));
    equal(&a, &ta, &b, &tb);
    for _ in 1..4 {
        a.structs.push(strukt(99, "filler", Ty::Bool));
    }
    a.structs[3] = strukt(3, "indexed", Ty::Bool);
    unequal(&a, &ta, &b, &tb);
    b.structs[0] = strukt(8, "indexed", Ty::Bool);
    equal(&a, &ta, &b, &tb);
    b.structs.clear();
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn every_struct_name_repr_size_align_field_name_offset_and_type_participates() {
    let (a, ta, b, tb) = structure_pair();
    equal(&a, &ta, &b, &tb);
    for change in 0..8 {
        let mut b = b.clone();
        let row = &mut b.structs[0];
        match change {
            0 => row.name.push('x'),
            1 => row.repr = StructRepr::C,
            2 => row.size = Some(17),
            3 => row.align = None,
            4 => row.fields[0].name.push('x'),
            5 => row.fields[0].offset = None,
            6 => row.fields[0].ty = Ty::Bool,
            _ => row.fields.push(field("tail", Ty::I8)),
        }
        unequal(&a, &ta, &b, &tb);
    }
}
#[test]
fn equal_different_and_unkeyed_clean_origins_obey_the_split_rule() {
    let (mut a, ta, mut b, tb) = structure_pair();
    a.structs[0].origin = Some(origin("same"));
    equal(&a, &ta, &b, &tb);
    b.structs[0].origin = Some(origin("same"));
    equal(&a, &ta, &b, &tb);
    b.structs[0].origin = Some(origin("different"));
    assert_eq!(check(&a, &ta, &b, &tb), TyEquivalence::Unequal);
    b.structs[0].origin = Some(origin("same"));
    b.structs[0].name = "other".into();
    let TyEquivalence::OriginConflict(c) = check(&a, &ta, &b, &tb) else {
        panic!("shared key needs conflict")
    };
    assert_eq!(c.origin, origin("same"));
    assert_eq!(
        (c.table, c.left.as_str(), c.right.as_str()),
        ("struct", "S", "other")
    );
    a.structs[0].origin = None;
    assert_eq!(check(&a, &ta, &b, &tb), TyEquivalence::Unequal);
}
#[test]
fn rust_origin_crate_path_algorithm_and_digest_bytes_are_all_identity() {
    let (mut a, ta, mut b, tb) = structure_pair();
    let key = TypeOrigin::Rust {
        stable_crate_id: 5,
        def_path_hash: [3; 16],
        args_digest: ProofDigest {
            algorithm: crate::ProofDigestAlgorithm::Sha256,
            bytes: [8; 32],
        },
    };
    a.structs[0].origin = Some(key.clone());
    b.structs[0].origin = Some(key);
    equal(&a, &ta, &b, &tb);
    for change in 0..4 {
        let mut b = b.clone();
        let Some(TypeOrigin::Rust {
            stable_crate_id,
            def_path_hash,
            args_digest,
        }) = &mut b.structs[0].origin
        else {
            panic!()
        };
        match change {
            0 => *stable_crate_id += 1,
            1 => def_path_hash[15] ^= 1,
            2 => args_digest.algorithm = crate::ProofDigestAlgorithm::TrustIrStableV1,
            _ => args_digest.bytes[31] ^= 1,
        }
        assert_eq!(check(&a, &ta, &b, &tb), TyEquivalence::Unequal);
    }
}
#[test]
fn coinductive_struct_and_type_id_cycles_keep_active_pairs_only() {
    let (mut a, ta, mut b, tb) = structure_pair();
    a.structs[0].fields[0].ty = Ty::Ref(Box::new(ta.clone()));
    b.structs[0].fields[0].ty = Ty::Ref(Box::new(tb.clone()));
    equal(&a, &ta, &b, &tb);
    b.structs[0].fields.push(field("later", Ty::Bool));
    unequal(&a, &ta, &b, &tb);
    a.types = vec![Ty::Sequence(TyId::new(0))];
    b.types = vec![Ty::Bool, Ty::Sequence(TyId::new(1))];
    equal(
        &a,
        &Ty::Sequence(TyId::new(0)),
        &b,
        &Ty::Sequence(TyId::new(1)),
    );
    b.types[1] = Ty::Array(TyId::new(1), 2);
    unequal(
        &a,
        &Ty::Sequence(TyId::new(0)),
        &b,
        &Ty::Sequence(TyId::new(1)),
    );
}
#[test]
fn completed_pairs_are_removed_and_repeated_siblings_really_revisit() {
    let (a, ta, b, tb) = structure_pair();
    let one = baseline(&a, &ta, &b, &tb);
    let two = baseline(
        &a,
        &Ty::Tuple(vec![ta.clone(), ta]),
        &b,
        &Ty::Tuple(vec![tb.clone(), tb]),
    );
    assert!(two.work > one.work);
    let mut state = State::new();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options(), &mut observer);
    let mut w = Work {
        session: &mut session,
        site: site(),
    };
    let key = (Kind::Struct, 3, 8);
    assert!(state.enter(key, None, &mut w).unwrap());
    assert!(!state.enter(key, None, &mut w).unwrap());
    let Some(Task::End(key, source)) = state.tasks.pop() else {
        panic!()
    };
    state.end(key, source, &mut w).unwrap();
    assert!(state.active.is_empty());
    assert!(state.enter(key, None, &mut w).unwrap());
    state.scratch(&mut w);
    state.owned(&mut w);
    assert_state_empty(&state);
}
#[test]
fn first_nested_conflict_is_retained_over_outer_conflicts() {
    let (mut a, ta, mut b, tb) = structure_pair();
    a.structs[0].origin = Some(origin("inner"));
    b.structs[0].origin = a.structs[0].origin.clone();
    b.structs[0].fields[0].ty = Ty::Bool;
    a.structs.push(strukt(4, "Outer", ta));
    b.structs.push(strukt(9, "Outer", tb));
    a.structs[1].origin = Some(origin("outer"));
    b.structs[1].origin = a.structs[1].origin.clone();
    let TyEquivalence::OriginConflict(c) = check(
        &a,
        &Ty::Struct(StructId::new(4)),
        &b,
        &Ty::Struct(StructId::new(9)),
    ) else {
        panic!()
    };
    assert_eq!(c.origin, origin("inner"));
    assert_eq!(c.table, "struct");
}
#[test]
fn record_and_closure_function_capture_order_and_missing_rows_match() {
    let mut a = Module::new("a");
    let mut b = Module::new("b");
    a.records.push(RecordDef {
        id: RecordId::new(3),
        name: "R".into(),
        fields: vec![field("a", Ty::Bool), field("b", Ty::I64)],
    });
    b.records.push(RecordDef {
        id: RecordId::new(8),
        ..a.records[0].clone()
    });
    let ta = Ty::Record(RecordId::new(3));
    let tb = Ty::Record(RecordId::new(8));
    equal(&a, &ta, &b, &tb);
    b.records[0].fields.swap(0, 1);
    unequal(&a, &ta, &b, &tb);
    a.func_types
        .push(FuncTy::unrecorded(vec![Ty::I64], vec![Ty::Bool], false));
    b.func_types.push(a.func_types[0].clone());
    a.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::I64, Ty::Bool],
    });
    b.closure_types = a.closure_types.clone();
    let ty = Ty::Closure(ClosureTyId::new(0));
    equal(&a, &ty, &b, &ty);
    b.closure_types[0].captures.swap(0, 1);
    unequal(&a, &ty, &b, &ty);
    b.closure_types.clear();
    unequal(&a, &ty, &b, &ty);
}
#[test]
fn enum_discriminants_canonical_tags_and_ignored_field_names_match() {
    let (a, ta, mut b, tb) = enum_pair();
    b.enums[0].variants[0].field_names = vec!["different fidelity metadata".into(), "extra".into()];
    equal(&a, &ta, &b, &tb);
    b.enums[0].discriminants = vec![Some(-3), Some(-2)];
    equal(&a, &ta, &b, &tb);
    b.enums[0].repr = Some(EnumTagRepr::I16);
    unequal(&a, &ta, &b, &tb);
    b.enums[0].repr = None;
    b.enums[0].discriminants[1] = Some(5);
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn equally_malformed_enums_keep_none_none_semantics_and_excess_tail_opacity() {
    let (mut a, ta, mut b, tb) = enum_pair();
    a.enums[0].discriminants = vec![Some(1), Some(1)];
    b.enums[0].discriminants = a.enums[0].discriminants.clone();
    equal(&a, &ta, &b, &tb);
    b.enums[0].discriminants.push(Some(100));
    equal(&a, &ta, &b, &tb);
    a.enums[0].discriminants = vec![Some(i128::MAX), None];
    b.enums[0].discriminants = a.enums[0].discriminants.clone();
    equal(&a, &ta, &b, &tb);
    a.enums[0].variants.clear();
    b.enums[0].variants.clear();
    equal(&a, &ta, &b, &tb);
}
#[test]
fn enum_raw_direct_niche_untagged_and_nested_offsets_are_complete_identity() {
    let (mut a, ta, mut b, tb) = enum_pair();
    let encodings = vec![
        EnumTagEncoding::Direct { tag_offset: 0 },
        EnumTagEncoding::Untagged,
        EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 2,
            niche_start: 5,
            niche_offset: 4,
            niche_ty: EnumTagRepr::U16,
        },
    ];
    for encoding in encodings {
        a.enums[0].layout = Some(EnumLayoutDescriptor {
            encoding,
            size: 40,
            align: 8,
            variant_field_offsets: vec![vec![8, 16], vec![24]],
        });
        b.enums[0].layout = a.enums[0].layout.clone();
        equal(&a, &ta, &b, &tb);
        for change in 0..5 {
            let mut b = b.clone();
            let layout = b.enums[0].layout.as_mut().unwrap();
            match change {
                0 => layout.size += 1,
                1 => layout.align += 1,
                2 => layout.variant_field_offsets[0][1] += 1,
                3 => layout.variant_field_offsets.push(vec![]),
                _ => layout.variant_field_offsets[1].push(1),
            }
            unequal(&a, &ta, &b, &tb);
        }
    }
    a.enums[0].origin = Some(origin("enum"));
    b.enums[0].origin = a.enums[0].origin.clone();
    b.enums[0].variants[0].name.push('x');
    assert!(matches!(
        check(&a, &ta, &b, &tb),
        TyEquivalence::OriginConflict(TypeOriginConflict { table: "enum", .. })
    ));
}

#[test]
fn every_niche_encoding_field_and_direct_tag_offset_remains_raw_identity() {
    let (mut a, ta, mut b, tb) = enum_pair();
    a.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Niche {
        untagged_variant: 0,
        niche_variants_start: 1,
        niche_variants_end: 2,
        niche_start: 5,
        niche_offset: 8,
        niche_ty: EnumTagRepr::U16,
    };
    b.enums[0].layout = a.enums[0].layout.clone();
    for change in 0..6 {
        let mut b = b.clone();
        let EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } = &mut b.enums[0].layout.as_mut().unwrap().encoding
        else {
            panic!()
        };
        match change {
            0 => *untagged_variant += 1,
            1 => *niche_variants_start += 1,
            2 => *niche_variants_end += 1,
            3 => *niche_start += 1,
            4 => *niche_offset += 1,
            _ => *niche_ty = EnumTagRepr::U32,
        }
        unequal(&a, &ta, &b, &tb);
    }
    a.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct { tag_offset: 0 };
    b.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct { tag_offset: 1 };
    unequal(&a, &ta, &b, &tb);
    b.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged;
    unequal(&a, &ta, &b, &tb);
}

#[test]
fn normalized_enum_tag_hints_and_explicit_128_discriminants_follow_ordinary() {
    let (mut a, ta, mut b, tb) = enum_pair();
    b.enums[0].repr = Some(EnumTagRepr::I8);
    equal(&a, &ta, &b, &tb);
    a.enums[0].discriminants = vec![Some(i128::MAX - 1), Some(i128::MAX)];
    b.enums[0].discriminants = a.enums[0].discriminants.clone();
    a.enums[0].repr = Some(EnumTagRepr::I128);
    b.enums[0].repr = Some(EnumTagRepr::I128);
    equal(&a, &ta, &b, &tb);
    b.enums[0].repr = None;
    unequal(&a, &ta, &b, &tb);
    a.enums[0].repr = Some(EnumTagRepr::U8);
    b.enums[0].repr = Some(EnumTagRepr::U16);
    // Both inadequate recorded hints produce the same canonical None.
    equal(&a, &ta, &b, &tb);
}
#[test]
fn recursive_function_closure_and_record_pairs_use_the_same_active_path_rule() {
    let mut a = Module::new("a");
    let mut b = Module::new("b");
    let ta = Ty::Func(FuncTyId::new(0));
    let tb = Ty::Func(FuncTyId::new(1));
    a.func_types
        .push(FuncTy::unrecorded(vec![ta.clone()], vec![Ty::Bool], false));
    b.func_types.push(FuncTy::unrecorded(vec![], vec![], false));
    b.func_types
        .push(FuncTy::unrecorded(vec![tb.clone()], vec![Ty::Bool], false));
    equal(&a, &ta, &b, &tb);
    b.func_types[1].returns[0] = Ty::I64;
    unequal(&a, &ta, &b, &tb);
    let ta = Ty::Closure(ClosureTyId::new(0));
    let tb = Ty::Closure(ClosureTyId::new(0));
    a.func_types[0] = FuncTy::unrecorded(vec![ta.clone()], vec![], false);
    b.func_types[1] = FuncTy::unrecorded(vec![tb.clone()], vec![], false);
    a.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![ta.clone()],
    });
    b.closure_types.push(ClosureTy {
        func: FuncTyId::new(1),
        captures: vec![tb.clone()],
    });
    equal(&a, &ta, &b, &tb);
    let ta = Ty::Record(RecordId::new(3));
    let tb = Ty::Record(RecordId::new(8));
    a.records.push(RecordDef {
        id: RecordId::new(3),
        name: "R".into(),
        fields: vec![field("r", ta.clone())],
    });
    b.records.push(RecordDef {
        id: RecordId::new(8),
        name: "R".into(),
        fields: vec![field("r", tb.clone())],
    });
    equal(&a, &ta, &b, &tb);
}
