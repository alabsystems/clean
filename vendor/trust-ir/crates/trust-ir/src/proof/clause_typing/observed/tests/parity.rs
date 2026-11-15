// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_eleven_place_tags_preserve_full_ordinary_resolution_and_refusal_data() {
    let m = fixture();
    let all = places();
    assert_eq!(all.len(), 11);
    for place in all {
        run(&m, FuncId::new(7), &place);
    }
}
#[test]
fn zero_and_multiple_physical_functions_precede_even_ambient_place_and_signature_checks() {
    for count in [0, 2, 3] {
        let mut m = fixture();
        let f = m.functions.pop().unwrap();
        m.functions = vec![f; count];
        m.func_types.clear();
        for place in places() {
            run(&m, FuncId::new(7), &place);
        }
    }
    let mut m = fixture();
    m.func_types.clear();
    for place in places() {
        run(&m, FuncId::new(7), &place);
    }
}
#[test]
fn sparse_reordered_unique_function_resolves_its_own_signature_without_slot_assumptions() {
    let mut m = fixture();
    m.func_types
        .push(FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::Unit], false));
    let mut f = m.functions[0].clone();
    f.id = FuncId::new(0);
    f.ty = FuncTyId::new(1);
    m.functions.push(f);
    for id in [7, 0, u32::MAX] {
        run(&m, FuncId::new(id), &ClausePlace::Param { index: 0 });
    }
}
#[test]
fn mutable_exit_requires_only_direct_refmut_or_ptrmut_for_every_current_type_tag() {
    let mut m = fixture();
    let all = types();
    assert_eq!(all.len(), 40);
    for ty in all {
        m.func_types[0].params = vec![ty];
        run(&m, FuncId::new(7), &ClausePlace::MutParamExit { index: 0 });
    }
}
#[test]
fn entry_pointee_requires_only_direct_reference_and_preserves_nested_references() {
    let mut m = fixture();
    for ty in types() {
        m.func_types[0].params = vec![ty];
        run(
            &m,
            FuncId::new(7),
            &ClausePlace::ParamPointeeEntry { index: 0 },
        );
    }
    m.func_types[0].params = vec![Ty::Ref(Box::new(Ty::Ref(Box::new(Ty::Bool))))];
    run(
        &m,
        FuncId::new(7),
        &ClausePlace::ParamPointeeEntry { index: 0 },
    );
}
#[test]
fn full_unsigned_indices_and_each_parameter_return_boundary_keep_exact_arities() {
    let m = fixture();
    for index in [0, 1, 3, 4, u32::MAX] {
        for place in [
            ClausePlace::Param { index },
            ClausePlace::ResultSlot { index },
            ClausePlace::MutParamExit { index },
            ClausePlace::ParamPointeeEntry { index },
        ] {
            run(&m, FuncId::new(7), &place);
        }
    }
}
#[test]
fn resolution_returns_the_exact_borrowed_type_without_cloning_nested_storage() {
    let mut m = fixture();
    m.func_types[0].params = vec![Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U8; 10000])))];
    let Ty::Ref(inner) = &m.func_types[0].params[0] else {
        unreachable!()
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let ty = resolve_clause_place_borrowed_observed(
        &m,
        FuncId::new(7),
        &ClausePlace::ParamPointeeEntry { index: 0 },
        &mut s,
        site(),
    )
    .unwrap()
    .unwrap();
    assert!(core::ptr::eq(ty, inner.as_ref()));
}
#[test]
fn full_sort_scalar_table_matches_all_current_type_tags_and_pointer_width_options() {
    let sorts = [
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(0),
        ClauseSort::BitVec(8),
        ClauseSort::BitVec(16),
        ClauseSort::BitVec(32),
        ClauseSort::BitVec(64),
        ClauseSort::BitVec(128),
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Float { eb: 5, sb: 11 },
        ClauseSort::Float { eb: 8, sb: 24 },
        ClauseSort::Float { eb: 11, sb: 53 },
        ClauseSort::Float {
            eb: 0,
            sb: u32::MAX,
        },
        ClauseSort::RoundingMode,
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        ClauseSort::Datatype {
            name: "D".into(),
            constructors: vec![],
        },
    ];
    for ty in types() {
        for sort in &sorts {
            for bits in [None, Some(0), Some(32), Some(64), Some(u32::MAX)] {
                admit(sort, &ty, bits);
            }
        }
    }
}
#[test]
fn pointer_integer_width_is_never_defaulted_and_char_and_float_boundaries_are_exact() {
    assert!(!admit(&ClauseSort::BitVec(64), &Ty::Usize, None).0);
    assert!(admit(&ClauseSort::Int, &Ty::Usize, None).0);
    assert!(admit(&ClauseSort::BitVec(32), &Ty::Char, None).0);
    assert!(!admit(&ClauseSort::BitVec(64), &Ty::Char, Some(64)).0);
    assert!(!admit(&ClauseSort::Float { eb: 8, sb: 23 }, &Ty::F32, None).0);
}
#[test]
fn rejected_recursive_sort_and_type_payloads_remain_opaque_under_the_finite_table() {
    let a = ClauseSort::Datatype {
        name: "small".into(),
        constructors: vec![],
    };
    let b = ClauseSort::Datatype {
        name: "unused".repeat(100000),
        constructors: vec![("unused".repeat(100000), vec![])],
    };
    let (_, one) = admit(&a, &Ty::Bool, None);
    let (_, two) = admit(&b, &Ty::Bool, None);
    assert_eq!(one.events, two.events);
    let (_, one) = admit(&ClauseSort::Int, &Ty::Tuple(vec![]), None);
    let (_, two) = admit(&ClauseSort::Int, &Ty::Tuple(vec![Ty::U8; 10000]), None);
    assert_eq!(one.events, two.events);
}
