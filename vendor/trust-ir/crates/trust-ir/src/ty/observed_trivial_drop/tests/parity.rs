// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_forty_current_type_constructors_match_the_original_table() {
    let types = vec![Ty::I32; 8];
    let yes = vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Unit,
        Ty::Never,
        Ty::Ptr,
        Ty::PtrConst(Box::new(Ty::Error)),
        Ty::PtrMut(Box::new(Ty::Error)),
        Ty::Ref(Box::new(Ty::Error)),
        Ty::RefMut(Box::new(Ty::Error)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Func(FuncTyId::new(9)),
        Ty::Vector(Box::new(Ty::Error), 8),
        Ty::Tuple(vec![]),
        Ty::Array(TyId::new(7), 64),
    ];
    let no = vec![
        Ty::Error,
        Ty::Struct(StructId::new(3)),
        Ty::Enum(EnumId::new(8)),
        Ty::Record(RecordId::new(3)),
        Ty::Closure(ClosureTyId::new(4)),
        Ty::Rc(Box::new(Ty::I32)),
        Ty::Sequence(TyId::new(2)),
        Ty::Set(TyId::new(1), SetRepr::Boxed),
        Ty::Refine(TyId::new(5), PredId::new(6)),
        Ty::Dialect(Box::new(DialectTy::new("d", "t", 1))),
        Ty::handle("Nat", "runtime"),
    ];
    assert_eq!(yes.len() + no.len(), 40);
    for ty in yes {
        assert!(run(&ty, &types).0)
    }
    for ty in no {
        assert!(!run(&ty, &types).0)
    }
}
#[test]
fn zero_length_array_never_reads_or_validates_its_element_table() {
    let empty = run(&Ty::Array(TyId::new(u32::MAX), 0), &[]);
    let owning = run(&Ty::Array(TyId::new(0), 0), &[Ty::Error]);
    assert!(empty.0 && owning.0);
    assert_eq!(empty.1.events, owning.1.events);
    assert!(!run(&Ty::Array(TyId::new(u32::MAX), 1), &[]).0);
}
#[test]
fn direct_and_mutual_array_cycles_are_false_without_confusing_done_diamonds() {
    for types in [
        vec![Ty::Array(TyId::new(0), 1)],
        vec![Ty::Array(TyId::new(1), 1), Ty::Array(TyId::new(0), 1)],
    ] {
        assert!(!run(&Ty::Array(TyId::new(0), 1), &types).0);
    }
    let ty = Ty::Tuple(vec![Ty::Array(TyId::new(0), 1), Ty::Array(TyId::new(0), 4)]);
    let (answer, o) = run(&ty, &[Ty::I32]);
    assert!(answer);
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation
                && e.work == 3
                && e.copy_bytes == size_of::<&Ty>())
            .count(),
        4
    );
}
#[test]
fn reverse_tuple_short_circuit_does_not_eagerly_visit_a_wide_unused_tail() {
    let make = |n| {
        let mut xs = vec![Ty::U32; n];
        xs.push(Ty::Error);
        Ty::Tuple(xs)
    };
    let small = run(&make(8), &[]);
    let wide = run(&make(100_000), &[]);
    assert!(!small.0 && !wide.0);
    assert_eq!(small.1.events, wide.1.events);
    let left = Ty::Tuple(vec![Ty::Error, Ty::U32]);
    assert!(!run(&left, &[]).0);
}
#[test]
fn nested_inline_tuples_and_long_array_chains_use_explicit_owned_scratch() {
    let mut deep = Ty::U32;
    for _ in 0..1024 {
        deep = Ty::Tuple(vec![deep]);
    }
    assert!(run(&deep, &[]).0);
    // Fixture disposal is explicitly iterative, outside predicate ownership.
    while let Ty::Tuple(mut xs) = deep {
        deep = xs.pop().unwrap();
    }
    let mut types = (0..128)
        .map(|i| Ty::Array(TyId::new(i + 1), 1))
        .collect::<Vec<_>>();
    types.push(Ty::U8);
    assert!(run(&Ty::Array(TyId::new(0), 1), &types).0);
    types[128] = Ty::Error;
    assert!(!run(&Ty::Array(TyId::new(0), 1), &types).0);
}
#[test]
fn borrowed_pointer_vector_and_nominal_payloads_stay_opaque_as_documented() {
    for ty in [
        Ty::PtrConst(Box::new(Ty::Error)),
        Ty::PtrMut(Box::new(Ty::Error)),
        Ty::Ref(Box::new(Ty::Error)),
        Ty::RefMut(Box::new(Ty::Error)),
        Ty::Vector(Box::new(Ty::Error), 0),
    ] {
        assert!(run(&ty, &[]).0);
    }
    for ty in [
        Ty::Rc(Box::new(Ty::Unit)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), SetRepr::Bitset),
    ] {
        assert!(!run(&ty, &[Ty::Unit]).0);
    }
}
#[test]
fn a_tensor_is_never_trivially_droppable_as_a_sequence_is_not() {
    for ty in [
        Ty::Tensor(Box::new(Ty::I32), 2),
        Ty::Tensor(Box::new(Ty::U8), 0),
    ] {
        assert!(!ty.is_trivially_droppable(&[]));
        assert!(!run(&ty, &[]).0);
    }
}
