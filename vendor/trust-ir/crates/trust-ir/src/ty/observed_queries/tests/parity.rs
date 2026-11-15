// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all40_constructible_variants_match_original_inline_predicates_and_width_modes() {
    let types = fixtures::all();
    assert_eq!(types.len(), 40);
    for ty in types {
        for query in ALL {
            parity(&ty, query);
        }
        for bits in [0, 1, 64, u32::MAX] {
            parity(&ty, Query::Target(bits));
        }
    }
}
#[test]
fn inner_overflow_cannot_be_recovered_by_an_outer_zero_lane_count() {
    for ty in [
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), u32::MAX)), 0),
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), 0)), u32::MAX),
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::Ptr), u32::MAX)), 0),
    ] {
        for query in [Query::Width, Query::Target(32), Query::Target(u32::MAX)] {
            parity(&ty, query);
        }
    }
    let inner_bad = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), u32::MAX)), 0);
    assert_eq!(parity(&inner_bad, Query::Width), Answer::Width(None));
    let inner_zero = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U128), 0)), u32::MAX);
    assert_eq!(parity(&inner_zero, Query::Width), Answer::Width(Some(0)));
}
#[test]
fn every_fat_kind_handle_and_function_keep_exact_context_free_and_target_width_rules() {
    for kind in [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(8)),
        FatPtrKind::TraitObject { trait_id: 9 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        for query in [
            Query::Width,
            Query::Target(0),
            Query::Target(32),
            Query::Target(64),
            Query::Target(u32::MAX),
        ] {
            parity(&Ty::FatPtr(kind), query);
        }
    }
    assert_eq!(
        parity(
            &Ty::Handle(Box::new(HandleTy::new("invalid\0", "raw\n"))),
            Query::Width
        ),
        Answer::Width(None)
    );
    assert_eq!(
        parity(
            &Ty::Handle(Box::new(HandleTy::new("invalid\0", "raw\n"))),
            Query::Target(32)
        ),
        Answer::Width(Some(32))
    );
    assert_eq!(
        parity(&Ty::Func(FuncTyId::new(0)), Query::Target(64)),
        Answer::Width(None)
    );
}
#[test]
fn bool_lane_predicate_follows_only_vectors_including_zero_lanes() {
    for ty in [
        Ty::Bool,
        vectors(Ty::Bool, 12, 0),
        vectors(Ty::U8, 12, 0),
        Ty::Tuple(vec![Ty::Bool]),
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Array(TyId::new(0), 1),
    ] {
        parity(&ty, Query::Bool);
    }
    assert_eq!(
        parity(&vectors(Ty::Bool, 12, 0), Query::Bool),
        Answer::Bool(true)
    );
}
#[test]
fn complete_inline_handle_and_dialect_visitors_preserve_all_seven_containers_and_nominal_opacity() {
    let inner = fixture();
    for ty in [
        Ty::Vector(Box::new(inner.clone()), 0),
        Ty::Ref(Box::new(inner.clone())),
        Ty::RefMut(Box::new(inner.clone())),
        Ty::PtrConst(Box::new(inner.clone())),
        Ty::PtrMut(Box::new(inner.clone())),
        Ty::Rc(Box::new(inner.clone())),
        Ty::Tuple(vec![Ty::U8, inner]),
    ] {
        for query in [Query::Handle, Query::Dialect] {
            assert_eq!(parity(&ty, query), Answer::Bool(true));
        }
    }
    for ty in [
        Ty::Array(TyId::new(0), 1),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Struct(StructId::new(0)),
        Ty::Func(FuncTyId::new(0)),
    ] {
        for query in [Query::Handle, Query::Dialect] {
            assert_eq!(parity(&ty, query), Answer::Bool(false));
        }
    }
}
#[test]
fn nonsemantic_handle_and_dialect_payload_sizes_are_not_copied_or_scanned() {
    for (small, large) in [
        (
            Ty::Handle(Box::new(HandleTy::new("a", "b"))),
            Ty::Handle(Box::new(HandleTy::new("λ".repeat(5000), "\0".repeat(5000)))),
        ),
        (
            Ty::Dialect(Box::new(DialectTy::new("a", "b", 1))),
            Ty::Dialect(Box::new(DialectTy::new(
                "λ".repeat(5000),
                "\0".repeat(5000),
                1,
            ))),
        ),
    ] {
        for query in ALL {
            assert_eq!(run(&small, query).1.events, run(&large, query).1.events);
            parity(&large, query);
        }
    }
}
#[test]
fn a_tensor_element_is_an_inline_child_and_a_tensor_has_no_width() {
    for ty in [
        Ty::Tensor(Box::new(Ty::I32), 2),
        Ty::Tensor(Box::new(Ty::Bool), 1),
        Ty::Tensor(Box::new(Ty::handle("Nat", "trust_bignum::Nat")), 0),
        Ty::Tensor(
            Box::new(Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1)))),
            3,
        ),
    ] {
        for query in ALL {
            parity(&ty, query);
        }
        for bits in [0, 1, 64, u32::MAX] {
            parity(&ty, Query::Target(bits));
        }
    }
    let handle = Ty::Tensor(Box::new(Ty::handle("Nat", "trust_bignum::Nat")), 0);
    assert_eq!(parity(&handle, Query::Handle), Answer::Bool(true));
    let plain = Ty::Tensor(Box::new(Ty::U8), 4);
    assert_eq!(parity(&plain, Query::Width), Answer::Width(None));
    assert_eq!(parity(&plain, Query::Target(64)), Answer::Width(None));
}
