// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::clone_on_copy,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_scalar_tags_and_error_match_the_actual_whole_relation() {
    let m = Module::new("scalar");
    let scalars = [
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
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
    ];
    for a in &scalars {
        for b in &scalars {
            assert_eq!(matches!(check(&m, a, &m, b), TyEquivalence::Equal), a == b);
        }
    }
    unequal(&m, &Ty::Error, &m, &Ty::Error);
    unequal(&m, &Ty::Error, &m, &Ty::I8);
}
#[test]
fn every_inline_wrapper_tuple_and_vector_keeps_order_and_length() {
    let m = Module::new("inline");
    let roots = vec![
        Ty::Vector(Box::new(Ty::I64), 3),
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::RefMut(Box::new(Ty::Bool)),
        Ty::PtrConst(Box::new(Ty::Bool)),
        Ty::PtrMut(Box::new(Ty::Bool)),
        Ty::Rc(Box::new(Ty::Bool)),
        Ty::Tuple(vec![Ty::I64, Ty::Bool]),
        Ty::Tuple(vec![]),
    ];
    for a in &roots {
        for b in &roots {
            check(&m, a, &m, b);
        }
    }
    unequal(&m, &roots[0], &m, &Ty::Vector(Box::new(Ty::I64), 4));
    unequal(&m, &roots[6], &m, &Ty::Tuple(vec![Ty::Bool, Ty::I64]));
}
#[test]
fn a_tensor_is_equivalent_exactly_at_its_rank_and_element() {
    let m = Module::new("tensor");
    let tensor = Ty::Tensor(Box::new(Ty::I32), 2);
    equal(&m, &tensor, &m, &Ty::Tensor(Box::new(Ty::I32), 2));
    unequal(&m, &tensor, &m, &Ty::Tensor(Box::new(Ty::I32), 3));
    unequal(&m, &tensor, &m, &Ty::Tensor(Box::new(Ty::U32), 2));
    unequal(&m, &tensor, &m, &Ty::Vector(Box::new(Ty::I32), 2));
    unequal(
        &m,
        &Ty::Tensor(Box::new(Ty::Error), 0),
        &m,
        &Ty::Tensor(Box::new(Ty::Error), 0),
    );
}
#[test]
fn different_registered_ids_expand_and_missing_ids_refuse_semantically() {
    let mut a = Module::new("a");
    let mut b = Module::new("b");
    a.types.push(Ty::I64);
    b.types.extend([Ty::Bool, Ty::I64]);
    let pairs = [
        (Ty::Array(TyId::new(0), 7), Ty::Array(TyId::new(1), 7)),
        (Ty::Sequence(TyId::new(0)), Ty::Sequence(TyId::new(1))),
        (
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Set(TyId::new(1), SetRepr::Boxed),
        ),
        (
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(1))),
        ),
    ];
    for (ta, tb) in &pairs {
        assert_ne!(ta, tb);
        equal(&a, ta, &b, tb);
    }
    b.types.clear();
    for (ta, tb) in &pairs {
        unequal(&a, ta, &b, tb);
    }
}
#[test]
fn fat_pointer_kinds_trait_ids_set_representations_and_lengths_stay_distinct() {
    let m = Module::new("pointers");
    let kinds = [
        FatPtrKind::Str,
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
        FatPtrKind::TraitObject { trait_id: 1 },
        FatPtrKind::TraitObject { trait_id: 2 },
    ];
    for a in &kinds {
        for b in &kinds {
            assert_eq!(
                matches!(
                    check(&m, &Ty::FatPtr(a.clone()), &m, &Ty::FatPtr(b.clone())),
                    TyEquivalence::Equal
                ),
                a == b
            );
        }
    }
    let mut m = m;
    m.types.push(Ty::Bool);
    unequal(
        &m,
        &Ty::Set(TyId::new(0), SetRepr::Bitset),
        &m,
        &Ty::Set(TyId::new(0), SetRepr::Boxed),
    );
    unequal(
        &m,
        &Ty::Array(TyId::new(0), 3),
        &m,
        &Ty::Array(TyId::new(0), 4),
    );
}
#[test]
fn dialect_namespace_name_version_and_handle_name_runtime_are_all_raw_identity() {
    let m = Module::new("nominal leaves");
    let a = Ty::Dialect(Box::new(DialectTy::new("λ".repeat(2049), "name", 7)));
    equal(&m, &a, &m, &a);
    for b in [
        Ty::Dialect(Box::new(DialectTy::new("x", "name", 7))),
        Ty::Dialect(Box::new(DialectTy::new("λ".repeat(2049), "other", 7))),
        Ty::Dialect(Box::new(DialectTy::new("λ".repeat(2049), "name", 8))),
    ] {
        unequal(&m, &a, &m, &b);
    }
    let a = Ty::Handle(Box::new(HandleTy::new("name", "runtime")));
    equal(&m, &a, &m, &a);
    for b in [
        Ty::Handle(Box::new(HandleTy::new("other", "runtime"))),
        Ty::Handle(Box::new(HandleTy::new("name", "other"))),
    ] {
        unequal(&m, &a, &m, &b);
    }
}
#[test]
fn deep_inline_types_use_continuations_with_no_semantic_depth_limit() {
    let m = Module::new("depth");
    let mut ty = Ty::Bool;
    for _ in 0..256 {
        ty = Ty::Ref(Box::new(ty));
    }
    equal(&m, &ty, &m, &ty);
}
