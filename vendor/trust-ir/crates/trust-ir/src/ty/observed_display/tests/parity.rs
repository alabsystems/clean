// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_constructible_type_variant_keeps_exact_ordinary_diagnostic_spelling() {
    let types = vec![
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
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(Box::new(Ty::U32), 8),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(StructId::new(3)),
        Ty::Array(TyId::new(7), 64),
        Ty::Tuple(vec![Ty::U32]),
        Ty::Enum(EnumId::new(8)),
        Ty::Func(FuncTyId::new(9)),
        Ty::Ref(Box::new(Ty::U8)),
        Ty::RefMut(Box::new(Ty::U16)),
        Ty::PtrConst(Box::new(Ty::U32)),
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::Rc(Box::new(Ty::I32)),
        Ty::Set(TyId::new(1), SetRepr::Boxed),
        Ty::Sequence(TyId::new(2)),
        Ty::Record(RecordId::new(3)),
        Ty::Closure(ClosureTyId::new(4)),
        Ty::Refine(TyId::new(5), PredId::new(6)),
        Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1))),
        Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat"))),
        Ty::Tensor(Box::new(Ty::I32), 2),
    ];
    assert_eq!(types.len(), 41); // Ext(NoExt) is unconstructible.
    for ty in types {
        parity(&ty);
    }
}

#[test]
fn all_fat_kinds_set_representations_and_maximum_ids_lengths_lanes_are_exact() {
    for kind in [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(u32::MAX)),
        FatPtrKind::TraitObject { trait_id: u32::MAX },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        parity(&Ty::FatPtr(kind));
    }
    for repr in [SetRepr::Bitset, SetRepr::Boxed] {
        parity(&Ty::Set(TyId::new(u32::MAX), repr));
    }
    for ty in [
        Ty::Array(TyId::new(u32::MAX), u64::MAX),
        Ty::Vector(Box::new(Ty::U8), u32::MAX),
        Ty::Tensor(Box::new(Ty::U8), u32::MAX),
        Ty::Tensor(Box::new(Ty::Tensor(Box::new(Ty::I64), 0)), 3),
        Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX)),
    ] {
        parity(&ty);
    }
}

#[test]
fn unit_empty_singleton_and_nested_tuple_punctuation_is_not_normalized() {
    assert_eq!(parity(&Ty::Unit), "()");
    assert_eq!(parity(&Ty::Tuple(vec![])), "(,)");
    assert_eq!(parity(&Ty::Tuple(vec![Ty::U8])), "(u8)");
    assert_eq!(
        parity(&Ty::Tuple(vec![
            Ty::Unit,
            Ty::Tuple(vec![]),
            Ty::Tuple(vec![Ty::U8, Ty::U16])
        ])),
        "((), (,), (u8, u16))"
    );
}

#[test]
fn raw_dialect_names_and_versions_are_not_debug_escaped_or_lexically_accepted() {
    let ty = Ty::Dialect(Box::new(DialectTy::new(
        "λ\0\n\"".repeat(700),
        "'🦀, <>".repeat(700),
        u32::MAX,
    )));
    let actual = parity(&ty);
    assert!(actual.contains('\0') && actual.contains('\n'));
    assert!(matches!(ty,Ty::Dialect(ref value) if value.validate().is_err()));
}

#[test]
fn malformed_handle_text_matches_debug_strings_for_ascii_and_unicode_extenders() {
    let mut name = (0u8..=127).map(char::from).collect::<String>();
    name.push_str("\u{85}\u{a0}\u{300}\u{34f}\u{2028}❤🦀\u{e000}\u{10ffff}");
    let runtime = "\u{300}x\u{301}'\"\\\u{200d}\u{feff}";
    let ty = Ty::Handle(Box::new(HandleTy::new(name, runtime)));
    let actual = parity(&ty);
    assert!(actual.contains("'"));
    assert!(actual.contains("\\\"") && actual.contains("\\u{300}"));
    assert!(matches!(ty,Ty::Handle(ref value) if value.validate().is_err()));
}

#[test]
fn wide_actual_tuple_children_and_all_reference_wrappers_keep_order() {
    let ty = Ty::Tuple(
        (0..1024)
            .map(|i| Ty::Refine(TyId::new(i), PredId::new(1023 - i)))
            .collect(),
    );
    parity(&ty);
    let mut ty = fixture();
    for _ in 0..64 {
        ty = Ty::Rc(Box::new(Ty::PtrMut(Box::new(Ty::RefMut(Box::new(ty))))));
    }
    parity(&ty);
}

#[test]
fn deep_borrowed_type_spelling_uses_no_recursive_display_or_input_drop() {
    let mut ty = Ty::U8;
    for _ in 0..50_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    let (actual, _) = run(&ty);
    assert_eq!(actual, "&".repeat(50_000) + "u8");
    while let Ty::Ref(inner) = ty {
        ty = *inner;
    }
}

#[test]
fn decimal_conversion_is_checked_and_exact_at_u128_max_without_narrowing() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut output = String::new();
    work.number(u128::MAX, &mut output).unwrap();
    assert_eq!(output, u128::MAX.to_string());
    work.retire(output);
}
