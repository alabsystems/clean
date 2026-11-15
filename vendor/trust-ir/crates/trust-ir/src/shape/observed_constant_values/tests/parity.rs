// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::collapsible_if,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_scalar_integer_widths_and_unicode_boundaries_match_actual_range_rule() {
    for ty in [
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
        Ty::Char,
    ] {
        for n in [
            i128::MIN,
            -1,
            0,
            127,
            128,
            255,
            256,
            0xd7ff,
            0xd800,
            0xdfff,
            0xe000,
            0x10ffff,
            0x110000,
            i128::MAX,
        ] {
            predicate(&Constant::Int(n), &ty, 64);
        }
    }
    assert!(predicate(&Constant::U128(u128::MAX), &Ty::U128, 64).0);
    assert!(predicate(&Constant::U128(0), &Ty::U128, 64).0);
    assert!(!predicate(&Constant::U128(u128::MAX), &Ty::I128, 64).0);
}
#[test]
fn explicit_original_pointer_width_including_invalid_widths_is_never_defaulted() {
    for bits in [0, 8, 16, 32, 64, 128, 129] {
        for ty in [Ty::Isize, Ty::Usize] {
            for n in [-1, 0, 255, 256, 1i128 << 32, i128::MAX] {
                predicate(&Constant::Int(n), &ty, bits);
            }
        }
    }
    assert!(!predicate(&Constant::Int(1i128 << 32), &Ty::Usize, 32).0);
    assert!(predicate(&Constant::Int(1i128 << 32), &Ty::Usize, 64).0);
}
#[test]
fn nested_branching_unary_and_empty_vectors_preserve_actual_value_order() {
    let (v, t) = branching();
    assert!(predicate(&v, &t, 64).0);
    let mut bad = v.clone();
    if let Constant::Vector(rows) = &mut bad {
        if let Constant::Vector(row) = &mut rows[1] {
            row[1] = Constant::Int(256);
        }
    }
    assert!(!predicate(&bad, &t, 64).0);
    assert!(
        predicate(
            &Constant::Vector(vec![]),
            &Ty::Vector(Box::new(Ty::Never), 0),
            64
        )
        .0
    );
    assert!(
        predicate(
            &Constant::Vector(vec![Constant::Int(3)]),
            &Ty::Vector(Box::new(Ty::U8), 1),
            64
        )
        .0
    );
}
#[test]
fn vector_arity_is_checked_before_payload_and_no_nonvector_shape_is_tightened() {
    let (v, _) = branching();
    assert!(!predicate(&v, &Ty::Vector(Box::new(Ty::U8), 1), 64).0);
    assert!(
        predicate(
            &Constant::Aggregate(vec![Constant::Bool(false)]),
            &Ty::Tuple(vec![]),
            64
        )
        .0
    );
    assert!(
        predicate(
            &Constant::Splat {
                elem: Box::new(Constant::Uninit),
                len: 0
            },
            &Ty::Array(TyId::new(99), 0),
            64
        )
        .0
    );
}
#[test]
fn table_free_pointer_symbol_fatpointer_and_other_closed_shapes_match_ordinary() {
    for (v, t) in [
        (Constant::Int(7), Ty::Ptr),
        (Constant::Bool(false), Ty::Bool),
        (Constant::Float(f64::NAN), Ty::F32),
        (Constant::FnDef(FuncId::new(4)), Ty::Func(FuncTyId::new(9))),
        (Constant::symbol_addr("unresolved"), Ty::Ptr),
        (
            Constant::symbol_addr("unresolved"),
            Ty::Ref(Box::new(Ty::Bool)),
        ),
        (
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            Ty::FatPtr(FatPtrKind::Str),
        ),
        (
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(1)]),
            Ty::FatPtr(FatPtrKind::Str),
        ),
        (Constant::PhantomData, Ty::Unit),
        (Constant::Uninit, Ty::Unit),
    ] {
        predicate(&v, &t, 64);
    }
}
#[test]
fn every_actual_label_family_matches_complete_ordinary_text_without_formatters() {
    for v in [
        Constant::Int(-1),
        Constant::U128(u128::MAX),
        Constant::Bytes {
            data: vec![0, 1],
            utf8: false,
        },
        Constant::Float(-0.0),
        Constant::Bool(true),
        Constant::Aggregate(vec![Constant::Int(1)]),
        Constant::Array(vec![]),
        Constant::Splat {
            elem: Box::new(Constant::Int(1)),
            len: u64::MAX,
        },
        Constant::Vector(vec![]),
        Constant::Sequence(vec![]),
        Constant::Set(vec![]),
        Constant::Record(vec![("unread".into(), Constant::Int(0))]),
        Constant::Closure {
            func: FuncId::new(u32::MAX),
            captures: vec![Constant::Bool(false)],
        },
        Constant::FnDef(FuncId::new(u32::MAX)),
        symbol(),
        Constant::PhantomData,
        Constant::Uninit,
    ] {
        label(&v);
    }
}
#[test]
fn exact_signed_addend_extremes_and_unescaped_long_unicode_symbol_are_preserved() {
    for addend in [i64::MIN, -1, 0, 1, i64::MAX] {
        let v = Constant::SymbolAddr {
            symbol: "é🦀<>+中".repeat(400),
            addend,
        };
        let text = label(&v).0;
        assert!(text.contains("é🦀<>+中"));
        assert!(text.ends_with(&format!(" + {addend}>")));
    }
}
#[test]
fn short_circuit_and_shape_labels_never_visit_unread_variable_child_payloads() {
    let mut traces = Vec::new();
    for tail in [
        Constant::Int(1),
        Constant::Vector(vec![Constant::Int(0); 500]),
    ] {
        let v = Constant::Vector(vec![Constant::Bool(false), tail]);
        let (ok, o, end) = predicate(&v, &Ty::Vector(Box::new(Ty::U8), 2), 64);
        assert!(!ok);
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
    let mut traces = Vec::new();
    for elem in [
        Constant::Int(1),
        Constant::Vector(vec![Constant::Int(0); 500]),
    ] {
        let (_, o, end) = label(&Constant::Splat {
            elem: Box::new(elem),
            len: u64::MAX,
        });
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
