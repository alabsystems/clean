// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn text(rows: &[Ty]) -> String {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.types_text(rows, &mut w).unwrap();
    assert_eq!(state.detail, format!("{rows:?}"));
    assert_eq!(state.tasks.capacity(), 0);
    let out = take(&mut state.detail);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    out
}
#[test]
fn all_forty_constructible_types_keep_exact_derived_debug_not_display() {
    let rows = types();
    assert_eq!(rows.len(), 40);
    for ty in rows {
        text(&[ty]);
    }
}
#[test]
fn empty_singleton_and_nested_tuple_boxes_keep_full_vec_debug_punctuation() {
    assert_eq!(text(&[]), "[]");
    assert_eq!(text(&[Ty::Unit]), "[Unit]");
    assert_eq!(
        text(&[Ty::Tuple(vec![]), Ty::Tuple(vec![Ty::U8])]),
        "[Tuple([]), Tuple([U8])]"
    );
    assert_eq!(
        text(&[Ty::Ref(Box::new(Ty::RefMut(Box::new(Ty::PtrConst(
            Box::new(Ty::U8)
        )))))]),
        "[Ref(RefMut(PtrConst(U8)))]"
    );
}
#[test]
fn all_fat_kinds_set_representations_and_extreme_ids_lanes_lengths_are_exact() {
    for kind in [
        FatPtrKind::Slice(TyId::new(u32::MAX)),
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: u32::MAX },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        text(&[Ty::FatPtr(kind)]);
    }
    for repr in [SetRepr::Boxed, SetRepr::Bitset] {
        text(&[Ty::Set(TyId::new(u32::MAX), repr)]);
    }
    text(&[
        Ty::Array(TyId::new(u32::MAX), u64::MAX),
        Ty::Vector(Box::new(Ty::Error), u32::MAX),
        Ty::Tensor(Box::new(Ty::I32), 2),
        Ty::Tensor(Box::new(Ty::Error), u32::MAX),
        Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX)),
    ]);
}
#[test]
fn malformed_handle_and_dialect_fields_preserve_scalar_debug_quotes_and_full_tails() {
    let mut raw = (0u8..=127).map(char::from).collect::<String>();
    raw.push_str("\u{300}x\u{301}'\"\\\u{200d}\u{feff}🦀");
    let rows = [
        Ty::Handle(Box::new(HandleTy::new(
            raw.clone(),
            "λ'\"\n\0".repeat(1500) + "TAIL",
        ))),
        Ty::Dialect(Box::new(DialectTy::new(
            raw,
            "λ'\"\n\0".repeat(1500) + "TAIL",
            u32::MAX,
        ))),
    ];
    let out = text(&rows);
    assert!(out.contains("TAIL") && out.contains("HandleTy {") && out.contains("DialectTy {"));
}
#[test]
fn wide_tuple_and_deep_box_debug_traverse_every_actual_child_in_order() {
    let row = Ty::Tuple(
        (0..1024)
            .map(|i| Ty::Refine(TyId::new(i), PredId::new(1023 - i)))
            .collect(),
    );
    text(&[row]);
    let mut nested = Ty::U8;
    for _ in 0..128 {
        nested = Ty::Rc(Box::new(Ty::PtrMut(Box::new(nested))));
    }
    text(&[nested]);
}
#[test]
fn nominal_type_ids_are_not_resolved_and_projection_reason_is_full_actual_debug() {
    let mut m = fixture();
    m.func_types[0].params = vec![
        Ty::Array(TyId::new(u32::MAX), 0),
        Ty::Tuple(vec![Ty::Error]),
    ];
    m.func_types[0].returns = vec![Ty::Dialect(Box::new(DialectTy::new("λ", "name", 0)))];
    let before = run(&m);
    m.types = types();
    let after = run(&m);
    assert_eq!(before.0, after.0);
    assert_eq!(before.1.events, after.1.events);
    assert_eq!(
        detail(&before.0[0]),
        format!(
            "projection signature must be non-variadic (&T) -> R, got params={:?}, returns={:?}, vararg=false",
            m.func_types[0].params, m.func_types[0].returns
        )
    );
}
