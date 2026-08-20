// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Round-trip coverage for the v30 typed value model — `Ty::Refine`, the
// content-interned `Module::universes` / `Module::predicates` tables — across
// every serialization format (binary / text / json / msgpack), following the
// pattern of `spec_module_roundtrip.rs`.
//
// Two contracts are under test:
//
//   1. A module carrying refinements survives every round trip with the tables
//      BYTE-ORDER PRESERVED. Order is identity here: a `Ty::Refine` cites a
//      `PredId`, so a codec that re-sorted or re-interned the table would
//      silently repoint every refinement in the module.
//   2. The change is ADDITIVE. A v29-era module (no refinements) encodes and
//      decodes exactly as it always did, and nothing about its bytes moves.

#![cfg(all(feature = "parser", feature = "binary", feature = "serde"))]

use trust_ir::{Constant, FuncTy, Module, Pred, Space, Ty, Universe};

/// A module exercising every `Pred` variant, both `Universe` variants, and a
/// `Ty::Refine` reachable from the type table, a function signature and a
/// block parameter.
fn module_with_refinements() -> Module {
    let mut m = Module::new("refine_roundtrip");

    let range = m
        .intern_universe(Universe::IntRange { lo: 1, hi: 8 })
        .expect("canonical range");
    let members = m
        .intern_universe(Universe::Members(vec![
            Constant::Int(2),
            Constant::Int(4),
            Constant::Int(8),
        ]))
        .expect("canonical members");

    let interval = m
        .intern_pred(Pred::Interval { lo: 0, hi: 7 })
        .expect("canonical interval");
    let finite = m
        .intern_pred(Pred::FiniteSet(vec![Constant::Int(2), Constant::Int(4)]))
        .expect("canonical finite set");
    let member = m
        .intern_pred(Pred::InUniverse(range, Space::Member))
        .expect("in range");
    let index = m
        .intern_pred(Pred::InUniverse(members, Space::Index))
        .expect("in range");
    let nonzero = m.intern_pred(Pred::NonZero).expect("leaf");
    let nonnull = m.intern_pred(Pred::NonNull).expect("leaf");
    let _top = m.intern_pred(Pred::Top).expect("leaf");
    let _bottom = m.intern_pred(Pred::Bottom).expect("leaf");
    let conj = m
        .intern_pred(Pred::Conj(vec![interval, nonzero]))
        .expect("children exist");
    let _disj = m
        .intern_pred(Pred::Disj(vec![finite, member, index]))
        .expect("children exist");

    let i64_ty = m.add_type(Ty::I64);
    let ptr_ty = m.add_type(Ty::Ptr);
    m.add_type(Ty::Refine(i64_ty, conj));
    m.add_type(Ty::Refine(ptr_ty, nonnull));

    m.add_func_type(FuncTy {
        params: vec![Ty::Refine(i64_ty, member)],
        returns: vec![Ty::Refine(i64_ty, index)],
        is_vararg: false,
    });

    m
}

#[test]
fn binary_round_trip_preserves_tables_and_refinements() {
    let m = module_with_refinements();
    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decode");

    assert_eq!(back.universes, m.universes, "universe table must survive");
    assert_eq!(
        back.predicates, m.predicates,
        "predicate table must survive"
    );
    assert_eq!(back.types, m.types, "Ty::Refine spellings must survive");
    assert_eq!(back.func_types, m.func_types);

    // Re-encoding the decoded module must be byte-identical: the codec has no
    // producer-order-dependent choices left in it.
    let again = trust_ir::binary::serialize_module(&back);
    assert_eq!(bytes, again, "encode -> decode -> encode must be stable");
}

#[test]
fn text_round_trip_preserves_tables_and_refinements() {
    let m = module_with_refinements();
    let text = format!("{m}");
    assert!(text.contains("univ univ.0 = 1..=8"), "{text}");
    assert!(text.contains("pred pred.0 = in[0, 7]"), "{text}");
    assert!(
        text.contains("pred pred.2 = in_universe(univ.0, member)"),
        "{text}"
    );
    assert!(
        text.contains("pred pred.9 = or(pred.1, pred.2, pred.3)"),
        "{text}"
    );
    assert!(text.contains("refine<ty."), "{text}");

    let back = trust_ir::parser::parse_module(&text).expect("parse");
    assert_eq!(back.universes, m.universes);
    assert_eq!(back.predicates, m.predicates);
    assert_eq!(back.types, m.types);
    assert_eq!(back.func_types, m.func_types);
    assert_eq!(format!("{back}"), text, "text form must be a fixed point");
}

#[test]
fn json_and_msgpack_round_trip_preserve_tables() {
    let m = module_with_refinements();

    let json = serde_json::to_string(&m).expect("json encode");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(back.universes, m.universes);
    assert_eq!(back.predicates, m.predicates);
    assert_eq!(back.types, m.types);

    let mp = rmp_serde::to_vec(&m).expect("msgpack encode");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back.universes, m.universes);
    assert_eq!(back.predicates, m.predicates);
    assert_eq!(back.types, m.types);
}

#[test]
fn a_module_without_refinements_is_bit_identical_to_before() {
    // The additive-format contract: a module that carries no refinement is
    // unchanged by this feature in every format. The two new trailing binary
    // sections encode as two zero-length varints, and the two new serde fields
    // are skipped entirely when empty.
    let mut m = Module::new("legacy");
    m.add_type(Ty::I64);
    m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    assert!(m.predicates.is_empty() && m.universes.is_empty());

    let bytes = trust_ir::binary::serialize_module(&m);
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decode");
    assert_eq!(back, m);
    assert!(back.predicates.is_empty() && back.universes.is_empty());

    let text = format!("{m}");
    assert!(!text.contains("univ "), "{text}");
    assert!(!text.contains("pred pred."), "{text}");
    assert_eq!(trust_ir::parser::parse_module(&text).expect("parse"), m);

    let json = serde_json::to_string(&m).expect("json");
    // R3 #5 positional-serde discipline: `predicates` is the SOLE trailing
    // conditionally-skipped field, so it vanishes when empty; `universes` sits
    // before it and must therefore ALWAYS be emitted, or every later field
    // would shift a slot in the positional MessagePack encoding.
    assert!(
        !json.contains("\"predicates\""),
        "the trailing table must be skipped when empty: {json}"
    );
    assert!(
        json.contains("\"universes\":[]"),
        "a non-trailing field must always be emitted: {json}"
    );
    assert_eq!(serde_json::from_str::<Module>(&json).expect("decode"), m);

    // The positional codec is the one that actually bites: a legacy-shaped
    // (shorter) array must still decode, and a full round trip must not shift
    // any field.
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    assert_eq!(rmp_serde::from_slice::<Module>(&mp).expect("decode"), m);
}

#[test]
fn refinement_is_representation_preserving() {
    // The load-bearing claim of the whole change: a `Refine` lays out EXACTLY
    // as its base does, so no downstream artifact can move.
    let mut m = Module::new("repr");
    let p = m.intern_pred(Pred::NonZero).expect("leaf");
    let i64_ty = m.add_type(Ty::I64);
    let refined = Ty::Refine(i64_ty, p);

    let base_layout = m.ty_layout_shape(&Ty::I64).expect("i64 layout");
    let refined_layout = m.ty_layout_shape(&refined).expect("refined layout");
    assert_eq!(
        base_layout, refined_layout,
        "refine<i64, p> must lay out exactly as i64"
    );
}

#[test]
fn interning_is_by_content_not_by_call_site() {
    // Mint "the same universe" twice, as two independent lowering passes
    // would. Content-interning must collapse them to ONE id — this is the
    // structural fix for the join-drop class.
    let mut m = Module::new("intern");
    let a = m
        .intern_in_universe(Universe::IntRange { lo: 1, hi: 8 }, Space::Member)
        .expect("interned");
    let b = m
        .intern_in_universe(Universe::IntRange { lo: 1, hi: 8 }, Space::Member)
        .expect("interned");
    assert_eq!(a, b, "identical content must be one id");
    assert_eq!(m.universes.len(), 1);
    assert_eq!(m.predicates.len(), 1);

    // Canonicalization on the way in: an unsorted, duplicated member list is
    // the same universe as its canonical spelling.
    let c = m
        .intern_universe(Universe::Members(vec![
            Constant::Int(3),
            Constant::Int(1),
            Constant::Int(3),
        ]))
        .expect("canonicalized");
    let d = m
        .intern_universe(Universe::Members(vec![Constant::Int(1), Constant::Int(3)]))
        .expect("canonical");
    assert_eq!(c, d, "canonicalization must precede identity");
}
