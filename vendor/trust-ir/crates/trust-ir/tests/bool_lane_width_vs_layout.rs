// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `bool` is one BIT of value in one BYTE of storage, and TrustIr carries that
// as two different questions with two different answers:
//
//   * `Ty::bit_width` — the VALUE width. `Bool` is 1, a vector is
//     lanes × element, so `<8 x bool>` is 8. This mirrors the Lean model's
//     `Ty.bitWidth` exactly (`lean/trust_ir-semantics/TrustIr/Basic.lean`,
//     "Mirrors Rust Ty::bit_width": `.Bool => some 1`,
//     `.Vector lanes elemTy => lanes * elemWidth`), and it is the width the
//     reference interpreter's `Bitcast` compares.
//   * `Module::ty_layout_shape` — the STORAGE size. `Bool` is one byte, so
//     `<8 x bool>` is 64 bits. This mirrors the Lean `Ty.byteSize .Bool =
//     some 1` and `encodeValue (.bool b) = [b]` (`Semantics/Memory.lean`) for
//     the scalar; for a vector the Lean model has no byte image at all
//     (`Ty.byteSize` and `encodeValue .vector` are both `none`: "Vectors stay
//     in SSA for this first executable path"), and the normative reference
//     interpreter (`docs/SPEC_RATIFICATIONS.md` §4) fixes it — `byte_size` is
//     lanes × 1 byte and the byte image is all-ones per true lane
//     (`crates/trust-ir/src/interpret.rs`,
//     `vector_bool_mask_reinterprets_as_all_ones_per_lane`).
//
// A trust-cg session measured the two answers for `<8 x bool>` (8 and 64) and
// read the 8× as the two validator paths disagreeing. They do not: each is
// the spec's answer to its own question, and the ratio is exactly the bits
// in a byte — it is the SAME 8× that scalar `bool` carries (1 vs 8). What the
// measurement does expose is that `bool` is the ONLY element type for which
// the two numbers differ, so no consumer may use one as the other for a
// bool-bearing type. The one that did was the `Bitcast` / `Transmute` lane:
// see `bool_lane_bitcast_refusal.rs` in `trust-ir-build` for the refusal.
//
// This file pins both numbers, for scalar `bool` and for `<n x bool>` at
// every lane count the format's mask contracts use, and pins that every
// other scalar and vector element type agrees between the two.

use trust_ir::ty::{FieldDef, StructDef, StructRepr, Ty};
use trust_ir::value::StructId;
use trust_ir::{CastLayoutEvidence, CastOp, DEFAULT_POINTER_BITS, LayoutError, Module};

fn v_bool(lanes: u32) -> Ty {
    Ty::Vector(Box::new(Ty::Bool), lanes)
}

/// Scalar `bool`: 1 bit of value, 8 bits (one byte) of storage.
#[test]
fn scalar_bool_is_one_bit_of_value_in_one_byte_of_storage() {
    let module = Module::new("bool_scalar");
    assert_eq!(Ty::Bool.bit_width(), Some(1), "Ty::bit_width(bool)");
    assert_eq!(
        Ty::Bool.bit_width_with(DEFAULT_POINTER_BITS),
        Some(1),
        "Ty::bit_width_with(bool)"
    );
    let layout = module
        .ty_layout_shape(&Ty::Bool)
        .expect("bool has a layout");
    assert_eq!(layout.size_bits, 8, "ty_layout_shape(bool).size_bits");
    assert_eq!(
        layout.size_bytes(),
        Some(1),
        "ty_layout_shape(bool).size_bytes"
    );
}

/// `<n x bool>`: n bits of value, 8n bits (n bytes) of storage — the
/// measured pair for `<8 x bool>` is (8, 64).
#[test]
fn bool_vector_value_width_is_lanes_and_storage_is_lanes_bytes() {
    let module = Module::new("bool_vectors");
    for lanes in [1u32, 2, 4, 8, 16, 32, 64] {
        let ty = v_bool(lanes);
        let width = ty.bit_width().expect("a bool vector has a value width");
        let layout = module
            .ty_layout_shape(&ty)
            .expect("a bool vector has a layout");
        assert_eq!(width, lanes, "bit_width({ty}) is one bit per lane");
        assert_eq!(
            layout.size_bits,
            u64::from(lanes) * 8,
            "ty_layout_shape({ty}).size_bits is one byte per lane"
        );
        assert_eq!(
            layout.size_bits / u64::from(width),
            8,
            "the ratio between the two answers for {ty} is exactly bits-per-byte"
        );
        assert_eq!(
            ty.bit_width_with(DEFAULT_POINTER_BITS),
            Some(width),
            "bit_width_with agrees with bit_width for {ty}"
        );
    }

    // The pair the trust-cg session measured, quoted as numbers.
    let v8 = v_bool(8);
    assert_eq!(v8.bit_width(), Some(8));
    assert_eq!(module.ty_layout_shape(&v8).unwrap().size_bits, 64);
}

/// `bool` is the ONLY element type for which value width and storage size
/// differ. For every other scalar the format lays out, and for vectors of
/// them, `bit_width_with(64)` IS `ty_layout_shape().size_bits` on the
/// canonical 64-bit reference layout.
#[test]
fn every_non_bool_scalar_and_vector_agrees_between_value_width_and_storage() {
    let module = Module::new("agreement");
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
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Char,
        Ty::Isize,
        Ty::Usize,
        Ty::Ptr,
        Ty::PtrConst(Box::new(Ty::U8)),
        Ty::Ref(Box::new(Ty::U8)),
    ];
    for scalar in &scalars {
        for ty in [
            scalar.clone(),
            Ty::Vector(Box::new(scalar.clone()), 2),
            Ty::Vector(Box::new(scalar.clone()), 4),
        ] {
            let width = ty
                .bit_width_with(DEFAULT_POINTER_BITS)
                .unwrap_or_else(|| panic!("{ty} has a value width at 64-bit pointers"));
            let layout = module
                .ty_layout_shape(&ty)
                .unwrap_or_else(|e| panic!("{ty} has a layout: {e}"));
            assert_eq!(
                u64::from(width),
                layout.size_bits,
                "{ty}: value width and storage size agree"
            );
        }
    }

    // And the divergence really is the bool lane, wherever it nests.
    let nested = Ty::Vector(Box::new(v_bool(4)), 2);
    assert_eq!(nested.bit_width(), Some(8));
    assert_eq!(module.ty_layout_shape(&nested).unwrap().size_bits, 64);
}

/// The layout authority (`Module::layout_sensitive_cast_evidence`, what the
/// module-level cast pass and the request digest consult) refuses a
/// reinterpret with a bool lane stored by value on either side BY NAME,
/// before any width is compared — including the two casts the two same-size
/// tests used to admit between them — and follows by-value table references
/// exactly as the layout walk does.
#[test]
fn the_layout_authority_refuses_a_bool_lane_reinterpret_by_name() {
    let mut module = Module::new("bool_lane_casts");
    let v8 = v_bool(8);
    let v8_id = module
        .add_type(v8.clone())
        .expect("Module::add_type: test fixture");
    let mask_struct = module.add_struct(StructDef {
        id: StructId(0),
        name: "mask".into(),
        fields: vec![FieldDef {
            name: "m".into(),
            ty: v8.clone(),
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    let refused = [
        // The structural width test said 8 == 8 for this one ...
        (CastOp::Bitcast, v8.clone(), Ty::U8),
        // ... and the storage size test said 64 == 64 for this one.
        (CastOp::Bitcast, v8.clone(), Ty::U64),
        (CastOp::Bitcast, Ty::U64, v8.clone()),
        (CastOp::Bitcast, Ty::Bool, Ty::U8),
        (CastOp::Transmute, v8.clone(), Ty::U64),
        (CastOp::Bitcast, Ty::Vector(Box::new(v_bool(4)), 2), Ty::U64),
        (CastOp::Bitcast, Ty::Array(v8_id, 2), Ty::U128),
        (CastOp::Bitcast, Ty::Struct(mask_struct), Ty::U64),
    ];
    for (op, src, dst) in refused {
        let evidence = module.layout_sensitive_cast_evidence(op, &src, &dst);
        assert!(
            matches!(evidence, Err(LayoutError::BoolLaneReinterpret { .. })),
            "{op} {src} -> {dst}: expected BoolLaneReinterpret, got {evidence:?}"
        );
        let text = evidence.unwrap_err().to_string();
        assert!(
            text.contains("a bool lane is one bit of value in one byte of storage"),
            "{op} {src} -> {dst}: the refusal must say why: {text}"
        );
    }
}

/// The identity cast is not a reinterpretation, a pointer TO a bool lane is
/// an address, and no non-bool reinterpret changed.
#[test]
fn the_layout_authority_still_admits_identity_pointer_and_non_bool_reinterprets() {
    let module = Module::new("controls");
    let v8 = v_bool(8);
    let same_size = |op: CastOp, src: &Ty, dst: &Ty, bits: u64| {
        let evidence = module.layout_sensitive_cast_evidence(op, src, dst);
        assert!(
            matches!(evidence, Ok(CastLayoutEvidence::SameSize { size_bits, .. }) if size_bits == bits),
            "{op} {src} -> {dst}: expected SameSize {bits}, got {evidence:?}"
        );
    };
    same_size(CastOp::Bitcast, &v8, &v8, 64);
    same_size(
        CastOp::Bitcast,
        &Ty::PtrConst(Box::new(v8.clone())),
        &Ty::U64,
        64,
    );
    same_size(CastOp::Bitcast, &Ty::v4_i32(), &Ty::v2_i64(), 128);
    same_size(CastOp::Bitcast, &Ty::U64, &Ty::F64, 64);

    // The by-value walk: a bool lane behind a pointer is not stored by the
    // pointer; one inside a tuple is stored by the tuple.
    assert!(!module.type_stores_bool_lane(&Ty::Ref(Box::new(v8))));
    assert!(module.type_stores_bool_lane(&Ty::Tuple(vec![Ty::U8, v_bool(2)])));
    assert!(!module.type_stores_bool_lane(&Ty::Vector(Box::new(Ty::U8), 8)));
    assert!(Ty::Vector(Box::new(v_bool(4)), 2).has_bool_lanes());
    assert!(!Ty::PtrConst(Box::new(v_bool(4))).has_bool_lanes());
}
