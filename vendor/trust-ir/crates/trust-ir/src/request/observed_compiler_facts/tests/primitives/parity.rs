// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn all_six_primitive_constituents_match_actual_original_helpers() {
    let f = fixture();
    for mode in [
        Mode::Pointer,
        Mode::PointerValues,
        Mode::Cast,
        Mode::CastResult,
        Mode::Metadata,
        Mode::Upcast,
    ] {
        assert!(parity(&f, mode).is_empty());
    }
}

#[test]
fn pointer_type_stride_layout_provenance_and_obligation_errors_keep_original_order() {
    for change in 0..9 {
        let mut f = fixture();
        match change {
            0 => {
                f.functions.clear();
            }
            1 => f.pointer.base_ty = Ty::U32,
            2 => f.pointer.offset_ty = Ty::Usize,
            3 => f.pointer.element_layout.align_bits = None,
            4 => f.pointer.stride_bits = 33,
            5 => {
                f.pointer.provenance = NativePointerOffsetProvenance::Unsupported(
                    NativeUnsupportedMode::new(NativeUnsupportedModeReason::Other, " \u{2003}"),
                )
            }
            6 => f.pointer.obligations = vec![ProofId::new(8), ProofId::new(8)],
            7 => f.pointer.pointee_ty = Ty::Enum(EnumId::new(99)),
            _ => f.pointer.pointee_ty = Ty::Record(crate::RecordId::new(99)),
        }
        parity(&f, Mode::Pointer);
        parity(&f, Mode::PointerValues);
    }
}

#[test]
fn pointer_result_unique_node_type_base_and_exact_single_index_guards_match() {
    for change in 0..9 {
        let mut f = fixture();
        match change {
            0 => f.pointer.result = None,
            1 => f.pointer.result = Some(ValueId::new(99)),
            2 => {
                let node = f.module.functions[0].blocks[0].body[0].clone();
                f.module.functions[0].blocks[0].body.push(node);
            }
            3 => f.module.functions[0].blocks[0].body[0]
                .results
                .push(ValueId::new(2)),
            4 => {
                if let Inst::GEP { base, .. } = &mut f.module.functions[0].blocks[0].body[0].inst {
                    *base = ValueId::new(9);
                }
            }
            5 => {
                if let Inst::GEP { indices, .. } = &mut f.module.functions[0].blocks[0].body[0].inst
                {
                    indices.clear();
                }
            }
            6 => {
                if let Inst::GEP { indices, .. } = &mut f.module.functions[0].blocks[0].body[0].inst
                {
                    indices.push(ValueId::new(1));
                }
            }
            7 => {
                if let Inst::GEP { pointee_ty, .. } =
                    &mut f.module.functions[0].blocks[0].body[0].inst
                {
                    *pointee_ty = Ty::Char;
                }
            }
            _ => {
                f.module.functions.clear();
            }
        }
        parity(&f, Mode::PointerValues);
    }
}

#[test]
fn value_lookup_preserves_parameters_then_supported_node_and_block_order() {
    let mut f = fixture();
    f.module.functions[0].blocks[0].params.remove(0);
    f.module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Return { values: vec![] }).with_result(ValueId::new(0)),
    );
    f.module.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: ValueId::new(9),
        })
        .with_result(ValueId::new(0)),
    );
    assert!(parity(&f, Mode::PointerValues).is_empty());
    f.module.functions[0].blocks[0]
        .params
        .insert(0, (ValueId::new(0), Ty::U32));
    assert!(!parity(&f, Mode::PointerValues).is_empty());
}

#[test]
fn indexed_function_slot_preference_is_preserved_even_with_duplicate_ids() {
    let mut f = fixture();
    let mut first = f.module.functions[0].clone();
    first.id = FuncId::new(1);
    first.blocks[0].params[0].1 = Ty::U32;
    let mut indexed = f.module.functions[0].clone();
    indexed.id = FuncId::new(1);
    f.module.functions = vec![first, indexed];
    f.pointer.function = FuncId::new(1);
    assert!(parity(&f, Mode::PointerValues).is_empty());
}

#[test]
fn complete_owned_value_type_clone_and_equality_include_nested_inline_payloads() {
    let mut f = fixture();
    let ty = Ty::PtrConst(Box::new(Ty::Tuple(vec![
        Ty::Tuple(vec![Ty::U32, Ty::Char]),
        Ty::Vector(Box::new(Ty::Bool), 3),
    ])));
    f.pointer.base_ty = ty.clone();
    f.module.functions[0].blocks[0].params[0].1 = ty;
    assert!(parity(&f, Mode::PointerValues).is_empty());
    f.pointer.base_ty = Ty::PtrConst(Box::new(Ty::Tuple(vec![
        Ty::Tuple(vec![Ty::U32, Ty::U32]),
        Ty::Vector(Box::new(Ty::Bool), 3),
    ])));
    assert!(!parity(&f, Mode::PointerValues).is_empty());
}

#[test]
fn native_instruction_result_type_branches_match_original_actual_type_outputs() {
    let complex = Ty::Tuple(vec![Ty::Vector(Box::new(Ty::U32), 2), Ty::Char]);
    let instructions = vec![
        Inst::Undef {
            ty: complex.clone(),
        },
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U32,
            dst_ty: complex.clone(),
            operand: ValueId::new(0),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::Vector(Box::new(complex.clone()), 0),
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: complex,
            ptr: ValueId::new(0),
        },
        Inst::NullPtr,
        Inst::Return { values: vec![] },
    ];
    for inst in instructions {
        let expected = crate::request::native_inst_result_ty(&inst);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let actual = values::inst_type(&inst, &mut session, site()).unwrap();
        assert_eq!(actual, expected);
        if let Some(actual) = actual {
            actual.retire_observed(&mut session, site()).unwrap();
        }
    }
}

#[test]
fn cast_result_optional_function_duplicate_node_op_and_exact_type_checks_match() {
    for change in 0..8 {
        let mut f = fixture();
        match change {
            0 => f.cast.result = None,
            1 => f.cast.result = Some(ValueId::new(99)),
            2 => {
                f.module.functions.clear();
            }
            3 => {
                let node = f.module.functions[0].blocks[0].body[1].clone();
                f.module.functions[0].blocks[0].body.push(node);
            }
            4 => f.module.functions[0].blocks[0].body[1]
                .results
                .push(ValueId::new(4)),
            5 => f.cast.op = CastOp::Transmute,
            6 => f.cast.source_ty = Ty::Char,
            _ => f.cast.target_ty = Ty::Char,
        }
        parity(&f, Mode::CastResult);
        parity(&f, Mode::Cast);
    }
}

#[test]
fn nonsensitive_cast_evidence_keeps_both_original_duplicate_diagnostics() {
    let mut f = fixture();
    f.cast.op = CastOp::ZExt;
    if let Inst::Cast { op, .. } = &mut f.module.functions[0].blocks[0].body[1].inst {
        *op = CastOp::ZExt;
    }
    let errors = parity(&f, Mode::Cast);
    assert_eq!(
        errors
            .iter()
            .filter(|error| matches!(
                error,
                E::InvalidCompilerFact {
                    field: "evidence",
                    ..
                }
            ))
            .count(),
        2
    );
}

#[test]
fn cast_layout_refusals_and_unknown_id_membership_keep_original_diagnostics() {
    for change in 0..7 {
        let mut f = fixture();
        match change {
            0 => {
                f.functions.clear();
            }
            1 => f.cast.obligations = vec![ProofId::new(8), ProofId::new(8)],
            2 => f.cast.target_ty = Ty::U64,
            3 => f.cast.target_ty = Ty::Bool,
            4 => f.cast.target_ty = Ty::Enum(EnumId::new(99)),
            5 => f.cast.target_ty = Ty::Record(crate::RecordId::new(99)),
            _ => f.cast.evidence = CastLayoutEvidence::NotLayoutSensitive,
        }
        parity(&f, Mode::Cast);
    }
}

#[test]
fn metadata_digest_symbol_type_id_function_and_obligation_errors_match_in_order() {
    for change in 0..9 {
        let mut f = fixture();
        match change {
            0 => f.metadata.ty = Ty::Ptr,
            1 => f.metadata.trait_id = 10,
            2 => f.metadata.vtable_symbol = "\u{2003}".repeat(1200),
            3 => f.metadata.stable_digest = ProofDigest::zero(),
            4 => f.metadata.stable_digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1,
            5 => f.metadata.function = Some(FuncId::new(99)),
            6 => f.metadata.obligations = vec![ProofId::new(9), ProofId::new(9)],
            7 => f.metadata.function = None,
            _ => f.metadata.vtable_symbol = "\u{200b}".into(),
        }
        parity(&f, Mode::Metadata);
    }
}

#[test]
fn upcast_source_pair_path_endpoint_and_unconstrained_interior_cases_match() {
    for change in 0..9 {
        let mut f = fixture();
        match change {
            0 => {
                f.metadata.source_ty = None;
                f.metadata.source_trait_id = None;
                f.metadata.upcast_path.clear();
            }
            1 => f.metadata.source_ty = None,
            2 => f.metadata.source_trait_id = None,
            3 => f.metadata.source_ty = Some(Ty::Ptr),
            4 => f.metadata.source_trait_id = Some(9),
            5 => f.metadata.upcast_path.clear(),
            6 => f.metadata.upcast_path[0] = 7,
            7 => f.metadata.upcast_path[1] = 10,
            _ => f.metadata.upcast_path = vec![8, 999, 8, 9],
        }
        parity(&f, Mode::Upcast);
        parity(&f, Mode::Metadata);
    }
}

#[test]
fn every_layout_kind_and_variable_field_name_matches_the_original_layout_equality() {
    let field = FieldOffsetShape {
        field: 1,
        name: "\u{3bb}".repeat(3000),
        ty_shape: TyShape::Bool,
        offset_bits: Some(8),
    };
    let kinds = vec![
        TyLayoutKind::Scalar(TyShape::Int {
            signed: true,
            bits: 32,
        }),
        TyLayoutKind::ThinPointer,
        TyLayoutKind::FatPointer(PointerMetadataShape::VTable { trait_id: 9 }),
        TyLayoutKind::Struct {
            id: StructId::new(9),
            fields: vec![field.clone()],
        },
        TyLayoutKind::Enum {
            id: EnumId::new(7),
            variants: 2,
        },
        TyLayoutKind::Array {
            elem: TyId::new(3),
            len: 9,
            stride_bits: 32,
        },
        TyLayoutKind::Vector {
            elem_shape: TyShape::Bool,
            lanes: 4,
            lane_bits: 8,
        },
        TyLayoutKind::Unit,
        TyLayoutKind::Never,
        TyLayoutKind::Tuple {
            fields: vec![field.clone()],
        },
        TyLayoutKind::Closure {
            id: crate::ClosureTyId::new(2),
            captures: vec![field],
        },
    ];
    let layouts: Vec<_> = kinds
        .into_iter()
        .map(|kind| TyLayoutShape {
            size_bits: 64,
            align_bits: Some(32),
            kind,
        })
        .collect();
    for left in &layouts {
        for right in &layouts {
            let mut observer = Observer::default();
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                layout_equal(left, right, &mut session, site()).unwrap(),
                left == right
            );
        }
    }
    let mut changed = layouts[3].clone();
    if let TyLayoutKind::Struct { fields, .. } = &mut changed.kind {
        fields[0].name.push('x');
    }
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(!layout_equal(&layouts[3], &changed, &mut session, site()).unwrap());
}
