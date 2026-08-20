// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable-digest byte writers for the native verification request/bundle schema.
//!
//! # The three serializations are deliberate, and unifying them is infeasible (audit #103)
//!
//! The request module carries the same logical data in THREE distinct wire
//! forms, each a separate cross-repo contract: this binary stable-digest
//! (`write_*_stable`), the `key=value` text (`*_rows` / `key_value_lines`), and
//! the hand-rolled JSON (`*_json_text`). The audit suggested collapsing them via
//! a single `Canonicalize` trait. That is **byte-infeasible**: the three formats
//! use different escaping, field ordering, and value representation, so one
//! encoder cannot reproduce all three byte streams — and any drift breaks the
//! frozen digest/wire contract ty/ay/TrustCg pin. (The digest-critical
//! width-distinct primitives — `write_u32`/`u64`/`i128_stable` differ only by
//! `to_le_bytes()` width — likewise cannot be merged without corrupting digests.)
//!
//! The maintenance risk the audit cited — changing one serializer and forgetting
//! another — is already GUARDED, not by unification but by the conformance
//! byte-golden corpus: `native_request_bundle_corpus_roundtrip` /
//! `proof_lineage_corpus_roundtrip` byte-check the binary, text, JSON, and
//! MessagePack encodings of every fixture, so a change to any one serializer
//! that is not mirrored in the others fails a golden. Three encoders, one
//! drift gate.

use super::*;

pub(crate) fn write_u8_stable(out: &mut Vec<u8>, value: u8) {
    out.push(value);
}

pub(crate) fn write_bool_stable(out: &mut Vec<u8>, value: bool) {
    write_u8_stable(out, u8::from(value));
}

pub(crate) fn write_u32_stable(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_u64_stable(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_len_stable(out: &mut Vec<u8>, value: usize) {
    write_u64_stable(
        out,
        u64::try_from(value).expect("identity length exceeds canonical u64 framing"),
    );
}

pub(crate) fn write_u128_stable(out: &mut Vec<u8>, value: u128) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_i128_stable(out: &mut Vec<u8>, value: i128) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_str_stable(out: &mut Vec<u8>, value: &str) {
    write_len_stable(out, value.len());
    out.extend_from_slice(value.as_bytes());
}

pub(crate) fn write_option_str_stable(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_str_stable(out, value);
        }
    }
}

pub(crate) fn write_option_u32_stable(out: &mut Vec<u8>, value: Option<u32>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, value);
        }
    }
}

pub(crate) fn write_option_u64_stable(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_u64_stable(out, value);
        }
    }
}

pub(crate) fn write_option_i128_stable(out: &mut Vec<u8>, value: Option<i128>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_i128_stable(out, value);
        }
    }
}

pub(crate) fn write_option_proof_status_stable(out: &mut Vec<u8>, value: Option<ProofStatus>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_proof_status_stable(out, value);
        }
    }
}

pub(crate) fn write_option_digest_stable(out: &mut Vec<u8>, value: Option<ProofDigest>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_digest_stable(out, &value);
        }
    }
}

pub(crate) fn write_digest_stable(out: &mut Vec<u8>, digest: &ProofDigest) {
    let algorithm = match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    };
    write_u8_stable(out, algorithm);
    out.extend_from_slice(&digest.bytes);
}

pub(crate) fn write_endianness_stable(out: &mut Vec<u8>, endianness: Endianness) {
    write_u8_stable(
        out,
        match endianness {
            Endianness::Little => 0,
            Endianness::Big => 1,
        },
    );
}

pub(crate) fn write_target_abi_identity_stable(
    out: &mut Vec<u8>,
    target_abi: &NativeTargetAbiIdentity,
) {
    write_str_stable(out, &target_abi.triple);
    write_u32_stable(out, target_abi.pointer_size);
    write_endianness_stable(out, target_abi.endianness);
    write_digest_stable(out, &target_abi.digest);
}

pub(crate) fn write_source_span_stable(out: &mut Vec<u8>, span: &SourceSpan) {
    write_u32_stable(out, span.file);
    write_u32_stable(out, span.line);
    write_u32_stable(out, span.col);
}

pub(crate) fn write_option_source_span_stable(out: &mut Vec<u8>, span: Option<SourceSpan>) {
    match span {
        None => write_u8_stable(out, 0),
        Some(span) => {
            write_u8_stable(out, 1);
            write_source_span_stable(out, &span);
        }
    }
}

pub(crate) fn write_option_assertion_id_stable(
    out: &mut Vec<u8>,
    assertion_id: Option<NativeAssertionId>,
) {
    match assertion_id {
        None => write_u8_stable(out, 0),
        Some(assertion_id) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, assertion_id.index());
        }
    }
}

pub(crate) fn write_set_repr_stable(out: &mut Vec<u8>, repr: SetRepr) {
    write_u8_stable(
        out,
        match repr {
            SetRepr::Bitset => 0,
            SetRepr::Boxed => 1,
        },
    );
}

pub(crate) fn write_fat_ptr_kind_stable(out: &mut Vec<u8>, kind: &crate::FatPtrKind) {
    match *kind {
        crate::FatPtrKind::Slice(elem) => {
            write_u8_stable(out, 0);
            write_u32_stable(out, elem.index());
        }
        crate::FatPtrKind::Str => write_u8_stable(out, 1),
        crate::FatPtrKind::TraitObject { trait_id } => {
            write_u8_stable(out, 2);
            write_u32_stable(out, trait_id);
        }
    }
}

pub(crate) fn write_ty_id_stable(out: &mut Vec<u8>, id: TyId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_struct_id_stable(out: &mut Vec<u8>, id: StructId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_enum_id_stable(out: &mut Vec<u8>, id: EnumId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_func_ty_id_stable(out: &mut Vec<u8>, id: FuncTyId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_record_id_stable(out: &mut Vec<u8>, id: RecordId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_closure_ty_id_stable(out: &mut Vec<u8>, id: ClosureTyId) {
    write_u32_stable(out, id.index());
}

pub(crate) fn write_ty_stable(out: &mut Vec<u8>, ty: &Ty) {
    match ty {
        Ty::I8 => write_u8_stable(out, 0),
        Ty::I16 => write_u8_stable(out, 1),
        Ty::I32 => write_u8_stable(out, 2),
        Ty::I64 => write_u8_stable(out, 3),
        Ty::I128 => write_u8_stable(out, 4),
        Ty::U8 => write_u8_stable(out, 5),
        Ty::U16 => write_u8_stable(out, 6),
        Ty::U32 => write_u8_stable(out, 7),
        Ty::U64 => write_u8_stable(out, 8),
        Ty::U128 => write_u8_stable(out, 9),
        // v25 B1 scalars (stable tags match the binary codec's 33-35).
        Ty::Isize => write_u8_stable(out, 33),
        Ty::Usize => write_u8_stable(out, 34),
        Ty::Char => write_u8_stable(out, 35),
        // Producer-internal typing placeholder: an obligation digest over a
        // module carrying Ty::Error would hash a typing hole - fail closed.
        Ty::Error => {
            panic!("Ty::Error is producer-internal and never reaches the obligation digest")
        }
        Ty::F16 => write_u8_stable(out, 31),
        Ty::F32 => write_u8_stable(out, 10),
        Ty::F64 => write_u8_stable(out, 11),
        Ty::Bool => write_u8_stable(out, 12),
        Ty::Ptr => write_u8_stable(out, 13),
        Ty::FatPtr(kind) => {
            write_u8_stable(out, 14);
            write_fat_ptr_kind_stable(out, kind);
        }
        Ty::Unit => write_u8_stable(out, 15),
        Ty::Never => write_u8_stable(out, 16),
        Ty::Struct(id) => {
            write_u8_stable(out, 17);
            write_struct_id_stable(out, *id);
        }
        Ty::Array(elem, len) => {
            write_u8_stable(out, 18);
            write_ty_id_stable(out, *elem);
            write_u64_stable(out, *len);
        }
        Ty::Tuple(elems) => {
            write_u8_stable(out, 19);
            write_len_stable(out, elems.len());
            for elem in elems {
                write_ty_stable(out, elem);
            }
        }
        Ty::Enum(id) => {
            write_u8_stable(out, 20);
            write_enum_id_stable(out, *id);
        }
        Ty::Func(id) => {
            write_u8_stable(out, 21);
            write_func_ty_id_stable(out, *id);
        }
        Ty::Ref(inner) => {
            write_u8_stable(out, 22);
            write_ty_stable(out, inner);
        }
        Ty::RefMut(inner) => {
            write_u8_stable(out, 23);
            write_ty_stable(out, inner);
        }
        Ty::PtrConst(inner) => {
            write_u8_stable(out, 24);
            write_ty_stable(out, inner);
        }
        Ty::PtrMut(inner) => {
            write_u8_stable(out, 25);
            write_ty_stable(out, inner);
        }
        Ty::Rc(inner) => {
            write_u8_stable(out, 26);
            write_ty_stable(out, inner);
        }
        Ty::Set(elem, repr) => {
            write_u8_stable(out, 27);
            write_ty_id_stable(out, *elem);
            write_set_repr_stable(out, *repr);
        }
        Ty::Sequence(elem) => {
            write_u8_stable(out, 28);
            write_ty_id_stable(out, *elem);
        }
        Ty::Record(id) => {
            write_u8_stable(out, 29);
            write_record_id_stable(out, *id);
        }
        Ty::Closure(id) => {
            write_u8_stable(out, 30);
            write_closure_ty_id_stable(out, *id);
        }
        // Stable tag 33 (next free after the v25 vector tag 32).
        Ty::Refine(base, pred) => {
            write_u8_stable(out, 33);
            write_ty_id_stable(out, *base);
            write_u32_stable(out, pred.index());
        }
        Ty::Vector(elem, lanes) => {
            write_u8_stable(out, 32);
            write_u32_stable(out, *lanes);
            write_ty_stable(out, elem);
        }
    }
}

pub(crate) fn write_constant_stable(out: &mut Vec<u8>, constant: &Constant) {
    match constant {
        Constant::Int(value) => {
            write_u8_stable(out, 0);
            write_i128_stable(out, *value);
        }
        // v24 U128: stable tag 13 (next free; matches the binary codec's tag).
        Constant::U128(value) => {
            write_u8_stable(out, 13);
            write_u128_stable(out, *value);
        }
        // v25 Bytes: stable tag 14 (matches the binary codec's tag).
        Constant::Bytes { data, utf8 } => {
            write_u8_stable(out, 14);
            write_bool_stable(out, *utf8);
            write_len_stable(out, data.len());
            out.extend_from_slice(data);
        }
        Constant::Float(value) => {
            write_u8_stable(out, 1);
            write_u64_stable(out, value.to_bits());
        }
        Constant::Bool(value) => {
            write_u8_stable(out, 2);
            write_bool_stable(out, *value);
        }
        Constant::Aggregate(values) => {
            write_u8_stable(out, 3);
            write_constants_stable(out, values);
        }
        Constant::Array(values) => {
            write_u8_stable(out, 4);
            write_constants_stable(out, values);
        }
        Constant::Vector(values) => {
            write_u8_stable(out, 11);
            write_constants_stable(out, values);
        }
        Constant::Sequence(values) => {
            write_u8_stable(out, 5);
            write_constants_stable(out, values);
        }
        Constant::Set(values) => {
            write_u8_stable(out, 6);
            write_constants_stable(out, values);
        }
        Constant::Record(fields) => {
            write_u8_stable(out, 7);
            write_len_stable(out, fields.len());
            for (name, value) in fields {
                write_str_stable(out, name);
                write_constant_stable(out, value);
            }
        }
        Constant::Closure { func, captures } => {
            write_u8_stable(out, 8);
            write_u32_stable(out, func.index());
            write_constants_stable(out, captures);
        }
        Constant::FnDef(func) => {
            write_u8_stable(out, 9);
            write_u32_stable(out, func.index());
        }
        Constant::SymbolAddr { symbol, addend } => {
            write_u8_stable(out, 12);
            write_str_stable(out, symbol);
            write_u64_stable(out, *addend as u64);
        }
        Constant::PhantomData => write_u8_stable(out, 10),
    }
}

pub(crate) fn write_constants_stable(out: &mut Vec<u8>, constants: &[Constant]) {
    write_len_stable(out, constants.len());
    for constant in constants {
        write_constant_stable(out, constant);
    }
}

pub(crate) fn write_ty_shape_stable(out: &mut Vec<u8>, shape: TyShape) {
    match shape {
        TyShape::Int { signed, bits } => {
            write_u8_stable(out, 0);
            write_bool_stable(out, signed);
            write_u32_stable(out, bits);
        }
        TyShape::Float { bits } => {
            write_u8_stable(out, 1);
            write_u32_stable(out, bits);
        }
        TyShape::Bool => write_u8_stable(out, 2),
        TyShape::ThinPointer => write_u8_stable(out, 3),
        TyShape::FatPointer => write_u8_stable(out, 4),
        TyShape::Unit => write_u8_stable(out, 5),
        TyShape::Never => write_u8_stable(out, 6),
        TyShape::Struct => write_u8_stable(out, 7),
        TyShape::Array => write_u8_stable(out, 8),
        TyShape::Tuple => write_u8_stable(out, 9),
        TyShape::Enum => write_u8_stable(out, 10),
        TyShape::Function => write_u8_stable(out, 11),
        TyShape::Ref => write_u8_stable(out, 12),
        TyShape::RefMut => write_u8_stable(out, 13),
        TyShape::PtrConst => write_u8_stable(out, 14),
        TyShape::PtrMut => write_u8_stable(out, 15),
        TyShape::Rc => write_u8_stable(out, 16),
        TyShape::Set => write_u8_stable(out, 17),
        TyShape::Sequence => write_u8_stable(out, 18),
        TyShape::Record => write_u8_stable(out, 19),
        TyShape::Closure => write_u8_stable(out, 20),
        TyShape::Vector => write_u8_stable(out, 21),
        // v25: pointer-width integer + error shapes.
        TyShape::PointerInt { signed } => {
            write_u8_stable(out, 22);
            write_bool_stable(out, signed);
        }
        TyShape::Error => write_u8_stable(out, 23),
        // v30: refinement shape (representation-preserving; the base type's
        // own shape is digested wherever the base is reachable).
        TyShape::Refine => write_u8_stable(out, 24),
    }
}

pub(crate) fn write_pointer_metadata_shape_stable(
    out: &mut Vec<u8>,
    metadata: PointerMetadataShape,
) {
    match metadata {
        PointerMetadataShape::SliceLen { elem } => {
            write_u8_stable(out, 0);
            write_ty_id_stable(out, elem);
        }
        PointerMetadataShape::StrLen => write_u8_stable(out, 1),
        PointerMetadataShape::VTable { trait_id } => {
            write_u8_stable(out, 2);
            write_u32_stable(out, trait_id);
        }
    }
}

pub(crate) fn write_option_pointer_metadata_shape_stable(
    out: &mut Vec<u8>,
    metadata: Option<PointerMetadataShape>,
) {
    match metadata {
        None => write_u8_stable(out, 0),
        Some(metadata) => {
            write_u8_stable(out, 1);
            write_pointer_metadata_shape_stable(out, metadata);
        }
    }
}

pub(crate) fn write_pointer_layout_shape_stable(out: &mut Vec<u8>, layout: PointerLayoutShape) {
    write_u32_stable(out, layout.data_bits);
    write_option_u32_stable(out, layout.metadata_bits);
    write_option_pointer_metadata_shape_stable(out, layout.metadata);
}

pub(crate) fn write_field_offset_shape_stable(out: &mut Vec<u8>, field: &FieldOffsetShape) {
    write_u32_stable(out, field.field);
    write_str_stable(out, &field.name);
    write_ty_shape_stable(out, field.ty_shape);
    write_option_u64_stable(out, field.offset_bits);
}

pub(crate) fn write_ty_layout_kind_stable(out: &mut Vec<u8>, kind: &TyLayoutKind) {
    match kind {
        TyLayoutKind::Scalar(shape) => {
            write_u8_stable(out, 0);
            write_ty_shape_stable(out, *shape);
        }
        TyLayoutKind::ThinPointer => write_u8_stable(out, 1),
        TyLayoutKind::FatPointer(metadata) => {
            write_u8_stable(out, 2);
            write_pointer_metadata_shape_stable(out, *metadata);
        }
        TyLayoutKind::Struct { id, fields } => {
            write_u8_stable(out, 3);
            write_struct_id_stable(out, *id);
            write_len_stable(out, fields.len());
            for field in fields {
                write_field_offset_shape_stable(out, field);
            }
        }
        TyLayoutKind::Enum { id, variants } => {
            write_u8_stable(out, 4);
            write_enum_id_stable(out, *id);
            write_u64_stable(out, *variants as u64);
        }
        TyLayoutKind::Array {
            elem,
            len,
            stride_bits,
        } => {
            write_u8_stable(out, 5);
            write_ty_id_stable(out, *elem);
            write_u64_stable(out, *len);
            write_u64_stable(out, *stride_bits);
        }
        TyLayoutKind::Unit => write_u8_stable(out, 6),
        TyLayoutKind::Never => write_u8_stable(out, 7),
        TyLayoutKind::Vector {
            elem_shape,
            lanes,
            lane_bits,
        } => {
            write_u8_stable(out, 8);
            write_ty_shape_stable(out, *elem_shape);
            write_u32_stable(out, *lanes);
            write_u64_stable(out, *lane_bits);
        }
    }
}

pub(crate) fn write_ty_layout_shape_stable(out: &mut Vec<u8>, layout: &TyLayoutShape) {
    write_u64_stable(out, layout.size_bits);
    write_option_u64_stable(out, layout.align_bits);
    write_ty_layout_kind_stable(out, &layout.kind);
}

pub(crate) fn write_cast_layout_evidence_stable(out: &mut Vec<u8>, evidence: &CastLayoutEvidence) {
    match evidence {
        CastLayoutEvidence::NotLayoutSensitive => write_u8_stable(out, 0),
        CastLayoutEvidence::PointerCast { src, dst } => {
            write_u8_stable(out, 1);
            write_pointer_layout_shape_stable(out, *src);
            write_pointer_layout_shape_stable(out, *dst);
        }
        CastLayoutEvidence::SameSize {
            size_bits,
            src_align_bits,
            dst_align_bits,
        } => {
            write_u8_stable(out, 2);
            write_u64_stable(out, *size_bits);
            write_option_u64_stable(out, *src_align_bits);
            write_option_u64_stable(out, *dst_align_bits);
        }
        CastLayoutEvidence::ReifyFnPointer { pointer_bits } => {
            write_u8_stable(out, 3);
            write_u32_stable(out, *pointer_bits);
        }
    }
}

pub(crate) fn write_obligation_kind_stable(out: &mut Vec<u8>, kind: &ObligationKind) {
    write_u8_stable(
        out,
        match kind {
            ObligationKind::Precondition => 0,
            ObligationKind::Postcondition => 1,
            ObligationKind::LoopInvariant => 2,
            ObligationKind::TypeInvariant => 3,
            ObligationKind::RefinementType => 4,
            ObligationKind::TranslationValidation => 5,
            ObligationKind::MemorySafety => 6,
            ObligationKind::PanicFreedom => 7,
            ObligationKind::TemporalSafety => 8,
            ObligationKind::Liveness => 9,
            ObligationKind::ArithmeticSafety => 10,
            ObligationKind::BoundsCheck => 11,
            ObligationKind::GiveBackRefinement => 12,
        },
    );
}

pub(crate) fn write_proof_status_stable(out: &mut Vec<u8>, status: ProofStatus) {
    write_u8_stable(
        out,
        match status {
            ProofStatus::Pending => 0,
            ProofStatus::Discharged => 1,
            ProofStatus::Failed => 2,
            ProofStatus::Trusted => 3,
            ProofStatus::Certified => 4,
        },
    );
}

pub(crate) fn write_bundle_producer_stable(out: &mut Vec<u8>, producer: NativeBundleProducer) {
    write_u8_stable(
        out,
        match producer {
            NativeBundleProducer::TRust => 0,
            NativeBundleProducer::TSwift => 1,
            NativeBundleProducer::TC => 2,
            NativeBundleProducer::TrustIr => 3,
        },
    );
}

pub(crate) fn write_semantic_relation_kind_stable(
    out: &mut Vec<u8>,
    relation: NativeSemanticRelationKind,
) {
    write_u8_stable(
        out,
        match relation {
            NativeSemanticRelationKind::NativeSuccessor => 0,
            NativeSemanticRelationKind::PetriSuccessor => 1,
        },
    );
}

pub(crate) fn write_semantic_bridge_evidence_status_stable(
    out: &mut Vec<u8>,
    status: NativeSemanticBridgeEvidenceStatus,
) {
    write_u8_stable(
        out,
        match status {
            NativeSemanticBridgeEvidenceStatus::Missing => 0,
            NativeSemanticBridgeEvidenceStatus::Present => 1,
        },
    );
}

pub(crate) fn write_semantic_bridge_status_stable(
    out: &mut Vec<u8>,
    status: NativeSemanticBridgeStatus,
) {
    write_u8_stable(
        out,
        match status {
            NativeSemanticBridgeStatus::Represented => 0,
            NativeSemanticBridgeStatus::Blocked => 1,
        },
    );
}

pub(crate) fn write_semantic_bridge_reason_stable(
    out: &mut Vec<u8>,
    reason: NativeSemanticBridgeReason,
) {
    write_u8_stable(
        out,
        match reason {
            NativeSemanticBridgeReason::Represented => 0,
            NativeSemanticBridgeReason::BundleInvalid => 1,
            NativeSemanticBridgeReason::MissingFunction => 2,
            NativeSemanticBridgeReason::MissingProofObligation => 3,
            NativeSemanticBridgeReason::MissingObligationSource => 4,
            NativeSemanticBridgeReason::FunctionMismatch => 5,
            NativeSemanticBridgeReason::UnsupportedObligationKind => 6,
            NativeSemanticBridgeReason::ProofPending => 7,
            NativeSemanticBridgeReason::ProofFailed => 8,
            NativeSemanticBridgeReason::TrustedProofNotAdmitted => 9,
            NativeSemanticBridgeReason::MissingEvidence => 10,
        },
    );
}

pub(crate) fn write_adapter_input_stable(out: &mut Vec<u8>, input: &NativeAdapterInput) {
    match input {
        NativeAdapterInput::RustMir { body_digest } => {
            write_u8_stable(out, 0);
            write_digest_stable(out, body_digest);
        }
        NativeAdapterInput::TrustIrModule => write_u8_stable(out, 1),
    }
}

pub(crate) fn write_source_language_stable(out: &mut Vec<u8>, language: NativeSourceLanguage) {
    write_u8_stable(
        out,
        match language {
            NativeSourceLanguage::Unknown => 0,
            NativeSourceLanguage::Rust => 1,
            NativeSourceLanguage::Swift => 2,
            NativeSourceLanguage::C => 3,
            NativeSourceLanguage::TrustIr => 4,
            NativeSourceLanguage::Other => 5,
        },
    );
}

pub(crate) fn write_tool_identity_stable(out: &mut Vec<u8>, tool: &NativeToolIdentity) {
    write_str_stable(out, &tool.canonical_name());
    write_option_str_stable(out, tool.version.as_deref());
    write_option_str_stable(out, tool.revision.as_deref());
    write_option_digest_stable(out, tool.digest);
}

pub(crate) fn write_tool_identities_stable(out: &mut Vec<u8>, tools: &[NativeToolIdentity]) {
    let mut tools = tools.to_vec();
    tools.sort();
    write_len_stable(out, tools.len());
    for tool in tools {
        write_tool_identity_stable(out, &tool);
    }
}

pub(crate) fn write_verifier_suite_stable(out: &mut Vec<u8>, suite: NativeVerifierSuite) {
    write_u8_stable(
        out,
        match suite {
            NativeVerifierSuite::Unknown => 0,
            NativeVerifierSuite::TrustVc => 1,
            NativeVerifierSuite::TrustMc => 2,
            NativeVerifierSuite::TrustWp => 3,
            NativeVerifierSuite::AY => 4,
            NativeVerifierSuite::TRust => 5,
            NativeVerifierSuite::TrustIr => 6,
            NativeVerifierSuite::Other => 7,
        },
    );
}

pub(crate) fn write_bundle_provenance_stable(
    out: &mut Vec<u8>,
    provenance: &NativeBundleProvenance,
) {
    write_str_stable(out, &provenance.producer_version);
    write_source_language_stable(out, provenance.source_language);
    write_option_str_stable(out, provenance.source_artifact.as_deref());
    write_option_digest_stable(out, provenance.source_digest);

    let mut tools = provenance.toolchain.clone();
    tools.sort();
    write_len_stable(out, tools.len());
    for tool in tools {
        write_tool_identity_stable(out, &tool);
    }
}

pub(crate) fn write_unknown_field_policy_stable(
    out: &mut Vec<u8>,
    policy: NativeUnknownFieldPolicy,
) {
    write_u8_stable(
        out,
        match policy {
            NativeUnknownFieldPolicy::Reject => 0,
            NativeUnknownFieldPolicy::Preserve => 1,
            NativeUnknownFieldPolicy::Ignore => 2,
        },
    );
}

pub(crate) fn write_serialization_policy_stable(
    out: &mut Vec<u8>,
    policy: &NativeSerializationPolicy,
) {
    write_u32_stable(out, policy.schema_version);
    write_bool_stable(out, policy.canonical_order);
    write_bool_stable(out, policy.sort_unordered_sets);
    write_bool_stable(out, policy.messagepack_named_fields);
    write_unknown_field_policy_stable(out, policy.unknown_fields);
}

pub(crate) fn write_diagnostic_level_stable(out: &mut Vec<u8>, level: NativeDiagnosticLevel) {
    write_u8_stable(
        out,
        match level {
            NativeDiagnosticLevel::Off => 0,
            NativeDiagnosticLevel::Error => 1,
            NativeDiagnosticLevel::Warn => 2,
            NativeDiagnosticLevel::Info => 3,
            NativeDiagnosticLevel::Trace => 4,
        },
    );
}

pub(crate) fn write_diagnostics_policy_stable(out: &mut Vec<u8>, policy: &NativeDiagnosticsPolicy) {
    write_diagnostic_level_stable(out, policy.level);
    write_bool_stable(out, policy.include_source_spans);
    write_bool_stable(out, policy.include_lineage);
    write_bool_stable(out, policy.emit_counterexamples);
    write_bool_stable(out, policy.emit_unsat_cores);
    write_bool_stable(out, policy.emit_proof_traces);
    write_u32_stable(out, policy.max_counterexamples);
}

pub(crate) fn write_replay_identity_stable(out: &mut Vec<u8>, replay: &ProofReplayIdentity) {
    write_str_stable(out, &replay.engine);
    write_str_stable(out, &replay.invocation);
    write_option_digest_stable(out, replay.transcript_digest);
}

pub(crate) fn write_proof_formula_stable(out: &mut Vec<u8>, formula: &ProofFormula) {
    write_str_stable(out, &formula.schema);
    write_str_stable(out, &formula.payload);
    write_option_str_stable(out, formula.smtlib.as_deref());
    write_option_str_stable(out, formula.sort.as_deref());
}

pub(crate) fn write_replay_atom_kind_stable(out: &mut Vec<u8>, kind: NativeReplayAtomKind) {
    write_u8_stable(
        out,
        match kind {
            NativeReplayAtomKind::Assumption => 0,
            NativeReplayAtomKind::Assertion => 1,
        },
    );
}

pub(crate) fn write_option_proof_id_stable(out: &mut Vec<u8>, value: Option<ProofId>) {
    match value {
        None => write_u8_stable(out, 0),
        Some(value) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, value.index());
        }
    }
}

pub(crate) fn write_replay_atom_stable(out: &mut Vec<u8>, atom: &NativeReplayAtom) {
    write_u32_stable(out, atom.id.index());
    write_replay_atom_kind_stable(out, atom.kind);
    write_proof_formula_stable(out, &atom.formula);
    write_digest_stable(out, &atom.payload_digest);
    write_option_proof_id_stable(out, atom.obligation);
    write_option_assertion_id_stable(out, atom.assertion_id);
    write_option_source_span_stable(out, atom.span);
}

pub(crate) fn write_unsupported_mode_reason_stable(
    out: &mut Vec<u8>,
    reason: NativeUnsupportedModeReason,
) {
    write_u8_stable(
        out,
        match reason {
            NativeUnsupportedModeReason::UnsupportedVerifierMode => 0,
            NativeUnsupportedModeReason::UnsupportedFormulaSchema => 1,
            NativeUnsupportedModeReason::UnsupportedCompilerFact => 2,
            NativeUnsupportedModeReason::MissingSourceSpan => 3,
            NativeUnsupportedModeReason::MissingReplayTranscript => 4,
            NativeUnsupportedModeReason::Other => 5,
        },
    );
}

pub(crate) fn write_unsupported_mode_stable(
    out: &mut Vec<u8>,
    unsupported: &NativeUnsupportedMode,
) {
    write_unsupported_mode_reason_stable(out, unsupported.reason);
    write_str_stable(out, &unsupported.detail);
}

pub(crate) fn write_replay_context_stable(out: &mut Vec<u8>, context: &NativeReplayContext) {
    let mut atoms: Vec<&NativeReplayAtom> = context.atoms.iter().collect();
    atoms.sort_by_key(|atom| atom.id);
    write_len_stable(out, atoms.len());
    for atom in atoms {
        write_replay_atom_stable(out, atom);
    }

    let mut unsupported_modes = context.unsupported_modes.clone();
    unsupported_modes.sort();
    write_len_stable(out, unsupported_modes.len());
    for unsupported in &unsupported_modes {
        write_unsupported_mode_stable(out, unsupported);
    }
}

pub(crate) fn write_request_provenance_stable(
    out: &mut Vec<u8>,
    provenance: &NativeRequestProvenance,
) {
    write_verifier_suite_stable(out, provenance.verifier_suite);
    write_tool_identity_stable(out, &provenance.expected_verifier);
    let mut solvers = provenance.solvers.clone();
    solvers.sort();
    write_len_stable(out, solvers.len());
    for solver in solvers {
        write_tool_identity_stable(out, &solver);
    }
    match &provenance.replay {
        None => write_u8_stable(out, 0),
        Some(replay) => {
            write_u8_stable(out, 1);
            write_replay_identity_stable(out, replay);
        }
    }
    if !provenance.replay_context.is_empty() {
        write_replay_context_stable(out, &provenance.replay_context);
    }
}

pub(crate) fn write_proof_ids_stable(out: &mut Vec<u8>, ids: &[ProofId]) {
    let mut ids = ids.to_vec();
    ids.sort();
    write_len_stable(out, ids.len());
    for id in ids {
        write_u32_stable(out, id.index());
    }
}

pub(crate) fn write_lineage_ids_stable(out: &mut Vec<u8>, ids: &[ProofLineageId]) {
    let mut ids = ids.to_vec();
    ids.sort();
    write_len_stable(out, ids.len());
    for id in ids {
        write_u32_stable(out, id.index());
    }
}

pub(crate) fn write_certificate_ref_stable(out: &mut Vec<u8>, cert: &ProofCertificateRef) {
    write_u32_stable(out, cert.obligation.index());
    write_str_stable(out, &cert.prover);
    write_digest_stable(out, &cert.evidence_digest);
}

pub(crate) fn write_certificate_refs_stable(out: &mut Vec<u8>, certs: &[ProofCertificateRef]) {
    let mut certs = certs.to_vec();
    certs.sort();
    write_len_stable(out, certs.len());
    for cert in certs {
        write_certificate_ref_stable(out, &cert);
    }
}

pub(crate) fn write_trust_vc_mode_stable(out: &mut Vec<u8>, mode: TrustVcVerificationMode) {
    write_u8_stable(
        out,
        match mode {
            TrustVcVerificationMode::ImportProofCertificates => 0,
            TrustVcVerificationMode::MergeProofCertificates => 1,
            TrustVcVerificationMode::DischargeProofObligations => 2,
        },
    );
}

pub(crate) fn write_trust_vc_options_stable(out: &mut Vec<u8>, options: &TrustVcRequestOptions) {
    write_u8_stable(
        out,
        match options.memory_semantics {
            TrustVcMemorySemantics::RustMir => 0,
            TrustVcMemorySemantics::TrustIr => 1,
            TrustVcMemorySemantics::StackedBorrows => 2,
        },
    );
    write_u8_stable(
        out,
        match options.trusted_evidence {
            TrustVcTrustedEvidencePolicy::Reject => 0,
            TrustVcTrustedEvidencePolicy::AllowWithDiagnostic => 1,
            TrustVcTrustedEvidencePolicy::Allow => 2,
        },
    );
    write_u8_stable(
        out,
        match options.merge_strategy {
            TrustVcMergeStrategy::RequireSameObligation => 0,
            TrustVcMergeStrategy::UnionDischargedObligations => 1,
            TrustVcMergeStrategy::PreferNewestLineage => 2,
        },
    );
    write_bool_stable(out, options.require_replay_identity);
}

pub(crate) fn write_trust_mc_mode_stable(out: &mut Vec<u8>, mode: TrustMcVerificationMode) {
    write_u8_stable(
        out,
        match mode {
            TrustMcVerificationMode::BoundedModelCheck => 0,
            TrustMcVerificationMode::Chc => 1,
            TrustMcVerificationMode::Pdr => 2,
        },
    );
}

pub(crate) fn write_trust_mc_options_stable(out: &mut Vec<u8>, options: &TrustMcRequestOptions) {
    write_u8_stable(
        out,
        match options.memory_model {
            TrustMcMemoryModel::TrustIrPlaces => 0,
            TrustMcMemoryModel::FlatArrays => 1,
            TrustMcMemoryModel::StackedBorrows => 2,
        },
    );
    write_u8_stable(
        out,
        match options.arithmetic_model {
            TrustMcArithmeticModel::FixedWidthBitvectors => 0,
            TrustMcArithmeticModel::MathematicalIntegers => 1,
            TrustMcArithmeticModel::RustChecked => 2,
        },
    );
    write_u32_stable(out, options.bmc.unwind_limit);
    write_bool_stable(out, options.bmc.unwinding_assertions);
    write_u8_stable(
        out,
        match options.chc.engine {
            TrustMcChcEngine::Z3Fixedpoint => 0,
            TrustMcChcEngine::Spacer => 1,
            TrustMcChcEngine::NativePdr => 2,
        },
    );
    write_u8_stable(
        out,
        match options.chc.invariant_source {
            TrustMcInvariantSource::None => 0,
            TrustMcInvariantSource::TrustIrProofObligations => 1,
            TrustMcInvariantSource::TrustWp => 2,
            TrustMcInvariantSource::TrustVc => 3,
            TrustMcInvariantSource::UserSupplied => 4,
        },
    );
    write_bool_stable(out, options.chc.pdr.enabled);
    write_option_u32_stable(out, options.chc.pdr.max_frames);
    write_u8_stable(
        out,
        match options.chc.pdr.generalization {
            TrustMcPdrGeneralization::None => 0,
            TrustMcPdrGeneralization::Cubes => 1,
            TrustMcPdrGeneralization::Interpolants => 2,
        },
    );
    write_bool_stable(out, options.chc.emit_horn_clauses);
    write_u8_stable(
        out,
        match options.slicing {
            TrustMcSlicingMode::None => 0,
            TrustMcSlicingMode::ObligationBackwardSlice => 1,
            TrustMcSlicingMode::ConstraintIndependence => 2,
        },
    );
}

pub(crate) fn write_trust_wp_mode_stable(out: &mut Vec<u8>, mode: TrustWpVerificationMode) {
    write_u8_stable(
        out,
        match mode {
            TrustWpVerificationMode::WeakestPrecondition => 0,
            TrustWpVerificationMode::StrongestPostcondition => 1,
            TrustWpVerificationMode::Abduction => 2,
        },
    );
}

pub(crate) fn write_trust_wp_options_stable(out: &mut Vec<u8>, options: &TrustWpRequestOptions) {
    write_u8_stable(
        out,
        match options.heap_model {
            TrustWpHeapModel::TrustIrMemory => 0,
            TrustWpHeapModel::RustBorrowGraph => 1,
            TrustWpHeapModel::SeparationLogic => 2,
        },
    );
    write_u8_stable(
        out,
        match options.loop_strategy {
            TrustWpLoopStrategy::RequireInvariants => 0,
            TrustWpLoopStrategy::InferInvariants => 1,
            TrustWpLoopStrategy::Havoc => 2,
        },
    );
    write_u8_stable(
        out,
        match options.frame_policy {
            TrustWpFramePolicy::Minimal => 0,
            TrustWpFramePolicy::BorrowRegions => 1,
            TrustWpFramePolicy::FullHeap => 2,
        },
    );
    write_u8_stable(
        out,
        match options.panic_semantics {
            TrustWpPanicSemantics::PanicFreeRequired => 0,
            TrustWpPanicSemantics::EncodePanicsAsErrors => 1,
            TrustWpPanicSemantics::Unwind => 2,
        },
    );
    write_u32_stable(out, options.max_abduced_preconditions);
    write_bool_stable(out, options.emit_verification_conditions);
}

pub(crate) fn write_cast_op_stable(out: &mut Vec<u8>, op: CastOp) {
    write_u8_stable(
        out,
        match op {
            CastOp::Trunc => 0,
            CastOp::ZExt => 1,
            CastOp::SExt => 2,
            CastOp::FPTrunc => 3,
            CastOp::FPExt => 4,
            CastOp::FPToUI => 5,
            CastOp::FPToSI => 6,
            CastOp::UIToFP => 7,
            CastOp::SIToFP => 8,
            CastOp::PtrToInt => 9,
            CastOp::IntToPtr => 10,
            CastOp::PtrToPtr => 11,
            CastOp::Bitcast => 12,
            CastOp::Transmute => 13,
            CastOp::ReifyFnPointer => 14,
            CastOp::FPToSISat => 15,
            CastOp::FPToUISat => 16,
        },
    );
}

pub(crate) fn write_enum_tag_encoding_stable(out: &mut Vec<u8>, encoding: NativeEnumTagEncoding) {
    write_u8_stable(
        out,
        match encoding {
            NativeEnumTagEncoding::Direct => 0,
            NativeEnumTagEncoding::Niche => 1,
            NativeEnumTagEncoding::Untagged => 2,
        },
    );
}

pub(crate) fn write_integer_range_stable(out: &mut Vec<u8>, range: NativeIntegerRange) {
    write_i128_stable(out, range.start);
    write_i128_stable(out, range.end);
}

pub(crate) fn write_enum_niche_fact_stable(out: &mut Vec<u8>, niche: &NativeEnumNicheFact) {
    write_u32_stable(out, niche.variant_index);
    write_option_u32_stable(out, niche.field);
    write_integer_range_stable(out, niche.valid_range);
}

pub(crate) fn write_option_enum_niche_fact_stable(
    out: &mut Vec<u8>,
    niche: Option<&NativeEnumNicheFact>,
) {
    match niche {
        None => write_u8_stable(out, 0),
        Some(niche) => {
            write_u8_stable(out, 1);
            write_enum_niche_fact_stable(out, niche);
        }
    }
}

pub(crate) fn write_enum_variant_layout_fact_stable(
    out: &mut Vec<u8>,
    variant: &NativeEnumVariantLayoutFact,
) {
    write_u32_stable(out, variant.variant_index);
    write_str_stable(out, &variant.name);
    write_option_i128_stable(out, variant.discriminant);
    write_len_stable(out, variant.fields.len());
    for field in &variant.fields {
        write_field_offset_shape_stable(out, field);
    }
    write_u64_stable(out, variant.size_bits);
    write_option_u64_stable(out, variant.align_bits);
}

pub(crate) fn write_enum_layout_fact_stable(out: &mut Vec<u8>, layout: &NativeEnumLayoutFact) {
    write_enum_id_stable(out, layout.enum_id);
    write_enum_tag_encoding_stable(out, layout.tag_encoding);
    write_option_u32_stable(out, layout.tag_bits);
    write_option_u64_stable(out, layout.discriminant_offset_bits);
    write_option_enum_niche_fact_stable(out, layout.niche.as_ref());
    write_len_stable(out, layout.variants.len());
    for variant in &layout.variants {
        write_enum_variant_layout_fact_stable(out, variant);
    }
}

pub(crate) fn write_option_enum_layout_fact_stable(
    out: &mut Vec<u8>,
    layout: Option<&NativeEnumLayoutFact>,
) {
    match layout {
        None => write_u8_stable(out, 0),
        Some(layout) => {
            write_u8_stable(out, 1);
            write_enum_layout_fact_stable(out, layout);
        }
    }
}

pub(crate) fn write_adt_layout_fact_stable(out: &mut Vec<u8>, fact: &NativeAdtLayoutFact) {
    write_u32_stable(out, fact.id.index());
    write_ty_stable(out, &fact.ty);
    write_ty_layout_shape_stable(out, &fact.layout);
    write_option_enum_layout_fact_stable(out, fact.enum_layout.as_ref());
}

pub(crate) fn write_fat_pointer_fact_stable(out: &mut Vec<u8>, fact: &NativeFatPointerFact) {
    write_u32_stable(out, fact.id.index());
    write_ty_stable(out, &fact.ty);
    write_pointer_layout_shape_stable(out, fact.layout);
}

pub(crate) fn write_trait_object_metadata_fact_stable(
    out: &mut Vec<u8>,
    fact: &NativeTraitObjectMetadataFact,
) {
    write_u32_stable(out, fact.id.index());
    write_ty_stable(out, &fact.ty);
    match &fact.source_ty {
        None => write_u8_stable(out, 0),
        Some(ty) => {
            write_u8_stable(out, 1);
            write_ty_stable(out, ty);
        }
    }
    write_u32_stable(out, fact.trait_id);
    write_option_u32_stable(out, fact.source_trait_id);
    write_len_stable(out, fact.upcast_path.len());
    for trait_id in &fact.upcast_path {
        write_u32_stable(out, *trait_id);
    }
    write_str_stable(out, &fact.vtable_symbol);
    write_digest_stable(out, &fact.stable_digest);
    match fact.function {
        None => write_u8_stable(out, 0),
        Some(function) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, function.index());
        }
    }
    write_proof_ids_stable(out, &fact.obligations);
}

pub(crate) fn write_pointer_offset_provenance_stable(
    out: &mut Vec<u8>,
    provenance: &NativePointerOffsetProvenance,
) {
    match provenance {
        NativePointerOffsetProvenance::SameAsBase => write_u8_stable(out, 0),
        NativePointerOffsetProvenance::Unsupported(unsupported) => {
            write_u8_stable(out, 1);
            write_unsupported_mode_stable(out, unsupported);
        }
    }
}

pub(crate) fn write_pointer_offset_fact_stable(out: &mut Vec<u8>, fact: &NativePointerOffsetFact) {
    write_u32_stable(out, fact.id.index());
    write_u32_stable(out, fact.function.index());
    match fact.result {
        None => write_u8_stable(out, 0),
        Some(result) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, result.index());
        }
    }
    write_u32_stable(out, fact.base.index());
    write_ty_stable(out, &fact.base_ty);
    write_ty_stable(out, &fact.pointee_ty);
    write_ty_layout_shape_stable(out, &fact.element_layout);
    write_u64_stable(out, fact.stride_bits);
    write_u32_stable(out, fact.offset.index());
    write_ty_stable(out, &fact.offset_ty);
    write_option_i128_stable(out, fact.signed_offset_const);
    write_pointer_offset_provenance_stable(out, &fact.provenance);
    write_option_source_span_stable(out, fact.span);
    write_proof_ids_stable(out, &fact.obligations);
}

pub(crate) fn write_cast_fact_stable(out: &mut Vec<u8>, fact: &NativeCastFact) {
    write_u32_stable(out, fact.id.index());
    write_u32_stable(out, fact.function.index());
    match fact.result {
        None => write_u8_stable(out, 0),
        Some(result) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, result.index());
        }
    }
    write_cast_op_stable(out, fact.op);
    write_ty_stable(out, &fact.source_ty);
    write_ty_stable(out, &fact.target_ty);
    write_cast_layout_evidence_stable(out, &fact.evidence);
    write_option_source_span_stable(out, fact.span);
    write_proof_ids_stable(out, &fact.obligations);
}

pub(crate) fn write_generic_arg_stable(out: &mut Vec<u8>, arg: &NativeGenericArg) {
    match arg {
        NativeGenericArg::Ty(ty) => {
            write_u8_stable(out, 0);
            write_ty_stable(out, ty);
        }
        NativeGenericArg::Const { ty, value } => {
            write_u8_stable(out, 1);
            write_ty_stable(out, ty);
            write_constant_stable(out, value);
        }
        NativeGenericArg::LifetimeErased => write_u8_stable(out, 2),
        NativeGenericArg::Placeholder { index } => {
            write_u8_stable(out, 3);
            write_u32_stable(out, *index);
        }
    }
}

pub(crate) fn write_monomorphization_fact_stable(
    out: &mut Vec<u8>,
    fact: &NativeMonomorphizationFact,
) {
    write_u32_stable(out, fact.id.index());
    write_str_stable(out, &fact.source_item);
    write_str_stable(out, &fact.symbol);
    write_len_stable(out, fact.generic_args.len());
    for arg in &fact.generic_args {
        write_generic_arg_stable(out, arg);
    }
    match fact.function {
        None => write_u8_stable(out, 0),
        Some(function) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, function.index());
        }
    }
    write_digest_stable(out, &fact.stable_digest);
}

pub(crate) fn write_obligation_cause_stable(out: &mut Vec<u8>, cause: NativeObligationCause) {
    write_u8_stable(
        out,
        match cause {
            NativeObligationCause::Precondition => 0,
            NativeObligationCause::Postcondition => 1,
            NativeObligationCause::Assert => 2,
            NativeObligationCause::BoundsCheck => 3,
            NativeObligationCause::OverflowCheck => 4,
            NativeObligationCause::LayoutCheck => 5,
            NativeObligationCause::CastCheck => 6,
            NativeObligationCause::BorrowCheck => 7,
            NativeObligationCause::Translation => 8,
            NativeObligationCause::Panic => 9,
            NativeObligationCause::Other => 10,
            NativeObligationCause::PointerOffset => 11,
            NativeObligationCause::Temporal => 12,
        },
    );
}

pub(crate) fn write_compiler_fact_ref_stable(out: &mut Vec<u8>, fact: NativeCompilerFactRef) {
    match fact {
        NativeCompilerFactRef::AdtLayout(id) => {
            write_u8_stable(out, 0);
            write_u32_stable(out, id.index());
        }
        NativeCompilerFactRef::FatPointer(id) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, id.index());
        }
        NativeCompilerFactRef::TraitObjectMetadata(id) => {
            write_u8_stable(out, 2);
            write_u32_stable(out, id.index());
        }
        NativeCompilerFactRef::Cast(id) => {
            write_u8_stable(out, 3);
            write_u32_stable(out, id.index());
        }
        NativeCompilerFactRef::Monomorphization(id) => {
            write_u8_stable(out, 4);
            write_u32_stable(out, id.index());
        }
        NativeCompilerFactRef::PointerOffset(id) => {
            write_u8_stable(out, 5);
            write_u32_stable(out, id.index());
        }
    }
}

pub(crate) fn write_obligation_source_stable(out: &mut Vec<u8>, source: &NativeObligationSource) {
    write_u32_stable(out, source.obligation.index());
    write_str_stable(out, &source.public_obligation_id);
    match source.function {
        None => write_u8_stable(out, 0),
        Some(function) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, function.index());
        }
    }
    write_option_source_span_stable(out, source.span);
    write_option_assertion_id_stable(out, source.assertion_id);
    write_obligation_cause_stable(out, source.cause);
    match source.monomorphization {
        None => write_u8_stable(out, 0),
        Some(id) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, id.index());
        }
    }
    let mut facts = source.facts.clone();
    facts.sort();
    write_len_stable(out, facts.len());
    for fact in facts {
        write_compiler_fact_ref_stable(out, fact);
    }
}

pub(crate) fn write_compiler_facts_stable(out: &mut Vec<u8>, facts: &NativeCompilerFacts) {
    let mut adt_layouts: Vec<&NativeAdtLayoutFact> = facts.adt_layouts.iter().collect();
    adt_layouts.sort_by_key(|fact| fact.id);
    write_len_stable(out, adt_layouts.len());
    for fact in adt_layouts {
        write_adt_layout_fact_stable(out, fact);
    }

    let mut fat_pointers: Vec<&NativeFatPointerFact> = facts.fat_pointers.iter().collect();
    fat_pointers.sort_by_key(|fact| fact.id);
    write_len_stable(out, fat_pointers.len());
    for fact in fat_pointers {
        write_fat_pointer_fact_stable(out, fact);
    }

    let mut trait_object_metadata: Vec<&NativeTraitObjectMetadataFact> =
        facts.trait_object_metadata.iter().collect();
    trait_object_metadata.sort_by_key(|fact| fact.id);
    write_len_stable(out, trait_object_metadata.len());
    for fact in trait_object_metadata {
        write_trait_object_metadata_fact_stable(out, fact);
    }

    let mut pointer_offsets: Vec<&NativePointerOffsetFact> = facts.pointer_offsets.iter().collect();
    pointer_offsets.sort_by_key(|fact| fact.id);
    write_len_stable(out, pointer_offsets.len());
    for fact in pointer_offsets {
        write_pointer_offset_fact_stable(out, fact);
    }

    let mut casts: Vec<&NativeCastFact> = facts.casts.iter().collect();
    casts.sort_by_key(|fact| fact.id);
    write_len_stable(out, casts.len());
    for fact in casts {
        write_cast_fact_stable(out, fact);
    }

    let mut monomorphizations: Vec<&NativeMonomorphizationFact> =
        facts.monomorphizations.iter().collect();
    monomorphizations.sort_by_key(|fact| fact.id);
    write_len_stable(out, monomorphizations.len());
    for fact in monomorphizations {
        write_monomorphization_fact_stable(out, fact);
    }

    let mut sources: Vec<&NativeObligationSource> = facts.obligation_sources.iter().collect();
    sources.sort_by_key(|source| (source.obligation, source.function, source.monomorphization));
    write_len_stable(out, sources.len());
    for source in sources {
        write_obligation_source_stable(out, source);
    }
}

pub(crate) fn native_request_variant_tag(request: &NativeVerificationRequest) -> u8 {
    match request {
        NativeVerificationRequest::TrustVc(_) => 0,
        NativeVerificationRequest::TrustMc(_) => 1,
        NativeVerificationRequest::TrustWp(_) => 2,
    }
}

pub(crate) fn native_request_mode_tag(request: &NativeVerificationRequest) -> u8 {
    match request {
        NativeVerificationRequest::TrustVc(request) => match request.mode {
            TrustVcVerificationMode::ImportProofCertificates => 0,
            TrustVcVerificationMode::MergeProofCertificates => 1,
            TrustVcVerificationMode::DischargeProofObligations => 2,
        },
        NativeVerificationRequest::TrustMc(request) => match request.mode {
            TrustMcVerificationMode::BoundedModelCheck => 0,
            TrustMcVerificationMode::Chc => 1,
            TrustMcVerificationMode::Pdr => 2,
        },
        NativeVerificationRequest::TrustWp(request) => match request.mode {
            TrustWpVerificationMode::WeakestPrecondition => 0,
            TrustWpVerificationMode::StrongestPostcondition => 1,
            TrustWpVerificationMode::Abduction => 2,
        },
    }
}

pub(crate) fn native_evidence_bundle_variant_tag(bundle: &NativeEvidenceBundle) -> u8 {
    match bundle {
        NativeEvidenceBundle::TrustVc(_) => 0,
        NativeEvidenceBundle::TrustMc(_) => 1,
        NativeEvidenceBundle::TrustWp(_) => 2,
    }
}

pub(crate) fn native_evidence_bundle_mode_tag(bundle: &NativeEvidenceBundle) -> u8 {
    match bundle {
        NativeEvidenceBundle::TrustVc(bundle) => match bundle.mode {
            TrustVcVerificationMode::ImportProofCertificates => 0,
            TrustVcVerificationMode::MergeProofCertificates => 1,
            TrustVcVerificationMode::DischargeProofObligations => 2,
        },
        NativeEvidenceBundle::TrustMc(bundle) => match bundle.mode {
            TrustMcVerificationMode::BoundedModelCheck => 0,
            TrustMcVerificationMode::Chc => 1,
            TrustMcVerificationMode::Pdr => 2,
        },
        NativeEvidenceBundle::TrustWp(bundle) => match bundle.mode {
            TrustWpVerificationMode::WeakestPrecondition => 0,
            TrustWpVerificationMode::StrongestPostcondition => 1,
            TrustWpVerificationMode::Abduction => 2,
        },
    }
}

pub(crate) fn write_native_request_stable(out: &mut Vec<u8>, request: &NativeVerificationRequest) {
    match request {
        NativeVerificationRequest::TrustVc(request) => {
            write_u8_stable(out, 0);
            write_u32_stable(out, request.id.index());
            write_trust_vc_mode_stable(out, request.mode);
            write_proof_ids_stable(out, &request.obligations);
            write_certificate_refs_stable(out, &request.certificates);
            write_lineage_ids_stable(out, &request.lineage_roots);
            write_trust_vc_options_stable(out, &request.options);
            write_diagnostics_policy_stable(out, &request.diagnostics);
            write_request_provenance_stable(out, &request.provenance);
            // DELIBERATE: `function` is written LAST and UNTAGGED, so `None`
            // emits zero bytes and every pre-existing TrustVc request digest
            // stays byte-identical. Do NOT normalize this to match the TrustMc
            // / TrustWp arms below, which write `function` mid-record, and do
            // NOT route it through `write_option_u32_stable` — either change
            // appends a discriminant byte to every existing stream and moves
            // every TrustVc request digest, the bundle digest, every evidence
            // `request_digest`, and every compiler artifact metadata value,
            // forcing a version bump of both the request and bundle domains.
            //
            // "None writes nothing" is NOT the whole argument. This is the
            // SECOND stacked trailing conditional: `write_request_provenance_stable`
            // already ends in one (`if !provenance.replay_context.is_empty()`).
            // Non-collision holds only because a written replay_context is >=16
            // bytes — `write_replay_context_stable` emits two unconditional u64
            // length prefixes — while this tail is exactly 4. So (empty ctx,
            // Some) and (non-empty ctx, None) cannot alias. Adding a THIRD
            // trailing conditional, or making this one variable-width, breaks
            // that argument and needs a fresh proof.
            if let Some(function) = request.function {
                write_u32_stable(out, function.index());
            }
        }
        NativeVerificationRequest::TrustMc(request) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, request.id.index());
            write_trust_mc_mode_stable(out, request.mode);
            write_u32_stable(out, request.function.index());
            write_proof_ids_stable(out, &request.obligations);
            write_lineage_ids_stable(out, &request.lineage_roots);
            write_trust_mc_options_stable(out, &request.options);
            write_diagnostics_policy_stable(out, &request.diagnostics);
            write_request_provenance_stable(out, &request.provenance);
        }
        NativeVerificationRequest::TrustWp(request) => {
            write_u8_stable(out, 2);
            write_u32_stable(out, request.id.index());
            write_trust_wp_mode_stable(out, request.mode);
            write_u32_stable(out, request.function.index());
            write_proof_ids_stable(out, &request.obligations);
            write_lineage_ids_stable(out, &request.lineage_roots);
            write_trust_wp_options_stable(out, &request.options);
            write_diagnostics_policy_stable(out, &request.diagnostics);
            write_request_provenance_stable(out, &request.provenance);
        }
    }
}

pub(crate) fn write_evidence_artifact_kind_stable(
    out: &mut Vec<u8>,
    kind: NativeEvidenceArtifactKind,
) {
    write_u8_stable(
        out,
        match kind {
            NativeEvidenceArtifactKind::TrustVcCertificateImport => 0,
            NativeEvidenceArtifactKind::TrustVcMergedCertificate => 1,
            NativeEvidenceArtifactKind::TrustMcHornClauses => 2,
            NativeEvidenceArtifactKind::TrustMcPdrTrace => 3,
            NativeEvidenceArtifactKind::TrustMcModel => 4,
            NativeEvidenceArtifactKind::TrustWpVerificationCondition => 5,
            NativeEvidenceArtifactKind::TrustWpReplayTrace => 6,
            NativeEvidenceArtifactKind::TrustWpAbducedPrecondition => 7,
            NativeEvidenceArtifactKind::ReplayTranscript => 8,
            NativeEvidenceArtifactKind::Other => 9,
            NativeEvidenceArtifactKind::Btor2Trace => 10,
            NativeEvidenceArtifactKind::Btor2Proof => 11,
            NativeEvidenceArtifactKind::NativeCompiledArtifact => 12,
            NativeEvidenceArtifactKind::BackendCapabilityMetadata => 13,
        },
    );
}

pub(crate) fn write_evidence_artifact_stable(out: &mut Vec<u8>, artifact: &NativeEvidenceArtifact) {
    write_str_stable(out, &artifact.name);
    write_evidence_artifact_kind_stable(out, artifact.kind);
    write_digest_stable(out, &artifact.digest);
}

pub(crate) fn write_evidence_artifacts_stable(
    out: &mut Vec<u8>,
    artifacts: &[NativeEvidenceArtifact],
) {
    let mut artifacts = artifacts.to_vec();
    artifacts.sort();
    write_len_stable(out, artifacts.len());
    for artifact in artifacts {
        write_evidence_artifact_stable(out, &artifact);
    }
}

pub(crate) fn write_native_evidence_bundle_stable(
    out: &mut Vec<u8>,
    bundle: &NativeEvidenceBundle,
) {
    match bundle {
        NativeEvidenceBundle::TrustVc(bundle) => {
            write_u8_stable(out, 0);
            write_u32_stable(out, bundle.request.index());
            write_trust_vc_mode_stable(out, bundle.mode);
            write_proof_ids_stable(out, &bundle.obligations);
            write_tool_identity_stable(out, &bundle.verifier);
            write_tool_identities_stable(out, &bundle.solvers);
            write_replay_identity_stable(out, &bundle.replay);
            write_digest_stable(out, &bundle.trust_ir_module_digest);
            write_digest_stable(out, &bundle.request_digest);
            write_evidence_artifacts_stable(out, &bundle.artifacts);
        }
        NativeEvidenceBundle::TrustMc(bundle) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, bundle.request.index());
            write_trust_mc_mode_stable(out, bundle.mode);
            write_proof_ids_stable(out, &bundle.obligations);
            write_tool_identity_stable(out, &bundle.verifier);
            write_tool_identities_stable(out, &bundle.solvers);
            write_replay_identity_stable(out, &bundle.replay);
            write_digest_stable(out, &bundle.trust_ir_module_digest);
            write_digest_stable(out, &bundle.request_digest);
            write_evidence_artifacts_stable(out, &bundle.artifacts);
        }
        NativeEvidenceBundle::TrustWp(bundle) => {
            write_u8_stable(out, 2);
            write_u32_stable(out, bundle.request.index());
            write_trust_wp_mode_stable(out, bundle.mode);
            write_proof_ids_stable(out, &bundle.obligations);
            write_tool_identity_stable(out, &bundle.verifier);
            write_tool_identities_stable(out, &bundle.solvers);
            write_replay_identity_stable(out, &bundle.replay);
            write_digest_stable(out, &bundle.trust_ir_module_digest);
            write_digest_stable(out, &bundle.request_digest);
            write_evidence_artifacts_stable(out, &bundle.artifacts);
        }
    }
}

pub(crate) fn canonical_tool_name(name: &str) -> String {
    let mut normalized = String::new();
    let mut pending_separator = false;

    for byte in name.trim().bytes() {
        if byte.is_ascii_alphanumeric() {
            if pending_separator && !normalized.is_empty() {
                normalized.push('-');
            }
            normalized.push(byte.to_ascii_lowercase() as char);
            pending_separator = false;
        } else if !normalized.is_empty() {
            pending_separator = true;
        }
    }

    for (compact, separated, family) in [
        ("trustvc", "trust-vc", "trust_vc"),
        ("trustmc", "trust-mc", "trust_mc"),
        ("trustwp", "trust-wp", "trust_wp"),
        ("trustir", "trust-ir", "trust-ir"),
    ] {
        if normalized == compact || normalized == separated {
            return family.to_string();
        }
        if let Some(suffix) = normalized.strip_prefix(&format!("{compact}-")) {
            return format!("{family}-{suffix}");
        }
        if let Some(suffix) = normalized.strip_prefix(&format!("{separated}-")) {
            return format!("{family}-{suffix}");
        }
    }

    normalized
}

pub(crate) fn verifier_identity_matches_suite(
    suite: NativeVerifierSuite,
    tool: &NativeToolIdentity,
) -> bool {
    let Some(family) = suite.canonical_family() else {
        return true;
    };
    let canonical = tool.canonical_name();
    canonical_name_matches_family(&canonical, family)
}

pub(crate) fn canonical_name_matches_family(canonical: &str, family: &str) -> bool {
    canonical == family
        || canonical
            .strip_prefix(family)
            .is_some_and(|suffix| suffix.starts_with('-'))
}

pub(crate) fn validate_certificate_prover_suite(
    request: NativeRequestId,
    suite: NativeVerifierSuite,
    cert: &ProofCertificateRef,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let Some(family) = suite.canonical_family() else {
        return;
    };
    let canonical = canonical_tool_name(&cert.prover);
    if !canonical_name_matches_family(&canonical, family) {
        errors.push(
            NativeVerificationBundleError::CertificateVerifierSuiteMismatch {
                request,
                expected: suite,
                obligation: cert.obligation,
                prover: cert.prover.clone(),
                canonical,
            },
        );
    }
}

pub(crate) fn validate_tool_identity(
    field: &'static str,
    tool: &NativeToolIdentity,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    if tool.name.trim().is_empty() {
        errors.push(NativeVerificationBundleError::EmptyProvenanceField(field));
    }
    if tool
        .version
        .as_deref()
        .is_some_and(|value| value.trim().is_empty())
    {
        errors.push(NativeVerificationBundleError::InvalidToolIdentityField {
            field,
            component: "version",
        });
    }
    if tool
        .revision
        .as_deref()
        .is_some_and(|value| value.trim().is_empty())
    {
        errors.push(NativeVerificationBundleError::InvalidToolIdentityField {
            field,
            component: "revision",
        });
    }
    if let Some(digest) = tool.digest
        && digest.is_zero()
    {
        errors.push(NativeVerificationBundleError::EmptyDigest { field });
    }
    if tool
        .digest
        .is_some_and(|digest| digest.algorithm != ProofDigestAlgorithm::Sha256)
    {
        errors.push(NativeVerificationBundleError::InvalidToolIdentityField {
            field,
            component: "digest.algorithm",
        });
    }
}

pub(crate) fn validate_expected_verifier_identity(
    request: NativeRequestId,
    suite: NativeVerifierSuite,
    tool: &NativeToolIdentity,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let canonical = tool.canonical_name();
    if !canonical.is_empty() && !verifier_identity_matches_suite(suite, tool) {
        errors.push(
            NativeVerificationBundleError::ExpectedVerifierIdentityMismatch {
                request,
                suite,
                verifier: tool.name.clone(),
                canonical,
            },
        );
    }
}

pub(crate) fn validate_replay_identity(
    request: NativeRequestId,
    suite: NativeVerifierSuite,
    replay: &ProofReplayIdentity,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let canonical = canonical_tool_name(&replay.engine);
    if replay.engine.trim().is_empty() {
        errors.push(NativeVerificationBundleError::InvalidReplayIdentity {
            request,
            field: "engine",
        });
    }
    if let Some(family) = suite.canonical_family()
        && !canonical.is_empty()
        && !canonical_name_matches_family(&canonical, family)
    {
        errors.push(
            NativeVerificationBundleError::ReplayIdentityVerifierSuiteMismatch {
                request,
                expected: suite,
                engine: replay.engine.clone(),
                canonical,
            },
        );
    }
    if replay.invocation.trim().is_empty() {
        errors.push(NativeVerificationBundleError::InvalidReplayIdentity {
            request,
            field: "invocation",
        });
    }
    match replay.transcript_digest {
        Some(digest) if digest.is_zero() => {
            errors.push(NativeVerificationBundleError::InvalidReplayIdentity {
                request,
                field: "transcript_digest",
            });
        }
        Some(digest) if digest.algorithm != ProofDigestAlgorithm::Sha256 => {
            errors.push(NativeVerificationBundleError::InvalidReplayIdentity {
                request,
                field: "transcript_digest.algorithm",
            });
        }
        Some(_) => {}
        None => errors.push(NativeVerificationBundleError::MissingReplayTranscriptDigest(request)),
    }
}

pub(crate) fn validate_replay_context(
    request: NativeRequestId,
    request_obligations: &BTreeSet<ProofId>,
    compiler_facts: &NativeCompilerFacts,
    context: &NativeReplayContext,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    for unsupported in &context.unsupported_modes {
        errors.push(
            NativeVerificationBundleError::UnsupportedNativeRequestMode {
                request,
                reason: unsupported.reason,
                detail: unsupported.detail.clone(),
            },
        );
    }

    let mut atom_ids = BTreeSet::new();
    for atom in &context.atoms {
        if !atom_ids.insert(atom.id) {
            errors.push(NativeVerificationBundleError::DuplicateReplayAtomId {
                request,
                atom: atom.id,
            });
        }
        if atom.formula.schema.trim().is_empty() {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "formula.schema",
            });
        }
        if atom.formula.payload.trim().is_empty() {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "formula.payload",
            });
        }
        if atom.payload_digest.is_zero() {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "payload_digest",
            });
        } else if atom.payload_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "payload_digest.algorithm",
            });
        } else {
            let expected = atom.expected_payload_digest();
            if atom.payload_digest != expected {
                errors.push(NativeVerificationBundleError::ReplayAtomDigestMismatch {
                    request,
                    atom: atom.id,
                    expected,
                    actual: atom.payload_digest,
                });
            }
        }
        if atom.kind == NativeReplayAtomKind::Assertion
            && atom.obligation.is_none()
            && atom.assertion_id.is_none()
        {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "assertion_binding",
            });
        }
        if atom.assertion_id.is_some() && atom.obligation.is_none() {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "assertion_id.obligation",
            });
        }
        if atom.span.is_some() && atom.obligation.is_none() {
            errors.push(NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom: atom.id,
                field: "span.obligation",
            });
        }
        let Some(obligation) = atom.obligation else {
            continue;
        };
        if !request_obligations.contains(&obligation) {
            errors.push(
                NativeVerificationBundleError::ReplayAtomObligationNotRequested {
                    request,
                    atom: atom.id,
                    obligation,
                },
            );
        }
        let Some(source) = compiler_facts.obligation_source(obligation) else {
            continue;
        };
        if let Some(assertion_id) = atom.assertion_id
            && source.assertion_id != Some(assertion_id)
        {
            errors.push(NativeVerificationBundleError::ReplayAtomAssertionMismatch {
                request,
                atom: atom.id,
                obligation,
                expected: source.assertion_id,
                actual: assertion_id,
            });
        }
        if let (Some(expected), Some(actual)) = (source.span, atom.span)
            && expected != actual
        {
            errors.push(
                NativeVerificationBundleError::ReplayAtomSourceSpanMismatch {
                    request,
                    atom: atom.id,
                    obligation,
                    expected,
                    actual,
                },
            );
        }
    }
}

pub(crate) fn validate_evidence_obligations(
    request: &NativeVerificationRequest,
    evidence: &NativeEvidenceBundle,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let request_id = request.id();
    let request_obligations: BTreeSet<ProofId> = request.obligations().iter().copied().collect();
    let evidence_obligations: BTreeSet<ProofId> = evidence.obligations().iter().copied().collect();

    for obligation in request_obligations.difference(&evidence_obligations) {
        errors.push(NativeVerificationBundleError::EvidenceObligationMismatch {
            request: request_id,
            obligation: *obligation,
        });
    }
    for obligation in evidence_obligations.difference(&request_obligations) {
        errors.push(NativeVerificationBundleError::EvidenceObligationMismatch {
            request: request_id,
            obligation: *obligation,
        });
    }
}

pub(crate) fn validate_evidence_provenance_binding(
    request: &NativeVerificationRequest,
    evidence: &NativeEvidenceBundle,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let request_id = request.id();
    if evidence.verifier() != request.expected_verifier_identity() {
        errors.push(NativeVerificationBundleError::EvidenceProvenanceMismatch {
            request: request_id,
            field: "verifier",
        });
    }

    let mut expected_solvers = request.solver_identities().to_vec();
    expected_solvers.sort();
    let mut actual_solvers = evidence.solvers().to_vec();
    actual_solvers.sort();
    if actual_solvers != expected_solvers {
        errors.push(NativeVerificationBundleError::EvidenceProvenanceMismatch {
            request: request_id,
            field: "solvers",
        });
    }

    if let Some(expected_replay) = request.provenance().replay_identity()
        && evidence.replay() != expected_replay
    {
        errors.push(NativeVerificationBundleError::EvidenceProvenanceMismatch {
            request: request_id,
            field: "replay",
        });
    }
}

pub(crate) fn consumed_certificates_for_evidence(
    request: &NativeVerificationRequest,
    evidence: &NativeEvidenceBundle,
) -> Vec<ProofCertificateRef> {
    let NativeVerificationRequest::TrustVc(request) = request else {
        return Vec::new();
    };

    let evidence_obligations: BTreeSet<ProofId> = evidence.obligations().iter().copied().collect();
    request
        .certificates
        .iter()
        .filter(|cert| evidence_obligations.contains(&cert.obligation))
        .cloned()
        .collect()
}

pub(crate) fn validate_evidence_artifacts(
    evidence: &NativeEvidenceBundle,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let request = evidence.request();
    let suite = evidence.verifier_suite();
    if evidence.artifacts().is_empty() {
        errors.push(NativeVerificationBundleError::MissingEvidenceArtifacts { request, suite });
    }

    let mut names = BTreeSet::new();
    for artifact in evidence.artifacts() {
        if artifact.name.trim().is_empty() {
            errors.push(NativeVerificationBundleError::InvalidEvidenceArtifact {
                request,
                name: artifact.name.clone(),
                field: "name",
            });
        }
        if artifact.digest.is_zero() {
            errors.push(NativeVerificationBundleError::InvalidEvidenceArtifact {
                request,
                name: artifact.name.clone(),
                field: "digest",
            });
        }
        if artifact.digest.algorithm != ProofDigestAlgorithm::Sha256 {
            errors.push(NativeVerificationBundleError::InvalidEvidenceArtifact {
                request,
                name: artifact.name.clone(),
                field: "digest.algorithm",
            });
        }
        if !names.insert(artifact.name.clone()) {
            errors.push(NativeVerificationBundleError::DuplicateEvidenceArtifact {
                request,
                name: artifact.name.clone(),
            });
        }
        if !evidence_artifact_matches_bundle(evidence, artifact.kind) {
            errors.push(
                NativeVerificationBundleError::EvidenceArtifactSuiteMismatch {
                    request,
                    suite,
                    kind: artifact.kind,
                },
            );
        }
    }
}

pub(crate) fn evidence_artifact_matches_bundle(
    evidence: &NativeEvidenceBundle,
    kind: NativeEvidenceArtifactKind,
) -> bool {
    match evidence {
        NativeEvidenceBundle::TrustVc(bundle) => match bundle.mode {
            TrustVcVerificationMode::ImportProofCertificates => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustVcCertificateImport
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            // A DISCHARGED certificate is not an IMPORTED one, so this
            // deliberately admits NO certificate kind yet: reusing
            // `TrustVcCertificateImport` here would label a certificate trust-vc
            // derived itself as one it received, which downstream admission gates
            // read as provenance. The dedicated kind lands with the discharge
            // capability, not ahead of it.
            TrustVcVerificationMode::DischargeProofObligations => matches!(
                kind,
                NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            TrustVcVerificationMode::MergeProofCertificates => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustVcMergedCertificate
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
        },
        NativeEvidenceBundle::TrustMc(bundle) => match bundle.mode {
            TrustMcVerificationMode::BoundedModelCheck => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustMcModel
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::Btor2Trace
                    | NativeEvidenceArtifactKind::Btor2Proof
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            TrustMcVerificationMode::Chc => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustMcHornClauses
                    | NativeEvidenceArtifactKind::TrustMcModel
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::Btor2Trace
                    | NativeEvidenceArtifactKind::Btor2Proof
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            TrustMcVerificationMode::Pdr => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustMcHornClauses
                    | NativeEvidenceArtifactKind::TrustMcPdrTrace
                    | NativeEvidenceArtifactKind::TrustMcModel
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::Btor2Trace
                    | NativeEvidenceArtifactKind::Btor2Proof
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
        },
        NativeEvidenceBundle::TrustWp(bundle) => match bundle.mode {
            TrustWpVerificationMode::WeakestPrecondition => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustWpVerificationCondition
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            TrustWpVerificationMode::StrongestPostcondition => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustWpVerificationCondition
                    | NativeEvidenceArtifactKind::TrustWpReplayTrace
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
            TrustWpVerificationMode::Abduction => matches!(
                kind,
                NativeEvidenceArtifactKind::TrustWpVerificationCondition
                    | NativeEvidenceArtifactKind::TrustWpReplayTrace
                    | NativeEvidenceArtifactKind::TrustWpAbducedPrecondition
                    | NativeEvidenceArtifactKind::ReplayTranscript
                    | NativeEvidenceArtifactKind::NativeCompiledArtifact
                    | NativeEvidenceArtifactKind::BackendCapabilityMetadata
                    | NativeEvidenceArtifactKind::Other
            ),
        },
    }
}

pub(crate) fn validate_bundle_diagnostics(
    diagnostics: &NativeDiagnosticsPolicy,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    if !diagnostics.include_source_spans {
        errors.push(
            NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy {
                field: "include_source_spans",
            },
        );
    }
    if !diagnostics.include_lineage {
        errors.push(
            NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy {
                field: "include_lineage",
            },
        );
    }
    if diagnostics.emit_counterexamples && diagnostics.max_counterexamples == 0 {
        errors.push(
            NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy {
                field: "max_counterexamples",
            },
        );
    }
}

pub(crate) fn validate_diagnostics(
    request: NativeRequestId,
    diagnostics: &NativeDiagnosticsPolicy,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    if !diagnostics.include_source_spans {
        errors.push(NativeVerificationBundleError::InvalidDiagnosticsPolicy {
            request,
            field: "include_source_spans",
        });
    }
    if !diagnostics.include_lineage {
        errors.push(NativeVerificationBundleError::InvalidDiagnosticsPolicy {
            request,
            field: "include_lineage",
        });
    }
    if diagnostics.emit_counterexamples && diagnostics.max_counterexamples == 0 {
        errors.push(NativeVerificationBundleError::InvalidDiagnosticsPolicy {
            request,
            field: "max_counterexamples",
        });
    }
}

pub(crate) fn validate_adt_layout_fact(
    module: &Module,
    fact: &NativeAdtLayoutFact,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    match (&fact.ty, &fact.layout.kind) {
        (Ty::Struct(id), TyLayoutKind::Struct { id: layout_id, .. }) if id == layout_id => {
            if module.struct_def(*id).is_none() {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "ty.struct_id",
                });
            }
            match module.ty_layout_shape(&fact.ty) {
                Ok(expected) if expected != fact.layout => {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact: NativeCompilerFactRef::AdtLayout(fact.id),
                        field: "layout",
                    });
                }
                Ok(_) | Err(LayoutError::MissingStruct(_)) => {}
                Err(_) => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "layout",
                }),
            }
            if fact.enum_layout.is_some() {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "enum_layout",
                });
            }
        }
        (
            Ty::Enum(id),
            TyLayoutKind::Enum {
                id: layout_id,
                variants,
            },
        ) if id == layout_id => {
            let Some(enum_def) = module.enum_def(*id) else {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "ty.enum_id",
                });
                return;
            };
            if *variants != enum_def.variants.len() {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "layout.kind.variants",
                });
            }
            let Some(enum_layout) = &fact.enum_layout else {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "enum_layout",
                });
                return;
            };
            if enum_layout.enum_id != *id {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "enum_layout.enum_id",
                });
            }
            if enum_layout.variants.len() != enum_def.variants.len() {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::AdtLayout(fact.id),
                    field: "enum_layout.variants",
                });
            }
            validate_native_enum_layout_fact(fact, enum_layout, enum_def, errors);
        }
        (Ty::Struct(_), _) | (Ty::Enum(_), _) => {
            errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                fact: NativeCompilerFactRef::AdtLayout(fact.id),
                field: "layout.kind",
            });
        }
        _ => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::AdtLayout(fact.id),
            field: "ty",
        }),
    }
}

pub(crate) fn validate_native_enum_layout_fact(
    fact: &NativeAdtLayoutFact,
    enum_layout: &NativeEnumLayoutFact,
    enum_def: &crate::EnumDef,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let fact_ref = NativeCompilerFactRef::AdtLayout(fact.id);
    let mut invalid = |field| {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field,
        });
    };

    // Native enum layouts are frontend-supplied rustc facts. TrustIr validates the
    // evidence shape here but still does not derive enum layouts locally.
    let mut seen_variants = BTreeSet::new();
    for variant in &enum_layout.variants {
        if !seen_variants.insert(variant.variant_index) {
            invalid("enum_layout.variant_index");
        }
        let Some(expected) = enum_def.variants.get(variant.variant_index as usize) else {
            invalid("enum_layout.variant");
            continue;
        };
        if expected.name != variant.name {
            invalid("enum_layout.variant");
        }
        if variant.fields.len() != expected.fields.len() {
            invalid("enum_layout.variant.fields");
        }
        for (field_index, field) in variant.fields.iter().enumerate() {
            let Some(expected_ty) = expected.fields.get(field_index) else {
                continue;
            };
            if field.field != field_index as u32 {
                invalid("enum_layout.variant.fields");
            }
            if field.ty_shape != expected_ty.shape() {
                invalid("enum_layout.variant.fields.ty_shape");
            }
        }
        if variant.size_bits > fact.layout.size_bits {
            invalid("layout.size_bits");
        }
        match (fact.layout.align_bits, variant.align_bits) {
            (_, Some(0)) => invalid("enum_layout.variant.align_bits"),
            (Some(layout_align), Some(variant_align))
                if layout_align == 0
                    || layout_align < variant_align
                    || !layout_align.is_multiple_of(variant_align) =>
            {
                invalid("layout.align_bits");
            }
            _ => {}
        }
    }

    match enum_layout.tag_encoding {
        NativeEnumTagEncoding::Direct => {
            if enum_layout.niche.is_some() {
                invalid("enum_layout.niche");
            }
            match (enum_layout.tag_bits, enum_layout.discriminant_offset_bits) {
                (Some(tag_bits), Some(offset_bits)) => {
                    if tag_bits == 0 {
                        invalid("enum_layout.tag_bits");
                        return;
                    }
                    if offset_bits
                        .checked_add(u64::from(tag_bits))
                        .is_none_or(|end_bits| end_bits > fact.layout.size_bits)
                    {
                        invalid("enum_layout.discriminant_offset_bits");
                    }
                }
                (None, _) => invalid("enum_layout.tag_bits"),
                (_, None) => invalid("enum_layout.discriminant_offset_bits"),
            }
            let mut discriminants = BTreeSet::new();
            for variant in &enum_layout.variants {
                let Some(discriminant) = variant.discriminant else {
                    invalid("enum_layout.variant.discriminant");
                    continue;
                };
                if !discriminants.insert(discriminant) {
                    invalid("enum_layout.variant.discriminant");
                }
            }
        }
        NativeEnumTagEncoding::Niche => {
            if enum_layout.tag_bits.is_some() {
                invalid("enum_layout.tag_bits");
            }
            if enum_layout.discriminant_offset_bits.is_some() {
                invalid("enum_layout.discriminant_offset_bits");
            }
            let Some(niche) = &enum_layout.niche else {
                invalid("enum_layout.niche");
                return;
            };
            if niche.valid_range.start > niche.valid_range.end {
                invalid("enum_layout.niche.valid_range");
            }
            let Some(variant) = enum_def.variants.get(niche.variant_index as usize) else {
                invalid("enum_layout.niche.variant_index");
                return;
            };
            if let Some(field) = niche.field
                && variant.fields.get(field as usize).is_none()
            {
                invalid("enum_layout.niche.field");
            }
        }
        NativeEnumTagEncoding::Untagged => {
            if enum_layout.tag_bits.is_some() {
                invalid("enum_layout.tag_bits");
            }
            if enum_layout.discriminant_offset_bits.is_some() {
                invalid("enum_layout.discriminant_offset_bits");
            }
            if enum_layout.niche.is_some() {
                invalid("enum_layout.niche");
            }
            if enum_layout
                .variants
                .iter()
                .any(|variant| variant.discriminant.is_some())
            {
                invalid("enum_layout.variant.discriminant");
            }
        }
    }
}

pub(crate) fn validate_fat_pointer_fact(
    module: &Module,
    fact: &NativeFatPointerFact,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    match fact.ty.pointer_layout_shape(module.pointer_bits()) {
        Some(expected) if expected == fact.layout && expected.is_fat() => {}
        Some(_) => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::FatPointer(fact.id),
            field: "layout",
        }),
        None => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::FatPointer(fact.id),
            field: "ty",
        }),
    }
}

pub(crate) fn validate_trait_object_metadata_fact(
    module: &Module,
    fact: &NativeTraitObjectMetadataFact,
    known_functions: &BTreeSet<FuncId>,
    known_obligations: &BTreeSet<ProofId>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let fact_ref = NativeCompilerFactRef::TraitObjectMetadata(fact.id);
    if fact.ty.pointer_layout_shape(module.pointer_bits())
        != Some(PointerLayoutShape::fat(
            module.pointer_bits(),
            PointerMetadataShape::VTable {
                trait_id: fact.trait_id,
            },
        ))
    {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "ty",
        });
    }
    if !matches!(
        fact.ty,
        Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id }) if trait_id == fact.trait_id
    ) {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "trait_id",
        });
    }
    if fact.vtable_symbol.trim().is_empty() {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "vtable_symbol",
        });
    }
    if fact.stable_digest.is_zero() {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "stable_digest",
        });
    }
    if fact.stable_digest.algorithm != ProofDigestAlgorithm::Sha256 {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "stable_digest.algorithm",
        });
    }
    if let Some(function) = fact.function
        && !known_functions.contains(&function)
    {
        errors.push(NativeVerificationBundleError::UnknownCompilerFactFunction {
            fact: fact_ref,
            function,
        });
    }
    for obligation in &fact.obligations {
        if !known_obligations.contains(obligation) {
            errors.push(
                NativeVerificationBundleError::UnknownCompilerFactObligation {
                    fact: fact_ref,
                    obligation: *obligation,
                },
            );
        }
    }
    validate_trait_object_upcast_metadata_fact(fact, fact_ref, errors);
}

pub(crate) fn validate_trait_object_upcast_metadata_fact(
    fact: &NativeTraitObjectMetadataFact,
    fact_ref: NativeCompilerFactRef,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    match (fact.source_trait_id, &fact.source_ty) {
        (None, None) if fact.upcast_path.is_empty() => {}
        (Some(source_trait_id), Some(source_ty)) => {
            if !matches!(
                source_ty,
                Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id })
                    if *trait_id == source_trait_id
            ) {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: fact_ref,
                    field: "source_ty",
                });
            }
            if source_trait_id == fact.trait_id {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: fact_ref,
                    field: "source_trait_id",
                });
            }
            if fact.upcast_path.first() != Some(&source_trait_id)
                || fact.upcast_path.last() != Some(&fact.trait_id)
            {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: fact_ref,
                    field: "upcast_path",
                });
            }
        }
        _ => {
            errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                fact: fact_ref,
                field: "upcast",
            });
        }
    }
}

pub(crate) fn validate_pointer_offset_fact(
    module: &Module,
    fact: &NativePointerOffsetFact,
    known_functions: &BTreeSet<FuncId>,
    known_obligations: &BTreeSet<ProofId>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let fact_ref = NativeCompilerFactRef::PointerOffset(fact.id);
    if !known_functions.contains(&fact.function) {
        errors.push(NativeVerificationBundleError::UnknownCompilerFactFunction {
            fact: fact_ref,
            function: fact.function,
        });
    }
    if !fact.base_ty.is_pointer_like() {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "base_ty",
        });
    }
    if !fact.offset_ty.is_signed() {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "offset_ty",
        });
    }
    match module.ty_layout_shape(&fact.pointee_ty) {
        Ok(expected) => {
            if expected != fact.element_layout {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: fact_ref,
                    field: "element_layout",
                });
            }
            if expected.size_bits != fact.stride_bits || !fact.stride_bits.is_multiple_of(8) {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: fact_ref,
                    field: "stride_bits",
                });
            }
        }
        Err(LayoutError::EnumLayoutUnavailable(_) | LayoutError::UnsupportedTyShape(_)) => {}
        Err(_) => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "element_layout",
        }),
    }
    if let NativePointerOffsetProvenance::Unsupported(unsupported) = &fact.provenance {
        if unsupported.detail.trim().is_empty() {
            errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                fact: fact_ref,
                field: "provenance.unsupported.detail",
            });
        }
        if !fact.obligations.is_empty() {
            errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                fact: fact_ref,
                field: "provenance",
            });
        }
    }
    validate_pointer_offset_fact_values(module, fact, errors);
    for obligation in &fact.obligations {
        if !known_obligations.contains(obligation) {
            errors.push(
                NativeVerificationBundleError::UnknownCompilerFactObligation {
                    fact: fact_ref,
                    obligation: *obligation,
                },
            );
        }
    }
}

pub(crate) fn validate_pointer_offset_fact_values(
    module: &Module,
    fact: &NativePointerOffsetFact,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let Some(function) = module.function_by_id(fact.function) else {
        return;
    };
    let fact_ref = NativeCompilerFactRef::PointerOffset(fact.id);
    if native_function_value_ty(function, fact.base).as_ref() != Some(&fact.base_ty) {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "base",
        });
    }
    if native_function_value_ty(function, fact.offset).as_ref() != Some(&fact.offset_ty) {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "offset",
        });
    }
    if let Some(result) = fact.result
        && !function_has_matching_pointer_offset_result(function, result, fact)
    {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "result",
        });
    }
}

pub(crate) fn function_has_matching_pointer_offset_result(
    function: &Function,
    result: ValueId,
    fact: &NativePointerOffsetFact,
) -> bool {
    let mut result_nodes = function
        .instructions()
        .filter(|node| node.results.contains(&result));
    let Some(node) = result_nodes.next() else {
        return false;
    };
    if result_nodes.next().is_some() || node.results.len() != 1 {
        return false;
    }
    matches!(
        &node.inst,
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } if pointee_ty == &fact.pointee_ty
            && *base == fact.base
            && indices.as_slice() == [fact.offset]
    )
}

pub(crate) fn native_function_value_ty(function: &Function, value: ValueId) -> Option<Ty> {
    let needle = value.index();
    for block in &function.blocks {
        for (param, ty) in &block.params {
            if param.index() == needle {
                return Some(ty.clone());
            }
        }
        for node in &block.body {
            if node.results.iter().any(|result| result.index() == needle)
                && let Some(ty) = native_inst_result_ty(&node.inst)
            {
                return Some(ty);
            }
        }
    }
    None
}

pub(crate) fn native_inst_result_ty(inst: &Inst) -> Option<Ty> {
    match inst {
        Inst::BinOp { ty, .. } => Some(ty.clone()),
        Inst::UnOp { ty, .. } => Some(ty.clone()),
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => Some(ty.comparison_result_ty()),
        Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
        Inst::Load { ty, .. } => Some(ty.clone()),
        Inst::Alloca { .. } | Inst::HeapAlloc { .. } | Inst::GEP { .. } | Inst::PtrData { .. } => {
            Some(Ty::Ptr)
        }
        Inst::PtrMetadata { metadata_ty, .. } => Some(metadata_ty.clone()),
        Inst::PtrFromParts { ptr_ty, .. } => Some(ptr_ty.clone()),
        Inst::AtomicLoad { ty, .. } | Inst::AtomicRMW { ty, .. } => Some(ty.clone()),
        Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => Some(ty.clone()),
        Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => Some(Ty::Ptr),
        Inst::IsUnique { .. } => Some(Ty::Bool),
        Inst::DialectOp(op) if op.result_tys.len() == 1 => Some(op.result_tys[0].clone()),
        _ => None,
    }
}

pub(crate) fn validate_cast_fact(
    module: &Module,
    fact: &NativeCastFact,
    known_functions: &BTreeSet<FuncId>,
    known_obligations: &BTreeSet<ProofId>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let fact_ref = NativeCompilerFactRef::Cast(fact.id);
    if !known_functions.contains(&fact.function) {
        errors.push(NativeVerificationBundleError::UnknownCompilerFactFunction {
            fact: fact_ref,
            function: fact.function,
        });
    }
    validate_cast_fact_result(module, fact, errors);
    for obligation in &fact.obligations {
        if !known_obligations.contains(obligation) {
            errors.push(
                NativeVerificationBundleError::UnknownCompilerFactObligation {
                    fact: fact_ref,
                    obligation: *obligation,
                },
            );
        }
    }
    if !fact.op.is_layout_sensitive() && fact.evidence != CastLayoutEvidence::NotLayoutSensitive {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "evidence",
        });
    }
    match module.layout_sensitive_cast_evidence(fact.op, &fact.source_ty, &fact.target_ty) {
        Ok(expected) if expected == fact.evidence => {}
        Ok(_) => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "evidence",
        }),
        Err(LayoutError::EnumLayoutUnavailable(_) | LayoutError::UnsupportedTyShape(_)) => {}
        Err(_) => errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: fact_ref,
            field: "evidence",
        }),
    }
}

pub(crate) fn validate_cast_fact_result(
    module: &Module,
    fact: &NativeCastFact,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let Some(result) = fact.result else {
        return;
    };
    let Some(function) = module.function_by_id(fact.function) else {
        return;
    };
    if !function_has_matching_cast_result(function, result, fact) {
        errors.push(NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Cast(fact.id),
            field: "result",
        });
    }
}

pub(crate) fn function_has_matching_cast_result(
    function: &Function,
    result: ValueId,
    fact: &NativeCastFact,
) -> bool {
    let mut result_nodes = function
        .instructions()
        .filter(|node| node.results.contains(&result));
    let Some(node) = result_nodes.next() else {
        return false;
    };
    if result_nodes.next().is_some() || node.results.len() != 1 {
        return false;
    }
    matches!(
        &node.inst,
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            ..
        } if *op == fact.op && src_ty == &fact.source_ty && dst_ty == &fact.target_ty
    )
}

pub(crate) struct NativeFactMapCollection<'a> {
    pub(crate) fat_pointer_facts: &'a BTreeMap<NativeCompilerFactId, &'a NativeFatPointerFact>,
    pub(crate) trait_object_metadata_facts:
        &'a BTreeMap<NativeCompilerFactId, &'a NativeTraitObjectMetadataFact>,
    pub(crate) pointer_offset_facts:
        &'a BTreeMap<NativeCompilerFactId, &'a NativePointerOffsetFact>,
    pub(crate) cast_facts: &'a BTreeMap<NativeCompilerFactId, &'a NativeCastFact>,
    pub(crate) monomorphization_facts:
        &'a BTreeMap<NativeMonomorphizationId, &'a NativeMonomorphizationFact>,
}

pub(crate) fn validate_obligation_source_fact_binding(
    source: &NativeObligationSource,
    fact: NativeCompilerFactRef,
    facts: &NativeFactMapCollection<'_>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    match fact {
        NativeCompilerFactRef::FatPointer(id) => {
            if let Some(fat_pointer) = facts.fat_pointer_facts.get(&id)
                && is_trait_object_fat_pointer_fact(fat_pointer)
                && !source_has_matching_trait_object_metadata_fact(
                    source,
                    fat_pointer,
                    facts.trait_object_metadata_facts,
                )
            {
                errors.push(
                    NativeVerificationBundleError::MissingObligationSourceTraitObjectMetadataFact {
                        obligation: source.obligation,
                        fat_pointer: id,
                    },
                );
            }
        }
        NativeCompilerFactRef::TraitObjectMetadata(id) => {
            if let Some(metadata) = facts.trait_object_metadata_facts.get(&id) {
                if let Some(function) = metadata.function {
                    validate_obligation_source_fact_function(source, fact, Some(function), errors);
                }
                if !metadata.obligations.contains(&source.obligation) {
                    errors.push(
                        NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                            obligation: source.obligation,
                            fact,
                        },
                    );
                }
            }
        }
        NativeCompilerFactRef::PointerOffset(id) => {
            if let Some(pointer_offset) = facts.pointer_offset_facts.get(&id) {
                validate_obligation_source_fact_function(
                    source,
                    fact,
                    Some(pointer_offset.function),
                    errors,
                );
                if !pointer_offset.obligations.contains(&source.obligation) {
                    errors.push(
                        NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                            obligation: source.obligation,
                            fact,
                        },
                    );
                }
                if matches!(
                    pointer_offset.provenance,
                    NativePointerOffsetProvenance::Unsupported(_)
                ) {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact,
                        field: "provenance",
                    });
                }
            }
        }
        NativeCompilerFactRef::Cast(id) => {
            if let Some(cast) = facts.cast_facts.get(&id) {
                validate_obligation_source_fact_function(source, fact, Some(cast.function), errors);
                if !cast.obligations.contains(&source.obligation) {
                    errors.push(
                        NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                            obligation: source.obligation,
                            fact,
                        },
                    );
                }
            }
        }
        NativeCompilerFactRef::Monomorphization(id) if source.monomorphization != Some(id) => {
            if let Some(monomorphization) = facts.monomorphization_facts.get(&id) {
                validate_obligation_source_fact_function(
                    source,
                    fact,
                    monomorphization.function,
                    errors,
                );
            }
        }
        NativeCompilerFactRef::AdtLayout(_) | NativeCompilerFactRef::Monomorphization(_) => {}
    }
}

pub(crate) fn validate_trait_object_metadata_source_coverage(
    source: &NativeObligationSource,
    fat_pointer_facts: &BTreeMap<NativeCompilerFactId, &NativeFatPointerFact>,
    trait_object_metadata_facts: &BTreeMap<NativeCompilerFactId, &NativeTraitObjectMetadataFact>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    for fact in &source.facts {
        let NativeCompilerFactRef::TraitObjectMetadata(id) = fact else {
            continue;
        };
        let Some(metadata) = trait_object_metadata_facts.get(id) else {
            continue;
        };
        let has_matching_fat_pointer = source.facts.iter().any(|source_fact| {
            let NativeCompilerFactRef::FatPointer(fat_pointer_id) = source_fact else {
                return false;
            };
            let Some(fat_pointer) = fat_pointer_facts.get(fat_pointer_id) else {
                return false;
            };
            trait_object_metadata_matches_fat_pointer(metadata, fat_pointer)
        });
        if !has_matching_fat_pointer {
            errors.push(
                NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                    obligation: source.obligation,
                    fact: *fact,
                },
            );
        }
    }
}

pub(crate) fn is_trait_object_fat_pointer_fact(fact: &NativeFatPointerFact) -> bool {
    matches!(
        (&fact.ty, fact.layout.metadata),
        (
            Ty::FatPtr(crate::FatPtrKind::TraitObject { .. }),
            Some(PointerMetadataShape::VTable { .. })
        )
    )
}

pub(crate) fn source_has_matching_trait_object_metadata_fact(
    source: &NativeObligationSource,
    fat_pointer: &NativeFatPointerFact,
    trait_object_metadata_facts: &BTreeMap<NativeCompilerFactId, &NativeTraitObjectMetadataFact>,
) -> bool {
    source.facts.iter().any(|fact| {
        let NativeCompilerFactRef::TraitObjectMetadata(id) = fact else {
            return false;
        };
        let Some(metadata) = trait_object_metadata_facts.get(id) else {
            return false;
        };
        trait_object_metadata_matches_fat_pointer(metadata, fat_pointer)
    })
}

pub(crate) fn trait_object_metadata_matches_fat_pointer(
    metadata: &NativeTraitObjectMetadataFact,
    fat_pointer: &NativeFatPointerFact,
) -> bool {
    metadata.ty == fat_pointer.ty
        && fat_pointer.layout.metadata
            == Some(PointerMetadataShape::VTable {
                trait_id: metadata.trait_id,
            })
}

pub(crate) fn obligation_source_has_bound_cast_fact(
    source: &NativeObligationSource,
    cast_facts: &BTreeMap<NativeCompilerFactId, &NativeCastFact>,
) -> bool {
    source.facts.iter().any(|fact| {
        let NativeCompilerFactRef::Cast(id) = fact else {
            return false;
        };
        let Some(cast) = cast_facts.get(id) else {
            return false;
        };
        source.function == Some(cast.function) && cast.obligations.contains(&source.obligation)
    })
}

pub(crate) fn obligation_source_has_bound_pointer_offset_fact(
    source: &NativeObligationSource,
    pointer_offset_facts: &BTreeMap<NativeCompilerFactId, &NativePointerOffsetFact>,
) -> bool {
    source.facts.iter().any(|fact| {
        let NativeCompilerFactRef::PointerOffset(id) = fact else {
            return false;
        };
        let Some(pointer_offset) = pointer_offset_facts.get(id) else {
            return false;
        };
        source.function == Some(pointer_offset.function)
            && pointer_offset.obligations.contains(&source.obligation)
            && matches!(
                pointer_offset.provenance,
                NativePointerOffsetProvenance::SameAsBase
            )
    })
}

pub(crate) fn validate_obligation_source_fact_function(
    source: &NativeObligationSource,
    fact: NativeCompilerFactRef,
    actual: Option<FuncId>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    if let Some(actual) = actual {
        match source.function {
            Some(expected) if expected == actual => {}
            expected => {
                errors.push(
                    NativeVerificationBundleError::ObligationSourceFactFunctionMismatch {
                        obligation: source.obligation,
                        fact,
                        expected,
                        actual: Some(actual),
                    },
                );
            }
        }
    }
}

pub(crate) fn validate_trust_vc_request(
    request: &TrustVcNativeRequest,
    known_certificate_evidence: &BTreeMap<ProofCertificateRef, &ProofCertificate>,
    known_obligation_status: &BTreeMap<ProofId, ProofStatus>,
    // Strong-status obligations backed by evidence replayed in this process.
    // A public status, opaque solver string/bytes, or lineage-only match never
    // enters this set.
    replayed_authority: &BTreeSet<ProofId>,
    _lineage_certificates: &BTreeSet<ProofCertificateRef>,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    let certificate_obligations: BTreeSet<ProofId> = request
        .certificates
        .iter()
        .map(|cert| cert.obligation)
        .collect();
    for obligation in &request.obligations {
        if !certificate_obligations.contains(obligation) {
            errors.push(
                NativeVerificationBundleError::MissingTrustVcEvidenceForObligation {
                    request: request.id,
                    obligation: *obligation,
                },
            );
        }
    }

    for cert_ref in &request.certificates {
        if let Some(cert) = known_certificate_evidence.get(cert_ref) {
            // SOUNDNESS: neither strong public label is authority. The exact
            // certificate must have been replayed by a validator capability in
            // this process; opaque SMT/Lean/Kani strings and self-digests do not
            // take the discharged path.
            if let Some(status) = known_obligation_status.get(&cert_ref.obligation) {
                let admissible_as_discharged = match status {
                    ProofStatus::Discharged | ProofStatus::Certified => {
                        replayed_authority.contains(&cert_ref.obligation)
                    }
                    ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Trusted => false,
                };
                if !admissible_as_discharged {
                    errors.push(
                        NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                            request: request.id,
                            obligation: cert_ref.obligation,
                            prover: cert_ref.prover.clone(),
                            status: *status,
                        },
                    );
                }
            }
            if request.options.trusted_evidence == TrustVcTrustedEvidencePolicy::Reject
                && cert.uses_trusted_evidence()
            {
                errors.push(NativeVerificationBundleError::TrustedCertificateRejected {
                    request: request.id,
                    obligation: cert_ref.obligation,
                    prover: cert_ref.prover.clone(),
                });
            }
        }
    }
}

pub(crate) fn validate_trust_mc_request(
    request: &TrustMcNativeRequest,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    match request.mode {
        TrustMcVerificationMode::BoundedModelCheck => {
            if request.options.bmc.unwind_limit == 0 {
                errors.push(NativeVerificationBundleError::InvalidTrustMcBmcOptions {
                    request: request.id,
                    field: "bmc.unwind_limit",
                });
            }
        }
        TrustMcVerificationMode::Chc => {
            if !request.options.chc.emit_horn_clauses {
                errors.push(NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: request.id,
                    field: "chc.emit_horn_clauses",
                });
            }
            if let Some(max_frames) = request.options.chc.pdr.max_frames
                && max_frames == 0
            {
                errors.push(NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: request.id,
                    field: "chc.pdr.max_frames",
                });
            }
        }
        TrustMcVerificationMode::Pdr => {
            if !request.options.chc.pdr.enabled {
                errors.push(NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: request.id,
                    field: "chc.pdr.enabled",
                });
            }
            if !request.options.chc.emit_horn_clauses {
                errors.push(NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: request.id,
                    field: "chc.emit_horn_clauses",
                });
            }
            if let Some(max_frames) = request.options.chc.pdr.max_frames
                && max_frames == 0
            {
                errors.push(NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: request.id,
                    field: "chc.pdr.max_frames",
                });
            }
        }
    }
}

pub(crate) fn validate_trust_wp_request(
    request: &TrustWpNativeRequest,
    errors: &mut Vec<NativeVerificationBundleError>,
) {
    if request.mode == TrustWpVerificationMode::StrongestPostcondition {
        let context = request.provenance.replay_context();
        let has_assumption = context
            .atoms
            .iter()
            .any(|atom| atom.kind == NativeReplayAtomKind::Assumption);
        let has_assertion = context.atoms.iter().any(|atom| {
            atom.kind == NativeReplayAtomKind::Assertion && atom.assertion_id.is_some()
        });
        if !has_assumption || !has_assertion {
            errors.push(
                NativeVerificationBundleError::MissingTrustWpStrongestPostconditionContext(
                    request.id,
                ),
            );
        }
    }
    if !request.options.emit_verification_conditions {
        errors.push(NativeVerificationBundleError::InvalidTrustWpOptions {
            request: request.id,
            field: "emit_verification_conditions",
        });
    }
    if request.mode == TrustWpVerificationMode::Abduction
        && request.options.max_abduced_preconditions == 0
    {
        errors.push(NativeVerificationBundleError::InvalidTrustWpOptions {
            request: request.id,
            field: "max_abduced_preconditions",
        });
    }
}

pub(crate) fn lineage_closure(
    manifest: &ProofLineageManifest,
    roots: &[ProofLineageId],
) -> (
    BTreeSet<ProofId>,
    BTreeSet<ProofCertificateRef>,
    BTreeSet<ProofDigest>,
) {
    let nodes: BTreeMap<ProofLineageId, &crate::ProofLineageNode> =
        manifest.nodes.iter().map(|node| (node.id, node)).collect();
    let mut seen = BTreeSet::new();
    let mut stack = roots.to_vec();
    let mut obligations = BTreeSet::new();
    let mut certificates = BTreeSet::new();
    let mut sources = BTreeSet::new();

    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(node) = nodes.get(&id) {
            obligations.extend(node.obligations.iter().copied());
            certificates.extend(node.certificates.iter().cloned());
            sources.insert(node.source_module);
            stack.extend(node.depends_on.iter().copied());
        }
    }

    (obligations, certificates, sources)
}

pub(crate) fn source_bound_lineage_membership(
    manifest: &ProofLineageManifest,
    roots: &[ProofLineageId],
    source_digest: Option<ProofDigest>,
) -> (BTreeSet<ProofId>, BTreeSet<ProofCertificateRef>) {
    let mut obligations = BTreeSet::new();
    let mut certificates = BTreeSet::new();

    for root in roots {
        let root_slice = [*root];
        let (root_obligations, root_certificates, root_sources) =
            lineage_closure(manifest, &root_slice);
        if source_digest.is_none_or(|source| root_sources.contains(&source)) {
            obligations.extend(root_obligations);
            certificates.extend(root_certificates);
        }
    }

    (obligations, certificates)
}
