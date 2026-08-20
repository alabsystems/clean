// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portable fixed-lane vector dialect.
//!
//! The `vector.*` dialect gives producers a structured way to describe lane
//! packing, constant-lane extraction/insertion, and logical mask compaction
//! without naming target opcodes. Backends such as TrustIr may lower these ops to
//! MOVD/MOVQ/PINSR/PEXTR/PMOVMSKB sequences, but the payload semantics remain
//! target-independent.

use crate::dialect::{AttrValue, Dialect, DialectError, DialectInst};
use crate::ty::Ty;
use crate::value::ValueId;

pub const DIALECT: &str = "vector";
pub const PACK_LANES_OP: &str = "pack_lanes";
pub const EXTRACT_LANE_OP: &str = "extract_lane";
pub const INSERT_LANE_OP: &str = "insert_lane";
pub const MASK_TO_BITS_OP: &str = "mask_to_bits";
/// Horizontal cross-lane reduction of an integer lane vector to a scalar
/// (`vector.reduce`). The `kind` attribute selects an associative, bounded
/// fold: [`REDUCE_ADD`] (wrapping integer sum) or [`REDUCE_OR`] (bitwise or).
pub const REDUCE_OP: &str = "reduce";
/// Static-index lane permutation (`vector.shuffle`). The `indices` byte
/// attribute maps each result lane to a source lane; every index must be in
/// range for the source vector.
pub const SHUFFLE_OP: &str = "shuffle";
/// Per-lane fused multiply-add over float lane vectors (`vector.fma`),
/// computing `a * b + c` with a single IEEE-754 rounding step per lane.
pub const FMA_OP: &str = "fma";

const OPS: &[&str] = &[
    PACK_LANES_OP,
    EXTRACT_LANE_OP,
    INSERT_LANE_OP,
    MASK_TO_BITS_OP,
    REDUCE_OP,
    SHUFFLE_OP,
    FMA_OP,
];
const VALIDATE_PASS: &str = "vector.validate";
const BIT_ORDER_ATTR: &str = "bit_order";
const LSB_LANE0: &str = "lsb_lane0";
const REDUCE_KIND_ATTR: &str = "kind";
const SHUFFLE_INDICES_ATTR: &str = "indices";
/// Wrapping integer horizontal sum (`vector.reduce kind = "add"`).
pub const REDUCE_ADD: &str = "add";
/// Bitwise-or horizontal reduction (`vector.reduce kind = "or"`).
pub const REDUCE_OR: &str = "or";

/// Associative, bounded horizontal reduction kinds supported by
/// [`REDUCE_OP`]. Both have a well-defined identity element and are
/// order-insensitive, so the left fold the interpreter computes agrees with
/// any tree reduction a backend might emit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReduceKind {
    /// Wrapping integer sum across lanes (identity `0`).
    Add,
    /// Bitwise or across lanes (identity `0`).
    Or,
}

impl ReduceKind {
    /// The canonical attribute spelling for this reduction kind.
    pub fn as_str(self) -> &'static str {
        match self {
            ReduceKind::Add => REDUCE_ADD,
            ReduceKind::Or => REDUCE_OR,
        }
    }

    fn parse(raw: &str) -> Option<Self> {
        match raw {
            REDUCE_ADD => Some(ReduceKind::Add),
            REDUCE_OR => Some(ReduceKind::Or),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackLanesSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtractLaneSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
    pub lane: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertLaneSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
    pub lane: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskToBitsSpec {
    pub mask_ty: Ty,
    pub lanes: u32,
    pub result_ty: Ty,
}

/// Decoded `vector.reduce`: a horizontal fold of an integer lane vector to a
/// single scalar of the element type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReduceSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
    pub kind: ReduceKind,
}

/// Decoded `vector.shuffle`: a static lane permutation. `indices[j]` is the
/// source lane copied into result lane `j`; the result vector has the same
/// type (and lane count) as the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShuffleSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
    pub indices: Vec<u8>,
}

/// Decoded `vector.fma`: per-lane fused multiply-add `a * b + c` over a float
/// lane vector. All three operands and the result share `vector_ty`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmaSpec {
    pub vector_ty: Ty,
    pub elem_ty: Ty,
    pub lanes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VectorSpec {
    PackLanes(PackLanesSpec),
    ExtractLane(ExtractLaneSpec),
    InsertLane(InsertLaneSpec),
    MaskToBits(MaskToBitsSpec),
    Reduce(ReduceSpec),
    Shuffle(ShuffleSpec),
    Fma(FmaSpec),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct VectorDialect;

impl Dialect for VectorDialect {
    fn name(&self) -> &'static str {
        DIALECT
    }

    fn version(&self) -> u32 {
        1
    }

    fn ops(&self) -> &'static [&'static str] {
        OPS
    }

    fn validate(&self, inst: &DialectInst) -> Result<(), DialectError> {
        inst.validate_names()?;
        if inst.dialect != self.name() {
            return Err(DialectError::NameMismatch {
                expected: self.name(),
                got: inst.dialect.clone(),
            });
        }
        if !self.has_op(&inst.op) {
            return Err(DialectError::UnknownOp {
                dialect: self.name(),
                op: inst.op.clone(),
            });
        }
        decode(inst)
            .map(|_| ())
            .map_err(|reason| DialectError::LoweringFailed {
                pass: VALIDATE_PASS.to_string(),
                reason,
            })
    }
}

pub fn pack_lanes(vector_ty: Ty, lanes: impl IntoIterator<Item = ValueId>) -> DialectInst {
    DialectInst::new(DIALECT, PACK_LANES_OP)
        .with_operands(lanes)
        .with_result_ty(vector_ty)
}

/// Build the canonical repeated-operand spelling of a vector splat.
///
/// This is still just `vector.pack_lanes`: no extra opcode or semantic case is
/// introduced. Consumers that optimize broadcasts can recognize the repeated
/// operands directly.
pub fn pack_lanes_repeated(vector_ty: Ty, lane: ValueId) -> Result<DialectInst, String> {
    let (_elem_ty, lanes) = supported_lane_vector_shape(&vector_ty).ok_or_else(|| {
        format!(
            "{DIALECT}.{PACK_LANES_OP} repeated-lane pack supports only <16 x i8>, <8 x i16>, <4 x i32>, <2 x i64>, and <8 x i8>, got {vector_ty:?}"
        )
    })?;
    Ok(pack_lanes(vector_ty, vec![lane; lanes as usize]))
}

pub fn v4_i32_splat_lane(lane: ValueId) -> Result<DialectInst, String> {
    pack_lanes_repeated(Ty::v4_i32(), lane)
}

pub fn v2_i64_splat_lane(lane: ValueId) -> Result<DialectInst, String> {
    pack_lanes_repeated(Ty::v2_i64(), lane)
}

pub fn extract_lane(vector_ty: Ty, vector: ValueId, lane: u32) -> DialectInst {
    let result_ty = vector_elem_ty(&vector_ty).unwrap_or(Ty::Never);
    DialectInst::new(DIALECT, EXTRACT_LANE_OP)
        .with_operand(vector)
        .with_result_ty(result_ty)
        .with_attr("vector_ty", AttrValue::Ty(vector_ty))
        .with_attr("lane", AttrValue::U64(u64::from(lane)))
}

pub fn insert_lane(vector_ty: Ty, vector: ValueId, lane: u32, value: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, INSERT_LANE_OP)
        .with_operands([vector, value])
        .with_result_ty(vector_ty)
        .with_attr("lane", AttrValue::U64(u64::from(lane)))
}

pub fn mask_to_bits(mask_ty: Ty, mask: ValueId, result_ty: Ty) -> DialectInst {
    DialectInst::new(DIALECT, MASK_TO_BITS_OP)
        .with_operand(mask)
        .with_result_ty(result_ty)
        .with_attr("mask_ty", AttrValue::Ty(mask_ty))
        .with_attr(BIT_ORDER_ATTR, AttrValue::Str(LSB_LANE0.to_string()))
}

/// Build `vector.reduce`: fold an integer lane vector down to one scalar of the
/// element type using the associative `kind` fold.
pub fn reduce(vector_ty: Ty, vector: ValueId, kind: ReduceKind) -> DialectInst {
    let result_ty = vector_elem_ty(&vector_ty).unwrap_or(Ty::Never);
    DialectInst::new(DIALECT, REDUCE_OP)
        .with_operand(vector)
        .with_result_ty(result_ty)
        .with_attr("vector_ty", AttrValue::Ty(vector_ty))
        .with_attr(REDUCE_KIND_ATTR, AttrValue::Str(kind.as_str().to_string()))
}

/// Build `vector.shuffle`: produce a vector whose lane `j` is the source
/// vector's lane `indices[j]`. The result vector type equals the source type.
pub fn shuffle(vector_ty: Ty, vector: ValueId, indices: impl Into<Vec<u8>>) -> DialectInst {
    DialectInst::new(DIALECT, SHUFFLE_OP)
        .with_operand(vector)
        .with_result_ty(vector_ty)
        .with_attr(SHUFFLE_INDICES_ATTR, AttrValue::Bytes(indices.into()))
}

/// Build `vector.fma`: per-lane fused multiply-add `a * b + c` over a float
/// lane vector. All operands and the result share `vector_ty`.
pub fn fma(vector_ty: Ty, a: ValueId, b: ValueId, c: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, FMA_OP)
        .with_operands([a, b, c])
        .with_result_ty(vector_ty)
}

pub fn is_vector_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && OPS.contains(&inst.op.as_str())
}

pub fn is_vector_dialect_inst(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT
}

pub fn is_pack_lanes_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == PACK_LANES_OP
}

pub fn is_extract_lane_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == EXTRACT_LANE_OP
}

pub fn is_insert_lane_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == INSERT_LANE_OP
}

pub fn is_mask_to_bits_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == MASK_TO_BITS_OP
}

pub fn is_reduce_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == REDUCE_OP
}

pub fn is_shuffle_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == SHUFFLE_OP
}

pub fn is_fma_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == FMA_OP
}

pub fn decode(inst: &DialectInst) -> Result<VectorSpec, String> {
    match inst.op.as_str() {
        PACK_LANES_OP => decode_pack_lanes(inst).map(VectorSpec::PackLanes),
        EXTRACT_LANE_OP => decode_extract_lane(inst).map(VectorSpec::ExtractLane),
        INSERT_LANE_OP => decode_insert_lane(inst).map(VectorSpec::InsertLane),
        MASK_TO_BITS_OP => decode_mask_to_bits(inst).map(VectorSpec::MaskToBits),
        REDUCE_OP => decode_reduce(inst).map(VectorSpec::Reduce),
        SHUFFLE_OP => decode_shuffle(inst).map(VectorSpec::Shuffle),
        FMA_OP => decode_fma(inst).map(VectorSpec::Fma),
        other => Err(format!(
            "unknown {DIALECT} op {other:?}; expected one of {OPS:?}"
        )),
    }
}

/// Decode a `vector.*` op and verify the SSA operand types supplied by a typed
/// consumer.
///
/// `DialectInst` stores operand ids, not their types. Registry validation can
/// therefore check payload arity, result types, and attributes, while lowering
/// consumers with an SSA type map should call this helper before selecting a
/// fast lane-pack/extract/mask lowering.
pub fn decode_with_operand_tys(
    inst: &DialectInst,
    operand_tys: &[Ty],
) -> Result<VectorSpec, String> {
    let spec = decode(inst)?;
    require_operand_ty_count(inst, operand_tys)?;
    match &spec {
        VectorSpec::PackLanes(spec) => {
            for index in 0..operand_tys.len() {
                require_operand_ty(inst, operand_tys, index, &spec.elem_ty, "lane")?;
            }
        }
        VectorSpec::ExtractLane(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.vector_ty, "vector")?;
        }
        VectorSpec::InsertLane(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.vector_ty, "vector")?;
            require_operand_ty(inst, operand_tys, 1, &spec.elem_ty, "lane value")?;
        }
        VectorSpec::MaskToBits(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.mask_ty, "mask")?;
        }
        VectorSpec::Reduce(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.vector_ty, "vector")?;
        }
        VectorSpec::Shuffle(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.vector_ty, "vector")?;
        }
        VectorSpec::Fma(spec) => {
            require_operand_ty(inst, operand_tys, 0, &spec.vector_ty, "multiplicand")?;
            require_operand_ty(inst, operand_tys, 1, &spec.vector_ty, "multiplier")?;
            require_operand_ty(inst, operand_tys, 2, &spec.vector_ty, "addend")?;
        }
    }
    Ok(spec)
}

pub fn decode_pack_lanes(inst: &DialectInst) -> Result<PackLanesSpec, String> {
    check_header(inst, PACK_LANES_OP)?;
    require_result_count(inst, 1)?;
    let vector_ty = inst.result_tys[0].clone();
    let (elem_ty, lanes) = supported_lane_vector_ty(inst, &vector_ty)?;
    if inst.operands.len() != lanes as usize {
        return Err(format!(
            "{} expects {lanes} lane operand(s), got {}",
            inst.qualified_name(),
            inst.operands.len()
        ));
    }
    Ok(PackLanesSpec {
        vector_ty,
        elem_ty,
        lanes,
    })
}

pub fn decode_extract_lane(inst: &DialectInst) -> Result<ExtractLaneSpec, String> {
    check_header(inst, EXTRACT_LANE_OP)?;
    require_operand_count(inst, 1)?;
    require_result_count(inst, 1)?;
    let vector_ty = attr_ty(inst, "vector_ty")?;
    let (elem_ty, lanes) = supported_lane_vector_ty(inst, &vector_ty)?;
    let lane = attr_lane(inst, lanes)?;
    if inst.result_tys[0] != elem_ty {
        return Err(format!(
            "{} result type {:?} does not match vector element type {:?}",
            inst.qualified_name(),
            inst.result_tys[0],
            elem_ty
        ));
    }
    Ok(ExtractLaneSpec {
        vector_ty,
        elem_ty,
        lanes,
        lane,
    })
}

pub fn decode_insert_lane(inst: &DialectInst) -> Result<InsertLaneSpec, String> {
    check_header(inst, INSERT_LANE_OP)?;
    require_operand_count(inst, 2)?;
    require_result_count(inst, 1)?;
    let vector_ty = inst.result_tys[0].clone();
    let (elem_ty, lanes) = supported_lane_vector_ty(inst, &vector_ty)?;
    let lane = attr_lane(inst, lanes)?;
    Ok(InsertLaneSpec {
        vector_ty,
        elem_ty,
        lanes,
        lane,
    })
}

pub fn decode_mask_to_bits(inst: &DialectInst) -> Result<MaskToBitsSpec, String> {
    check_header(inst, MASK_TO_BITS_OP)?;
    require_operand_count(inst, 1)?;
    require_result_count(inst, 1)?;
    let mask_ty = attr_ty(inst, "mask_ty")?;
    let lanes = supported_bool_mask_ty(inst, &mask_ty)?;
    let result_ty = inst.result_tys[0].clone();
    validate_mask_result_ty(inst, lanes, &result_ty)?;
    validate_bit_order(inst)?;
    Ok(MaskToBitsSpec {
        mask_ty,
        lanes,
        result_ty,
    })
}

pub fn decode_reduce(inst: &DialectInst) -> Result<ReduceSpec, String> {
    check_header(inst, REDUCE_OP)?;
    require_operand_count(inst, 1)?;
    require_result_count(inst, 1)?;
    let vector_ty = attr_ty(inst, "vector_ty")?;
    let (elem_ty, lanes) = supported_lane_vector_ty(inst, &vector_ty)?;
    let kind = attr_reduce_kind(inst)?;
    if inst.result_tys[0] != elem_ty {
        return Err(format!(
            "{} result type {:?} does not match vector element type {:?}",
            inst.qualified_name(),
            inst.result_tys[0],
            elem_ty
        ));
    }
    Ok(ReduceSpec {
        vector_ty,
        elem_ty,
        lanes,
        kind,
    })
}

pub fn decode_shuffle(inst: &DialectInst) -> Result<ShuffleSpec, String> {
    check_header(inst, SHUFFLE_OP)?;
    require_operand_count(inst, 1)?;
    require_result_count(inst, 1)?;
    let vector_ty = inst.result_tys[0].clone();
    let (elem_ty, lanes) = supported_lane_vector_ty(inst, &vector_ty)?;
    let indices = attr_shuffle_indices(inst, lanes)?;
    Ok(ShuffleSpec {
        vector_ty,
        elem_ty,
        lanes,
        indices,
    })
}

pub fn decode_fma(inst: &DialectInst) -> Result<FmaSpec, String> {
    check_header(inst, FMA_OP)?;
    require_operand_count(inst, 3)?;
    require_result_count(inst, 1)?;
    let vector_ty = inst.result_tys[0].clone();
    let (elem_ty, lanes) = supported_float_lane_vector_ty(inst, &vector_ty)?;
    Ok(FmaSpec {
        vector_ty,
        elem_ty,
        lanes,
    })
}

fn check_header(inst: &DialectInst, expected_op: &str) -> Result<(), String> {
    if inst.dialect != DIALECT {
        return Err(format!(
            "expected {DIALECT:?} dialect op, got {:?}",
            inst.dialect
        ));
    }
    if inst.op != expected_op {
        return Err(format!(
            "expected {DIALECT}.{expected_op}, got {}",
            inst.qualified_name()
        ));
    }
    if inst.version != 1 {
        return Err(format!(
            "{} version {} is unsupported; expected version 1",
            inst.qualified_name(),
            inst.version
        ));
    }
    Ok(())
}

fn require_operand_count(inst: &DialectInst, expected: usize) -> Result<(), String> {
    if inst.operands.len() != expected {
        return Err(format!(
            "{} expects {expected} operand(s), got {}",
            inst.qualified_name(),
            inst.operands.len()
        ));
    }
    Ok(())
}

fn require_result_count(inst: &DialectInst, expected: usize) -> Result<(), String> {
    if inst.result_tys.len() != expected {
        return Err(format!(
            "{} expects {expected} result type(s), got {}",
            inst.qualified_name(),
            inst.result_tys.len()
        ));
    }
    Ok(())
}

fn require_operand_ty_count(inst: &DialectInst, operand_tys: &[Ty]) -> Result<(), String> {
    if operand_tys.len() != inst.operands.len() {
        return Err(format!(
            "{} expected {} operand type(s) for {} operand id(s), got {}",
            inst.qualified_name(),
            inst.operands.len(),
            inst.operands.len(),
            operand_tys.len()
        ));
    }
    Ok(())
}

fn require_operand_ty(
    inst: &DialectInst,
    operand_tys: &[Ty],
    index: usize,
    expected: &Ty,
    role: &str,
) -> Result<(), String> {
    let actual = operand_tys
        .get(index)
        .expect("typed vector validation checks operand type count first");
    if actual != expected {
        let operand = inst.operands[index];
        return Err(format!(
            "{} {role} operand {index} (%{operand}) type {actual} does not match expected {expected}",
            inst.qualified_name()
        ));
    }
    Ok(())
}

fn attr_ty(inst: &DialectInst, name: &str) -> Result<Ty, String> {
    inst.attr(name)
        .and_then(AttrValue::as_ty)
        .cloned()
        .ok_or_else(|| format!("{} requires Ty attribute {name:?}", inst.qualified_name()))
}

fn attr_lane(inst: &DialectInst, lanes: u32) -> Result<u32, String> {
    let raw = inst
        .attr("lane")
        .and_then(AttrValue::as_u64)
        .ok_or_else(|| format!("{} requires U64 attribute \"lane\"", inst.qualified_name()))?;
    let lane = u32::try_from(raw).map_err(|_| {
        format!(
            "{} lane attribute {raw} does not fit in u32",
            inst.qualified_name()
        )
    })?;
    if lane >= lanes {
        return Err(format!(
            "{} lane {lane} is out of range for {lanes} lane vector",
            inst.qualified_name()
        ));
    }
    Ok(lane)
}

fn validate_bit_order(inst: &DialectInst) -> Result<(), String> {
    match inst.attr(BIT_ORDER_ATTR) {
        None => Ok(()),
        Some(AttrValue::Str(value)) if value == LSB_LANE0 => Ok(()),
        Some(AttrValue::Str(other)) => Err(format!(
            "{} unsupported bit_order {other:?}; expected {LSB_LANE0:?}",
            inst.qualified_name()
        )),
        Some(_) => Err(format!(
            "{} requires Str attribute {BIT_ORDER_ATTR:?}",
            inst.qualified_name()
        )),
    }
}

fn attr_reduce_kind(inst: &DialectInst) -> Result<ReduceKind, String> {
    let raw = inst
        .attr(REDUCE_KIND_ATTR)
        .and_then(AttrValue::as_str)
        .ok_or_else(|| {
            format!(
                "{} requires Str attribute {REDUCE_KIND_ATTR:?}",
                inst.qualified_name()
            )
        })?;
    ReduceKind::parse(raw).ok_or_else(|| {
        format!(
            "{} unsupported reduce kind {raw:?}; expected {REDUCE_ADD:?} or {REDUCE_OR:?}",
            inst.qualified_name()
        )
    })
}

fn attr_shuffle_indices(inst: &DialectInst, lanes: u32) -> Result<Vec<u8>, String> {
    let raw = inst
        .attr(SHUFFLE_INDICES_ATTR)
        .and_then(AttrValue::as_bytes)
        .ok_or_else(|| {
            format!(
                "{} requires Bytes attribute {SHUFFLE_INDICES_ATTR:?}",
                inst.qualified_name()
            )
        })?;
    if raw.len() != lanes as usize {
        return Err(format!(
            "{} expects {lanes} shuffle index/indices, got {}",
            inst.qualified_name(),
            raw.len()
        ));
    }
    for (lane, &index) in raw.iter().enumerate() {
        if u32::from(index) >= lanes {
            return Err(format!(
                "{} shuffle index {index} for result lane {lane} is out of range for {lanes} lane vector",
                inst.qualified_name()
            ));
        }
    }
    Ok(raw.to_vec())
}

fn supported_float_lane_vector_ty(inst: &DialectInst, ty: &Ty) -> Result<(Ty, u32), String> {
    supported_float_lane_vector_shape(ty).ok_or_else(|| {
        format!(
            "{} supports only <4 x f32> and <2 x f64> float lane vectors, got {:?}",
            inst.qualified_name(),
            ty
        )
    })
}

fn supported_float_lane_vector_shape(ty: &Ty) -> Option<(Ty, u32)> {
    match ty {
        Ty::Vector(elem, 4) if elem.as_ref() == &Ty::F32 => Some((Ty::F32, 4)),
        Ty::Vector(elem, 2) if elem.as_ref() == &Ty::F64 => Some((Ty::F64, 2)),
        _ => None,
    }
}

fn vector_elem_ty(vector_ty: &Ty) -> Option<Ty> {
    match vector_ty {
        Ty::Vector(elem, _) => Some(elem.as_ref().clone()),
        _ => None,
    }
}

fn supported_lane_vector_ty(inst: &DialectInst, ty: &Ty) -> Result<(Ty, u32), String> {
    supported_lane_vector_shape(ty).ok_or_else(|| {
        format!(
            "{} supports only <16 x i8>, <8 x i16>, <4 x i32>, <2 x i64>, and <8 x i8> lane vectors, got {:?}",
            inst.qualified_name(),
            ty
        )
    })
}

fn supported_lane_vector_shape(ty: &Ty) -> Option<(Ty, u32)> {
    match ty {
        Ty::Vector(elem, 16) if elem.as_ref() == &Ty::I8 => Some((Ty::I8, 16)),
        Ty::Vector(elem, 8) if elem.as_ref() == &Ty::I16 => Some((Ty::I16, 8)),
        Ty::Vector(elem, 4) if elem.as_ref() == &Ty::I32 => Some((Ty::I32, 4)),
        Ty::Vector(elem, 2) if elem.as_ref() == &Ty::I64 => Some((Ty::I64, 2)),
        // 64-bit (D-register) NEON byte vector: `<8 x i8>` backs hashbrown's
        // `uint8x8_t`/`int8x8_t` control-byte group scan. Admitting it lets a
        // `vector.pack_lanes` splat (8 repeated lanes) lower to a genuine
        // aarch64 `dup.8b` (V64) instead of a scalar `x * 0x0101_0101_0101_0101`
        // byte broadcast. The other 64-bit shapes (<4 x i16>, <2 x i32>,
        // <1 x i64>) stay unadmitted — no producer emits them yet.
        Ty::Vector(elem, 8) if elem.as_ref() == &Ty::I8 => Some((Ty::I8, 8)),
        _ => None,
    }
}

fn supported_bool_mask_ty(inst: &DialectInst, ty: &Ty) -> Result<u32, String> {
    match ty {
        Ty::Vector(elem, 16) if elem.as_ref() == &Ty::Bool => Ok(16),
        Ty::Vector(elem, 8) if elem.as_ref() == &Ty::Bool => Ok(8),
        Ty::Vector(elem, 4) if elem.as_ref() == &Ty::Bool => Ok(4),
        Ty::Vector(elem, 2) if elem.as_ref() == &Ty::Bool => Ok(2),
        _ => Err(format!(
            "{} supports only logical <16 x bool>, <8 x bool>, <4 x bool>, and <2 x bool> masks, got {:?}",
            inst.qualified_name(),
            ty
        )),
    }
}

fn validate_mask_result_ty(inst: &DialectInst, lanes: u32, result_ty: &Ty) -> Result<(), String> {
    match (lanes, result_ty) {
        (16, Ty::I32) | (8, Ty::I32) => Ok(()),
        (4, Ty::I32) | (2, Ty::I32 | Ty::I64) => Ok(()),
        (16, other) => Err(format!(
            "{} <16 x bool> mask_to_bits result must be i32, got {:?}",
            inst.qualified_name(),
            other
        )),
        (8, other) => Err(format!(
            "{} <8 x bool> mask_to_bits result must be i32, got {:?}",
            inst.qualified_name(),
            other
        )),
        (4, other) => Err(format!(
            "{} <4 x bool> mask_to_bits result must be i32, got {:?}",
            inst.qualified_name(),
            other
        )),
        (2, other) => Err(format!(
            "{} <2 x bool> mask_to_bits result must be i32 or i64, got {:?}",
            inst.qualified_name(),
            other
        )),
        _ => unreachable!("supported_bool_mask_ty only returns 2, 4, 8, or 16 lanes"),
    }
}

use crate::dialect::lowering::{LoweringContext, LoweringPass, RewriteOutcome};
use crate::inst::{BinOp, Inst};
use crate::node::InstrNode;

/// Lowering pass for the vector dialect.
///
/// Expands composite ops like `pack_lanes` and `mask_to_bits` into core IR sequences.
pub struct VectorLoweringPass;

impl LoweringPass for VectorLoweringPass {
    fn name(&self) -> &'static str {
        "vector-lower"
    }

    fn rewrite(
        &self,
        _node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        if op.dialect != DIALECT {
            return RewriteOutcome::NoChange;
        }

        match op.op.as_str() {
            PACK_LANES_OP => self.lower_pack_lanes(op, results, ctx),
            MASK_TO_BITS_OP => self.lower_mask_to_bits(op, results, ctx),
            REDUCE_OP => self.lower_reduce(op, results, ctx),
            SHUFFLE_OP => self.lower_shuffle(op, results, ctx),
            // `vector.fma` DELIBERATELY has no core-IR scalar fallback. Its
            // contract (and the reference interpreter) is a single IEEE-754
            // rounding step per lane; the only core-IR expansion available
            // (`FMul` then `FAdd`) rounds twice, so it would be a silent
            // numerics change, not a refinement — a lowering the Lean
            // `runsAgreeFrom_*` proof family could never discharge. The op
            // therefore stays a dialect payload: backends on targets with FMA
            // hardware lower it to the fused instruction, and targets without
            // must reject the module or supply a correctly-rounded softfloat
            // (backend policy, out of scope for this pass). See
            // docs/roadmap/fast-4-vector-crosslane-ops.md.
            FMA_OP => RewriteOutcome::NoChange,
            _ => RewriteOutcome::NoChange,
        }
    }
}

impl VectorLoweringPass {
    /// Both `pack_lanes` and `mask_to_bits` lower to a chain whose final node
    /// re-uses the original op's single result `ValueId` so downstream SSA uses
    /// stay valid. A dialect-op node with an empty `results` vector (no
    /// attached result id) cannot be lowered that way — historically this
    /// indexed `results[0]` and panicked with an out-of-bounds slice access.
    /// Fail closed with a descriptive `Err` instead so `lower_module` surfaces
    /// a `DialectError::LoweringFailed` rather than aborting the process.
    fn require_single_result(
        op: &DialectInst,
        results: &[ValueId],
    ) -> Result<ValueId, RewriteOutcome> {
        match results {
            [single] => Ok(*single),
            _ => Err(RewriteOutcome::Err(format!(
                "{} lowering requires exactly one result id, got {}",
                op.qualified_name(),
                results.len()
            ))),
        }
    }

    fn lower_pack_lanes(
        &self,
        op: &DialectInst,
        results: &[ValueId],
        ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        let spec = match decode_pack_lanes(op) {
            Ok(s) => s,
            Err(e) => return RewriteOutcome::Err(e.to_string()),
        };
        let final_result = match Self::require_single_result(op, results) {
            Ok(r) => r,
            Err(outcome) => return outcome,
        };

        let mut nodes = Vec::new();
        let vector_ty = spec.vector_ty.clone();

        // 1. Emit a defined zero-vector base.
        //
        // `decode_pack_lanes` guarantees `operands.len() == lanes`, so the
        // InsertElement chain below overwrites every lane — the seed's contents
        // are observationally irrelevant. We seed with a fully-defined zero
        // `Const` (rather than `Undef`) so the emitted sequence carries no
        // undef/poison value and the Lean refinement proof
        // (`TrustIr.VectorDialect.lowerPackLanesFrom` / `runsAgreeFrom_pack_lanes`)
        // discharges against the *exact* sequence this pass emits.
        let mut curr_val = ctx.alloc_value();
        nodes.push(
            InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Vector(vec![
                    crate::constant::Constant::Int(0);
                    spec.lanes as usize
                ]),
                ty: vector_ty.clone(),
            })
            .with_result(curr_val),
        );

        // 2. Insert each lane
        for (i, &lane_id) in op.operands.iter().enumerate() {
            // Index constant
            let idx_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(i as i128),
                    ty: Ty::I64,
                })
                .with_result(idx_val),
            );

            // Result of this insertion
            let next_val = if i == op.operands.len() - 1 {
                final_result // Final result uses original ID
            } else {
                ctx.alloc_value()
            };

            nodes.push(
                InstrNode::new(Inst::InsertElement {
                    ty: vector_ty.clone(),
                    array: curr_val,
                    index: idx_val,
                    value: lane_id,
                })
                .with_result(next_val),
            );

            curr_val = next_val;
        }

        RewriteOutcome::Replace(nodes)
    }

    fn lower_mask_to_bits(
        &self,
        op: &DialectInst,
        results: &[ValueId],
        ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        let spec = match decode_mask_to_bits(op) {
            Ok(s) => s,
            Err(e) => return RewriteOutcome::Err(e.to_string()),
        };
        let final_result = match Self::require_single_result(op, results) {
            Ok(r) => r,
            Err(outcome) => return outcome,
        };

        let mut nodes = Vec::new();
        let result_ty = spec.result_ty.clone();
        // `decode_mask_to_bits` already enforced exactly one operand.
        let mask_id = op.operands[0];

        // Prologue constant order is load-bearing for the refinement proof: the
        // shared `Select` else-branch zero is emitted FIRST (allocator id
        // `base`), the seed accumulator SECOND (id `base + 1`). This is exactly
        // the layout proven by `TrustIr.VectorDialect.lowerMaskToBitsFrom` /
        // `run_maskLoopFrom` (Select else reads `ValueId.mk base`; the lane-`j`
        // accumulator reads `base + 1 + 5*j`).

        // Shared zero constant (the `Select` else branch, common to all lanes).
        let zero_const = ctx.alloc_value();
        nodes.push(
            InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Int(0),
                ty: result_ty.clone(),
            })
            .with_result(zero_const),
        );

        // Seed accumulator (0). Lane 0 ORs its contribution into this.
        let mut curr_acc = ctx.alloc_value();
        nodes.push(
            InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Int(0),
                ty: result_ty.clone(),
            })
            .with_result(curr_acc),
        );

        // 2. Process each lane
        for i in 0..spec.lanes {
            // Index constant
            let idx_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(i as i128),
                    ty: Ty::I64,
                })
                .with_result(idx_val),
            );

            // Extract bit
            let bit_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::Bool,
                    array: mask_id,
                    index: idx_val,
                })
                .with_result(bit_val),
            );

            // Select pow2 contribution
            let pow2_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(1 << i),
                    ty: result_ty.clone(),
                })
                .with_result(pow2_val),
            );

            let contrib_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Select {
                    ty: result_ty.clone(),
                    cond: bit_val,
                    then_val: pow2_val,
                    else_val: zero_const,
                })
                .with_result(contrib_val),
            );

            // Accumulate
            let next_acc = if i == spec.lanes - 1 {
                final_result
            } else {
                ctx.alloc_value()
            };

            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    ty: result_ty.clone(),
                    lhs: curr_acc,
                    rhs: contrib_val,
                })
                .with_result(next_acc),
            );

            curr_acc = next_acc;
        }

        RewriteOutcome::Replace(nodes)
    }

    fn lower_reduce(
        &self,
        op: &DialectInst,
        results: &[ValueId],
        ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        let spec = match decode_reduce(op) {
            Ok(s) => s,
            Err(e) => return RewriteOutcome::Err(e.to_string()),
        };
        let final_result = match Self::require_single_result(op, results) {
            Ok(r) => r,
            Err(outcome) => return outcome,
        };

        let mut nodes = Vec::new();
        let elem_ty = spec.elem_ty.clone();
        // `decode_reduce` already enforced exactly one operand.
        let vector_id = op.operands[0];
        // Both supported kinds fold with a core integer `BinOp`: `add` is the
        // wrapping lane sum, `or` the bitwise lane union. Both have identity 0.
        let fold_op = match spec.kind {
            ReduceKind::Add => BinOp::Add,
            ReduceKind::Or => BinOp::Or,
        };

        // Allocator layout is load-bearing for the refinement proof
        // (`TrustIr.VectorDialect.lowerReduceFrom` / `run_reduceLoopFrom`):
        // the seed accumulator (the fold identity `0`) is emitted FIRST
        // (allocator id `base`); lane `j` then binds its index constant at
        // `base + 1 + 3*j`, the extracted lane at `base + 2 + 3*j`, and the
        // folded accumulator at `base + 3 + 3*j`, so the accumulator feeding
        // lane `j` is uniformly at `base + 3*j`.

        // Seed accumulator (identity 0 for both `add` and `or`).
        let mut curr_acc = ctx.alloc_value();
        nodes.push(
            InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Int(0),
                ty: elem_ty.clone(),
            })
            .with_result(curr_acc),
        );

        // Fold each lane into the accumulator.
        for i in 0..spec.lanes {
            // Lane index constant
            let idx_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(i as i128),
                    ty: Ty::I64,
                })
                .with_result(idx_val),
            );

            // Extract the lane
            let lane_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::ExtractElement {
                    ty: elem_ty.clone(),
                    array: vector_id,
                    index: idx_val,
                })
                .with_result(lane_val),
            );

            // Accumulate
            let next_acc = if i == spec.lanes - 1 {
                final_result
            } else {
                ctx.alloc_value()
            };
            nodes.push(
                InstrNode::new(Inst::BinOp {
                    op: fold_op,
                    ty: elem_ty.clone(),
                    lhs: curr_acc,
                    rhs: lane_val,
                })
                .with_result(next_acc),
            );

            curr_acc = next_acc;
        }

        RewriteOutcome::Replace(nodes)
    }

    fn lower_shuffle(
        &self,
        op: &DialectInst,
        results: &[ValueId],
        ctx: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        let spec = match decode_shuffle(op) {
            Ok(s) => s,
            Err(e) => return RewriteOutcome::Err(e.to_string()),
        };
        let final_result = match Self::require_single_result(op, results) {
            Ok(r) => r,
            Err(outcome) => return outcome,
        };

        let mut nodes = Vec::new();
        let vector_ty = spec.vector_ty.clone();
        let elem_ty = spec.elem_ty.clone();
        // `decode_shuffle` already enforced exactly one operand and one
        // in-range index per result lane.
        let vector_id = op.operands[0];

        // Allocator layout is load-bearing for the refinement proof
        // (`TrustIr.VectorDialect.lowerShuffleFrom` / `run_shuffleInsertsFrom`):
        // the zero-vector seed is emitted FIRST (allocator id `base`); result
        // lane `j` then binds its source-index constant at `base + 1 + 4*j`,
        // the extracted source lane at `base + 2 + 4*j`, its destination-index
        // constant at `base + 3 + 4*j`, and the updated vector at
        // `base + 4 + 4*j`, so the running vector feeding lane `j` is
        // uniformly at `base + 4*j`.

        // Defined zero-vector seed. `decode_shuffle` guarantees one index per
        // result lane, so the InsertElement chain overwrites every lane; as
        // with pack_lanes we seed with a fully-defined zero `Const` (not
        // `Undef`) so the emitted sequence carries no undef/poison value and
        // matches the Lean model exactly.
        let mut curr_vec = ctx.alloc_value();
        nodes.push(
            InstrNode::new(Inst::Const {
                value: crate::constant::Constant::Vector(vec![
                    crate::constant::Constant::Int(0);
                    spec.lanes as usize
                ]),
                ty: vector_ty.clone(),
            })
            .with_result(curr_vec),
        );

        for (j, &source) in spec.indices.iter().enumerate() {
            // Source lane index constant
            let src_idx = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(i128::from(source)),
                    ty: Ty::I64,
                })
                .with_result(src_idx),
            );

            // Extract the source lane (always from the ORIGINAL vector, which
            // is never overwritten — the chain only binds fresh ids).
            let lane_val = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::ExtractElement {
                    ty: elem_ty.clone(),
                    array: vector_id,
                    index: src_idx,
                })
                .with_result(lane_val),
            );

            // Destination lane index constant
            let dst_idx = ctx.alloc_value();
            nodes.push(
                InstrNode::new(Inst::Const {
                    value: crate::constant::Constant::Int(j as i128),
                    ty: Ty::I64,
                })
                .with_result(dst_idx),
            );

            // Insert into the running result vector
            let next_vec = if j == spec.indices.len() - 1 {
                final_result
            } else {
                ctx.alloc_value()
            };
            nodes.push(
                InstrNode::new(Inst::InsertElement {
                    ty: vector_ty.clone(),
                    array: curr_vec,
                    index: dst_idx,
                    value: lane_val,
                })
                .with_result(next_vec),
            );

            curr_vec = next_vec;
        }

        RewriteOutcome::Replace(nodes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    #[test]
    fn builders_produce_stable_payloads() {
        let pack = pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2), v(3)]);
        assert_eq!(pack.dialect, DIALECT);
        assert_eq!(pack.op, PACK_LANES_OP);
        assert_eq!(pack.operands, vec![v(0), v(1), v(2), v(3)]);
        assert_eq!(pack.result_tys, vec![Ty::v4_i32()]);

        let v4_splat = v4_i32_splat_lane(v(8)).unwrap();
        assert_eq!(v4_splat.op, PACK_LANES_OP);
        assert_eq!(v4_splat.operands, vec![v(8), v(8), v(8), v(8)]);
        assert_eq!(v4_splat.result_tys, vec![Ty::v4_i32()]);

        let v2_splat = v2_i64_splat_lane(v(9)).unwrap();
        assert_eq!(v2_splat.op, PACK_LANES_OP);
        assert_eq!(v2_splat.operands, vec![v(9), v(9)]);
        assert_eq!(v2_splat.result_tys, vec![Ty::v2_i64()]);

        let extract = extract_lane(Ty::v2_i64(), v(4), 1);
        assert_eq!(extract.op, EXTRACT_LANE_OP);
        assert_eq!(extract.operands, vec![v(4)]);
        assert_eq!(extract.result_tys, vec![Ty::I64]);
        assert_eq!(
            extract.attr("vector_ty"),
            Some(&AttrValue::Ty(Ty::v2_i64()))
        );
        assert_eq!(extract.attr("lane"), Some(&AttrValue::U64(1)));

        let insert = insert_lane(Ty::v4_i32(), v(5), 3, v(6));
        assert_eq!(insert.op, INSERT_LANE_OP);
        assert_eq!(insert.operands, vec![v(5), v(6)]);
        assert_eq!(insert.result_tys, vec![Ty::v4_i32()]);
        assert_eq!(insert.attr("lane"), Some(&AttrValue::U64(3)));

        let mask = mask_to_bits(Ty::v2_bool(), v(7), Ty::I64);
        assert_eq!(mask.op, MASK_TO_BITS_OP);
        assert_eq!(mask.operands, vec![v(7)]);
        assert_eq!(mask.result_tys, vec![Ty::I64]);
        assert_eq!(mask.attr("mask_ty"), Some(&AttrValue::Ty(Ty::v2_bool())));
        assert_eq!(
            mask.attr(BIT_ORDER_ATTR),
            Some(&AttrValue::Str(LSB_LANE0.to_string()))
        );
    }

    #[test]
    fn decoders_accept_supported_shapes() {
        assert_eq!(
            decode_pack_lanes(&pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2), v(3)])).unwrap(),
            PackLanesSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
            }
        );
        assert_eq!(
            decode_pack_lanes(&v4_i32_splat_lane(v(0)).unwrap()).unwrap(),
            PackLanesSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
            }
        );
        assert_eq!(
            decode_pack_lanes(&v2_i64_splat_lane(v(0)).unwrap()).unwrap(),
            PackLanesSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
            }
        );
        // 64-bit (D-register) `<8 x i8>` splat: the hashbrown group-scan
        // `simd_splat` broadcast that lowers to a genuine `dup.8b`.
        assert_eq!(
            decode_pack_lanes(&pack_lanes_repeated(Ty::Vector(Box::new(Ty::I8), 8), v(0)).unwrap())
                .unwrap(),
            PackLanesSpec {
                vector_ty: Ty::Vector(Box::new(Ty::I8), 8),
                elem_ty: Ty::I8,
                lanes: 8,
            }
        );
        assert_eq!(
            decode_extract_lane(&extract_lane(Ty::v2_i64(), v(0), 1)).unwrap(),
            ExtractLaneSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
                lane: 1,
            }
        );
        assert_eq!(
            decode_insert_lane(&insert_lane(Ty::v4_i32(), v(0), 3, v(1))).unwrap(),
            InsertLaneSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
                lane: 3,
            }
        );
        assert_eq!(
            decode_mask_to_bits(&mask_to_bits(Ty::v2_bool(), v(0), Ty::I64)).unwrap(),
            MaskToBitsSpec {
                mask_ty: Ty::v2_bool(),
                lanes: 2,
                result_ty: Ty::I64,
            }
        );
        assert_eq!(
            decode_mask_to_bits(&mask_to_bits(Ty::v2_bool(), v(0), Ty::I32)).unwrap(),
            MaskToBitsSpec {
                mask_ty: Ty::v2_bool(),
                lanes: 2,
                result_ty: Ty::I32,
            }
        );
        assert_eq!(
            decode_mask_to_bits(&mask_to_bits(Ty::v8_bool(), v(0), Ty::I32)).unwrap(),
            MaskToBitsSpec {
                mask_ty: Ty::v8_bool(),
                lanes: 8,
                result_ty: Ty::I32,
            }
        );
        assert_eq!(
            decode_mask_to_bits(&mask_to_bits(Ty::v16_bool(), v(0), Ty::I32)).unwrap(),
            MaskToBitsSpec {
                mask_ty: Ty::v16_bool(),
                lanes: 16,
                result_ty: Ty::I32,
            }
        );
    }

    #[test]
    fn typed_decoder_accepts_supported_operand_types() {
        assert_eq!(
            decode_with_operand_tys(
                &pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2), v(3)]),
                &[Ty::I32, Ty::I32, Ty::I32, Ty::I32],
            )
            .unwrap(),
            VectorSpec::PackLanes(PackLanesSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
            })
        );
        assert_eq!(
            decode_with_operand_tys(&pack_lanes(Ty::v2_i64(), [v(0), v(1)]), &[Ty::I64, Ty::I64],)
                .unwrap(),
            VectorSpec::PackLanes(PackLanesSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
            })
        );
        assert_eq!(
            decode_with_operand_tys(&extract_lane(Ty::v4_i32(), v(0), 3), &[Ty::v4_i32()]).unwrap(),
            VectorSpec::ExtractLane(ExtractLaneSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
                lane: 3,
            })
        );
        assert_eq!(
            decode_with_operand_tys(&extract_lane(Ty::v2_i64(), v(0), 1), &[Ty::v2_i64()]).unwrap(),
            VectorSpec::ExtractLane(ExtractLaneSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
                lane: 1,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &extract_lane(Ty::Vector(Box::new(Ty::I8), 16), v(0), 15),
                &[Ty::Vector(Box::new(Ty::I8), 16)],
            )
            .unwrap(),
            VectorSpec::ExtractLane(ExtractLaneSpec {
                vector_ty: Ty::Vector(Box::new(Ty::I8), 16),
                elem_ty: Ty::I8,
                lanes: 16,
                lane: 15,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &insert_lane(Ty::v4_i32(), v(0), 2, v(1)),
                &[Ty::v4_i32(), Ty::I32],
            )
            .unwrap(),
            VectorSpec::InsertLane(InsertLaneSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
                lane: 2,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &insert_lane(Ty::v2_i64(), v(0), 1, v(1)),
                &[Ty::v2_i64(), Ty::I64],
            )
            .unwrap(),
            VectorSpec::InsertLane(InsertLaneSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
                lane: 1,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &insert_lane(Ty::Vector(Box::new(Ty::I16), 8), v(0), 7, v(1)),
                &[Ty::Vector(Box::new(Ty::I16), 8), Ty::I16],
            )
            .unwrap(),
            VectorSpec::InsertLane(InsertLaneSpec {
                vector_ty: Ty::Vector(Box::new(Ty::I16), 8),
                elem_ty: Ty::I16,
                lanes: 8,
                lane: 7,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &mask_to_bits(Ty::v4_bool(), v(0), Ty::I32),
                &[Ty::v4_bool()]
            )
            .unwrap(),
            VectorSpec::MaskToBits(MaskToBitsSpec {
                mask_ty: Ty::v4_bool(),
                lanes: 4,
                result_ty: Ty::I32,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &mask_to_bits(Ty::v2_bool(), v(0), Ty::I64),
                &[Ty::v2_bool()]
            )
            .unwrap(),
            VectorSpec::MaskToBits(MaskToBitsSpec {
                mask_ty: Ty::v2_bool(),
                lanes: 2,
                result_ty: Ty::I64,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &mask_to_bits(Ty::v8_bool(), v(0), Ty::I32),
                &[Ty::v8_bool()]
            )
            .unwrap(),
            VectorSpec::MaskToBits(MaskToBitsSpec {
                mask_ty: Ty::v8_bool(),
                lanes: 8,
                result_ty: Ty::I32,
            })
        );
        assert_eq!(
            decode_with_operand_tys(
                &mask_to_bits(Ty::v16_bool(), v(0), Ty::I32),
                &[Ty::v16_bool()]
            )
            .unwrap(),
            VectorSpec::MaskToBits(MaskToBitsSpec {
                mask_ty: Ty::v16_bool(),
                lanes: 16,
                result_ty: Ty::I32,
            })
        );
    }

    #[test]
    fn typed_decoder_rejects_operand_type_mismatches() {
        let err = decode_with_operand_tys(
            &pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2), v(3)]),
            &[Ty::I32, Ty::I32, Ty::I64, Ty::I32],
        )
        .expect_err("pack lanes must match element type");
        assert!(err.contains("lane operand 2 (%2) type i64 does not match expected i32"));

        let err = decode_with_operand_tys(&pack_lanes(Ty::v2_i64(), [v(0), v(1)]), &[Ty::I64])
            .expect_err("typed consumer must provide one type per operand");
        assert!(err.contains("expected 2 operand type(s)"));

        let err = decode_with_operand_tys(&extract_lane(Ty::v4_i32(), v(0), 0), &[Ty::v2_i64()])
            .expect_err("extract operand must match vector type");
        assert!(err.contains("vector operand 0 (%0) type <2 x i64>"));
        assert!(err.contains("does not match expected <4 x i32>"));

        let err = decode_with_operand_tys(
            &insert_lane(Ty::v2_i64(), v(0), 1, v(1)),
            &[Ty::v2_i64(), Ty::I32],
        )
        .expect_err("inserted lane value must match element type");
        assert!(err.contains("lane value operand 1 (%1) type i32"));
        assert!(err.contains("does not match expected i64"));

        let err =
            decode_with_operand_tys(&mask_to_bits(Ty::v4_bool(), v(0), Ty::I32), &[Ty::v4_i32()])
                .expect_err("mask_to_bits consumes logical bool masks only");
        assert!(err.contains("mask operand 0 (%0) type <4 x i32>"));
        assert!(err.contains("does not match expected <4 x bool>"));
    }

    #[test]
    fn dialect_validate_accepts_all_first_slice_ops() {
        let dialect = VectorDialect;
        for op in [
            pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2), v(3)]),
            pack_lanes(Ty::v2_i64(), [v(0), v(1)]),
            extract_lane(Ty::v4_i32(), v(0), 2),
            insert_lane(Ty::v2_i64(), v(0), 1, v(1)),
            mask_to_bits(Ty::v4_bool(), v(0), Ty::I32),
            mask_to_bits(Ty::v8_bool(), v(0), Ty::I32),
            mask_to_bits(Ty::v16_bool(), v(0), Ty::I32),
            mask_to_bits(Ty::v2_bool(), v(0), Ty::I32),
            mask_to_bits(Ty::v2_bool(), v(0), Ty::I64),
        ] {
            dialect
                .validate(&op)
                .unwrap_or_else(|err| panic!("{} should validate: {err}", op.qualified_name()));
            assert!(is_vector_op(&op));
        }
    }

    #[test]
    fn dialect_schema_pins_portable_op_names() {
        let dialect = VectorDialect;
        assert_eq!(dialect.name(), DIALECT);
        assert_eq!(dialect.version(), 1);
        assert_eq!(
            dialect.ops(),
            &[
                PACK_LANES_OP,
                EXTRACT_LANE_OP,
                INSERT_LANE_OP,
                MASK_TO_BITS_OP,
                REDUCE_OP,
                SHUFFLE_OP,
                FMA_OP,
            ]
        );

        let misspelled = DialectInst::new(DIALECT, "pack_lane").with_result_ty(Ty::v4_i32());
        let err = dialect
            .validate(&misspelled)
            .expect_err("misspelled vector op names must fail closed");
        assert!(matches!(
            err,
            DialectError::UnknownOp {
                dialect: DIALECT,
                ref op
            } if op == "pack_lane"
        ));
        assert!(is_vector_dialect_inst(&misspelled));
        assert!(!is_vector_op(&misspelled));
    }

    #[test]
    fn decode_rejects_malformed_ops() {
        let err = decode_pack_lanes(&pack_lanes(Ty::v4_i32(), [v(0), v(1), v(2)]))
            .expect_err("pack lane count must match vector lanes");
        assert!(err.contains("expects 4 lane operand"));

        let err = pack_lanes_repeated(Ty::Vector(Box::new(Ty::I32), 2), v(0))
            .expect_err("repeated-lane helper accepts only canonical lane vectors");
        assert!(err.contains("supports only <16 x i8>, <8 x i16>, <4 x i32>"));

        let err = decode_extract_lane(&extract_lane(Ty::v4_i32(), v(0), 4))
            .expect_err("extract lane must be in range");
        assert!(err.contains("lane 4 is out of range"));

        let mut bad_extract = extract_lane(Ty::v2_i64(), v(0), 0);
        bad_extract.result_tys[0] = Ty::I32;
        let err =
            decode_extract_lane(&bad_extract).expect_err("extract result must match element type");
        assert!(err.contains("does not match vector element type"));

        let err = decode_insert_lane(&insert_lane(
            Ty::Vector(Box::new(Ty::I32), 2),
            v(0),
            0,
            v(1),
        ))
        .expect_err("only first slice vectors are accepted");
        assert!(err.contains("supports only <16 x i8>, <8 x i16>, <4 x i32>"));

        let err = decode_mask_to_bits(&mask_to_bits(Ty::v4_i32(), v(0), Ty::I32))
            .expect_err("physical integer masks are not logical bool masks");
        assert!(err.contains("logical <16 x bool>, <8 x bool>, <4 x bool>, and <2 x bool>"));

        let err = decode_mask_to_bits(&mask_to_bits(Ty::v4_bool(), v(0), Ty::I64))
            .expect_err("v4 bool mask compacts to i32 only");
        assert!(err.contains("<4 x bool> mask_to_bits result must be i32"));

        let err = decode_mask_to_bits(&mask_to_bits(Ty::v8_bool(), v(0), Ty::I64))
            .expect_err("v8 bool mask compacts to i32 only");
        assert!(err.contains("<8 x bool> mask_to_bits result must be i32"));

        let err = decode_mask_to_bits(&mask_to_bits(Ty::v16_bool(), v(0), Ty::I64))
            .expect_err("v16 bool mask compacts to i32 only");
        assert!(err.contains("<16 x bool> mask_to_bits result must be i32"));
    }

    #[test]
    fn validate_reports_unknown_version_and_bad_bit_order() {
        let dialect = VectorDialect;

        let bad_version = pack_lanes(Ty::v2_i64(), [v(0), v(1)]).with_version(2);
        let err = dialect
            .validate(&bad_version)
            .expect_err("unsupported version must fail");
        assert!(matches!(
            err,
            DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("version 2 is unsupported")
        ));

        let mut bad_bit_order = mask_to_bits(Ty::v2_bool(), v(0), Ty::I32);
        bad_bit_order
            .attrs
            .iter_mut()
            .find(|attr| attr.name == BIT_ORDER_ATTR)
            .expect("builder attaches bit_order")
            .value = AttrValue::Str("msb_lane0".to_string());
        let err = dialect
            .validate(&bad_bit_order)
            .expect_err("unsupported bit order must fail");
        assert!(matches!(
            err,
            DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("unsupported bit_order")
        ));

        let mut malformed_bit_order = mask_to_bits(Ty::v2_bool(), v(0), Ty::I32);
        malformed_bit_order
            .attrs
            .iter_mut()
            .find(|attr| attr.name == BIT_ORDER_ATTR)
            .expect("builder attaches bit_order")
            .value = AttrValue::Bool(true);
        let err = dialect
            .validate(&malformed_bit_order)
            .expect_err("malformed bit_order attr must fail");
        assert!(matches!(
            err,
            DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("requires Str attribute \"bit_order\"")
        ));
    }

    #[test]
    fn op_predicates_match_only_vector_ops() {
        let pack = pack_lanes(Ty::v2_i64(), [v(0), v(1)]);
        assert!(is_pack_lanes_op(&pack));
        assert!(!is_extract_lane_op(&pack));
        assert!(is_vector_dialect_inst(&pack));

        let other = DialectInst::new("other", PACK_LANES_OP).with_result_ty(Ty::v2_i64());
        assert!(!is_vector_dialect_inst(&other));
        assert!(!is_vector_op(&other));
    }

    #[test]
    fn crosslane_builders_and_decoders_round_trip() {
        let red = reduce(Ty::v4_i32(), v(0), ReduceKind::Add);
        assert_eq!(red.op, REDUCE_OP);
        assert_eq!(red.operands, vec![v(0)]);
        assert_eq!(red.result_tys, vec![Ty::I32]);
        assert_eq!(red.attr("vector_ty"), Some(&AttrValue::Ty(Ty::v4_i32())));
        assert_eq!(
            red.attr(REDUCE_KIND_ATTR),
            Some(&AttrValue::Str(REDUCE_ADD.to_string()))
        );
        assert_eq!(
            decode_reduce(&red).unwrap(),
            ReduceSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
                kind: ReduceKind::Add,
            }
        );
        assert_eq!(
            decode_reduce(&reduce(Ty::v2_i64(), v(0), ReduceKind::Or)).unwrap(),
            ReduceSpec {
                vector_ty: Ty::v2_i64(),
                elem_ty: Ty::I64,
                lanes: 2,
                kind: ReduceKind::Or,
            }
        );

        let shuf = shuffle(Ty::v4_i32(), v(0), [3u8, 2, 1, 0]);
        assert_eq!(shuf.op, SHUFFLE_OP);
        assert_eq!(shuf.operands, vec![v(0)]);
        assert_eq!(shuf.result_tys, vec![Ty::v4_i32()]);
        assert_eq!(
            shuf.attr(SHUFFLE_INDICES_ATTR),
            Some(&AttrValue::Bytes(vec![3, 2, 1, 0]))
        );
        assert_eq!(
            decode_shuffle(&shuf).unwrap(),
            ShuffleSpec {
                vector_ty: Ty::v4_i32(),
                elem_ty: Ty::I32,
                lanes: 4,
                indices: vec![3, 2, 1, 0],
            }
        );

        let f = fma(Ty::v4_f32(), v(0), v(1), v(2));
        assert_eq!(f.op, FMA_OP);
        assert_eq!(f.operands, vec![v(0), v(1), v(2)]);
        assert_eq!(f.result_tys, vec![Ty::v4_f32()]);
        assert_eq!(
            decode_fma(&f).unwrap(),
            FmaSpec {
                vector_ty: Ty::v4_f32(),
                elem_ty: Ty::F32,
                lanes: 4,
            }
        );
        assert_eq!(
            decode_fma(&fma(Ty::v2_f64(), v(0), v(1), v(2))).unwrap(),
            FmaSpec {
                vector_ty: Ty::v2_f64(),
                elem_ty: Ty::F64,
                lanes: 2,
            }
        );

        assert!(is_reduce_op(&red));
        assert!(is_shuffle_op(&shuf));
        assert!(is_fma_op(&f));
        for op in [&red, &shuf, &f] {
            assert!(is_vector_op(op));
            VectorDialect.validate(op).expect("crosslane op validates");
        }
    }

    #[test]
    fn crosslane_decoders_reject_malformed_ops() {
        // reduce: unknown kind.
        let mut bad_kind = reduce(Ty::v4_i32(), v(0), ReduceKind::Add);
        bad_kind
            .attrs
            .iter_mut()
            .find(|attr| attr.name == REDUCE_KIND_ATTR)
            .expect("builder attaches kind")
            .value = AttrValue::Str("mul".to_string());
        let err = decode_reduce(&bad_kind).expect_err("unsupported reduce kind must fail");
        assert!(err.contains("unsupported reduce kind"));

        // reduce: result must match element type.
        let mut bad_result = reduce(Ty::v2_i64(), v(0), ReduceKind::Add);
        bad_result.result_tys[0] = Ty::I32;
        let err = decode_reduce(&bad_result).expect_err("reduce result must match element type");
        assert!(err.contains("does not match vector element type"));

        // reduce: float lane vectors are out of scope.
        let err = decode_reduce(&reduce(Ty::v4_f32(), v(0), ReduceKind::Add))
            .expect_err("reduce only folds integer lane vectors");
        assert!(err.contains("supports only <16 x i8>, <8 x i16>, <4 x i32>"));

        // shuffle: index out of range.
        let err = decode_shuffle(&shuffle(Ty::v4_i32(), v(0), [4u8, 0, 1, 2]))
            .expect_err("shuffle index must be in range");
        assert!(err.contains("is out of range for 4 lane vector"));

        // shuffle: wrong index count.
        let err = decode_shuffle(&shuffle(Ty::v4_i32(), v(0), [0u8, 1, 2]))
            .expect_err("shuffle needs one index per result lane");
        assert!(err.contains("expects 4 shuffle"));

        // fma: integer lane vectors are out of scope.
        let err = decode_fma(&fma(Ty::v4_i32(), v(0), v(1), v(2)))
            .expect_err("fma only operates on float lane vectors");
        assert!(err.contains("supports only <4 x f32> and <2 x f64>"));

        // fma: arity must be exactly three operands.
        let mut bad_arity = fma(Ty::v4_f32(), v(0), v(1), v(2));
        bad_arity.operands.pop();
        let err = decode_fma(&bad_arity).expect_err("fma needs three operands");
        assert!(err.contains("expects 3 operand"));
    }
}

#[cfg(test)]
mod lowering_tests {
    use super::*;
    use crate::dialect::lowering::{LoweringPass, lower_module};
    use crate::inst::{BinOp, Inst};
    use crate::node::InstrNode;
    use crate::value::{BlockId, FuncId, FuncTyId, ValueId};
    use crate::{Block, Function, Module};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }

    fn module_with_ops(ops: Vec<DialectInst>) -> Module {
        let mut m = Module::new("m");
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        for (i, op) in ops.into_iter().enumerate() {
            let mut node = InstrNode::new(Inst::DialectOp(Box::new(op)));
            node.results = vec![v(i as u32 + 100)];
            b.body.push(node);
        }
        f.blocks.push(b);
        m.add_function(f);
        m
    }

    #[test]
    fn test_pack_lanes_lowering() {
        let pack = pack_lanes(Ty::v2_i64(), [v(0), v(1)]);
        let mut module = module_with_ops(vec![pack]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let result = lower_module(&mut module, &passes, 8).expect("lowering failed");
        assert!(result.fixpoint_reached);

        let body = &module.functions[0].blocks[0].body;
        // Should have: zero-vector seed, const 0, insert, const 1, insert
        assert_eq!(body.len(), 5);
        // The seed is a defined zero-vector Const (matching the Lean proof),
        // not Undef.
        assert!(matches!(
            body[0].inst,
            Inst::Const {
                value: crate::constant::Constant::Vector(ref lanes),
                ..
            } if lanes.len() == 2
                && lanes.iter().all(|c| matches!(c, crate::constant::Constant::Int(0)))
        ));
        assert!(matches!(body[1].inst, Inst::Const { .. }));
        assert!(matches!(body[2].inst, Inst::InsertElement { .. }));
        assert!(matches!(body[3].inst, Inst::Const { .. }));
        assert!(matches!(body[4].inst, Inst::InsertElement { .. }));

        // Final result ID should be preserved
        assert_eq!(body[4].results, vec![v(100)]);
    }

    #[test]
    fn test_mask_to_bits_lowering() {
        let mask_ty = Ty::Vector(Box::new(Ty::Bool), 16);
        let op = mask_to_bits(mask_ty, v(0), Ty::I32);
        let mut module = module_with_ops(vec![op]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let result = lower_module(&mut module, &passes, 8).expect("lowering failed");
        assert!(result.fixpoint_reached);

        let body = &module.functions[0].blocks[0].body;
        // 2 initial consts + 16 * (const, extract, const, select, binop) = 2 + 80 = 82
        assert_eq!(body.len(), 82);
        assert!(matches!(
            body[body.len() - 1].inst,
            Inst::BinOp { op: BinOp::Or, .. }
        ));
        assert_eq!(body[body.len() - 1].results, vec![v(100)]);
    }

    /// Build a single-op module whose dialect node has NO attached result id.
    fn module_with_resultless_op(op: DialectInst) -> Module {
        let mut m = Module::new("m");
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        // Deliberately leave `results` empty (the default).
        b.body.push(InstrNode::new(Inst::DialectOp(Box::new(op))));
        f.blocks.push(b);
        m.add_function(f);
        m
    }

    /// FIX: lowering a `vector.pack_lanes` node that carries no result id must
    /// fail closed with `DialectError::LoweringFailed`, NOT panic on a
    /// `results[0]` out-of-bounds index.
    #[test]
    fn pack_lanes_with_empty_results_fails_closed() {
        let pack = pack_lanes(Ty::v2_i64(), [v(0), v(1)]);
        let mut module = module_with_resultless_op(pack);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let err = lower_module(&mut module, &passes, 8)
            .expect_err("resultless pack_lanes must not lower (and must not panic)");
        match err {
            crate::dialect::DialectError::LoweringFailed { reason, .. } => {
                assert!(
                    reason.contains("requires exactly one result id"),
                    "unexpected reason: {reason}"
                );
            }
            other => panic!("expected LoweringFailed, got {other:?}"),
        }
    }

    /// Same guard for `vector.mask_to_bits`.
    #[test]
    fn mask_to_bits_with_empty_results_fails_closed() {
        let op = mask_to_bits(Ty::v16_bool(), v(0), Ty::I32);
        let mut module = module_with_resultless_op(op);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let err = lower_module(&mut module, &passes, 8)
            .expect_err("resultless mask_to_bits must not lower (and must not panic)");
        assert!(matches!(
            err,
            crate::dialect::DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("requires exactly one result id")
        ));
    }

    #[test]
    fn test_reduce_lowering() {
        let red = reduce(Ty::v4_i32(), v(0), ReduceKind::Add);
        let mut module = module_with_ops(vec![red]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let result = lower_module(&mut module, &passes, 8).expect("lowering failed");
        assert!(result.fixpoint_reached);

        let body = &module.functions[0].blocks[0].body;
        // Seed const + 4 * (index const, extract, binop) = 1 + 12 = 13.
        assert_eq!(body.len(), 13);
        // Seed is the fold identity 0 of the element type (matching the Lean
        // proof's `lowerReduceFrom`).
        assert!(matches!(
            body[0].inst,
            Inst::Const {
                value: crate::constant::Constant::Int(0),
                ty: Ty::I32,
            }
        ));
        for lane in 0..4usize {
            assert!(matches!(
                body[1 + 3 * lane].inst,
                Inst::Const {
                    value: crate::constant::Constant::Int(idx),
                    ty: Ty::I64,
                } if idx == lane as i128
            ));
            assert!(matches!(
                body[2 + 3 * lane].inst,
                Inst::ExtractElement { ty: Ty::I32, array, .. } if array == v(0)
            ));
            assert!(matches!(
                body[3 + 3 * lane].inst,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    ..
                }
            ));
        }

        // Final fold reuses the original result ID.
        assert_eq!(body[12].results, vec![v(100)]);
    }

    #[test]
    fn test_reduce_or_lowering_folds_with_binop_or() {
        let red = reduce(Ty::v2_i64(), v(0), ReduceKind::Or);
        let mut module = module_with_ops(vec![red]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        lower_module(&mut module, &passes, 8).expect("lowering failed");

        let body = &module.functions[0].blocks[0].body;
        // Seed const + 2 * (index const, extract, binop) = 1 + 6 = 7.
        assert_eq!(body.len(), 7);
        assert!(matches!(
            body[3].inst,
            Inst::BinOp {
                op: BinOp::Or,
                ty: Ty::I64,
                ..
            }
        ));
        assert!(matches!(
            body[6].inst,
            Inst::BinOp {
                op: BinOp::Or,
                ty: Ty::I64,
                ..
            }
        ));
        assert_eq!(body[6].results, vec![v(100)]);
    }

    /// Same fail-closed guard as pack_lanes/mask_to_bits: a resultless
    /// `vector.reduce` node must surface `LoweringFailed`, not panic.
    #[test]
    fn reduce_with_empty_results_fails_closed() {
        let red = reduce(Ty::v4_i32(), v(0), ReduceKind::Add);
        let mut module = module_with_resultless_op(red);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let err = lower_module(&mut module, &passes, 8)
            .expect_err("resultless reduce must not lower (and must not panic)");
        assert!(matches!(
            err,
            crate::dialect::DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("requires exactly one result id")
        ));
    }

    #[test]
    fn test_shuffle_lowering() {
        let shuf = shuffle(Ty::v4_i32(), v(0), [3u8, 2, 1, 0]);
        let mut module = module_with_ops(vec![shuf]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let result = lower_module(&mut module, &passes, 8).expect("lowering failed");
        assert!(result.fixpoint_reached);

        let body = &module.functions[0].blocks[0].body;
        // Zero-vector seed + 4 * (src const, extract, dst const, insert) = 17.
        assert_eq!(body.len(), 17);
        // Seed is a defined zero-vector Const (matching the Lean model), not
        // Undef.
        assert!(matches!(
            body[0].inst,
            Inst::Const {
                value: crate::constant::Constant::Vector(ref lanes),
                ..
            } if lanes.len() == 4
                && lanes.iter().all(|c| matches!(c, crate::constant::Constant::Int(0)))
        ));
        for (lane, &source) in [3u8, 2, 1, 0].iter().enumerate() {
            assert!(matches!(
                body[1 + 4 * lane].inst,
                Inst::Const {
                    value: crate::constant::Constant::Int(idx),
                    ty: Ty::I64,
                } if idx == i128::from(source)
            ));
            assert!(matches!(
                body[2 + 4 * lane].inst,
                Inst::ExtractElement { ty: Ty::I32, array, .. } if array == v(0)
            ));
            assert!(matches!(
                body[3 + 4 * lane].inst,
                Inst::Const {
                    value: crate::constant::Constant::Int(idx),
                    ty: Ty::I64,
                } if idx == lane as i128
            ));
            assert!(matches!(
                body[4 + 4 * lane].inst,
                Inst::InsertElement { .. }
            ));
        }

        // Final insert reuses the original result ID.
        assert_eq!(body[16].results, vec![v(100)]);
    }

    /// POLICY: `vector.fma` must NOT be scalar-lowered. An `FMul`+`FAdd`
    /// expansion rounds twice where the op's contract rounds once, so the
    /// pass leaves the op untouched (an fma-less target must reject or
    /// supply a correctly-rounded softfloat — backend policy). This test
    /// pins the explicit NoChange: the dialect payload survives lowering
    /// bit-identically and the run still reaches a fixpoint.
    #[test]
    fn fma_is_deliberately_not_lowered() {
        let f = fma(Ty::v4_f32(), v(0), v(1), v(2));
        let mut module = module_with_ops(vec![f.clone()]);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let result = lower_module(&mut module, &passes, 8).expect("lowering runs");
        assert!(result.fixpoint_reached);
        assert_eq!(result.rewrites_applied, 0);

        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), 1);
        assert!(matches!(
            &body[0].inst,
            Inst::DialectOp(op) if **op == f
        ));
    }

    /// Same fail-closed guard for `vector.shuffle`.
    #[test]
    fn shuffle_with_empty_results_fails_closed() {
        let shuf = shuffle(Ty::v2_i64(), v(0), [1u8, 0]);
        let mut module = module_with_resultless_op(shuf);
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];

        let err = lower_module(&mut module, &passes, 8)
            .expect_err("resultless shuffle must not lower (and must not panic)");
        assert!(matches!(
            err,
            crate::dialect::DialectError::LoweringFailed { ref reason, .. }
                if reason.contains("requires exactly one result id")
        ));
    }
}

/// Interpreter cross-checks: the dialect-op module and its lowered core-IR
/// expansion must compute the same result through the reference interpreter.
/// This is the executable counterpart of the Lean `runsAgreeFrom_*` refinement
/// proofs, and it also covers the lane shapes (`<16 x i8>`, `<8 x i16>`) that
/// sit outside the Lean executable subset.
#[cfg(test)]
mod interpreter_crosscheck_tests {
    use super::*;
    use crate::constant::Constant;
    use crate::dialect::lowering::{LoweringPass, lower_module};
    use crate::inst::Inst;
    use crate::interpret::{InterpretValue, Interpreter};
    use crate::node::InstrNode;
    use crate::value::{BlockId, FuncId, FuncTyId, ValueId};
    use crate::{Block, FuncTy, Function, Module};

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }

    /// Single-function module: `Const vector; <dialect op on it>; Return`.
    fn module_returning_op(vector_ty: Ty, vector: Constant, op: DialectInst) -> Module {
        let result_ty = op.result_tys[0].clone();
        let mut module = Module::new("crosscheck");
        module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![result_ty],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        let mut const_node = InstrNode::new(Inst::Const {
            ty: vector_ty,
            value: vector,
        });
        const_node.results = vec![v(0)];
        block.body.push(const_node);
        let mut op_node = InstrNode::new(Inst::DialectOp(Box::new(op)));
        op_node.results = vec![v(1)];
        block.body.push(op_node);
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    fn interpret_returns(module: &Module) -> Vec<InterpretValue> {
        Interpreter::with_module(module)
            .execute_func(FuncId::new(0), [])
            .expect("module executes")
            .returns
    }

    fn vector_signed(value: &InterpretValue) -> Vec<i128> {
        match &value.kind {
            crate::interpret::InterpretValueKind::Vector(lanes) => lanes
                .iter()
                .map(|lane| lane.as_int().expect("integer lane").as_signed())
                .collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    }

    /// Run the dialect module as-is, then lower it and run again; both must
    /// return the identical value.
    fn assert_lowering_preserves_result(module: &Module) -> Vec<InterpretValue> {
        let dialect_result = interpret_returns(module);

        let mut lowered = module.clone();
        let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(VectorLoweringPass)];
        let outcome = lower_module(&mut lowered, &passes, 8).expect("lowering succeeds");
        assert!(outcome.fixpoint_reached);
        // The dialect op must actually be gone: the lowered module is pure
        // core IR (no `Inst::DialectOp` left for the interpreter to reject).
        assert!(
            lowered.functions[0].blocks[0]
                .body
                .iter()
                .all(|node| !matches!(node.inst, Inst::DialectOp(_)))
        );

        let lowered_result = interpret_returns(&lowered);
        assert_eq!(dialect_result, lowered_result);
        dialect_result
    }

    #[test]
    fn lowered_reduce_add_matches_dialect_result() {
        let module = module_returning_op(
            Ty::v4_i32(),
            Constant::v4_i32([1, -2, 30, 4]),
            reduce(Ty::v4_i32(), v(0), ReduceKind::Add),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(returns[0].as_int().map(|i| i.as_signed()), Some(33));
    }

    #[test]
    fn lowered_reduce_add_wraps_like_dialect_op() {
        let module = module_returning_op(
            Ty::v4_i32(),
            Constant::v4_i32([i32::MAX, 1, 1, 0]),
            reduce(Ty::v4_i32(), v(0), ReduceKind::Add),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(
            returns[0].as_int().map(|i| i.as_signed()),
            Some(i128::from(i32::MIN + 1))
        );
    }

    #[test]
    fn lowered_reduce_or_matches_dialect_result() {
        let module = module_returning_op(
            Ty::v2_i64(),
            Constant::v2_i64([0b0011, 0b1100]),
            reduce(Ty::v2_i64(), v(0), ReduceKind::Or),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(returns[0].as_int().map(|i| i.as_unsigned()), Some(0b1111));
    }

    #[test]
    fn lowered_shuffle_reverse_matches_dialect_result() {
        let module = module_returning_op(
            Ty::v4_i32(),
            Constant::v4_i32([10, 20, 30, 40]),
            shuffle(Ty::v4_i32(), v(0), [3u8, 2, 1, 0]),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(vector_signed(&returns[0]), vec![40, 30, 20, 10]);
    }

    #[test]
    fn lowered_shuffle_broadcast_matches_dialect_result() {
        let module = module_returning_op(
            Ty::v2_i64(),
            Constant::v2_i64([7, -9]),
            shuffle(Ty::v2_i64(), v(0), [1u8, 1]),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(vector_signed(&returns[0]), vec![-9, -9]);
    }

    /// `<8 x i16>` sits outside the Lean executable subset; the Rust pass
    /// still lowers it, so pin the agreement here.
    #[test]
    fn lowered_shuffle_v8_i16_interleave_matches_dialect_result() {
        let vector_ty = Ty::Vector(Box::new(Ty::I16), 8);
        let lanes = (0..8).map(|i| Constant::Int(i * 10 - 30)).collect();
        let module = module_returning_op(
            vector_ty.clone(),
            Constant::Vector(lanes),
            shuffle(vector_ty, v(0), [0u8, 4, 1, 5, 2, 6, 3, 7]),
        );
        let returns = assert_lowering_preserves_result(&module);
        assert_eq!(
            vector_signed(&returns[0]),
            vec![-30, 10, -20, 20, -10, 30, 0, 40]
        );
    }

    /// `<16 x i8>` sits outside the Lean executable subset; the Rust pass
    /// still lowers it, so pin the agreement (including i8 wrap) here.
    #[test]
    fn lowered_reduce_add_v16_i8_matches_dialect_result() {
        let vector_ty = Ty::Vector(Box::new(Ty::I8), 16);
        let mut lanes = vec![Constant::Int(100); 2];
        lanes.extend(vec![Constant::Int(9); 14]);
        let module = module_returning_op(
            vector_ty.clone(),
            Constant::Vector(lanes),
            reduce(vector_ty, v(0), ReduceKind::Add),
        );
        let returns = assert_lowering_preserves_result(&module);
        // 2*100 + 14*9 = 326 wraps to 326 - 256 = 70 in i8.
        assert_eq!(returns[0].as_int().map(|i| i.as_signed()), Some(70));
    }
}
