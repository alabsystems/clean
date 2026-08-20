// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Apple Neural Engine (ANE) dialect.
//!
//! Provides hardware-accelerated tensor operations for the Apple Neural Engine.
//!
//! # Opaque payload-only contract (no lowering yet)
//!
//! `ane.*` is an **opaque payload-only** dialect: the stable contract is the
//! serialized [`DialectInst`] payload (dialect name, op name, operands, result
//! types, attributes), which round-trips through every TrustIr serialization
//! format. This crate validates and decodes those payloads but ships **no
//! lowering pass** — [`AneDialect`] uses the default empty
//! [`Dialect::lowerings`].
//!
//! Per the "semantics first" rule, no lowering is invented here: ANE tensor
//! conv / matmul / DMA ops have no portable, verified expansion into core
//! TrustIr — they are driven by Apple's CoreML / ANE compiler and described
//! through hardware-specific descriptors that only the backend can emit. The
//! `decode*` helpers and the [`AneSpec`] view exist so a consumer can
//! pattern-match the payload without re-parsing attributes; a backend that
//! offloads to the ANE registers its own lowering.

use crate::dialect::{AttrValue, Dialect, DialectError, DialectInst};
use crate::ty::Ty;
use crate::value::ValueId;

pub const DIALECT: &str = "ane";

pub const TENSOR_CONV_OP: &str = "tensor_conv";
pub const TENSOR_MATMUL_OP: &str = "tensor_matmul";
pub const DMA_TRANSFER_OP: &str = "dma_transfer";

const OPS: &[&str] = &[TENSOR_CONV_OP, TENSOR_MATMUL_OP, DMA_TRANSFER_OP];

const STRIDE_ATTR: &str = "stride";
const PADDING_ATTR: &str = "padding";
const DIRECTION_ATTR: &str = "direction";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TensorConvSpec {
    pub input: ValueId,
    pub weights: ValueId,
    pub bias: Option<ValueId>,
    pub stride: u32,
    pub padding: u32,
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TensorMatmulSpec {
    pub a: ValueId,
    pub b: ValueId,
    pub bias: Option<ValueId>,
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DmaTransferSpec {
    pub src: ValueId,
    pub dst: ValueId,
    pub size: ValueId,
    pub direction: String, // e.g. "main_to_ane", "ane_to_main"
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AneSpec {
    TensorConv(TensorConvSpec),
    TensorMatmul(TensorMatmulSpec),
    DmaTransfer(DmaTransferSpec),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct AneDialect;

impl Dialect for AneDialect {
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
        decode(inst).map(|_| ())
    }
}

pub fn decode(inst: &DialectInst) -> Result<AneSpec, DialectError> {
    match inst.op.as_str() {
        TENSOR_CONV_OP => decode_tensor_conv(inst).map(AneSpec::TensorConv),
        TENSOR_MATMUL_OP => decode_tensor_matmul(inst).map(AneSpec::TensorMatmul),
        DMA_TRANSFER_OP => decode_dma_transfer(inst).map(AneSpec::DmaTransfer),
        _ => Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        }),
    }
}

fn decode_tensor_conv(inst: &DialectInst) -> Result<TensorConvSpec, DialectError> {
    if inst.operands.len() < 2 || inst.operands.len() > 3 {
        return Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        });
    }
    require_results(inst, 1)?;
    let stride = inst.attr(STRIDE_ATTR).and_then(|a| a.as_u64()).unwrap_or(1) as u32;
    let padding = inst
        .attr(PADDING_ATTR)
        .and_then(|a| a.as_u64())
        .unwrap_or(0) as u32;
    Ok(TensorConvSpec {
        input: inst.operands[0],
        weights: inst.operands[1],
        bias: inst.operands.get(2).copied(),
        stride,
        padding,
        result_ty: inst.result_tys[0].clone(),
    })
}

fn decode_tensor_matmul(inst: &DialectInst) -> Result<TensorMatmulSpec, DialectError> {
    if inst.operands.len() < 2 || inst.operands.len() > 3 {
        return Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        });
    }
    require_results(inst, 1)?;
    Ok(TensorMatmulSpec {
        a: inst.operands[0],
        b: inst.operands[1],
        bias: inst.operands.get(2).copied(),
        result_ty: inst.result_tys[0].clone(),
    })
}

fn decode_dma_transfer(inst: &DialectInst) -> Result<DmaTransferSpec, DialectError> {
    require_operands(inst, 3)?;
    require_results(inst, 0)?;
    let direction = inst
        .attr(DIRECTION_ATTR)
        .and_then(|a| a.as_str())
        .unwrap_or("unknown")
        .to_string();
    Ok(DmaTransferSpec {
        src: inst.operands[0],
        dst: inst.operands[1],
        size: inst.operands[2],
        direction,
    })
}

fn require_operands(inst: &DialectInst, count: usize) -> Result<(), DialectError> {
    if inst.operands.len() != count {
        return Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        });
    }
    Ok(())
}

fn require_results(inst: &DialectInst, count: usize) -> Result<(), DialectError> {
    if inst.result_tys.len() != count {
        return Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        });
    }
    Ok(())
}

pub fn tensor_conv(
    result_ty: Ty,
    input: ValueId,
    weights: ValueId,
    bias: Option<ValueId>,
    stride: u32,
    padding: u32,
) -> DialectInst {
    let mut inst = DialectInst::new(DIALECT, TENSOR_CONV_OP)
        .with_operand(input)
        .with_operand(weights)
        .with_result_ty(result_ty)
        .with_attr(STRIDE_ATTR, AttrValue::U64(stride as u64))
        .with_attr(PADDING_ATTR, AttrValue::U64(padding as u64));
    if let Some(b) = bias {
        inst = inst.with_operand(b);
    }
    inst
}

pub fn tensor_matmul(result_ty: Ty, a: ValueId, b: ValueId, bias: Option<ValueId>) -> DialectInst {
    let mut inst = DialectInst::new(DIALECT, TENSOR_MATMUL_OP)
        .with_operand(a)
        .with_operand(b)
        .with_result_ty(result_ty);
    if let Some(bi) = bias {
        inst = inst.with_operand(bi);
    }
    inst
}

pub fn dma_transfer(src: ValueId, dst: ValueId, size: ValueId, direction: &str) -> DialectInst {
    DialectInst::new(DIALECT, DMA_TRANSFER_OP)
        .with_operand(src)
        .with_operand(dst)
        .with_operand(size)
        .with_attr(DIRECTION_ATTR, AttrValue::Str(direction.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::Dialect;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    /// `ane.*` is opaque payload-only: it ships NO lowering pass.
    #[test]
    fn ane_dialect_is_payload_only_no_lowerings() {
        assert!(
            AneDialect.lowerings().is_empty(),
            "ane.* must not ship an (unverified) lowering pass"
        );
        assert_eq!(AneDialect.name(), DIALECT);
        assert_eq!(AneDialect.version(), 1);
    }

    /// Builders round-trip through decode + validate, with and without the
    /// optional bias operand.
    #[test]
    fn builders_round_trip_through_decode_and_validate() {
        let dialect = AneDialect;

        let conv = tensor_conv(Ty::Ptr, v(0), v(1), Some(v(2)), 2, 1);
        assert_eq!(conv.dialect, DIALECT);
        assert_eq!(
            decode(&conv).unwrap(),
            AneSpec::TensorConv(TensorConvSpec {
                input: v(0),
                weights: v(1),
                bias: Some(v(2)),
                stride: 2,
                padding: 1,
                result_ty: Ty::Ptr,
            })
        );
        dialect.validate(&conv).expect("tensor_conv validates");

        let conv_no_bias = tensor_conv(Ty::Ptr, v(0), v(1), None, 1, 0);
        assert_eq!(
            decode(&conv_no_bias).unwrap(),
            AneSpec::TensorConv(TensorConvSpec {
                input: v(0),
                weights: v(1),
                bias: None,
                stride: 1,
                padding: 0,
                result_ty: Ty::Ptr,
            })
        );
        dialect
            .validate(&conv_no_bias)
            .expect("biasless tensor_conv validates");

        let matmul = tensor_matmul(Ty::Ptr, v(0), v(1), Some(v(2)));
        assert_eq!(
            decode(&matmul).unwrap(),
            AneSpec::TensorMatmul(TensorMatmulSpec {
                a: v(0),
                b: v(1),
                bias: Some(v(2)),
                result_ty: Ty::Ptr,
            })
        );
        dialect.validate(&matmul).expect("tensor_matmul validates");

        let dma = dma_transfer(v(0), v(1), v(2), "main_to_ane");
        assert_eq!(
            decode(&dma).unwrap(),
            AneSpec::DmaTransfer(DmaTransferSpec {
                src: v(0),
                dst: v(1),
                size: v(2),
                direction: "main_to_ane".to_string(),
            })
        );
        dialect.validate(&dma).expect("dma_transfer validates");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn payload_round_trips_through_serde_json() {
        let op = tensor_conv(Ty::Ptr, v(0), v(1), Some(v(2)), 2, 1);
        let json = serde_json::to_string(&op).expect("serialize");
        let back: DialectInst = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(op, back);
        assert_eq!(decode(&back).unwrap(), decode(&op).unwrap());
    }

    #[test]
    fn validate_rejects_unknown_op_and_bad_arity() {
        let dialect = AneDialect;
        assert!(matches!(
            dialect.validate(&DialectInst::new(DIALECT, "softmax")),
            Err(DialectError::UnknownOp { .. })
        ));
        // dma_transfer requires exactly three operands and no results.
        let bad = DialectInst::new(DIALECT, DMA_TRANSFER_OP)
            .with_operand(v(0))
            .with_operand(v(1));
        assert!(dialect.validate(&bad).is_err());
    }
}
