// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AVX-512 dialect.
//!
//! Provides x86 AVX-512 specific operations including masked comparisons,
//! ternary bitwise logic (vpternlog), and mask-driven compress/expand.
//!
//! # Opaque payload-only contract (no lowering yet)
//!
//! `avx512.*` is an **opaque payload-only** dialect: the stable contract is the
//! serialized [`DialectInst`] payload (dialect name, op name, operands, result
//! types, attributes), which round-trips through every TrustIr serialization
//! format. This crate validates and decodes those payloads but ships **no
//! lowering pass** — [`Avx512Dialect`] uses the default empty
//! [`Dialect::lowerings`].
//!
//! Per the "semantics first" rule, no lowering is invented here: the correct
//! expansion of `avx512.vpternlog` / `avx512.mask_cmp` / `avx512.compress` /
//! `avx512.expand` is a target-specific instruction-selection decision the
//! backend (TrustCg) owns, and writing an unverified core-IR expansion would be
//! worse than leaving the op opaque. A backend that targets AVX-512 registers
//! its own lowering; until then these ops survive verbatim. The `decode*`
//! helpers and the [`Avx512Spec`] view exist so a consumer can pattern-match the
//! payload without re-parsing attributes.

use crate::dialect::{AttrValue, Dialect, DialectError, DialectInst};
use crate::inst::ICmpOp;
use crate::ty::Ty;
use crate::value::ValueId;

pub const DIALECT: &str = "avx512";

pub const MASK_CMP_OP: &str = "mask_cmp";
pub const VPTERNLOG_OP: &str = "vpternlog";
pub const COMPRESS_OP: &str = "compress";
pub const EXPAND_OP: &str = "expand";

const OPS: &[&str] = &[MASK_CMP_OP, VPTERNLOG_OP, COMPRESS_OP, EXPAND_OP];

const PREDICATE_ATTR: &str = "predicate";
const IMM8_ATTR: &str = "imm8";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskCmpSpec {
    pub op: ICmpOp,
    pub lhs: ValueId,
    pub rhs: ValueId,
    pub result_ty: Ty, // Must be <N x bool>
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VpternlogSpec {
    pub imm8: u8,
    pub a: ValueId,
    pub b: ValueId,
    pub c: ValueId,
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompressSpec {
    pub src: ValueId,
    pub mask: ValueId,
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpandSpec {
    pub src: ValueId,
    pub mask: ValueId,
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Avx512Spec {
    MaskCmp(MaskCmpSpec),
    Vpternlog(VpternlogSpec),
    Compress(CompressSpec),
    Expand(ExpandSpec),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Avx512Dialect;

impl Dialect for Avx512Dialect {
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

pub fn decode(inst: &DialectInst) -> Result<Avx512Spec, DialectError> {
    match inst.op.as_str() {
        MASK_CMP_OP => decode_mask_cmp(inst).map(Avx512Spec::MaskCmp),
        VPTERNLOG_OP => decode_vpternlog(inst).map(Avx512Spec::Vpternlog),
        COMPRESS_OP => decode_compress(inst).map(Avx512Spec::Compress),
        EXPAND_OP => decode_expand(inst).map(Avx512Spec::Expand),
        _ => Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        }),
    }
}

fn decode_mask_cmp(inst: &DialectInst) -> Result<MaskCmpSpec, DialectError> {
    require_operands(inst, 2)?;
    require_results(inst, 1)?;
    let pred_str = inst
        .attr(PREDICATE_ATTR)
        .ok_or_else(|| DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        })?
        .as_str()
        .ok_or_else(|| DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        })?;
    let op = match pred_str {
        "eq" => ICmpOp::Eq,
        "ne" => ICmpOp::Ne,
        "ult" => ICmpOp::Ult,
        "ule" => ICmpOp::Ule,
        "ugt" => ICmpOp::Ugt,
        "uge" => ICmpOp::Uge,
        "slt" => ICmpOp::Slt,
        "sle" => ICmpOp::Sle,
        "sgt" => ICmpOp::Sgt,
        "sge" => ICmpOp::Sge,
        _ => {
            return Err(DialectError::UnknownOp {
                dialect: DIALECT,
                op: inst.op.clone(),
            });
        }
    };
    Ok(MaskCmpSpec {
        op,
        lhs: inst.operands[0],
        rhs: inst.operands[1],
        result_ty: inst.result_tys[0].clone(),
    })
}

fn decode_vpternlog(inst: &DialectInst) -> Result<VpternlogSpec, DialectError> {
    require_operands(inst, 3)?;
    require_results(inst, 1)?;
    let imm8 = inst
        .attr(IMM8_ATTR)
        .ok_or_else(|| DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        })?
        .as_u64()
        .ok_or_else(|| DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        })? as u8;
    Ok(VpternlogSpec {
        imm8,
        a: inst.operands[0],
        b: inst.operands[1],
        c: inst.operands[2],
        result_ty: inst.result_tys[0].clone(),
    })
}

fn decode_compress(inst: &DialectInst) -> Result<CompressSpec, DialectError> {
    require_operands(inst, 2)?;
    require_results(inst, 1)?;
    Ok(CompressSpec {
        src: inst.operands[0],
        mask: inst.operands[1],
        result_ty: inst.result_tys[0].clone(),
    })
}

fn decode_expand(inst: &DialectInst) -> Result<ExpandSpec, DialectError> {
    require_operands(inst, 2)?;
    require_results(inst, 1)?;
    Ok(ExpandSpec {
        src: inst.operands[0],
        mask: inst.operands[1],
        result_ty: inst.result_tys[0].clone(),
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

pub fn mask_cmp(op: ICmpOp, result_ty: Ty, lhs: ValueId, rhs: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, MASK_CMP_OP)
        .with_operand(lhs)
        .with_operand(rhs)
        .with_result_ty(result_ty)
        .with_attr(PREDICATE_ATTR, AttrValue::Str(format!("{}", op)))
}

pub fn vpternlog(imm8: u8, result_ty: Ty, a: ValueId, b: ValueId, c: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, VPTERNLOG_OP)
        .with_operand(a)
        .with_operand(b)
        .with_operand(c)
        .with_result_ty(result_ty)
        .with_attr(IMM8_ATTR, AttrValue::U64(imm8 as u64))
}

pub fn compress(result_ty: Ty, src: ValueId, mask: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, COMPRESS_OP)
        .with_operand(src)
        .with_operand(mask)
        .with_result_ty(result_ty)
}

pub fn expand(result_ty: Ty, src: ValueId, mask: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, EXPAND_OP)
        .with_operand(src)
        .with_operand(mask)
        .with_result_ty(result_ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::Dialect;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    /// `avx512.*` is opaque payload-only: it ships NO lowering pass.
    #[test]
    fn avx512_dialect_is_payload_only_no_lowerings() {
        assert!(
            Avx512Dialect.lowerings().is_empty(),
            "avx512.* must not ship an (unverified) lowering pass"
        );
        assert_eq!(Avx512Dialect.name(), DIALECT);
        assert_eq!(Avx512Dialect.version(), 1);
    }

    /// Every builder produces a payload that decodes back to its spec and
    /// validates — the opaque round-trip the backend relies on.
    #[test]
    fn builders_round_trip_through_decode_and_validate() {
        let dialect = Avx512Dialect;

        let mask = mask_cmp(ICmpOp::Slt, Ty::v4_bool(), v(0), v(1));
        assert_eq!(mask.dialect, DIALECT);
        assert_eq!(
            decode(&mask).unwrap(),
            Avx512Spec::MaskCmp(MaskCmpSpec {
                op: ICmpOp::Slt,
                lhs: v(0),
                rhs: v(1),
                result_ty: Ty::v4_bool(),
            })
        );
        dialect.validate(&mask).expect("mask_cmp validates");

        let tern = vpternlog(0xCA, Ty::v4_i32(), v(0), v(1), v(2));
        assert_eq!(
            decode(&tern).unwrap(),
            Avx512Spec::Vpternlog(VpternlogSpec {
                imm8: 0xCA,
                a: v(0),
                b: v(1),
                c: v(2),
                result_ty: Ty::v4_i32(),
            })
        );
        dialect.validate(&tern).expect("vpternlog validates");

        let comp = compress(Ty::v4_i32(), v(0), v(1));
        assert_eq!(
            decode(&comp).unwrap(),
            Avx512Spec::Compress(CompressSpec {
                src: v(0),
                mask: v(1),
                result_ty: Ty::v4_i32(),
            })
        );
        dialect.validate(&comp).expect("compress validates");

        let exp = expand(Ty::v4_i32(), v(0), v(1));
        assert_eq!(
            decode(&exp).unwrap(),
            Avx512Spec::Expand(ExpandSpec {
                src: v(0),
                mask: v(1),
                result_ty: Ty::v4_i32(),
            })
        );
        dialect.validate(&exp).expect("expand validates");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn payload_round_trips_through_serde_json() {
        let op = vpternlog(0x96, Ty::v4_i32(), v(0), v(1), v(2));
        let json = serde_json::to_string(&op).expect("serialize");
        let back: DialectInst = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(op, back);
        assert_eq!(decode(&back).unwrap(), decode(&op).unwrap());
    }

    #[test]
    fn validate_rejects_unknown_op_and_bad_arity() {
        let dialect = Avx512Dialect;
        assert!(matches!(
            dialect.validate(&DialectInst::new(DIALECT, "vpconflict")),
            Err(DialectError::UnknownOp { .. })
        ));
        // mask_cmp requires two operands.
        let bad = DialectInst::new(DIALECT, MASK_CMP_OP)
            .with_operand(v(0))
            .with_result_ty(Ty::v4_bool())
            .with_attr(PREDICATE_ATTR, AttrValue::Str("eq".to_string()));
        assert!(dialect.validate(&bad).is_err());
    }
}
