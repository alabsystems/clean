// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_assert_kind<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    canonical: Option<Canonical<'_>>,
    kind: &AssertKind,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    match kind {
        AssertKind::Unspecified => return Err(ObservedValueError::UnsupportedValue),
        AssertKind::Overflow(op) => {
            observed_write_u8(buf, 0)?;
            observed_write_assert_overflow_op(buf, op)?;
        }
        AssertKind::DivByZero => observed_write_u8(buf, 1)?,
        AssertKind::RemByZero => observed_write_u8(buf, 2)?,
        AssertKind::BoundsCheck { index, len } => {
            observed_write_u8(buf, 3)?;
            observed_write_projected_value_id(buf, canonical, *index)?;
            observed_write_projected_value_id(buf, canonical, *len)?;
        }
        AssertKind::MisalignedPtr { required, found } => {
            observed_write_u8(buf, 4)?;
            observed_write_projected_value_id(buf, canonical, *required)?;
            observed_write_projected_value_id(buf, canonical, *found)?;
        }
        AssertKind::NullPtr => observed_write_u8(buf, 5)?,
    }

    Ok(())
}

pub(super) fn observed_write_assert_overflow_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &AssertOverflowOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        AssertOverflowOp::Add => 0,
        AssertOverflowOp::Sub => 1,
        AssertOverflowOp::Mul => 2,
        AssertOverflowOp::Div => 3,
        AssertOverflowOp::Rem => 4,
        AssertOverflowOp::Shl => 5,
        AssertOverflowOp::Shr => 6,
        AssertOverflowOp::Neg => 7,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_atomic_rmw_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &AtomicRMWOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        AtomicRMWOp::Xchg => 0,
        AtomicRMWOp::Add => 1,
        AtomicRMWOp::Sub => 2,
        AtomicRMWOp::And => 3,
        AtomicRMWOp::Or => 4,
        AtomicRMWOp::Xor => 5,
        AtomicRMWOp::Max => 6,
        AtomicRMWOp::Min => 7,
        AtomicRMWOp::UMax => 8,
        AtomicRMWOp::UMin => 9,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_attr_value<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    v: &crate::dialect::AttrValue,
) -> R {
    buf.poll()?;
    use crate::dialect::AttrValue;
    match v {
        AttrValue::I64(x) => {
            observed_write_u8(buf, 0)?;
            // Stored as u64 bit pattern; read back via signed cast.
            buf.extend_from_slice(&x.to_le_bytes())?;
        }
        AttrValue::U64(x) => {
            observed_write_u8(buf, 1)?;
            observed_write_v64(buf, *x)?;
        }
        AttrValue::F64(x) => {
            observed_write_u8(buf, 2)?;
            observed_write_f64(buf, *x)?;
        }
        AttrValue::Bool(x) => {
            observed_write_u8(buf, 3)?;
            observed_write_bool(buf, *x)?;
        }
        AttrValue::Str(s) => {
            observed_write_u8(buf, 4)?;
            observed_write_str(buf, pool, s)?;
        }
        AttrValue::Bytes(b) => {
            observed_write_u8(buf, 5)?;
            observed_write_bytes(buf, b)?;
        }
        AttrValue::Ty(t) => {
            observed_write_u8(buf, 6)?;
            observed_write_ty(buf, pool, t)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_binop<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &BinOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        BinOp::Add => 0,
        BinOp::Sub => 1,
        BinOp::Mul => 2,
        BinOp::UDiv => 3,
        BinOp::SDiv => 4,
        BinOp::URem => 5,
        BinOp::SRem => 6,
        BinOp::FAdd => 7,
        BinOp::FSub => 8,
        BinOp::FMul => 9,
        BinOp::FDiv => 10,
        BinOp::FRem => 11,
        BinOp::And => 12,
        BinOp::Or => 13,
        BinOp::Xor => 14,
        BinOp::Shl => 15,
        BinOp::LShr => 16,
        BinOp::AShr => 17,
        BinOp::FMin => 18,
        BinOp::FMax => 19,
        BinOp::BAnd => 20,
        BinOp::BOr => 21,
        BinOp::BXor => 22,
        BinOp::RotL => 23,
        BinOp::RotR => 24,
        BinOp::FCopySign => 25,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_block<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    canonical: Option<Canonical<'_>>,
    function: FuncId,
    block: &BlockG<NoExt>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_block_id(buf, block.id)?;
    observed_write_count(buf, "Block.params", block.params.len())?;
    for (vid, ty) in &block.params {
        buf.poll()?;
        observed_write_projected_value_id(buf, canonical, *vid)?;
        observed_write_ty(buf, pool, ty)?;
    }
    observed_write_count(buf, "Block.body", block.body.len())?;
    for (index, node) in block.body.iter().enumerate() {
        buf.poll()?;
        // An instruction ahead of its wire tag (the ONE list is
        // `Inst::binary_wire_gap`, empty since v51) is refused here, at its
        // node, and nothing is written for it.
        if let Some(construct) = node.inst.binary_wire_gap() {
            buf.refuse(|| WireRefusal::NoWireTag {
                construct,
                site: Some(WireNodeSite {
                    function: function.index(),
                    block: block.id.index(),
                    index,
                }),
            })?;
            continue;
        }
        observed_write_instr_node(buf, pool, canonical, node)?;
    }

    Ok(())
}

pub(super) fn observed_write_block_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: BlockId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_body_gate<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    gate: Option<&crate::BodyGate>,
) -> R {
    buf.poll()?;
    match gate {
        None => observed_write_u8(buf, 0)?,
        Some(crate::BodyGate::Ungated) => observed_write_u8(buf, 1)?,
        Some(crate::BodyGate::Gated {
            authority,
            evidence: None,
        }) => {
            observed_write_u8(buf, 2)?;
            observed_write_str(buf, pool, authority)?;
        }
        // v61: the evidenced license. Tag 2 keeps its exact bytes; the
        // evidence is a separate tag, so no pre-v61 reader misreads it.
        Some(crate::BodyGate::Gated {
            authority,
            evidence: Some(evidence),
        }) => {
            observed_write_u8(buf, 3)?;
            observed_write_str(buf, pool, authority)?;
            observed_write_v32(buf, evidence.obligation.index())?;
            observed_write_proof_digest(buf, &evidence.body_digest)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_bool<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: bool) -> R {
    buf.poll()?;
    buf.push(if v { 1 } else { 0 })?;

    Ok(())
}

pub(super) fn observed_write_bytes<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    data: &[u8],
) -> R {
    buf.poll()?;
    observed_write_count(buf, "byte string", data.len())?;
    buf.extend_from_slice(data)?;

    Ok(())
}

pub(super) fn observed_write_calling_conv<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    v: &CallingConv,
) -> R {
    buf.poll()?;
    observed_write_u8(
        buf,
        match v {
            CallingConv::C => 0,
            CallingConv::Fast => 1,
            CallingConv::Cold => 2,
            CallingConv::Rust => 3,
            CallingConv::Swift => 4,
            CallingConv::CUnwind => 5,
            CallingConv::SysV64 => 6,
            CallingConv::Win64 => 7,
            CallingConv::Aapcs => 8,
            CallingConv::EfiApi => 9,
            CallingConv::VectorCall => 10,
            CallingConv::RustCold => 11,
        },
    )?;

    Ok(())
}

pub(super) fn observed_write_cast_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &CastOp,
) -> R {
    buf.poll()?;
    let tag = match value {
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
        CastOp::Bitcast => 11,
        CastOp::PtrToPtr => 12,
        CastOp::Transmute => 13,
        CastOp::ReifyFnPointer => 14,
        CastOp::FPToSISat => 15,
        CastOp::FPToUISat => 16,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_certificate_binding<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    binding: &crate::proof::CertificateBinding,
) -> R {
    buf.poll()?;
    // Exhaustive destructure: a field added to `CertificateBinding` without a
    // carrier is a compile error here, never a silently dropped field (the
    // WS1.13 island arrived after this carrier was first written).
    let crate::proof::CertificateBinding {
        environment_digest,
        statement_digest,
        origin_module,
        source,
        callees,
        environment,
    } = binding;
    observed_write_proof_digest(buf, environment_digest)?;
    observed_write_proof_digest(buf, statement_digest)?;
    match origin_module {
        None => observed_write_u8(buf, 0)?,
        Some(digest) => {
            observed_write_u8(buf, 1)?;
            observed_write_proof_digest(buf, digest)?;
        }
    }
    match source {
        None => observed_write_u8(buf, 0)?,
        Some(source) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, &source.decl)?;
            observed_write_proof_digest(buf, &source.closure_digest)?;
        }
    }
    observed_write_count(buf, "CertificateBinding.callees", callees.len())?;
    for callee in callees {
        buf.poll()?;
        observed_write_str(buf, pool, callee)?;
    }
    // WS1.13: the island rides the carrier as the SAME opaque bytes, with the
    // digest it RECORDS (the validator recomputes and compares it; a reader
    // that recomputed here would launder a forged digest into a true one).
    match environment {
        None => observed_write_u8(buf, 0)?,
        Some(island) => {
            observed_write_u8(buf, 1)?;
            observed_write_bytes(buf, &island.declarations)?;
            observed_write_proof_digest(buf, &island.digest)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_clause_place<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    place: &ClausePlace,
) -> R {
    buf.poll()?;
    match place {
        ClausePlace::Param { index } => {
            observed_write_u8(buf, 0)?;
            observed_write_v32(buf, *index)?;
        }
        ClausePlace::ResultSlot { index } => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, *index)?;
        }
        ClausePlace::MutParamExit { index } => {
            observed_write_u8(buf, 2)?;
            observed_write_v32(buf, *index)?;
        }
        ClausePlace::World => observed_write_u8(buf, 3)?,
        ClausePlace::Unwind => observed_write_u8(buf, 4)?,
        ClausePlace::Value(v) => {
            observed_write_u8(buf, 5)?;
            observed_write_value_id(buf, *v)?;
        }
        // v46: the spec-variable index space. Selection is driven by the
        // string collector, which raises `pool.minimum_version` for every
        // carrier that can hold one.
        ClausePlace::SpecVar { index } => {
            observed_write_u8(buf, 6)?;
            observed_write_v32(buf, *index)?;
        }
        ClausePlace::SpecVarNext { index } => {
            observed_write_u8(buf, 7)?;
            observed_write_v32(buf, *index)?;
        }
        // v59: the world epochs, tag only. Selection is driven by the string
        // collector, which raises `pool.minimum_version` wherever one is bound.
        ClausePlace::WorldPre => observed_write_u8(buf, 8)?,
        ClausePlace::WorldPost => observed_write_u8(buf, 9)?,
        // v62: tag 10 (8 and 9 are the v59 world epochs). Selected, like them and the
        // spec-variable places, by the formula string collector.
        ClausePlace::ParamPointeeEntry { index } => {
            observed_write_u8(buf, 10)?;
            observed_write_v32(buf, *index)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_closure_ty<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ct: &ClosureTy,
) -> R {
    buf.poll()?;
    observed_write_func_ty_id(buf, ct.func)?;
    observed_write_count(buf, "ClosureTy.captures", ct.captures.len())?;
    for c in &ct.captures {
        buf.poll()?;
        observed_write_ty(buf, pool, c)?;
    }

    Ok(())
}

pub(super) fn observed_write_closure_ty_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: ClosureTyId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_count<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    what: &'static str,
    count: usize,
) -> R {
    buf.poll()?;
    // `usize` is at most 64 bits on every target Rust supports, so this
    // widening cast is exact.
    let count = count as u64;
    if count > u64::from(u32::MAX) {
        buf.note_over_limit(what, count)?;
    }
    observed_write_v64(buf, count)?;

    Ok(())
}

pub(super) fn observed_write_dialect_inst<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    canonical: Option<Canonical<'_>>,
    op: &crate::dialect::DialectInst,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_str(buf, pool, &op.dialect)?;
    observed_write_str(buf, pool, &op.op)?;
    observed_write_vec_value_id(buf, canonical, &op.operands)?;
    observed_write_count(buf, "DialectInst.result_tys", op.result_tys.len())?;
    for t in &op.result_tys {
        buf.poll()?;
        observed_write_ty(buf, pool, t)?;
    }
    observed_write_count(buf, "DialectInst.attrs", op.attrs.len())?;
    for entry in &op.attrs {
        buf.poll()?;
        observed_write_str(buf, pool, &entry.name)?;
        observed_write_attr_value(buf, pool, &entry.value)?;
    }
    observed_write_v32(buf, op.version)?;

    Ok(())
}
