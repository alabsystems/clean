// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_obligation_kind<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    kind: &ObligationKind,
) -> R {
    buf.poll()?;
    match kind {
        ObligationKind::Precondition => observed_write_u8(buf, 0)?,
        ObligationKind::Postcondition => observed_write_u8(buf, 1)?,
        ObligationKind::LoopInvariant => observed_write_u8(buf, 2)?,
        ObligationKind::TypeInvariant => observed_write_u8(buf, 3)?,
        ObligationKind::RefinementType => observed_write_u8(buf, 4)?,
        ObligationKind::TranslationValidation => observed_write_u8(buf, 5)?,
        ObligationKind::MemorySafety => observed_write_u8(buf, 6)?,
        ObligationKind::PanicFreedom => observed_write_u8(buf, 7)?,
        ObligationKind::TemporalSafety => observed_write_u8(buf, 8)?,
        ObligationKind::Liveness => observed_write_u8(buf, 9)?,
        // Trust (trust-ir-spine item T1): panic-class routing-grade kinds.
        ObligationKind::ArithmeticSafety => observed_write_u8(buf, 10)?,
        ObligationKind::BoundsCheck => observed_write_u8(buf, 11)?,
        // Aeneas-style give-back refinement view (trust-ir-giveback).
        ObligationKind::GiveBackRefinement => observed_write_u8(buf, 12)?,
        ObligationKind::Termination => observed_write_u8(buf, 13)?,
        ObligationKind::Ownership => observed_write_u8(buf, 14)?,
        ObligationKind::Custom { namespace, name } => {
            observed_write_u8(buf, 15)?;
            observed_write_str(buf, pool, namespace)?;
            observed_write_str(buf, pool, name)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_opt_str<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    v: Option<&str>,
) -> R {
    buf.poll()?;
    match v {
        None => observed_write_u8(buf, 0)?,
        Some(s) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, s)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_opt_u64<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    v: Option<u64>,
) -> R {
    buf.poll()?;
    match v {
        None => observed_write_u8(buf, 0)?,
        Some(val) => {
            observed_write_u8(buf, 1)?;
            observed_write_v64(buf, val)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_opt_v32<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    v: Option<u32>,
) -> R {
    buf.poll()?;
    match v {
        None => observed_write_u8(buf, 0)?,
        Some(val) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, val)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_ordering<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &Ordering,
) -> R {
    buf.poll()?;
    let tag = match value {
        Ordering::Relaxed => 0,
        Ordering::Acquire => 1,
        Ordering::Release => 2,
        Ordering::AcqRel => 3,
        Ordering::SeqCst => 4,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_overflow_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &OverflowOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        OverflowOp::AddOverflow => 0,
        OverflowOp::SubOverflow => 1,
        OverflowOp::MulOverflow => 2,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_panic_location<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    canonical: Option<Canonical<'_>>,
    location: &PanicLocation,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    match location {
        PanicLocation::Global(global) => {
            observed_write_u8(buf, 0)?;
            observed_write_v32(buf, global.index())?;
        }
        PanicLocation::Value(value) => {
            observed_write_u8(buf, 1)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_param_attrs<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    pa: &ParamAttrs,
) -> R {
    buf.poll()?;
    let mut flags: u8 = 0;
    if pa.nonnull {
        flags |= 0b0001;
    }
    if pa.noalias {
        flags |= 0b0010;
    }
    if pa.readonly {
        flags |= 0b0100;
    }
    // VERSION >= 20 (ABI pinning): byval/sret aggregate-passing classification.
    if pa.byval {
        flags |= 0b0_1000;
    }
    if pa.sret {
        flags |= 0b1_0000;
    }
    // v45 (WS3.11): the integer extension rides flag bits 5 and 6. They are
    // MUTUALLY EXCLUSIVE — both set is not a third extension — and setting
    // either raised the writer to v45 in the collection walk, so no pre-v45
    // blob carries one. Bit 7 is unallocated and never written.
    match pa.ext {
        ArgExt::None => {}
        ArgExt::ZeroExt => flags |= 0b010_0000,
        ArgExt::SignExt => flags |= 0b100_0000,
    }
    observed_write_u8(buf, flags)?;
    observed_write_opt_u64(buf, pa.dereferenceable)?;
    observed_write_opt_u64(buf, pa.align)?;
    // v45: the pass mode, a presence-tagged record after `align`.
    if abi_surface(pool) {
        observed_write_pass_mode(buf, pool, pa.pass.as_ref())?;
    }

    Ok(())
}

pub(super) fn observed_write_pass_mode<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    pass: Option<&PassMode>,
) -> R {
    buf.poll()?;
    match pass {
        None => observed_write_u8(buf, 0)?,
        Some(PassMode::Ignore) => observed_write_u8(buf, 1)?,
        Some(PassMode::Direct) => observed_write_u8(buf, 2)?,
        Some(PassMode::Pair) => observed_write_u8(buf, 3)?,
        Some(PassMode::Cast { pieces }) => {
            observed_write_u8(buf, 4)?;
            observed_write_count(buf, "PassMode::Cast pieces", pieces.len())?;
            for piece in pieces {
                buf.poll()?;
                observed_write_ty(buf, pool, piece)?;
            }
        }
        Some(PassMode::Indirect { on_stack }) => {
            observed_write_u8(buf, 5)?;
            observed_write_bool(buf, *on_stack)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_pred<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    p: &crate::pred::Pred,
) -> R {
    buf.poll()?;
    use crate::pred::Pred;
    match p {
        Pred::Interval { lo, hi } => {
            observed_write_u8(buf, 0)?;
            observed_write_i128(buf, *lo)?;
            observed_write_i128(buf, *hi)?;
        }
        Pred::FiniteSet(items) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "Pred::FiniteSet items", items.len())?;
            for c in items {
                buf.poll()?;
                observed_write_constant(buf, pool, c)?;
            }
        }
        Pred::InUniverse(u, space) => {
            observed_write_u8(buf, 2)?;
            observed_write_v32(buf, u.index())?;
            observed_write_space(buf, *space)?;
        }
        Pred::NonZero => observed_write_u8(buf, 3)?,
        Pred::NonNull => observed_write_u8(buf, 4)?,
        Pred::Conj(children) => {
            observed_write_u8(buf, 5)?;
            observed_write_count(buf, "Pred::Conj children", children.len())?;
            for c in children {
                buf.poll()?;
                observed_write_v32(buf, c.index())?;
            }
        }
        Pred::Disj(children) => {
            observed_write_u8(buf, 6)?;
            observed_write_count(buf, "Pred::Disj children", children.len())?;
            for c in children {
                buf.poll()?;
                observed_write_v32(buf, c.index())?;
            }
        }
        Pred::Top => observed_write_u8(buf, 7)?,
        Pred::Bottom => observed_write_u8(buf, 8)?,
    }

    Ok(())
}

pub(super) fn observed_write_producer<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    producer: &Producer,
) -> R {
    buf.poll()?;
    match producer {
        Producer::TRust => observed_write_u8(buf, 0)?,
        Producer::Clean => observed_write_u8(buf, 1)?,
        Producer::TrustIr => observed_write_u8(buf, 2)?,
        Producer::TSwift => observed_write_u8(buf, 3)?,
        Producer::TC => observed_write_u8(buf, 4)?,
        Producer::Other(s) => {
            observed_write_u8(buf, 5)?;
            observed_write_str(buf, pool, s)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_projected_value_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    canonical: Option<Canonical<'_>>,
    id: ValueId,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    let id = match canonical {
        Some(plan) => plan.map_value(id, buf)?,
        None => id,
    };
    observed_write_value_id(buf, id)?;

    Ok(())
}

pub(super) fn observed_write_proof_annotation<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    _pool: &SealedPool,
    ann: &ProofAnnotation,
) -> R {
    buf.poll()?;
    match ann {
        ProofAnnotation::InBounds => observed_write_u8(buf, 0)?,
        ProofAnnotation::NotNull => observed_write_u8(buf, 1)?,
        ProofAnnotation::ValidBorrow => observed_write_u8(buf, 2)?,
        ProofAnnotation::UniqueBorrow => observed_write_u8(buf, 3)?,
        ProofAnnotation::SharedBorrow => observed_write_u8(buf, 4)?,
        ProofAnnotation::ValidDealloc => observed_write_u8(buf, 5)?,
        ProofAnnotation::NoOverflow => observed_write_u8(buf, 6)?,
        ProofAnnotation::NoWrap => observed_write_u8(buf, 7)?,
        ProofAnnotation::DivNonZero => observed_write_u8(buf, 8)?,
        ProofAnnotation::ShiftInRange => observed_write_u8(buf, 9)?,
        ProofAnnotation::Pure => observed_write_u8(buf, 10)?,
        ProofAnnotation::Terminates => observed_write_u8(buf, 11)?,
        ProofAnnotation::Deterministic => observed_write_u8(buf, 12)?,
        ProofAnnotation::Associative => observed_write_u8(buf, 13)?,
        ProofAnnotation::Commutative => observed_write_u8(buf, 14)?,
        ProofAnnotation::DataRaceFree => observed_write_u8(buf, 15)?,
        ProofAnnotation::AtomicOrdering(ord) => {
            observed_write_u8(buf, 16)?;
            observed_write_ordering(buf, ord)?;
        }
        ProofAnnotation::BoundedOutput { lo, hi } => {
            observed_write_u8(buf, 17)?;
            observed_write_f64(buf, *lo)?;
            observed_write_f64(buf, *hi)?;
        }
        ProofAnnotation::Monotonic => observed_write_u8(buf, 18)?,
        ProofAnnotation::NoAlias => observed_write_u8(buf, 19)?,
        ProofAnnotation::Aligned(n) => {
            observed_write_u8(buf, 20)?;
            observed_write_u64(buf, *n)?;
        }
        ProofAnnotation::NoPanic => observed_write_u8(buf, 21)?,
        ProofAnnotation::NoUndef => observed_write_u8(buf, 22)?,
        ProofAnnotation::Tainted => observed_write_u8(buf, 35)?,
        ProofAnnotation::TrustedSink => observed_write_u8(buf, 36)?,
        ProofAnnotation::FreshSymbolicHavoc => observed_write_u8(buf, 37)?,
        ProofAnnotation::RegionHavocStore => observed_write_u8(buf, 38)?,
        ProofAnnotation::Custom(tag) => {
            observed_write_u8(buf, 23)?;
            observed_write_v32(buf, tag.0)?;
        }
        ProofAnnotation::ReadonlyTable => observed_write_u8(buf, 24)?,
        ProofAnnotation::AppendOnlyBuffer => observed_write_u8(buf, 25)?,
        ProofAnnotation::AtomicSetInsert => observed_write_u8(buf, 26)?,
        ProofAnnotation::ParallelMap => observed_write_u8(buf, 27)?,
        ProofAnnotation::BoundedLoop(n) => {
            observed_write_u8(buf, 28)?;
            observed_write_u64(buf, *n)?;
        }
        ProofAnnotation::DivergenceClass(d) => {
            observed_write_u8(buf, 29)?;
            observed_write_divergence(buf, d)?;
        }
        ProofAnnotation::ProofRef(id) => {
            observed_write_u8(buf, 30)?;
            observed_write_proof_id(buf, *id)?;
        }
        ProofAnnotation::ValueRange { lo, hi } => {
            observed_write_u8(buf, 31)?;
            observed_write_i128(buf, *lo)?;
            observed_write_i128(buf, *hi)?;
        }
        ProofAnnotation::KnownBits { zeros, ones } => {
            observed_write_u8(buf, 32)?;
            observed_write_u128(buf, *zeros)?;
            observed_write_u128(buf, *ones)?;
        }
        ProofAnnotation::Wrapping => observed_write_u8(buf, 33)?,
        ProofAnnotation::BranchWeights(weights) => {
            observed_write_u8(buf, 34)?;
            observed_write_count(buf, "ProofAnnotation::BranchWeights weights", weights.len())?;
            for w in weights {
                buf.poll()?;
                observed_write_v32(buf, *w)?;
            }
        }
        // Filtered out by `observed_write_proof_annotation_list` before reaching here:
        // the fusion obligation is not part of the stable binary wire format.
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(_) => return Err(ObservedValueError::UnsupportedValue),
    }

    Ok(())
}

pub(super) fn observed_write_proof_certificate<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    cert: &ProofCertificate,
) -> R {
    buf.poll()?;
    observed_write_proof_id(buf, cert.obligation)?;
    observed_write_str(buf, pool, &cert.prover)?;
    observed_write_proof_evidence(buf, pool, &cert.evidence)?;
    // v41: coverage assurance projected from the evidence bundle.
    if contract_surface(pool) {
        match &cert.assurance {
            None => observed_write_u8(buf, 0)?,
            Some(assurance) => {
                observed_write_u8(buf, 1)?;
                match assurance.bound {
                    CoverageBound::Unbounded => observed_write_u8(buf, 0)?,
                    CoverageBound::UnwindBounded { depth } => {
                        observed_write_u8(buf, 1)?;
                        observed_write_u64(buf, depth)?;
                    }
                    CoverageBound::ModelBounded { size } => {
                        observed_write_u8(buf, 2)?;
                        observed_write_u64(buf, size)?;
                    }
                    CoverageBound::Unrecorded => observed_write_u8(buf, 3)?,
                }
                observed_write_proof_digest(buf, &assurance.request_digest)?;
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_proof_digest<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    digest: &ProofDigest,
) -> R {
    buf.poll()?;
    match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => observed_write_u8(buf, 0)?,
        ProofDigestAlgorithm::TrustIrStableV1 => observed_write_u8(buf, 1)?,
    }
    buf.extend_from_slice(&digest.bytes)?;

    Ok(())
}
