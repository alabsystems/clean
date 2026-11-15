// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_proof_evidence<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ev: &ProofEvidence,
) -> R {
    buf.poll()?;
    match ev {
        ProofEvidence::SmtProof(data) => {
            observed_write_u8(buf, 0)?;
            observed_write_bytes(buf, data)?;
        }
        ProofEvidence::LeanProof(s) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, s)?;
        }
        ProofEvidence::KaniHarness(s) => {
            observed_write_u8(buf, 2)?;
            observed_write_str(buf, pool, s)?;
        }
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => {
            observed_write_u8(buf, 3)?;
            observed_write_f64(buf, *epsilon)?;
            observed_write_v32(buf, *verified_layers)?;
        }
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            observed_write_u8(buf, 4)?;
            observed_write_str(buf, pool, rule_name)?;
            buf.extend_from_slice(smt_hash)?;
        }
        ProofEvidence::Trusted(s) => {
            observed_write_u8(buf, 5)?;
            observed_write_str(buf, pool, s)?;
        }
        // Module-local inheritance keeps tag 6 and its exact two-varint payload.
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external: None,
        } => {
            observed_write_u8(buf, 6)?;
            observed_write_v32(buf, callee.index())?;
            observed_write_v32(buf, obligation.index())?;
        }
        // v41 cross-crate inheritance takes a NEW tag, so an older reader
        // refuses it (`InvalidTag(8)`) instead of reading it as local.
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external: Some(reference),
        } => {
            observed_write_u8(buf, 8)?;
            observed_write_v32(buf, callee.index())?;
            observed_write_v32(buf, obligation.index())?;
            observed_write_extern_ref(buf, pool, reference)?;
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck,
        } => {
            observed_write_u8(buf, 7)?;
            observed_write_bytes(buf, term)?;
            observed_write_bytes(buf, context)?;
            observed_write_proof_digest(buf, lineage)?;
            match kernel_recheck {
                None => observed_write_u8(buf, 0)?,
                Some(recheck) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_str(buf, pool, &recheck.module)?;
                    observed_write_count(
                        buf,
                        "CleanCicKernelRecheck.theorems",
                        recheck.theorems.len(),
                    )?;
                    for thm in &recheck.theorems {
                        buf.poll()?;
                        observed_write_str(buf, pool, thm)?;
                    }
                    observed_write_str(buf, pool, &recheck.anchor)?;
                    observed_write_count(
                        buf,
                        "CleanCicKernelRecheck.allowed_axioms",
                        recheck.allowed_axioms.len(),
                    )?;
                    for ax in &recheck.allowed_axioms {
                        buf.poll()?;
                        observed_write_str(buf, pool, ax)?;
                    }
                    // v61+: the certificate binding (WS1.12a), a presence
                    // byte after the directive. A binding raises its module
                    // to v61 during collection, so below v61 there is none to
                    // write — never one narrowed to `None`.
                    if pool.minimum_version() >= CERTIFICATE_BINDING_FORMAT_VERSION {
                        match recheck.binding.as_deref() {
                            None => observed_write_u8(buf, 0)?,
                            Some(binding) => {
                                observed_write_u8(buf, 1)?;
                                observed_write_certificate_binding(buf, pool, binding)?;
                            }
                        }
                    } else {
                        if recheck.binding.is_some() {
                            return Err(ObservedValueError::UnsupportedValue);
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_proof_formula<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    f: &ProofFormula,
) -> R {
    buf.poll()?;
    observed_write_proof_formula_in(buf, pool, f, None)?;

    Ok(())
}

pub(super) fn observed_write_proof_formula_in<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    f: &ProofFormula,
    canonical: Option<Canonical<'_>>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_str(buf, pool, &f.schema)?;
    observed_write_str(buf, pool, &f.payload)?;
    observed_write_opt_str(buf, pool, f.smtlib.as_deref())?;
    observed_write_opt_str(buf, pool, f.sort.as_deref())?;
    if contract_surface(pool) {
        // An empty vector is the legacy shape and reads as UNBINDABLE.
        observed_write_count(buf, "ProofFormula.bindings", f.bindings.len())?;
        for (name, binding) in &f.bindings {
            buf.poll()?;
            observed_write_str(buf, pool, name)?;
            observed_write_clause_sort(buf, pool, &binding.sort)?;
            match (&binding.place, canonical) {
                (ClausePlace::Value(value), Some(plan)) => {
                    let mapped = plan.map_binding_value(*value, buf)?;
                    observed_write_clause_place(buf, &ClausePlace::Value(mapped))?;
                }
                (place, _) => observed_write_clause_place(buf, place)?,
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_proof_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: ProofId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_proof_obligation<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    po: &ProofObligation,
    canonical: Option<Canonical<'_>>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_proof_id(buf, po.id)?;
    observed_write_obligation_kind(buf, pool, &po.kind)?;
    observed_write_proof_status(buf, &po.status)?;
    observed_write_str(buf, pool, &po.description)?;
    match &po.formula {
        None => observed_write_u8(buf, 0)?,
        Some(formula) => {
            observed_write_u8(buf, 1)?;
            // ONE formula encoder. This used to be an inline duplicate of
            // `observed_write_proof_formula`, kept in lockstep by comment; it silently
            // dropped v41 `bindings` the moment the shared encoder grew them.
            // `canonical` is the owning function's plan (WS4.4, NEW-1).
            observed_write_proof_formula_in(buf, pool, formula, canonical)?;
        }
    }
    // v5+: owning-function scope (B4)
    match &po.function {
        None => observed_write_u8(buf, 0)?,
        Some(f) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, f.index())?;
        }
    }
    // v28+: embedded source/public identity. The nested option keeps the
    // public identifier and semantic digest atomic on the wire.
    match &po.source {
        None => observed_write_u8(buf, 0)?,
        Some(source) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, &source.source_id)?;
            observed_write_str(buf, pool, &source.assertion_id)?;
            match &source.range {
                None => observed_write_u8(buf, 0)?,
                Some(range) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_v32(buf, range.file)?;
                    observed_write_v32(buf, range.start_line)?;
                    observed_write_v32(buf, range.start_col)?;
                    observed_write_v32(buf, range.end_line)?;
                    observed_write_v32(buf, range.end_col)?;
                }
            }
            match &source.public {
                None => observed_write_u8(buf, 0)?,
                Some(public) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_str(buf, pool, &public.obligation_id)?;
                    observed_write_proof_digest(buf, &public.semantic_digest)?;
                }
            }
        }
    }
    // v34+: IR-position backref (the obligation<->VC-condition binding).
    match &po.site {
        None => observed_write_u8(buf, 0)?,
        Some(site) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, site.function.index())?;
            observed_write_v32(buf, site.block.index())?;
            observed_write_v32(buf, site.inst_index)?;
        }
    }
    // v46+: the named temporal property this obligation discharges.
    if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
        match &po.spec {
            None => observed_write_u8(buf, 0)?,
            Some(spec) => {
                observed_write_u8(buf, 1)?;
                observed_write_str(buf, pool, &spec.machine)?;
                observed_write_str(buf, pool, &spec.temporal)?;
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_proof_status<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &ProofStatus,
) -> R {
    buf.poll()?;
    let tag = match value {
        ProofStatus::Pending => 0,
        ProofStatus::Discharged => 1,
        ProofStatus::Failed => 2,
        ProofStatus::Trusted => 3,
        ProofStatus::Certified => 4,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_proofs<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    proofs: &[crate::spec::SpecProof],
) -> R {
    buf.poll()?;
    use crate::spec::ProofKind;
    observed_write_count(buf, "SpecModule.proofs", proofs.len())?;
    for p in proofs {
        buf.poll()?;
        observed_write_str(buf, pool, &p.machine)?;
        observed_write_str(buf, pool, &p.action)?;
        observed_write_str(buf, pool, &p.proof_name)?;
        match &p.kind {
            ProofKind::Kani => observed_write_u8(buf, 0)?,
            // v46. Selection is driven by the string collector, which raises
            // the collected minimum version when a `CleanTheorem` binding occurs.
            ProofKind::CleanTheorem { name } => {
                observed_write_u8(buf, 1)?;
                observed_write_str(buf, pool, name)?;
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_raw_str<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    s: &str,
) -> R {
    buf.poll()?;
    observed_write_count(buf, "string length", s.len())?;
    buf.extend_from_slice(s.as_bytes())?;

    Ok(())
}

pub(super) fn observed_write_record_def<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    rd: &RecordDef,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, rd.id.0)?;
    observed_write_str(buf, pool, &rd.name)?;
    observed_write_count(buf, "RecordDef.fields", rd.fields.len())?;
    for f in &rd.fields {
        buf.poll()?;
        observed_write_field_def(buf, pool, f)?;
    }

    Ok(())
}

pub(super) fn observed_write_record_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: RecordId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_set_repr<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    repr: &SetRepr,
) -> R {
    buf.poll()?;
    let tag: u8 = match repr {
        SetRepr::Bitset => 0,
        SetRepr::Boxed => 1,
    };
    observed_write_u8(buf, tag)?;

    Ok(())
}

pub(super) fn observed_write_sited_assert_payload<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    canonical: Option<Canonical<'_>>,
    cond: ValueId,
    kind: &AssertKind,
    site: &PanicSite,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_projected_value_id(buf, canonical, cond)?;
    if kind.is_unspecified() {
        observed_write_u8(buf, 0)?;
    } else {
        observed_write_u8(buf, 1)?;
        observed_write_assert_kind(buf, canonical, kind)?;
    }
    observed_write_func_id(buf, site.entry)?;
    observed_write_panic_location(buf, canonical, &site.location)?;

    Ok(())
}

pub(super) fn observed_write_space<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    space: crate::pred::Space,
) -> R {
    buf.poll()?;
    observed_write_u8(
        buf,
        match space {
            crate::pred::Space::Index => 0,
            crate::pred::Space::Member => 1,
        },
    )?;

    Ok(())
}
