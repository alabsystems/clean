// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_function<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    func: &FunctionG<NoExt>,
    name: Option<&str>,
    canonical: Option<Canonical<'_>>,
    retain_source_provenance: bool,
    include_codegen_license: bool,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_func_id(buf, func.id)?;
    observed_write_str(buf, pool, name.unwrap_or(&func.name))?;
    observed_write_func_ty_id(buf, func.ty)?;
    observed_write_block_id(buf, func.entry)?;
    observed_write_count(buf, "Function.blocks", func.blocks.len())?;
    if let Some(canonical) = canonical {
        for &block_index in canonical.block_order(buf)? {
            buf.poll()?;
            observed_write_block(
                buf,
                pool,
                Some(canonical),
                func.id,
                &func.blocks[block_index],
            )?;
        }
    } else {
        for block in &func.blocks {
            buf.poll()?;
            observed_write_block(buf, pool, None, func.id, block)?;
        }
    }
    observed_write_proof_annotation_list(buf, pool, &func.proofs)?;
    observed_write_calling_conv(buf, &func.calling_conv)?;
    observed_write_linkage(buf, &func.linkage)?;
    let attrs_len = match canonical {
        Some(plan) => Some(plan.param_attrs_len(buf)?),
        None => None,
    };
    observed_write_func_attrs(buf, pool, &func.attrs, attrs_len)?;
    // v18+: separate-compilation contract. Presence byte then payload, so a
    // body-less declaration carrying a summary round-trips.
    match &func.summary {
        None => observed_write_u8(buf, 0)?,
        Some(summary) => {
            observed_write_u8(buf, 1)?;
            observed_write_function_summary(buf, pool, summary, canonical)?;
        }
    }
    // v23+: producer provenance. Presence byte then the stable producer tag.
    match &func.producer {
        None => observed_write_u8(buf, 0)?,
        Some(producer) => {
            observed_write_u8(buf, 1)?;
            observed_write_producer(buf, pool, producer)?;
        }
    }
    // v32+: debug value names (C2-names). Presence byte, then (ValueId, name) pairs.
    match &func.value_names {
        None => observed_write_u8(buf, 0)?,
        Some(names) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "Function.value_names", names.len())?;
            for (v, n) in names {
                buf.poll()?;
                observed_write_projected_value_id(buf, canonical, *v)?;
                observed_write_str(buf, pool, n)?;
            }
        }
    }
    // v33+: lexical scope tree (C2-scopes). Presence byte, then one
    // (parent, span) entry per scope. No strings, so the up-front pool needs
    // no companion entry here — the v32 trap does not repeat.
    match &func.scopes {
        None => observed_write_u8(buf, 0)?,
        Some(scopes) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "Function.scopes", scopes.len())?;
            for (index, sc) in scopes.iter().enumerate() {
                buf.poll()?;
                // WS4.19: fail closed. The chain has no carrier at any
                // version yet, and dropping it would make the round trip a
                // silent lie. Refused by this arm, at its untruncated
                // position (`Module::wire_image_refusal` is this walk).
                if sc.inlined_at.is_some() {
                    buf.refuse(|| WireRefusal::InlinedScopeChain {
                        function: func.id.index(),
                        scope: index,
                    })?;
                }
                match sc.parent {
                    None => observed_write_u8(buf, 0)?,
                    Some(p) => {
                        observed_write_u8(buf, 1)?;
                        observed_write_v32(buf, p)?;
                    }
                }
                match &sc.span {
                    None => observed_write_u8(buf, 0)?,
                    Some(span) => {
                        observed_write_u8(buf, 1)?;
                        observed_write_v32(buf, span.file)?;
                        observed_write_v32(buf, span.line)?;
                        observed_write_v32(buf, span.col)?;
                    }
                }
            }
        }
    }
    // v35+: semantic source-loop/place provenance.
    let source_provenance = buf.provenance(func, canonical, retain_source_provenance)?;
    match source_provenance {
        None => observed_write_u8(buf, 0)?,
        Some(provenance) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, provenance.schema)?;
            observed_write_proof_digest(buf, &provenance.compiler_source_digest)?;
            observed_write_proof_digest(buf, &provenance.semantic_body_digest)?;
            observed_write_proof_digest(buf, &provenance.binding_digest)?;
            observed_write_count(buf, "SourceProvenance.loops", provenance.loops.len())?;
            for source_loop in &provenance.loops {
                buf.poll()?;
                observed_write_v32(buf, source_loop.source_loop_id)?;
                observed_write_v32(buf, source_loop.hir_local_id)?;
                observed_write_block_id(buf, source_loop.header)?;
                observed_write_count(
                    buf,
                    "SourceLoopProvenance.bindings",
                    source_loop.bindings.len(),
                )?;
                for binding in &source_loop.bindings {
                    buf.poll()?;
                    observed_write_str(buf, pool, &binding.name)?;
                    observed_write_v32(buf, binding.hir_local_id)?;
                    match binding.place {
                        SourcePlace::FunctionParameter { index } => {
                            observed_write_u8(buf, 0)?;
                            observed_write_v32(buf, index)?;
                        }
                        SourcePlace::LoopParameter { index } => {
                            observed_write_u8(buf, 1)?;
                            observed_write_v32(buf, index)?;
                        }
                    }
                }
            }
        }
    }
    // v41: codegen license, then the display path. A projection that omits
    // the license still has to spell it once some OTHER v41 feature holds the
    // image at v41: tag 0 ("no licensing claim") and an absent path, so the
    // image decodes as an unlicensed module and, matching the collector, no
    // authority or path string is looked up in the pool.
    if contract_surface(pool) {
        if include_codegen_license {
            observed_write_body_gate(buf, pool, func.body_gate.as_ref())?;
            match &func.display_path {
                None => observed_write_u8(buf, 0)?,
                Some(path) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_str(buf, pool, path)?;
                }
            }
        } else {
            observed_write_body_gate(buf, pool, None)?;
            observed_write_u8(buf, 0)?;
        }
    }
    // v45 (WS3.10): section, visibility, retention — `Global`'s v41 triple.
    if abi_surface(pool) {
        observed_write_opt_str(buf, pool, func.section.as_deref())?;
        observed_write_visibility(buf, &func.visibility)?;
        observed_write_bool(buf, func.retained)?;
    }

    Ok(())
}

pub(super) fn observed_write_function_summary<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    s: &FunctionSummary,
    canonical: Option<Canonical<'_>>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_count(buf, "FunctionSummary.requires", s.requires.len())?;
    for c in &s.requires {
        buf.poll()?;
        observed_write_proof_formula_in(buf, pool, c, canonical)?;
    }
    observed_write_count(buf, "FunctionSummary.ensures", s.ensures.len())?;
    for c in &s.ensures {
        buf.poll()?;
        observed_write_proof_formula_in(buf, pool, c, canonical)?;
    }
    observed_write_count(buf, "FunctionSummary.params", s.params.len())?;
    for p in &s.params {
        buf.poll()?;
        observed_write_str(buf, pool, p)?;
    }
    observed_write_u8(buf, u8::from(s.proved))?;
    // v41: termination measures, then the cross-crate backing of `proved`.
    if contract_surface(pool) {
        observed_write_count(buf, "FunctionSummary.decreases", s.decreases.len())?;
        for c in &s.decreases {
            buf.poll()?;
            observed_write_proof_formula_in(buf, pool, c, canonical)?;
        }
        match &s.backed_by {
            None => observed_write_u8(buf, 0)?,
            Some(reference) => {
                observed_write_u8(buf, 1)?;
                observed_write_extern_ref(buf, pool, reference)?;
            }
        }
    }
    // v59: the effect summary, presence-tagged. Written on EVERY summary once
    // the module is at v59, so `None` (UNRECORDED) stays spellable.
    if pool.minimum_version() >= EFFECT_SUMMARY_FORMAT_VERSION {
        match &s.effects {
            None => observed_write_u8(buf, 0)?,
            Some(effects) => {
                observed_write_u8(buf, 1)?;
                observed_write_effect_summary(buf, effects)?;
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_global<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    g: &GlobalG<NoExt>,
    name: Option<&str>,
) -> R {
    buf.poll()?;
    observed_write_str(buf, pool, name.unwrap_or(&g.name))?;
    observed_write_ty(buf, pool, &g.ty)?;
    observed_write_bool(buf, g.mutable)?;
    match &g.initializer {
        None => observed_write_u8(buf, 0)?,
        Some(c) => {
            observed_write_u8(buf, 1)?;
            observed_write_constant(buf, pool, c)?;
        }
    }
    observed_write_linkage(buf, &g.linkage)?;
    match g.tls {
        None => observed_write_u8(buf, 0)?,
        Some(tls) => {
            observed_write_u8(buf, 1)?;
            observed_write_tls_model(buf, &tls)?;
        }
    }
    // v26: declared storage alignment (presence byte + v32).
    match g.align {
        None => observed_write_u8(buf, 0)?,
        Some(align) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, align)?;
        }
    }
    // v41: section, visibility, retention.
    if contract_surface(pool) {
        observed_write_opt_str(buf, pool, g.section.as_deref())?;
        observed_write_visibility(buf, &g.visibility)?;
        observed_write_bool(buf, g.retained)?;
    }

    Ok(())
}

pub(super) fn observed_write_i128<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: i128) -> R {
    buf.poll()?;
    buf.extend_from_slice(&v.to_le_bytes())?;

    Ok(())
}

pub(super) fn observed_write_icmp_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &ICmpOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        ICmpOp::Eq => 0,
        ICmpOp::Ne => 1,
        ICmpOp::Ult => 2,
        ICmpOp::Ule => 3,
        ICmpOp::Ugt => 4,
        ICmpOp::Uge => 5,
        ICmpOp::Slt => 6,
        ICmpOp::Sle => 7,
        ICmpOp::Sgt => 8,
        ICmpOp::Sge => 9,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_identity_scheme<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    scheme: IdentityScheme,
) -> R {
    buf.poll()?;
    observed_write_u8(
        buf,
        match scheme {
            IdentityScheme::V2 => 0,
            IdentityScheme::V3 => 1,
        },
    )?;

    Ok(())
}
