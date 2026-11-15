// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The actual legacy collection order, with fallible inner traversal.

use super::*;

pub(super) fn observed_collect_evidence_strings<O: ExecutionObserver>(
    ev: &ProofEvidence,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    match ev {
        ProofEvidence::LeanProof(s) | ProofEvidence::KaniHarness(s) | ProofEvidence::Trusted(s) => {
            pool.intern(s, out)?;
        }
        ProofEvidence::TranslationValidation { rule_name, .. } => {
            pool.intern(rule_name, out)?;
        }
        ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } => {
            pool.intern(&recheck.module, out)?;
            for thm in &recheck.theorems {
                out.poll()?;
                pool.intern(thm, out)?;
            }
            pool.intern(&recheck.anchor, out)?;
            for ax in &recheck.allowed_axioms {
                out.poll()?;
                pool.intern(ax, out)?;
            }
            // v61: a certificate binding selects the version that carries it,
            // for THIS module only.
            if let Some(binding) = recheck.binding.as_deref() {
                pool.raise_to(CERTIFICATE_BINDING_FORMAT_VERSION);
                if let Some(source) = &binding.source {
                    pool.intern(&source.decl, out)?;
                }
                for callee in &binding.callees {
                    out.poll()?;
                    pool.intern(callee, out)?;
                }
            }
        }
        _ => {}
    }

    Ok(())
}

pub(super) fn observed_collect_function_strings<O: ExecutionObserver>(
    function: &FunctionG<NoExt>,
    name: &str,
    canonical: Option<Canonical<'_>>,
    retain_source_provenance: bool,
    include_codegen_license: bool,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    out.poll()?;
    pool.intern(name, out)?;
    // v41 function-level contract surface. When the projection omits the
    // codegen license, neither `body_gate` nor `display_path` may raise the
    // version or pool a string; `write_function` is handed the same flag and
    // makes the same choice. The sealed table catches ONE direction of a
    // disagreement: if the writer spells a license string this walk skipped,
    // `id_of` panics by name. It does not catch the other direction at all —
    // a raise or an intern HERE that the writer does not match still emits a
    // v41 header and shifts every later string id, with nothing for the
    // sealed pool to object to. What pins that direction is a test:
    // `executable_content_projection_strips_the_codegen_license` asserts the
    // license-only image is byte-identical to the same module unlicensed and
    // that its header is `BASE_FORMAT_VERSION`. MEASURED 2026-09-20 —
    // forcing `licensed = true` here, writer untouched, compiles silently and
    // fails that assertion (`left: 41, right: 38`), nothing else.
    let licensed = include_codegen_license
        && (function.body_gate.is_some() || function.display_path.is_some());
    if licensed
        || function.attrs.naked
        || !function.attrs.target_features.is_empty()
        || function.linkage.requires_contract_surface()
    {
        observed_raise_to_contract_surface(pool, out)?;
    }
    if include_codegen_license {
        if let Some(crate::BodyGate::Gated {
            authority,
            evidence,
        }) = &function.body_gate
        {
            pool.intern(authority, out)?;
            // v61: an evidenced license is tag 3, carried by the
            // proof-surface version, for THIS module only.
            if evidence.is_some() {
                pool.raise_to(CERTIFICATE_BINDING_FORMAT_VERSION);
            }
        }
        if let Some(path) = &function.display_path {
            pool.intern(path, out)?;
        }
    }
    for feature in &function.attrs.target_features {
        out.poll()?;
        pool.intern(feature, out)?;
    }
    // v45 (WS3.10): function symbol attributes. Written on EVERY projection —
    // they are facts about the executable image, not a verdict about it.
    if function.has_symbol_attributes()
        || function.calling_conv.is_abi_surface()
        || uses_abi_surface_observed(&function.attrs, out)?
    {
        observed_raise_to_abi_surface(pool, out)?;
    }
    // v45 (WS3.11): a `PassMode::Cast` names lane types, which pool their
    // identity strings exactly like any other type.
    for slot in function.attrs.params.iter().chain([&function.attrs.ret]) {
        out.poll()?;
        if let Some(crate::PassMode::Cast { pieces }) = &slot.pass {
            for piece in pieces {
                out.poll()?;
                observed_collect_type_strings(piece, pool, out)?;
            }
        }
    }
    if let Some(section) = &function.section {
        pool.intern(section, out)?;
    }
    if let Some(canonical) = canonical {
        for &block_index in canonical.block_order(out)? {
            out.poll()?;
            let block = &function.blocks[block_index];
            for (_, ty) in &block.params {
                out.poll()?;
                observed_collect_type_strings(ty, pool, out)?;
            }
            for node in &block.body {
                out.poll()?;
                observed_collect_inst_strings(&node.inst, pool, out)?;
            }
        }
    } else {
        for block in &function.blocks {
            out.poll()?;
            for (_, ty) in &block.params {
                out.poll()?;
                observed_collect_type_strings(ty, pool, out)?;
            }
            for node in &block.body {
                out.poll()?;
                observed_collect_inst_strings(&node.inst, pool, out)?;
            }
        }
    }
    if let Some(summary) = &function.summary {
        for clause in summary
            .requires
            .iter()
            .chain(summary.ensures.iter())
            .chain(summary.decreases.iter())
        {
            out.poll()?;
            observed_collect_proof_formula_strings(clause, pool, out)?;
        }
        for parameter in &summary.params {
            out.poll()?;
            pool.intern(parameter, out)?;
        }
        if !summary.decreases.is_empty() || summary.backed_by.is_some() {
            observed_raise_to_contract_surface(pool, out)?;
        }
        if let Some(reference) = &summary.backed_by {
            pool.intern(&reference.symbol, out)?;
        }
        // v59: an effect summary pools no string; it only selects the version
        // that can spell it.
        if summary.effects.is_some() {
            pool.raise_to(EFFECT_SUMMARY_FORMAT_VERSION);
        }
    }
    if let Some(names) = &function.value_names {
        for (_, name) in names {
            out.poll()?;
            pool.intern(name, out)?;
        }
    }
    let source_provenance = out.provenance(function, canonical, retain_source_provenance)?;
    if let Some(provenance) = source_provenance {
        for source_loop in &provenance.loops {
            out.poll()?;
            for binding in &source_loop.bindings {
                out.poll()?;
                pool.intern(&binding.name, out)?;
            }
        }
    }
    if let Some(Producer::Other(producer)) = &function.producer {
        pool.intern(producer, out)?;
    }

    Ok(())
}

pub(super) fn observed_collect_obligation_kind_strings<O: ExecutionObserver>(
    kind: &ObligationKind,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    match kind {
        ObligationKind::Termination | ObligationKind::Ownership => {
            observed_raise_to_contract_surface(pool, out)?
        }
        ObligationKind::Custom { namespace, name } => {
            observed_raise_to_contract_surface(pool, out)?;
            pool.intern(namespace, out)?;
            pool.intern(name, out)?;
        }
        _ => {}
    }

    Ok(())
}

pub(super) fn observed_collect_proof_formula_strings<O: ExecutionObserver>(
    formula: &ProofFormula,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    pool.intern(&formula.schema, out)?;
    pool.intern(&formula.payload, out)?;
    if let Some(smtlib) = &formula.smtlib {
        pool.intern(smtlib, out)?;
    }
    if let Some(sort) = &formula.sort {
        pool.intern(sort, out)?;
    }
    if !formula.bindings.is_empty() {
        observed_raise_to_contract_surface(pool, out)?;
        for (name, binding) in &formula.bindings {
            out.poll()?;
            pool.intern(name, out)?;
            observed_collect_clause_sort_strings(&binding.sort, pool, out)?;
            // v46: the spec-variable places have no encoding before v46, so a
            // formula that uses one selects the version wherever it is carried.
            if matches!(
                binding.place,
                ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. }
            ) {
                pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            }
            // v59: the world epochs likewise have no encoding before v59.
            if matches!(
                binding.place,
                ClausePlace::WorldPre | ClausePlace::WorldPost
            ) {
                pool.raise_to(EFFECT_SUMMARY_FORMAT_VERSION);
            }
            // v62: likewise the entry-state pointee place (roadmap DG-63).
            if matches!(binding.place, ClausePlace::ParamPointeeEntry { .. }) {
                pool.raise_to(PARAM_POINTEE_PLACE_FORMAT_VERSION);
            }
        }
    }

    Ok(())
}

pub(super) fn observed_collect_proof_obligation_strings<O: ExecutionObserver>(
    obligation: &ProofObligation,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    pool.intern(&obligation.description, out)?;
    observed_collect_obligation_kind_strings(&obligation.kind, pool, out)?;
    if let Some(formula) = &obligation.formula {
        observed_collect_proof_formula_strings(formula, pool, out)?;
    }
    if let Some(source) = &obligation.source {
        pool.intern(&source.source_id, out)?;
        pool.intern(&source.assertion_id, out)?;
        if let Some(public) = &source.public {
            pool.intern(&public.obligation_id, out)?;
        }
    }
    if let Some(spec) = &obligation.spec {
        pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
        pool.intern(&spec.machine, out)?;
        pool.intern(&spec.temporal, out)?;
    }

    Ok(())
}

pub(super) fn observed_collect_spec_module_strings<O: ExecutionObserver>(
    sm: &crate::spec::SpecModule,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    pool.intern(&sm.name, out)?;
    for v in &sm.vars {
        out.poll()?;
        pool.intern(&v.name, out)?;
        pool.intern(&v.ty, out)?;
        if let Some(sort) = &v.sort {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            observed_collect_clause_sort_strings(sort, pool, out)?;
        }
    }
    for a in &sm.actions {
        out.poll()?;
        pool.intern(a, out)?;
    }
    for inv in &sm.invariants {
        out.poll()?;
        pool.intern(&inv.name, out)?;
        pool.intern(&inv.formula, out)?;
        if let Some(typed) = &inv.typed {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            observed_collect_proof_formula_strings(typed, pool, out)?;
        }
    }
    for anchor in &sm.anchors {
        out.poll()?;
        pool.intern(&anchor.machine, out)?;
        pool.intern(&anchor.action, out)?;
        pool.intern(&anchor.rust_symbol, out)?;
        pool.intern(&anchor.span, out)?;
        if let Some(p) = &anchor.project {
            pool.intern(p, out)?;
        }
    }
    for w in &sm.waivers {
        out.poll()?;
        pool.intern(&w.machine, out)?;
        pool.intern(&w.action, out)?;
        pool.intern(&w.reason, out)?;
    }
    for p in &sm.proofs {
        out.poll()?;
        pool.intern(&p.machine, out)?;
        pool.intern(&p.action, out)?;
        pool.intern(&p.proof_name, out)?;
        if let crate::spec::ProofKind::CleanTheorem { name } = &p.kind {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            pool.intern(name, out)?;
        }
    }
    if !sm.temporal.is_empty() {
        pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
    }
    for property in &sm.temporal {
        out.poll()?;
        pool.intern(&property.name, out)?;
        if let Some(action) = property.form.action() {
            pool.intern(action, out)?;
        }
        for (formula, _) in property.form.formulas_iter() {
            out.poll()?;
            observed_collect_proof_formula_strings(formula, pool, out)?;
        }
    }
    if let crate::spec::SpecOrigin::External(path) = &sm.origin {
        pool.intern(path, out)?;
    }

    Ok(())
}
