// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The actual legacy collection order, with fallible inner traversal.

use super::*;

pub(super) fn observed_collect_strings_into<O: ExecutionObserver>(
    module: &ModuleG<NoExt>,
    view: Option<&ModuleWireView>,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    if view.is_some() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    out.poll()?;
    if !module.closure_layouts.is_empty() {
        pool.raise_to(NOMINAL_IDENTITY_FORMAT_VERSION);
        for descriptor in &module.closure_layouts {
            out.poll()?;
            if descriptor.origin.is_some() {
                pool.raise_to(CLOSURE_ORIGIN_FORMAT_VERSION);
                observed_collect_type_origin_strings(descriptor.origin.as_ref(), pool, out)?;
            }
        }
    }
    if !module.tuple_layouts.is_empty() {
        pool.raise_to(TUPLE_LAYOUT_FORMAT_VERSION);
    }
    // v55 (amendment D): a module with a drop-glue row writes the trailing
    // section; each key is an inline type whose strings the sealed pool must
    // hold (and which may itself raise the header, e.g. a handle key).
    if !module.drop_glue.is_empty() {
        pool.raise_to(DROP_GLUE_FORMAT_VERSION);
        for entry in &module.drop_glue {
            out.poll()?;
            observed_collect_type_identity_strings(&entry.ty, pool, out)?;
        }
    }
    // v70 (PKG-U13e): a module with a blob table row writes the trailing
    // blob section. A row holds no interned string.
    if !module.blobs.is_empty() {
        pool.raise_to(TENSOR_BLOB_FORMAT_VERSION);
    }
    // The v30 universe / predicate tables carry constants too (scalar-only
    // when well-formed). Walk them like every other constant carrier, so a
    // gated constant tag (v49 `Uninit`, v50 `Splat`) can never be written under a header
    // that refuses it, even for a module the validator would reject.
    for universe in &module.universes {
        out.poll()?;
        if let crate::pred::Universe::Members(items) = universe {
            for item in items {
                out.poll()?;
                observed_collect_constant_strings(item, pool, out)?;
            }
        }
    }
    for pred in &module.predicates {
        out.poll()?;
        if let crate::pred::Pred::FiniteSet(items) = pred {
            for item in items {
                out.poll()?;
                observed_collect_constant_strings(item, pool, out)?;
            }
        }
    }
    let include_proof_sidecars = view.is_none_or(ModuleWireView::includes_proof_sidecars);
    pool.intern(
        view.map_or(&module.name, |view| view.module_name(module)),
        out,
    )?;
    for ty in &module.types {
        out.poll()?;
        observed_collect_type_strings(ty, pool, out)?;
    }
    for signature in &module.func_types {
        out.poll()?;
        if signature.abi.is_some() {
            pool.raise_to(SIGNATURE_ABI_FORMAT_VERSION);
        }
        for ty in signature.params.iter().chain(&signature.returns) {
            out.poll()?;
            observed_collect_type_strings(ty, pool, out)?;
        }
    }
    for closure in &module.closure_types {
        out.poll()?;
        for ty in &closure.captures {
            out.poll()?;
            observed_collect_type_strings(ty, pool, out)?;
        }
    }

    if let Some(ti) = &module.target_info {
        pool.intern(&ti.triple, out)?;
        // Stable ABI identifier (VERSION >= 20).
        if let Some(abi) = &ti.abi {
            pool.intern(abi, out)?;
        }
    }

    // Debug-info source-file table paths (VERSION >= 9). Under the v3
    // identity projection each path is spelled `""` (length kept).
    for path in &module.files {
        out.poll()?;
        let spelled = pool.debug_file(path);
        pool.intern(spelled, out)?;
    }

    // Obligation-diagnostic strings (VERSION >= 11).
    if include_proof_sidecars {
        for d in &module.obligation_diagnostics {
            out.poll()?;
            pool.intern(&d.message, out)?;
            if let Some(detail) = &d.detail {
                pool.intern(detail, out)?;
            }
        }
    }

    for sd in &module.structs {
        out.poll()?;
        pool.intern(&sd.name, out)?;
        for fd in &sd.fields {
            out.poll()?;
            pool.intern(&fd.name, out)?;
            observed_collect_type_strings(&fd.ty, pool, out)?;
        }
        observed_collect_type_origin_strings(sd.origin.as_ref(), pool, out)?;
    }

    for ed in &module.enums {
        out.poll()?;
        if ed.variants.is_empty()
            || ed.layout.as_ref().is_some_and(|layout| {
                matches!(layout.encoding, EnumTagEncoding::SingleInhabited { .. })
            })
        {
            pool.raise_to(SINGLE_INHABITED_ENUM_FORMAT_VERSION);
        }
        // v45 (WS3.14(b)): a 128-bit tag repr — the explicit hint or a niche
        // lane — raises the writer, so no pre-v45 blob carries tag 9 or 10.
        if ed.repr.is_some_and(EnumTagRepr::is_abi_surface)
            || matches!(
                &ed.layout,
                Some(layout) if matches!(
                    &layout.encoding,
                    crate::ty::EnumTagEncoding::Niche { niche_ty, .. }
                        if niche_ty.is_abi_surface()
                )
            )
        {
            observed_raise_to_abi_surface(pool, out)?;
        }
        pool.intern(&ed.name, out)?;
        for v in &ed.variants {
            out.poll()?;
            pool.intern(&v.name, out)?;
            for ty in &v.fields {
                out.poll()?;
                observed_collect_type_strings(ty, pool, out)?;
            }
            for name in &v.field_names {
                out.poll()?;
                pool.intern(name, out)?;
            }
        }
        observed_collect_type_origin_strings(ed.origin.as_ref(), pool, out)?;
    }

    for rd in &module.records {
        out.poll()?;
        pool.intern(&rd.name, out)?;
        for fd in &rd.fields {
            out.poll()?;
            pool.intern(&fd.name, out)?;
            observed_collect_type_strings(&fd.ty, pool, out)?;
        }
    }

    for (index, g) in module.globals.iter().enumerate() {
        out.poll()?;
        pool.intern(view.map_or(&g.name, |view| view.global_name(g, index)), out)?;
        observed_collect_type_strings(&g.ty, pool, out)?;
        if let Some(c) = &g.initializer {
            observed_collect_constant_strings(c, pool, out)?;
        }
        // v41 global ABI residue.
        if g.section.is_some()
            || g.visibility != Visibility::Default
            || g.retained
            || g.linkage.requires_contract_surface()
        {
            observed_raise_to_contract_surface(pool, out)?;
        }
        if let Some(section) = &g.section {
            pool.intern(section, out)?;
        }
    }

    if let Some(view) = view {
        for &index in &view.function_order {
            out.poll()?;
            let function = &module.functions[index];
            observed_collect_function_strings(
                function,
                view.function_name(function, index),
                view.canonical_function(index).map(Canonical::Ordinary),
                view.retain_source_provenance,
                view.includes_codegen_license(),
                pool,
                out,
            )?;
        }
    } else {
        for function in out.functions(module)? {
            out.poll()?;
            observed_collect_function_strings(
                function,
                &function.name,
                None,
                false,
                true,
                pool,
                out,
            )?;
        }
    }

    // v41 module-level sections.
    if !module.global_asm.is_empty() || !module.imports.is_empty() {
        observed_raise_to_contract_surface(pool, out)?;
    }
    for asm in &module.global_asm {
        out.poll()?;
        pool.intern(asm, out)?;
    }
    for import in &module.imports {
        out.poll()?;
        pool.intern(&import.name, out)?;
        if let Some(Producer::Other(producer)) = &import.producer {
            pool.intern(producer, out)?;
        }
        // v44: a row recorded under any scheme but the legacy V2 needs the
        // per-row scheme tag. A table of V2 rows keeps its v41..=v43 bytes.
        if !import.scheme.is_v2() {
            pool.raise_to(IMPORT_SCHEME_FORMAT_VERSION);
        }
    }

    if include_proof_sidecars {
        if let Some(view) = view {
            for &index in &view.obligation_rows {
                out.poll()?;
                observed_collect_proof_obligation_strings(
                    &module.proof_obligations[index],
                    pool,
                    out,
                )?;
            }
        } else {
            for obligation in &module.proof_obligations {
                out.poll()?;
                observed_collect_proof_obligation_strings(obligation, pool, out)?;
            }
        }

        for pc in &module.proof_certificates {
            out.poll()?;
            pool.intern(&pc.prover, out)?;
            observed_collect_evidence_strings(&pc.evidence, pool, out)?;
            if pc.assurance.is_some() {
                observed_raise_to_contract_surface(pool, out)?;
            }
            if let ProofEvidence::InheritedFromCallee {
                external: Some(reference),
                ..
            } = &pc.evidence
            {
                observed_raise_to_contract_surface(pool, out)?;
                pool.intern(&reference.symbol, out)?;
            }
        }
    }

    for sm in &module.spec_modules {
        out.poll()?;
        observed_collect_spec_module_strings(sm, pool, out)?;
    }

    Ok(())
}

pub(super) fn observed_collect_type_identity_strings<O: ExecutionObserver>(
    ty: &TyG<NoExt>,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    match ty {
        TyG::Dialect(ty) => {
            pool.raise_to(DIALECT_TYPE_FORMAT_VERSION);
            pool.intern(&ty.namespace, out)?;
            pool.intern(&ty.name, out)?;
        }
        // v40: the writer must raise the header for every feature the reader
        // gates, or it emits a self-inconsistent blob (sub-tag 4 under a v38
        // header, which `read_fat_ptr_kind` refuses with `InvalidTag(4)`).
        TyG::FatPtr(FatPtrKind::ContainerVtable) => {
            pool.raise_to(CONTAINER_VTABLE_FORMAT_VERSION);
        }
        // v43: same discipline — raise the header for the feature the reader
        // gates, or the writer emits tag 38 under a header that refuses it.
        TyG::Handle(ty) => {
            pool.raise_to(HANDLE_TYPE_FORMAT_VERSION);
            pool.intern(&ty.name, out)?;
            pool.intern(&ty.runtime, out)?;
        }
        // v64 and v67: the same discipline for type tags 40 and 41, exactly
        // as `collect_type_identity_strings` raises them, so this identity's
        // header is the canonical writer's (`stable_digest`) and never a
        // lower one carrying a tag that header refuses.
        TyG::Storage(_) => pool.raise_to(STORAGE_LAYOUT_FORMAT_VERSION),
        TyG::Tensor(..) => pool.raise_to(TENSOR_FORMAT_VERSION),
        _ => {}
    }

    Ok(())
}

pub(super) fn observed_collect_type_origin_strings<O: ExecutionObserver>(
    origin: Option<&TypeOrigin>,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    let Some(origin) = origin else {
        return Ok(());
    };
    pool.raise_to(NOMINAL_IDENTITY_FORMAT_VERSION);
    if let TypeOrigin::Clean { decl, .. } = origin {
        pool.intern(decl, out)?;
    }

    Ok(())
}

pub(super) fn observed_raise_to_abi_surface<O: ExecutionObserver>(
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    pool.raise_to(ABI_SURFACE_FORMAT_VERSION);

    Ok(())
}

pub(super) fn observed_raise_to_contract_surface<O: ExecutionObserver>(
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    pool.raise_to(CONTRACT_SURFACE_FORMAT_VERSION);

    Ok(())
}
