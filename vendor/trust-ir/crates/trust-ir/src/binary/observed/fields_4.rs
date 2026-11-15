// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_instr_node<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    canonical: Option<Canonical<'_>>,
    node: &InstrNodeG<NoExt>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_inst(buf, pool, canonical, &node.inst)?;
    observed_write_vec_value_id(buf, canonical, &node.results)?;
    observed_write_proof_annotation_list(buf, pool, &node.proofs)?;
    match &node.span {
        None => observed_write_u8(buf, 0)?,
        Some(span) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, span.file)?;
            observed_write_v32(buf, span.line)?;
            observed_write_v32(buf, span.col)?;
        }
    }
    // v6+: per-call-site proof context (B5)
    match &node.proof_context {
        None => observed_write_u8(buf, 0)?,
        Some(pc) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "ProofContext.assumes", pc.assumes.len())?;
            for o in &pc.assumes {
                buf.poll()?;
                observed_write_proof_id(buf, *o)?;
            }
            observed_write_count(buf, "ProofContext.establishes", pc.establishes.len())?;
            for o in &pc.establishes {
                buf.poll()?;
                observed_write_proof_id(buf, *o)?;
            }
        }
    }
    // v33+: lexical scope index (C2-scopes).
    match node.scope {
        None => observed_write_u8(buf, 0)?,
        Some(scope) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, scope)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_linkage<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    v: &Linkage,
) -> R {
    buf.poll()?;
    observed_write_u8(
        buf,
        match v {
            Linkage::External => 0,
            Linkage::Internal => 1,
            Linkage::Private => 2,
            Linkage::Weak => 3,
            Linkage::LinkOnce => 4,
            Linkage::AvailableExternally => 5,
            Linkage::ExternalWeak => 6,
            Linkage::WeakOdr => 7,
            Linkage::LinkOnceOdr => 8,
        },
    )?;

    Ok(())
}

pub(super) fn observed_write_module_import<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    import: &crate::ModuleImport,
) -> R {
    buf.poll()?;
    observed_write_str(buf, pool, &import.name)?;
    observed_write_proof_digest(buf, &import.digest)?;
    match &import.producer {
        None => observed_write_u8(buf, 0)?,
        Some(producer) => {
            observed_write_u8(buf, 1)?;
            observed_write_producer(buf, pool, producer)?;
        }
    }
    // v44: the identity scheme the digest was recorded under. Written only
    // under a v44+ header, which the writer selects exactly when some row is
    // not V2 — so every row of such a table carries its tag.
    if pool.minimum_version() >= IMPORT_SCHEME_FORMAT_VERSION {
        observed_write_identity_scheme(buf, import.scheme)?;
    }

    Ok(())
}

pub(super) fn observed_write_module_sections<O: ExecutionObserver>(
    module: &ModuleG<NoExt>,
    view: Option<&ModuleWireView>,
    pool: &SealedPool,
    buf: &mut Output<'_, '_, O>,
) -> R {
    if view.is_some() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    let include_proof_sidecars = view.is_none_or(ModuleWireView::includes_proof_sidecars);
    // Module name
    observed_write_str(
        buf,
        pool,
        view.map_or(&module.name, |view| view.module_name(module)),
    )?;

    // Func types
    observed_write_count(buf, "Module.func_types", module.func_types.len())?;
    for (signature, ft) in module.func_types.iter().enumerate() {
        buf.poll()?;
        observed_write_func_ty(buf, pool, signature, ft)?;
    }

    // Structs
    observed_write_count(buf, "Module.structs", module.structs.len())?;
    for sd in &module.structs {
        buf.poll()?;
        observed_write_struct_def(buf, pool, sd)?;
    }

    // Enums
    observed_write_count(buf, "Module.enums", module.enums.len())?;
    for ed in &module.enums {
        buf.poll()?;
        observed_write_enum_def(buf, pool, ed)?;
    }

    // Records
    observed_write_count(buf, "Module.records", module.records.len())?;
    for rd in &module.records {
        buf.poll()?;
        observed_write_record_def(buf, pool, rd)?;
    }

    // Closure types
    observed_write_count(buf, "Module.closure_types", module.closure_types.len())?;
    for ct in &module.closure_types {
        buf.poll()?;
        observed_write_closure_ty(buf, pool, ct)?;
    }

    // Globals
    observed_write_count(buf, "Module.globals", module.globals.len())?;
    for (index, global) in module.globals.iter().enumerate() {
        buf.poll()?;
        let name = view.map(|view| view.global_name(global, index));
        observed_write_global(buf, pool, global, name)?;
    }

    // Types
    observed_write_count(buf, "Module.types", module.types.len())?;
    for ty in &module.types {
        buf.poll()?;
        observed_write_ty(buf, pool, ty)?;
    }

    // Functions
    let functions = buf.functions(module)?;
    observed_write_count(buf, "Module.functions", functions.len())?;
    if let Some(view) = view {
        for &index in &view.function_order {
            buf.poll()?;
            let function = &module.functions[index];
            observed_write_function(
                buf,
                pool,
                function,
                Some(view.function_name(function, index)),
                view.canonical_function(index).map(Canonical::Ordinary),
                view.retain_source_provenance,
                view.includes_codegen_license(),
            )?;
        }
    } else {
        for function in functions {
            buf.poll()?;
            observed_write_function(buf, pool, function, None, None, false, true)?;
        }
    }

    // Proof obligations
    let obligation_count = if include_proof_sidecars {
        view.map_or(module.proof_obligations.len(), |view| {
            view.obligation_rows.len()
        })
    } else {
        0
    };
    observed_write_count(buf, "Module.proof_obligations", obligation_count)?;
    if include_proof_sidecars {
        if let Some(view) = view {
            // WS4.4 (NEW-1): an obligation's `Value` bindings follow its
            // owning function's canonical renumbering, resolved exactly as
            // `format::into_canonical` resolves them.
            let positions = view
                .canonical_functions
                .is_some()
                .then(|| crate::canonicalize::unique_function_positions(module));
            for &index in &view.obligation_rows {
                buf.poll()?;
                let obligation = &module.proof_obligations[index];
                let plan = positions.as_ref().and_then(|positions| {
                    crate::canonicalize::obligation_owner(obligation)
                        .and_then(|owner| positions.get(&owner))
                        .and_then(|&position| {
                            view.canonical_function(position).map(Canonical::Ordinary)
                        })
                });
                observed_write_proof_obligation(buf, pool, obligation, plan)?;
            }
        } else {
            for obligation in &module.proof_obligations {
                buf.poll()?;
                observed_write_proof_obligation(buf, pool, obligation, None)?;
            }
        }
    }

    // Proof certificates
    let certificate_count = if include_proof_sidecars {
        module.proof_certificates.len()
    } else {
        0
    };
    observed_write_count(buf, "Module.proof_certificates", certificate_count)?;
    if include_proof_sidecars {
        for cert in &module.proof_certificates {
            buf.poll()?;
            observed_write_proof_certificate(buf, pool, cert)?;
        }
    }

    // Target info
    match &module.target_info {
        None => observed_write_u8(buf, 0)?,
        Some(ti) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, &ti.triple)?;
            observed_write_v32(buf, ti.pointer_size)?;
            observed_write_endianness(buf, &ti.endianness)?;
            // ABI pinning (VERSION >= 20): stable ABI id + struct-passing
            // policy. Digest-bearing: these bytes feed Module::stable_digest.
            observed_write_opt_str(buf, pool, ti.abi.as_deref())?;
            observed_write_u8(
                buf,
                match ti.struct_passing {
                    StructPassingPolicy::NativeC => 0,
                    StructPassingPolicy::AlwaysMemory => 1,
                    // v36: additive tag. A pre-v36 reader never sees it — the version gate
                    // rejects a v36 blob before reaching this byte — so MIN_READ_VERSION holds.
                    StructPassingPolicy::Unclassified => 2,
                },
            )?;
        }
    }

    // Debug-info source-file table (VERSION >= 9). Additive trailing section:
    // older readers stop before it; newer readers gate on the version.
    observed_write_count(buf, "Module.files", module.files.len())?;
    for path in &module.files {
        buf.poll()?;
        let spelled = pool.debug_file(path);
        observed_write_str(buf, pool, spelled)?;
    }

    // Obligation-diagnostics sidecar (VERSION >= 11). Additive trailing section.
    let diagnostic_count = if include_proof_sidecars {
        module.obligation_diagnostics.len()
    } else {
        0
    };
    observed_write_count(buf, "Module.obligation_diagnostics", diagnostic_count)?;
    if include_proof_sidecars {
        for d in &module.obligation_diagnostics {
            buf.poll()?;
            observed_write_proof_id(buf, d.obligation)?;
            observed_write_u8(
                buf,
                match d.severity {
                    crate::proof::DiagnosticSeverity::Error => 0,
                    crate::proof::DiagnosticSeverity::Warning => 1,
                    crate::proof::DiagnosticSeverity::Note => 2,
                },
            )?;
            observed_write_str(buf, pool, &d.message)?;
            match &d.location {
                None => observed_write_u8(buf, 0)?,
                Some(s) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_v32(buf, s.file)?;
                    observed_write_v32(buf, s.line)?;
                    observed_write_v32(buf, s.col)?;
                }
            }
            match &d.detail {
                None => observed_write_u8(buf, 0)?,
                Some(detail) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_str(buf, pool, detail)?;
                }
            }
        }
    }

    // Spec modules (VERSION >= 13). Additive trailing section; the current
    // writer always emits it, older readers stop before reaching it.
    observed_write_count(buf, "Module.spec_modules", module.spec_modules.len())?;
    for sm in &module.spec_modules {
        buf.poll()?;
        observed_write_spec_module(buf, pool, sm)?;
    }

    // Typed value model (VERSION >= 30). Two additive trailing sections.
    // Universes FIRST: a predicate may cite a `UnivId`, so the referent table
    // precedes the referencing one.
    observed_write_count(buf, "Module.universes", module.universes.len())?;
    for u in &module.universes {
        buf.poll()?;
        observed_write_universe(buf, pool, u)?;
    }
    observed_write_count(buf, "Module.predicates", module.predicates.len())?;
    for p in &module.predicates {
        buf.poll()?;
        observed_write_pred(buf, pool, p)?;
    }
    // v41: module-level `global_asm!` blocks, then the cross-crate import table.
    if contract_surface(pool) {
        observed_write_count(buf, "Module.global_asm", module.global_asm.len())?;
        for asm in &module.global_asm {
            buf.poll()?;
            observed_write_str(buf, pool, asm)?;
        }
        observed_write_count(buf, "Module.imports", module.imports.len())?;
        for import in &module.imports {
            buf.poll()?;
            observed_write_module_import(buf, pool, import)?;
        }
    }
    if pool.minimum_version() >= TUPLE_LAYOUT_FORMAT_VERSION {
        observed_write_count(buf, "Module.tuple_layouts", module.tuple_layouts.len())?;
        for desc in &module.tuple_layouts {
            buf.poll()?;
            observed_write_v32(buf, desc.tuple_type.index())?;
            observed_write_v64(buf, desc.size)?;
            observed_write_v64(buf, desc.align)?;
            observed_write_count(
                buf,
                "TupleLayoutDescriptor.field_offsets",
                desc.field_offsets.len(),
            )?;
            for offset in &desc.field_offsets {
                buf.poll()?;
                observed_write_v64(buf, *offset)?;
            }
        }
    }
    // v55 (amendment D): the drop-glue table, rows in the canonical
    // (ascending-glue) order the module holds them in.
    if pool.minimum_version() >= DROP_GLUE_FORMAT_VERSION {
        observed_write_count(buf, "Module.drop_glue", module.drop_glue.len())?;
        for entry in &module.drop_glue {
            buf.poll()?;
            observed_write_func_id(buf, entry.glue)?;
            observed_write_ty(buf, pool, &entry.ty)?;
        }
    }

    // v58 declared closure layouts. Written AFTER the v55 drop-glue table (and
    // so after the v42 tuple table, whose record shape it shares), so a module
    // carrying all three keeps one section order.
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        observed_write_count(buf, "Module.closure_layouts", module.closure_layouts.len())?;
        for desc in &module.closure_layouts {
            buf.poll()?;
            observed_write_v32(buf, desc.closure.index())?;
            observed_write_v64(buf, desc.size)?;
            observed_write_v64(buf, desc.align)?;
            observed_write_count(
                buf,
                "ClosureLayoutDescriptor.capture_offsets",
                desc.capture_offsets.len(),
            )?;
            for offset in &desc.capture_offsets {
                buf.poll()?;
                observed_write_v64(buf, *offset)?;
            }
            if pool.minimum_version() >= CLOSURE_ORIGIN_FORMAT_VERSION {
                observed_write_type_origin(buf, pool, desc.origin.as_ref())?;
            }
        }
    }
    // v70 (PKG-U13e): the blob table, after the v58 closure layouts, rows in
    // the canonical (strictly ascending digest) order the module holds them in.
    if pool.minimum_version() >= TENSOR_BLOB_FORMAT_VERSION {
        observed_write_count(buf, "Module.blobs", module.blobs.len())?;
        for blob in &module.blobs {
            buf.poll()?;
            buf.extend_from_slice(&blob.digest.0)?;
            observed_write_count(buf, "Blob.data", blob.data.len())?;
            buf.extend_from_slice(&blob.data)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_module_with_pool<O: ExecutionObserver>(
    module: &Module,
    view: Option<&ModuleWireView>,
    pool: &SealedPool,
    buf: &mut Output<'_, '_, O>,
) -> R {
    if view.is_some() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    // WS5.3b: fail closed. A completeness claim has no carrier at any version
    // yet, and dropping it would make a `Partial` module read back as "no
    // claim". Refused by this arm, whatever the view
    // (`Module::wire_image_refusal` is this walk).
    if module.completeness_claim_unencodable() {
        buf.refuse(|| WireRefusal::CompletenessClaim)?;
    }

    // Header
    buf.extend_from_slice(MAGIC)?;
    observed_write_u32(buf, pool.minimum_version())?;

    observed_write_count(buf, "string table", pool.strings().len())?;
    for s in pool.strings() {
        buf.poll()?;
        observed_write_raw_bytes(buf, s)?;
    }

    observed_write_module_sections(module, view, pool, buf)?;

    Ok(())
}
