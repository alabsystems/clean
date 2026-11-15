// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn collect<O: ExecutionObserver>(
    f: &Function,
    plan: &Plan,
    rows: &[Row<'_>],
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    if !rows.is_empty() {
        pool.raise_to(DROP_GLUE_FORMAT_VERSION);
        for entry in rows {
            out.poll()?;
            observed_collect_type_identity_strings(entry.ty, pool, out)?;
        }
    }
    pool.intern("", out)?;
    observed_collect_function_strings(
        f,
        &f.name,
        Some(Canonical::Body(plan)),
        true,
        false,
        pool,
        out,
    )
}
pub(super) fn write<O: ExecutionObserver>(
    f: &Function,
    plan: &Plan,
    rows: &[Row<'_>],
    pool: &SealedPool,
    out: &mut Output<'_, '_, O>,
) -> R {
    out.poll()?;
    out.extend_from_slice(MAGIC)?;
    observed_write_u32(out, pool.minimum_version())?;
    observed_write_count(out, "string table", pool.strings().len())?;
    for text in pool.strings() {
        out.poll()?;
        observed_write_raw_bytes(out, text)?;
    }
    observed_write_str(out, pool, "")?;
    // Exact Module::new("") empty sections, with only this function and its
    // resolved drop-glue rows present. No table is borrowed from the source.
    for label in [
        "Module.func_types",
        "Module.structs",
        "Module.enums",
        "Module.records",
        "Module.closure_types",
        "Module.globals",
        "Module.types",
    ] {
        observed_write_count(out, label, 0)?;
    }
    observed_write_count(out, "Module.functions", 1)?;
    observed_write_function(out, pool, f, None, Some(Canonical::Body(plan)), true, false)?;
    observed_write_count(out, "Module.proof_obligations", 0)?;
    observed_write_count(out, "Module.proof_certificates", 0)?;
    observed_write_u8(out, 0)?; // target_info None
    for label in [
        "Module.files",
        "Module.obligation_diagnostics",
        "Module.spec_modules",
        "Module.universes",
        "Module.predicates",
    ] {
        observed_write_count(out, label, 0)?;
    }
    if contract_surface(pool) {
        observed_write_count(out, "Module.global_asm", 0)?;
        observed_write_count(out, "Module.imports", 0)?;
    }
    if pool.minimum_version() >= TUPLE_LAYOUT_FORMAT_VERSION {
        observed_write_count(out, "Module.tuple_layouts", 0)?;
    }
    if pool.minimum_version() >= DROP_GLUE_FORMAT_VERSION {
        observed_write_count(out, "Module.drop_glue", rows.len())?;
        for entry in rows {
            out.poll()?;
            observed_write_func_id(out, entry.glue)?;
            observed_write_ty(out, pool, entry.ty)?;
        }
    }
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        observed_write_count(out, "Module.closure_layouts", 0)?;
    }
    // v70: a body that names a blob raises the image's header; the image
    // carries no blob table (the body reads the digest, never the bytes).
    if pool.minimum_version() >= TENSOR_BLOB_FORMAT_VERSION {
        observed_write_count(out, "Module.blobs", 0)?;
    }
    Ok(())
}
