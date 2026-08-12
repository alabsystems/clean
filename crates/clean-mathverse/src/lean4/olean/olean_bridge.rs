// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge from `.olean` files to `.mathverse` shards with full provenance.
//!
//! Connects the clean-olean parser with the lean4_alpha importer and the
//! provenance sidecar to produce `.mathverse` shards with complete metadata.
//!
//! Entry points:
//! - [`convert_olean_to_mathverse`]: Convert a single `.olean` file to an in-memory shard.
//! - [`convert_modules_to_mathverse`]: Convert multiple parsed modules into one `.mathverse` shard.
//! - [`convert_olean_dir_to_mathverse`]: Batch-convert a directory of `.olean` files to a shard file.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::time::SystemTime;

use clean_olean::module::{ParsedConstant, ParsedModule};
use clean_olean::{
    parse_module_file, parse_module_incremental, parse_module_incremental_types_only,
    parse_module_types_only,
};

use crate::error::{MathverseError, MathverseResult};
use crate::lean4::olean::alpha::{
    apply_inductive_header_metadata, compute_axiom_profile, ImportStats, LoweringCtx,
};
use crate::lean4::olean::batch::path_to_module_name;
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};
use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// ConvertResult
// ---------------------------------------------------------------------------

/// Result of converting `.olean` file(s) to an `.mathverse` shard.
#[derive(Clone, Debug, Default)]
pub struct ConvertResult {
    /// Total constants imported.
    pub total_constants: u32,
    /// Constants with proof terms (kernel-verified confidence).
    pub kernel_verified: u32,
    /// Constants marked kernel-verified due to actual type-checker verification.
    pub kernel_verified_from_tc: u32,
    /// Constants without proof terms (axiomatized confidence).
    pub axiomatized: u32,
    /// Constants that were skipped.
    pub skipped: u32,
    /// Number of provenance records generated.
    pub provenance_records: u32,
    /// Module names processed.
    pub modules: Vec<String>,
    /// Files that failed to parse.
    pub failures: Vec<(String, String)>,
}

impl ConvertResult {
    fn accum_stats(&mut self, stats: &ImportStats) {
        self.total_constants += stats.total;
        self.kernel_verified += stats.kernel_verified;
        self.kernel_verified_from_tc += stats.kernel_verified_from_tc;
        self.axiomatized += stats.axiomatized;
        self.skipped += stats.skipped;
    }
}

// ---------------------------------------------------------------------------
// Single-module conversion with provenance
// ---------------------------------------------------------------------------

/// Import a single `ParsedModule` into a `ShardWriter` with full provenance.
///
/// Unlike the bare `import_module`, this function:
/// 1. Generates a `ProvenanceRecord` for every constant
/// 2. Wires `sidecar_digest` and `provenance_idx` into each `MathverseConstantHeader`
/// 3. Serializes the provenance sidecar into the shard
///
/// Returns the import statistics.
pub fn import_module_with_provenance(
    module: &ParsedModule,
    writer: &mut ShardWriter,
    sidecar: &mut ProvenanceSidecar,
    module_name: Option<&str>,
) -> MathverseResult<ImportStats> {
    import_module_with_provenance_verified(module, writer, sidecar, module_name, None)
}

/// Import a single `ParsedModule` into a `ShardWriter` with full provenance,
/// upgrading constants in `verified_names` to `KernelVerified`.
///
/// Constants whose names appear in `verified_names` receive
/// `ImportConfidence::KernelVerified` regardless of the heuristic.
pub fn import_module_with_provenance_verified(
    module: &ParsedModule,
    writer: &mut ShardWriter,
    sidecar: &mut ProvenanceSidecar,
    module_name: Option<&str>,
    verified_names: Option<&HashSet<String>>,
) -> MathverseResult<ImportStats> {
    let mut stats = ImportStats::default();
    let mut ctx = LoweringCtx::new(writer);
    let mut added_names: HashSet<String> = HashSet::new();
    let now_ts = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();

    for constant in &module.constants {
        // SOUNDNESS: skip Lean compiler-IR stage decls (`._cstage1`/`._cstage2`).
        // These are code-generator artifacts whose types reference the runtime
        // pseudo-types `_obj`/`_neutral`; they are never kernel-checkable and
        // must not enter the shard (they would re-verify as UnknownConst and
        // pollute the KernelVerified accounting). See
        // `clean_olean::import::is_compiler_ir_name`.
        if clean_olean::import::is_compiler_ir_name(&constant.name) {
            continue;
        }
        if !added_names.insert(constant.name.clone()) {
            continue;
        }
        let name_idx = ctx.intern_string(&constant.name);
        let heuristic = confidence_for_constant(constant);
        let verified_by_tc = verified_names.is_some_and(|names| names.contains(&constant.name));
        let confidence = if verified_by_tc {
            ImportConfidence::KernelVerified
        } else {
            heuristic
        };
        let profile = compute_axiom_profile(constant);

        // Lower the type expression.
        let type_idx: u32 = match &constant.type_ {
            Some(type_expr) => ctx.lower_expr(type_expr),
            None => {
                let l0 = ctx.writer.add_level(clean_kernel::flat::FlatLevel::zero());
                ctx.writer.add_expr(clean_kernel::flat::FlatExpr::sort(l0))
            }
        };

        // Lower the value expression if present.
        let value_idx: u32 = if has_value_for(constant) {
            match &constant.value {
                Some(val_expr) => ctx.lower_expr(val_expr),
                None => {
                    let l0 = ctx.writer.add_level(clean_kernel::flat::FlatLevel::zero());
                    ctx.writer.add_expr(clean_kernel::flat::FlatExpr::sort(l0))
                }
            }
        } else {
            NO_VALUE
        };

        // Store level parameter names as a CONTIGUOUS string-table block. A
        // plain intern loop dedups params already present in the table (e.g. a
        // `u_1` first seen inside the decl's type), scattering the rest and
        // making the `[start..start+count)` window read unrelated strings as
        // universe parameters — a spurious `UndefinedLevelParam` rejection of an
        // otherwise valid declaration. See `add_level_param_block`.
        let (lp_start, lp_count) = ctx.add_level_param_block(&constant.level_params);

        // Build provenance record.
        let mut builder = ProvenanceBuilder::new(&constant.name)
            .import_timestamp(now_ts)
            .pipeline_version(1);
        if let Some(mn) = module_name {
            builder = builder.module_path(mn);
        }
        builder = builder.note(&format!("kind: {:?}", constant.kind));
        let record = builder.build();
        let (prov_idx, digest) = add_provenance(sidecar, record);

        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: crate::lean4::olean::decl_kind::decl_kind_from_olean(&constant.kind) as u8,
            axiom_profile: profile,
            sidecar_digest: digest,
            provenance_idx: prov_idx,
            level_params_start: lp_start,
            level_params_count: lp_count,
            _pad2: [0u8; 26],
        };
        apply_inductive_header_metadata(&mut header, constant, ctx.writer);

        // Persist Lean's `DefinitionSafety` (safe/unsafe/partial) into the
        // header (`_pad2[25]`, 0x80|tag; 0 = unset ⇒ safe). The incremental
        // replay reads it back to route `unsafe def`s (recursive, no
        // termination proof — Lean bars them from proofs) to the
        // trusted-context `UnsafeAccepted` lane instead of a masked axiom
        // fallback (2026-07-06 census Class 3).
        if let Some(safety) = constant.definition_safety {
            header.set_definition_safety(safety);
        }

        ctx.writer.add_constant(header);
        stats.total += 1;
        if verified_by_tc
            && heuristic != ImportConfidence::KernelVerified
            && heuristic != ImportConfidence::SourceVerified
        {
            stats.kernel_verified_from_tc += 1;
        }
        match confidence {
            ImportConfidence::KernelVerified | ImportConfidence::SourceVerified => {
                stats.kernel_verified += 1;
            }
            ImportConfidence::Axiomatized => stats.axiomatized += 1,
            _ => stats.skipped += 1,
        }
    }

    Ok(stats)
}

// ---------------------------------------------------------------------------
// Public conversion API
// ---------------------------------------------------------------------------

/// Convert a single `.olean` file to an in-memory `.mathverse` shard (as bytes).
///
/// Parses the `.olean` file, imports all constants with provenance tracking,
/// and serializes the result into a complete `.mathverse` shard.
///
/// Lean stores theorem PROOF TERMS in the `.olean.private` companion, not the
/// base `.olean` (which keeps types and definition values but strips theorem
/// proofs). When the sibling companions exist they are parsed and their
/// constant VALUES are merged by name into the base module so that re-checked
/// theorems have a proof to feed the kernel (see
/// [`parse_target_module_with_proofs`]). The companions are not authoritative:
/// they only fill in value-less base stubs; a decl still earns
/// `KernelVerified` only when the kernel's `check_type` later accepts it.
pub fn convert_olean_to_mathverse(olean_path: &Path) -> MathverseResult<(Vec<u8>, ConvertResult)> {
    let module = parse_target_module_with_proofs(olean_path)?;

    let module_name = olean_path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string());

    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();
    let stats =
        import_module_with_provenance(&module, &mut writer, &mut sidecar, module_name.as_deref())?;

    // Close axiom profiles over the in-shard dependency graph so a constant's
    // reported axiom set includes axioms reachable through any depth of
    // dependency, not just its local (one-level) usage.
    writer.finalize_axiom_profiles();

    // Attach provenance sidecar to the shard.
    let prov_bytes = sidecar.to_bytes()?;
    writer.set_provenance(prov_bytes);

    // Serialize the shard.
    let mut buf = Vec::new();
    writer.write(&mut buf)?;

    let mut result = ConvertResult::default();
    result.accum_stats(&stats);
    result.provenance_records = sidecar.len() as u32;
    if let Some(name) = module_name {
        result.modules.push(name);
    }

    Ok((buf, result))
}

/// Parse a target `.olean` module and fill in theorem proof values from the
/// sibling `.olean.private` (and `.olean.server`) companions.
///
/// The base `.olean` carries every declaration's type and definition values,
/// but theorem proof terms are stored separately in the `.olean.private`
/// companion (e.g. `Mathlib/Logic/Basic.olean` is ~439 KB of types while the
/// matching `.olean.private` is ~1 MB of proofs). Converting only the base
/// therefore yields value-less theorem stubs that the re-verifier can only
/// register as axioms (`axiom_accepted`) — never proof-check.
///
/// This loads the companions with [`parse_module_incremental`] (whose
/// `server_bytes` argument is optional, so a module with `.private` but no
/// `.server` is still handled) and, for any companion constant whose name
/// matches a VALUE-LESS base entry, replaces that stub in place with the
/// companion's proof-carrying record (its true kind, type, and value — see
/// [`merge_companion_values`]). Companion constants with no base entry are
/// appended so dependents can resolve them.
///
/// SOUNDNESS: merging only supplies more candidate values to the downstream
/// kernel re-check. It never marks anything verified and never overwrites a
/// value the base already carries. Merge is by NAME into the matching base
/// entry, so no constant is duplicated or shadowed. If a companion is absent or
/// fails to parse, the base module is returned unchanged (best-effort fill-in).
pub fn parse_target_module_with_proofs(olean_path: &Path) -> MathverseResult<ParsedModule> {
    let mut module = parse_module_file(olean_path).map_err(|e| MathverseError::ImportFailed {
        system: "Lean4".to_string(),
        reason: format!("{}: {e}", olean_path.display()),
    })?;

    // The companions reference the base address space, so the base bytes are
    // required as the anchor for incremental region parsing.
    let private_path = olean_path.with_extension("olean.private");
    if !private_path.exists() {
        return Ok(module);
    }
    let Ok(base_bytes) = std::fs::read(olean_path) else {
        return Ok(module);
    };
    let Ok(private_bytes) = std::fs::read(&private_path) else {
        return Ok(module);
    };

    // `.server` is optional: Mathlib modules often ship `.private` without a
    // `.server`. When present it is passed through because private objects may
    // reference server-region constants.
    let server_path = olean_path.with_extension("olean.server");
    let server_bytes = if server_path.exists() {
        std::fs::read(&server_path).ok()
    } else {
        None
    };

    match parse_module_incremental(&base_bytes, server_bytes.as_deref(), &private_bytes) {
        Ok(private_module) => {
            merge_companion_values(&mut module, private_module.constants);
        }
        Err(e) => {
            // Best-effort: a malformed/unsupported companion leaves the base
            // module untouched rather than aborting the whole conversion.
            if std::env::var("CLEAN_DIAG_PRIVATE").is_ok() {
                eprintln!(
                    "CLEAN_DIAG_PRIVATE: {} .olean.private parse FAILED: {e}",
                    olean_path.display()
                );
            }
        }
    }

    Ok(module)
}

/// Parse a TRUSTED-dependency `.olean` module TYPES-ONLY: every constant's TYPE
/// (and every `Definition` value, kept for δ-reduction) is reconstructed, but the
/// proof-term VALUE of every `Theorem`/`Opaque` is skipped — in the base module
/// AND in the `.olean.private`/`.olean.server` companions.
///
/// This is the per-constant streaming verifier's loader for the trusted-import
/// closure (everything EXCEPT the target). The kernel NEVER δ-unfolds a
/// `Theorem`/`Opaque` value during type-checking, so a dependency's proof body is
/// dead weight; the base `.olean` already carries every theorem's TYPE (as a
/// value-less stub), so a type-only dependency needs nothing from the proof-heavy
/// `.olean.private` except the occasional `Definition` body. Reconstructing those
/// hundreds of analysis-module proof `Expr`s is exactly the peak-RSS cost that
/// OOMs the full-value path; skipping it is what lets MVT/Taylor verify in ≤16 GB.
///
/// SOUNDNESS: identical to [`parse_target_module_with_proofs`] for the trusted
/// path — nothing here is verified or stamped. Only the TARGET (loaded WITH its
/// value via [`parse_target_module_with_proofs`]) flows through the kernel's
/// `check_type`. A missing/omitted trusted value can only make the target's own
/// re-check conservatively FAIL, never falsely pass; and a `Theorem`/`Opaque`
/// value is one the kernel would never consult regardless.
pub fn parse_dep_module_types_only(olean_path: &Path) -> MathverseResult<ParsedModule> {
    let mut module =
        parse_module_types_only_file(olean_path).map_err(|e| MathverseError::ImportFailed {
            system: "Lean4".to_string(),
            reason: format!("{}: {e}", olean_path.display()),
        })?;

    let private_path = olean_path.with_extension("olean.private");
    if !private_path.exists() {
        return Ok(module);
    }
    let Ok(base_bytes) = std::fs::read(olean_path) else {
        return Ok(module);
    };
    let Ok(private_bytes) = std::fs::read(&private_path) else {
        return Ok(module);
    };

    let server_path = olean_path.with_extension("olean.server");
    let server_bytes = if server_path.exists() {
        std::fs::read(&server_path).ok()
    } else {
        None
    };

    // Types-only companion parse: `Theorem`/`Opaque` proof terms in the private
    // region are NOT reconstructed (they merge as value-less and thus never
    // overwrite a base stub in `merge_companion_values`), so only `Definition`
    // bodies and private-helper TYPES are merged in.
    if let Ok(private_module) =
        parse_module_incremental_types_only(&base_bytes, server_bytes.as_deref(), &private_bytes)
    {
        merge_companion_values(&mut module, private_module.constants);
    }

    Ok(module)
}

/// `parse_module_types_only` from a path (mirrors `parse_module_file`).
fn parse_module_types_only_file(olean_path: &Path) -> clean_olean::OleanResult<ParsedModule> {
    let bytes = std::fs::read(olean_path)?;
    parse_module_types_only(&bytes)
}

/// Merge proof-carrying companion constants into a base module by name.
///
/// Lean's base `.olean` stores a stripped, value-less stub for every theorem
/// (and any definition whose body lives in the private region): the base parser
/// surfaces such a stub as a value-less entry — for theorems, as a
/// `ConstantKind::Axiom`-shaped record with a type but no proof. The matching
/// `.olean.private` constant is the authoritative, proof-carrying version of
/// the SAME declaration (same name, same type), tagged with its true kind
/// (`Theorem`/`Definition`) and its value.
///
/// For each companion constant:
/// - If the base has a matching VALUE-LESS entry, that stub is replaced in
///   place by the companion's proof-carrying record (kind, type, value, and
///   the rest), so the downstream re-check sees a `Theorem`/`Definition` with a
///   proof instead of a value-less axiom stub.
/// - If the base entry already carries a value, it is left untouched (the base
///   is authoritative for decls it fully exports; the companion never clobbers).
/// - If there is no base entry at all (e.g. a private match helper), the
///   companion is appended once so dependents can resolve the name.
///
/// SOUNDNESS: this only supplies the kernel with a candidate proof term for a
/// stub it would otherwise register as a value-less axiom. It performs no
/// verification and stamps nothing; every replaced decl is still independently
/// re-checked by `check_type` downstream and earns `KernelVerified` only on a
/// genuine pass. Replacement is keyed by NAME and gated on the base entry being
/// value-less, so no value-bearing decl is overwritten and no name is
/// duplicated or shadowed.
fn merge_companion_values(base: &mut ParsedModule, companion_constants: Vec<ParsedConstant>) {
    // Index base entries by name to merge in place without duplicating.
    let base_index: HashMap<String, usize> = base
        .constants
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();

    let mut appended: HashSet<String> = HashSet::new();
    for companion in companion_constants {
        match base_index.get(&companion.name) {
            Some(&idx) => {
                let entry = &mut base.constants[idx];
                // Replace a value-less stub with the companion's proof-carrying
                // record; never touch a base entry that already has a value.
                if entry.value.is_none() && companion.value.is_some() {
                    *entry = companion;
                }
            }
            None => {
                // Companion-only constant (e.g. private match helper). Append it
                // once so dependents can resolve the name.
                if appended.insert(companion.name.clone()) {
                    base.constants.push(companion);
                }
            }
        }
    }
}

/// Convert multiple `ParsedModule`s into one `.mathverse` shard (as bytes).
///
/// All constants from all modules are combined into a single shard with
/// a unified string table, expression arena, and provenance sidecar.
pub fn convert_modules_to_mathverse(
    modules: &[(&str, &ParsedModule)],
) -> MathverseResult<(Vec<u8>, ConvertResult)> {
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();
    let mut result = ConvertResult::default();

    for (module_name, module) in modules {
        let stats =
            import_module_with_provenance(module, &mut writer, &mut sidecar, Some(module_name))?;
        result.accum_stats(&stats);
        result.modules.push(module_name.to_string());
    }

    // Close axiom profiles over the combined dependency graph (all modules
    // share one expression arena, so cross-module dependencies are resolved).
    writer.finalize_axiom_profiles();

    result.provenance_records = sidecar.len() as u32;

    // Attach provenance sidecar.
    let prov_bytes = sidecar.to_bytes()?;
    writer.set_provenance(prov_bytes);

    let mut buf = Vec::new();
    writer.write(&mut buf)?;

    Ok((buf, result))
}

/// Batch-convert a directory of `.olean` files into a single `.mathverse` shard file.
///
/// Discovers all `.olean` files under `olean_dir`, parses each one, imports
/// all constants with provenance tracking, and writes the result to `output_path`.
///
/// Files that fail to parse are recorded in the result but do not abort the
/// batch.
pub fn convert_olean_dir_to_mathverse(
    olean_dir: &Path,
    output_path: &Path,
    module_filter: Option<&[String]>,
) -> MathverseResult<ConvertResult> {
    let mut files = Vec::new();
    collect_olean_files_bridge(olean_dir, &mut files)?;
    files.sort();

    // Apply filter if specified.
    if let Some(prefixes) = module_filter {
        files.retain(|p| {
            let name = path_to_module_name(p, olean_dir);
            prefixes.iter().any(|pfx| name.starts_with(pfx))
        });
    }

    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();
    let mut result = ConvertResult::default();

    for path in &files {
        let module_name = path_to_module_name(path, olean_dir);
        match parse_module_file(path) {
            Ok(module) => {
                let stats = import_module_with_provenance(
                    &module,
                    &mut writer,
                    &mut sidecar,
                    Some(&module_name),
                )?;
                result.accum_stats(&stats);
                result.modules.push(module_name);
            }
            Err(e) => {
                result
                    .failures
                    .push((path.display().to_string(), format!("{e}")));
            }
        }
    }

    // Close axiom profiles over the combined dependency graph before writing.
    writer.finalize_axiom_profiles();

    result.provenance_records = sidecar.len() as u32;

    // Attach provenance sidecar.
    let prov_bytes = sidecar.to_bytes()?;
    writer.set_provenance(prov_bytes);

    writer.write_to_file(output_path)?;

    Ok(result)
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Determine confidence for a parsed constant (mirrors the honest
/// [`crate::lean4::olean::alpha::confidence_for`] logic).
///
/// This is the *un-typechecked* heuristic path: it never sees OUR clean
/// kernel, so it must NOT emit `KernelVerified`. The most it can honestly
/// claim is `SourceVerified` — Lean 4's own type checker accepted the
/// source `.olean`, but the reconstructed mathverse representation has not
/// been independently kernel-checked. Only the TC-verified path (constants
/// whose names appear in `verified_names`, set by
/// `import_module_with_provenance_verified`) may upgrade to `KernelVerified`.
fn confidence_for_constant(constant: &ParsedConstant) -> ImportConfidence {
    use clean_olean::module::ConstantKind;
    match constant.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => ImportConfidence::Axiomatized,
        ConstantKind::Theorem | ConstantKind::Definition => {
            if constant.value.is_some() {
                ImportConfidence::SourceVerified
            } else {
                ImportConfidence::Axiomatized
            }
        }
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
            ImportConfidence::SourceVerified
        }
        ConstantKind::Quot => ImportConfidence::SourceVerified,
        _ => ImportConfidence::Unverified,
    }
}

/// Determine whether a constant has a meaningful value.
fn has_value_for(constant: &ParsedConstant) -> bool {
    use clean_olean::module::ConstantKind;
    match constant.kind {
        ConstantKind::Theorem | ConstantKind::Definition => constant.value.is_some(),
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => true,
        ConstantKind::Quot => true,
        ConstantKind::Axiom | ConstantKind::Opaque => false,
        _ => false,
    }
}

/// Recursively collect `.olean` files (bridge-local to avoid pub(crate) issues).
fn collect_olean_files_bridge(
    dir: &Path,
    out: &mut Vec<std::path::PathBuf>,
) -> MathverseResult<()> {
    if !dir.exists() {
        return Err(MathverseError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("directory not found: {}", dir.display()),
        )));
    }
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        let path = entry.path();
        if ft.is_dir() {
            collect_olean_files_bridge(&path, out)?;
        } else if ft.is_file() {
            if let Some(ext) = path.extension() {
                if ext == "olean" {
                    out.push(path);
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    include!("olean_bridge_tests.rs");

    use std::collections::HashSet;

    #[test]
    fn test_import_module_with_provenance_verified_promotes_tc_verified_axiom() {
        let module = mock_module(vec![mock_constant(
            "verified_axiom",
            ConstantKind::Axiom,
            false,
        )]);
        let verified_names = HashSet::from([String::from("verified_axiom")]);
        let mut writer = ShardWriter::new();
        let mut sidecar = ProvenanceSidecar::new();

        let stats = import_module_with_provenance_verified(
            &module,
            &mut writer,
            &mut sidecar,
            Some("Init.Core"),
            Some(&verified_names),
        )
        .unwrap();

        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 1);
        assert_eq!(stats.axiomatized, 0);

        writer.set_provenance(sidecar.to_bytes().unwrap());
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::KernelVerified as u8
        );
    }

    #[test]
    fn test_import_module_with_provenance_verified_keeps_heuristic_for_unverified_constant() {
        let module = mock_module(vec![mock_constant(
            "unverified_axiom",
            ConstantKind::Axiom,
            false,
        )]);
        let verified_names = HashSet::from([String::from("other_constant")]);
        let mut writer = ShardWriter::new();
        let mut sidecar = ProvenanceSidecar::new();

        let stats = import_module_with_provenance_verified(
            &module,
            &mut writer,
            &mut sidecar,
            Some("Init.Core"),
            Some(&verified_names),
        )
        .unwrap();

        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 0);
        assert_eq!(stats.axiomatized, 1);

        writer.set_provenance(sidecar.to_bytes().unwrap());
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::Axiomatized as u8
        );
    }

    #[test]
    fn test_merge_companion_values_fills_value_less_theorem_stub() {
        // Base: a value-less theorem stub (proof stripped, as in a Mathlib base
        // .olean) plus a definition that already carries its value.
        let mut base = mock_module(vec![
            mock_constant("Logic.thm", ConstantKind::Theorem, false),
            rich_constant(
                "Logic.def",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_id()),
            ),
        ]);
        // Companion (.private): supplies the proof value for the theorem and a
        // (different) value for the definition that must NOT clobber the base.
        let companion = vec![
            rich_constant("Logic.thm", ConstantKind::Theorem, type0(), Some(nat_id())),
            rich_constant(
                "Logic.def",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_const()),
            ),
        ];

        merge_companion_values(&mut base, companion);

        // Theorem stub now has its proof value filled in.
        assert!(
            base.constants[0].value.is_some(),
            "value-less theorem stub must receive its proof from the companion"
        );
        // Definition keeps its original value (never overwritten).
        assert!(matches!(base.constants[1].value, Some(ParsedExpr::Lam(..))));
        // No duplication: still exactly two constants.
        assert_eq!(base.constants.len(), 2);
    }

    #[test]
    fn test_merge_companion_values_appends_companion_only_constant_once() {
        let mut base = mock_module(vec![mock_constant(
            "Logic.thm",
            ConstantKind::Theorem,
            false,
        )]);
        // Companion has a private helper not present in the base, listed twice.
        let companion = vec![
            rich_constant(
                "Logic.match_1",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_id()),
            ),
            rich_constant(
                "Logic.match_1",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_id()),
            ),
        ];

        merge_companion_values(&mut base, companion);

        let names: Vec<&str> = base.constants.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, vec!["Logic.thm", "Logic.match_1"]);
    }

    #[test]
    fn test_merge_companion_values_does_not_overwrite_existing_value() {
        let original_value = Some(nat_id());
        let mut base = mock_module(vec![rich_constant(
            "Logic.thm",
            ConstantKind::Theorem,
            type0(),
            original_value,
        )]);
        // Companion supplies a different value for the same name.
        let companion = vec![rich_constant(
            "Logic.thm",
            ConstantKind::Theorem,
            type0(),
            Some(nat_const()),
        )];

        merge_companion_values(&mut base, companion);

        // The base's pre-existing value is preserved (companion never clobbers).
        assert!(matches!(base.constants[0].value, Some(ParsedExpr::Lam(..))));
        assert_eq!(base.constants.len(), 1);
    }

    #[test]
    fn test_import_module_with_provenance_verified_none_preserves_existing_behavior() {
        let module = mock_module(vec![
            mock_constant("axiom1", ConstantKind::Axiom, false),
            mock_constant("thm1", ConstantKind::Theorem, true),
        ]);
        let mut heuristic_writer = ShardWriter::new();
        let mut heuristic_sidecar = ProvenanceSidecar::new();
        let mut verified_writer = ShardWriter::new();
        let mut verified_sidecar = ProvenanceSidecar::new();

        let heuristic_stats = import_module_with_provenance(
            &module,
            &mut heuristic_writer,
            &mut heuristic_sidecar,
            Some("Init.Core"),
        )
        .unwrap();
        let verified_stats = import_module_with_provenance_verified(
            &module,
            &mut verified_writer,
            &mut verified_sidecar,
            Some("Init.Core"),
            None,
        )
        .unwrap();

        assert_eq!(verified_stats, heuristic_stats);

        heuristic_writer.set_provenance(heuristic_sidecar.to_bytes().unwrap());
        let mut heuristic_buf = Vec::new();
        heuristic_writer.write(&mut heuristic_buf).unwrap();
        let heuristic_reader = ShardReader::from_bytes(&heuristic_buf).unwrap();

        verified_writer.set_provenance(verified_sidecar.to_bytes().unwrap());
        let mut verified_buf = Vec::new();
        verified_writer.write(&mut verified_buf).unwrap();
        let verified_reader = ShardReader::from_bytes(&verified_buf).unwrap();

        let heuristic_confidences: Vec<u8> = heuristic_reader
            .constants
            .iter()
            .map(|constant| constant.import_confidence)
            .collect();
        let verified_confidences: Vec<u8> = verified_reader
            .constants
            .iter()
            .map(|constant| constant.import_confidence)
            .collect();
        assert_eq!(verified_confidences, heuristic_confidences);

        // Honesty contract: the un-typechecked heuristic path must NEVER stamp
        // KernelVerified (no OUR-kernel check runs here). An axiom-without-value
        // is Axiomatized; a theorem-with-proof is at most SourceVerified.
        assert_eq!(
            heuristic_reader.constants[0].import_confidence,
            ImportConfidence::Axiomatized as u8,
            "axiom1 must be Axiomatized on the heuristic path"
        );
        assert_eq!(
            heuristic_reader.constants[1].import_confidence,
            ImportConfidence::SourceVerified as u8,
            "thm1 (heuristic, un-typechecked) must be SourceVerified, NOT KernelVerified"
        );
        assert_ne!(
            heuristic_reader.constants[1].import_confidence,
            ImportConfidence::KernelVerified as u8,
            "heuristic path must never stamp KernelVerified without an OUR-kernel check"
        );
    }
}
