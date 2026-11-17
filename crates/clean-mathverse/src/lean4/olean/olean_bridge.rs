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

use std::collections::HashSet;
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
    super::require_lean_records_only(module)?;
    let mut stats = ImportStats::default();
    let mut ctx = LoweringCtx::new(writer);
    let mut added_names: HashSet<String> = HashSet::new();
    let now_ts = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();

    for constant in &module.constants {
        // Keep safe compiler-looking kernel records. Only the record
        // itself can supply unsafe/partial replay-exclusion authority.
        if clean_olean::import::is_nonreplayable_compiler_constant(constant) {
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
/// A module-system artifact stores theorem PROOF TERMS in its `.olean.private`,
/// not its `.olean` (which keeps types and strips theorem proofs), so the
/// module is read from the artifact's authoritative part (see
/// [`parse_target_module_with_proofs`]), and an artifact whose parts disagree
/// is refused. A decl still earns `KernelVerified` only when the kernel's
/// `check_type` later accepts it.
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

/// Read the module whose `.olean` is `olean_path` the way pinned Lean does
/// (docs/DECISIONS.md R113): its parts through `clean_olean::read_artifact`,
/// which refuses an artifact whose parts disagree (a header, a value, or a name
/// the part an importer reads does not declare), then the AUTHORITATIVE part
/// alone — `.olean.private` for a module-system artifact, `.olean` otherwise.
/// Over an artifact the rule admits, that part holds every declaration with
/// its value, so nothing is merged: another part only restates it, or (in a
/// module-system artifact) holds a value-free stub of its value, and since
/// R131 a non-module artifact's companion may only restate its `.olean`.
///
/// Before R113 the bridge took the `.olean` as the module and merged the
/// private part into it, keeping the `.olean`'s value where both carried one
/// and the `.olean`'s names and imports: `per-constant-verify` and the
/// sequential `stamp-verified` modes then checked a module `leanchecker` never
/// reads (review findings P1, P2, P7).
fn read_authoritative_part(olean_path: &Path, types_only: bool) -> MathverseResult<ParsedModule> {
    let label = olean_path
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();
    let read = clean_olean::read_artifact(&label, olean_path, clean_olean::ArtifactDepth::Records)
        .map_err(|e| MathverseError::ArtifactRefused {
            path: olean_path.display().to_string(),
            reason: e.to_string(),
        })?;
    let parse_failed = |e: clean_olean::OleanError| MathverseError::ImportFailed {
        system: "Lean4".to_string(),
        reason: format!("{}: {e}", olean_path.display()),
    };
    if !read.is_module {
        return if types_only {
            parse_module_types_only_file(olean_path)
        } else {
            parse_module_file(olean_path)
        }
        .map_err(parse_failed);
    }
    // A module-system artifact: `read_artifact` proved all three parts present.
    let part = |ext: &str| {
        let path = olean_path.with_extension(ext);
        std::fs::read(&path).map_err(|e| MathverseError::ImportFailed {
            system: "Lean4".to_string(),
            reason: format!("{}: {e}", path.display()),
        })
    };
    let (base, server, private) = (
        part("olean")?,
        part("olean.server")?,
        part("olean.private")?,
    );
    if types_only {
        parse_module_incremental_types_only(&base, Some(&server), &private)
    } else {
        parse_module_incremental(&base, Some(&server), &private)
    }
    .map_err(parse_failed)
}

/// Parse a TARGET `.olean` module with every proof value: the authoritative
/// part of the artifact (see [`read_authoritative_part`]). A module-system
/// artifact keeps its theorem proofs in the `.olean.private` (e.g.
/// `Mathlib/Logic/Basic.olean` is ~439 KB of types while its `.olean.private` is
/// ~1 MB of proofs), which is the part read.
///
/// SOUNDNESS: reading supplies candidate values to the downstream kernel
/// re-check; it marks nothing verified. A refused artifact is an error, never a
/// best-effort fallback to another part.
pub fn parse_target_module_with_proofs(olean_path: &Path) -> MathverseResult<ParsedModule> {
    read_authoritative_part(olean_path, false)
}

/// Parse a TRUSTED-dependency `.olean` module TYPES-ONLY: the authoritative part
/// (see [`read_authoritative_part`]) with every constant's TYPE (and every
/// `Definition` value, kept for δ-reduction) reconstructed, and the proof-term
/// VALUE of every `Theorem`/`Opaque` skipped.
///
/// This is the per-constant streaming verifier's loader for the trusted-import
/// closure (everything EXCEPT the target). The kernel NEVER δ-unfolds a
/// `Theorem`/`Opaque` value during type-checking, so a dependency's proof body is
/// dead weight; reconstructing hundreds of analysis-module proof `Expr`s is
/// exactly the peak-RSS cost that OOMs the full-value path.
///
/// SOUNDNESS: nothing here is verified or stamped; the artifact rule is the
/// same one the target and the `.olean` loader read through.
pub fn parse_dep_module_types_only(olean_path: &Path) -> MathverseResult<ParsedModule> {
    read_authoritative_part(olean_path, true)
}

/// `parse_module_types_only` from a path (mirrors `parse_module_file`).
fn parse_module_types_only_file(olean_path: &Path) -> clean_olean::OleanResult<ParsedModule> {
    let bytes = std::fs::read(olean_path)?;
    parse_module_types_only(&bytes)
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
///
/// An `opaque` KEEPS its value. Lean's kernel checks it
/// (`environment.cpp` `add_opaque`: `check(v.get_value())` against the type),
/// and `Lean.Environment.replay` re-checks it. A shard that dropped it (as this
/// function did until 2026-09-24) left the stamp lanes unable to check an
/// opaque at all. Replayed in Lean's order, that means every constant that uses
/// one could never be admitted either: each `irreducible_def` wrapper, and
/// through it, for example, every use of `Real.add`. An opaque never
/// δ-unfolds, so carrying its value changes no reduction.
fn has_value_for(constant: &ParsedConstant) -> bool {
    use clean_olean::module::ConstantKind;
    match constant.kind {
        ConstantKind::Theorem | ConstantKind::Definition | ConstantKind::Opaque => {
            constant.value.is_some()
        }
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => true,
        ConstantKind::Quot => true,
        ConstantKind::Axiom => false,
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

    // The bridge no longer merges parts (docs/DECISIONS.md R113), so the unit
    // tests of `merge_companion_values` went with it. What they pinned is now
    // pinned on real artifacts: a module-system target's proofs come from its
    // `.olean.private` (`batch::tests_module_system`); a name only a companion
    // declares, and parts that state a declaration differently, are refused
    // (`cli::replay_forged_lane_tests::parts` and `::misplaced`, and
    // `clean-olean`'s `olean_parts_tests`).

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
