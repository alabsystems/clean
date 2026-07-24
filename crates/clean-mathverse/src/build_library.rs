// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bulk build pipeline for constructing an Mathverse Library from Lean 4
//! `.olean` files.
//!
//! [`build_lean4_library`] discovers, parses, and imports all `.olean` files
//! from a Lean 4 toolchain directory into `.mathverse` shards, writing a manifest
//! for later loading via [`load_built_library`].

use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::error::{MathverseError, MathverseResult};
use crate::lean4::olean::batch::{Lean4BatchConfig, Lean4BatchImporter};
use crate::library::MathverseLibrary;
use crate::manifest::LibraryLoader;
use crate::shard::ShardWriter;
use crate::trust::policy::TrustPolicy;

// ---------------------------------------------------------------------------
// BuildConfig
// ---------------------------------------------------------------------------

/// Configuration for building an Mathverse Library from Lean 4 `.olean` files.
#[derive(Clone, Debug)]
pub struct BuildConfig {
    /// Root directory containing `.olean` files
    /// (e.g., `~/.elan/toolchains/.../lib/lean/`).
    pub lean_lib_dir: PathBuf,
    /// Output directory where `.mathverse` shards and manifest will be written.
    pub output_dir: PathBuf,
    /// Module prefixes to import (e.g., `["Init", "Std"]`).
    /// Empty means import all modules.
    pub modules: Vec<String>,
    /// Maximum constants per shard before splitting.
    pub shard_size_limit: usize,
    /// Maximum .olean file size in bytes to process (0 = no limit).
    /// Files larger than this are skipped. Useful for avoiding multi-MB
    /// compiler-internal files (Init/Meta.olean ~3.4MB) that dominate build time.
    pub max_file_size: u64,
    /// Print progress information to stderr.
    pub verbose: bool,
}

// ---------------------------------------------------------------------------
// BuildResult
// ---------------------------------------------------------------------------

/// Result of a bulk library build operation.
#[derive(Clone, Debug, Default)]
pub struct BuildResult {
    /// Total `.olean` files discovered (after filtering).
    pub total_files: usize,
    /// Files successfully parsed and imported.
    pub files_parsed: usize,
    /// Files that failed to parse.
    pub files_failed: usize,
    /// Total constants imported across all shards.
    pub total_constants: usize,
    /// Total axiomatized constants (no proof term).
    pub total_axioms: usize,
    /// Total constants with proof values (kernel-verified).
    pub total_with_value: usize,
    /// Number of shard files written.
    pub shards_written: usize,
    /// Failed files with their error messages.
    pub failed_files: Vec<(PathBuf, String)>,
    /// Wall-clock elapsed time in milliseconds.
    pub elapsed_ms: u64,
}

// ---------------------------------------------------------------------------
// build_lean4_library
// ---------------------------------------------------------------------------

/// Build an Mathverse Library from Lean 4 `.olean` files.
///
/// Discovers all `.olean` files under `config.lean_lib_dir`, optionally
/// filtered by `config.modules`, parses each one, imports constants into
/// shards (splitting at `config.shard_size_limit`), and writes a manifest.
///
/// Parse failures are recorded but do not abort the build.
pub fn build_lean4_library(config: &BuildConfig) -> MathverseResult<BuildResult> {
    let start = Instant::now();

    // Set up the batch importer for discovery.
    let mut batch_config = Lean4BatchConfig::new(config.lean_lib_dir.clone());
    if !config.modules.is_empty() {
        batch_config = batch_config.with_filter(config.modules.clone());
    }
    let importer = Lean4BatchImporter::new(batch_config);
    let files = importer.discover_files()?;

    let mut result = BuildResult {
        total_files: files.len(),
        ..Default::default()
    };

    if config.verbose {
        eprintln!(
            "[build_library] discovered {} .olean files under {}",
            files.len(),
            config.lean_lib_dir.display()
        );
    }

    // Set up the output directory structure via LibraryLoader.
    let loader = LibraryLoader::new(config.output_dir.clone());
    loader.init()?;

    let mut writer = ShardWriter::new();
    let mut shard_constants: usize = 0;
    let mut shard_idx: u32 = 0;

    // Shards are sealed (in-shard axiom closure run, named) here and buffered,
    // then written after the cross-shard closure pass below. Buffering is
    // required because the cross-shard fixed-point needs every shard's
    // dependency graph in scope at once to resolve by-name dependencies whose
    // defining constant lands in a different shard. See
    // `finalize_library_axiom_profiles`.
    let mut sealed: Vec<SealedShard> = Vec::new();

    for (i, path) in files.iter().enumerate() {
        // Skip files exceeding size limit.
        if config.max_file_size > 0 {
            if let Ok(meta) = std::fs::metadata(path) {
                if meta.len() > config.max_file_size {
                    if config.verbose {
                        eprintln!(
                            "[build_library] skip {} ({} bytes > {} limit)",
                            path.display(),
                            meta.len(),
                            config.max_file_size
                        );
                    }
                    result.files_failed += 1;
                    result.failed_files.push((
                        path.clone(),
                        format!("file too large: {} bytes", meta.len()),
                    ));
                    continue;
                }
            }
        }
        match importer.import_file(path, &mut writer) {
            Ok(stats) => {
                result.files_parsed += 1;
                let added = stats.total as usize;
                shard_constants += added;
                result.total_constants += added;
                result.total_axioms += stats.axiomatized as usize;
                result.total_with_value += stats.kernel_verified as usize;
            }
            Err(e) => {
                result.files_failed += 1;
                result.failed_files.push((path.clone(), e.to_string()));
                continue;
            }
        }

        // Split shard when size limit is exceeded.
        if config.shard_size_limit > 0 && shard_constants >= config.shard_size_limit {
            let name = format!("lean4_{shard_idx:04}");
            seal_shard(
                &mut sealed,
                &mut writer,
                name,
                shard_constants,
                config.verbose,
            );

            shard_constants = 0;
            shard_idx += 1;
        }

        // Progress reporting.
        if config.verbose && (i + 1) % 100 == 0 {
            eprintln!(
                "[build_library] progress: {}/{} files, {} constants, {} failures",
                i + 1,
                files.len(),
                result.total_constants,
                result.files_failed
            );
        }
    }

    // Seal remaining constants.
    if shard_constants > 0 {
        let name = format!("lean4_{shard_idx:04}");
        seal_shard(
            &mut sealed,
            &mut writer,
            name,
            shard_constants,
            config.verbose,
        );
    }

    // Cross-shard closure: union axiom bits across shard boundaries so a
    // constant's profile reflects axioms reachable through dependencies defined
    // in *other* shards (which the per-shard pass necessarily skipped by name).
    let cross_upgraded = finalize_library_axiom_profiles(&mut sealed);
    if config.verbose && cross_upgraded > 0 {
        eprintln!(
            "[build_library] cross-shard closure upgraded {cross_upgraded} constant profiles"
        );
    }

    // Write every sealed shard to disk and register it in the manifest.
    for shard in &sealed {
        loader.write_shard(&shard.writer, &shard.name, false)?;
        result.shards_written += 1;
        if config.verbose {
            eprintln!(
                "[build_library] wrote shard {} ({} constants)",
                shard.name, shard.constant_count
            );
        }
    }

    result.elapsed_ms = start.elapsed().as_millis() as u64;

    if config.verbose {
        eprintln!(
            "[build_library] done: {} files parsed, {} constants, {} shards, {} failures, {}ms",
            result.files_parsed,
            result.total_constants,
            result.shards_written,
            result.files_failed,
            result.elapsed_ms
        );
    }

    Ok(result)
}

/// A shard that has been sealed (in-shard axiom closure run, named) and is
/// buffered awaiting the cross-shard closure pass and the final disk write.
struct SealedShard {
    name: String,
    writer: ShardWriter,
    /// Number of constants contributed by this shard (for verbose logging).
    constant_count: usize,
}

/// Finalize the in-shard axiom closure for `writer`, take ownership of it, and
/// push it onto the sealed-shard buffer (replacing `writer` with a fresh empty
/// one). The caller continues importing into the fresh writer.
fn seal_shard(
    sealed: &mut Vec<SealedShard>,
    writer: &mut ShardWriter,
    name: String,
    constant_count: usize,
    verbose: bool,
) {
    // Close axiom profiles over this shard's in-shard dependency graph before
    // it is frozen, so cross-shard closure starts from exact within-shard
    // profiles.
    writer.finalize_axiom_profiles();
    if verbose {
        eprintln!("[build_library] sealed shard {name} ({constant_count} constants)");
    }
    let finished = std::mem::take(writer);
    sealed.push(SealedShard {
        name,
        writer: finished,
        constant_count,
    });
}

/// Run the library-level cross-shard axiom-profile closure over all sealed
/// shards, in place, and return the number of constant headers upgraded.
///
/// Each shard's headers already carry their exact *within-shard* transitive
/// profile (set by [`seal_shard`]). This step resolves the by-name dependencies
/// whose defining constant lives in a *different* shard, so a constant's profile
/// honestly reflects axioms reachable through any depth of dependency across the
/// whole library. Delegates to
/// [`crate::lean4::olean::axiom_profile::propagate_cross_shard_axiom_profiles`].
fn finalize_library_axiom_profiles(sealed: &mut [SealedShard]) -> usize {
    // Borrow the writers as a contiguous slice for the closure pass.
    let mut writers: Vec<&mut ShardWriter> = sealed.iter_mut().map(|s| &mut s.writer).collect();
    cross_shard_closure_over(&mut writers)
}

/// Run the cross-shard closure over a set of borrowed writers.
///
/// Split out so the closure can be driven both from the buffered multi-shard
/// builder and from tests that construct writers directly.
fn cross_shard_closure_over(writers: &mut [&mut ShardWriter]) -> usize {
    crate::lean4::olean::axiom_profile::propagate_cross_shard_axiom_profiles_borrowed(writers)
}

/// Write a single self-contained shard to disk and register it in the manifest.
///
/// Closes axiom profiles over the shard's in-shard dependency graph first. This
/// path is for standalone shards written outside the buffered multi-shard
/// assembly (e.g. the Coq stdlib shard), which have no cross-shard dependencies
/// to resolve against the Lean shards already on disk; within that single shard
/// the closure is exact.
fn write_shard(
    loader: &LibraryLoader,
    writer: &mut ShardWriter,
    name: &str,
) -> MathverseResult<()> {
    writer.finalize_axiom_profiles();
    loader.write_shard(writer, name, false)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// load_built_library
// ---------------------------------------------------------------------------

/// Load a previously built Mathverse Library from disk.
///
/// Reads the manifest, loads all shards, and builds the in-memory indexes
/// (name lookup, discrimination tree, etc.) with a permissive trust policy.
pub fn load_built_library(output_dir: &Path) -> MathverseResult<MathverseLibrary> {
    let loader = LibraryLoader::new(output_dir.to_path_buf());
    let mut library = loader.load_library(TrustPolicy::permissive())?;

    // If a kernel-verified manifest sits alongside the shards, apply it so the
    // constants Clean's own kernel re-verified carry KernelVerified confidence
    // in-memory — the trust-gated `mathverse use` tactic then accepts them at the
    // top tier. Non-fatal when absent or unreadable.
    let manifest_path = output_dir.join("kernel-verified.json");
    if manifest_path.exists() {
        if let Ok(manifest) =
            crate::verify::kernel_verified_manifest::KernelVerifiedManifest::from_file(
                &manifest_path,
            )
        {
            let upgraded = library.apply_kernel_verified_manifest(&manifest);
            if upgraded > 0 {
                eprintln!(
                    "  Applied kernel-verified manifest: {upgraded} constants -> KernelVerified"
                );
            }
        }
    }

    // If a shipped `MVBIDX01` baseline novelty index sits alongside the shards,
    // open it (fail-closed validation) so a downloaded corpus is queryable
    // without rescanning all constants. Discovery + validation only here; the
    // in-memory query wiring onto `MathverseLibrary` is a follow-up. Non-fatal
    // when absent or unreadable — the index is an accelerator, not a gate.
    let index_path = output_dir.join(crate::release::BASELINE_INDEX_FILENAME);
    if index_path.exists() {
        match crate::graduate::BaselineIndex::load(&index_path) {
            Ok(index) => eprintln!(
                "  Baseline index present: {} ({} names, {} statement hashes, {} semantic)",
                crate::release::BASELINE_INDEX_FILENAME,
                index.name_count(),
                index.hash_count(),
                index.semantic_count()
            ),
            Err(e) => eprintln!(
                "  Baseline index present but unreadable ({}): {e}",
                index_path.display()
            ),
        }
    }

    Ok(library)
}

// ---------------------------------------------------------------------------
// build_combined_library — Lean 4 + Coq combined
// ---------------------------------------------------------------------------

/// Build a combined Mathverse Library from Lean 4 .olean files and Coq stdlib.
///
/// Imports Lean 4 constants from the toolchain, then imports Coq constants
/// from the extracted Print output, and writes everything to disk.
pub fn build_combined_library(
    lean_lib_dir: &Path,
    coq_extract_path: Option<&Path>,
    output_dir: &Path,
    max_file_size: u64,
    verbose: bool,
) -> MathverseResult<CombinedBuildResult> {
    let start = Instant::now();

    // Phase 1: Import Lean 4
    let lean_config = BuildConfig {
        lean_lib_dir: lean_lib_dir.to_path_buf(),
        output_dir: output_dir.to_path_buf(),
        modules: vec![],
        shard_size_limit: 10_000,
        max_file_size,
        verbose,
    };
    let lean_result = build_lean4_library(&lean_config)?;

    if verbose {
        eprintln!(
            "[combined] Lean 4: {} constants from {} files",
            lean_result.total_constants, lean_result.files_parsed
        );
    }

    // Phase 2: Import Coq stdlib
    let mut coq_constants = 0usize;
    if let Some(coq_path) = coq_extract_path {
        if coq_path.exists() {
            let text =
                std::fs::read_to_string(coq_path).map_err(crate::error::MathverseError::Io)?;

            let mut writer = ShardWriter::new();
            let stats = crate::coq::print_parser::import_coq_print_output(&text, &mut writer)?;
            coq_constants = (stats.inductives + stats.definitions + stats.axioms) as usize;

            let loader = LibraryLoader::new(output_dir.to_path_buf());
            write_shard(&loader, &mut writer, "coq_stdlib")?;

            if verbose {
                eprintln!(
                    "[combined] Coq: {} constants imported from {}",
                    coq_constants,
                    coq_path.display()
                );
            }
        }
    }

    let elapsed = start.elapsed().as_millis() as u64;

    if verbose {
        eprintln!(
            "[combined] done: {} Lean4 + {} Coq = {} total constants, {}ms",
            lean_result.total_constants,
            coq_constants,
            lean_result.total_constants + coq_constants,
            elapsed
        );
    }

    Ok(CombinedBuildResult {
        lean4: lean_result,
        coq_constants,
        total_constants: 0, // filled after load
        elapsed_ms: elapsed,
    })
}

/// Result of a combined Lean 4 + Coq library build.
#[derive(Clone, Debug)]
pub struct CombinedBuildResult {
    pub lean4: BuildResult,
    pub coq_constants: usize,
    pub total_constants: usize,
    pub elapsed_ms: u64,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search::MathverseSearch;

    /// Path to the Lean 4 v4.13.0 toolchain library.
    const LEAN4_LIB: &str = concat!(
        env!("HOME"),
        "/.elan/toolchains/leanprover--lean4---v4.13.0/lib/lean"
    );

    fn lean4_lib_available() -> bool {
        Path::new(LEAN4_LIB).exists()
    }

    // -----------------------------------------------------------------------
    // Builder-level cross-shard closure (no toolchain required)
    //
    // These drive the *exact* seal -> cross-shard finalize sequence the builder
    // runs, using synthetic shards, so they prove the wiring without depending
    // on a Lean toolchain being installed.
    // -----------------------------------------------------------------------

    use clean_olean::expr::ParsedExpr;
    use clean_olean::level::ParsedLevel;
    use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

    fn mock_module(constants: Vec<ParsedConstant>) -> ParsedModule {
        ParsedModule {
            const_names: constants.iter().map(|c| c.name.clone()).collect(),
            constants,
            extra_const_names: Vec::new(),
            imports: Vec::new(),
            entries: Vec::new(),
            clean_payload: None,
        }
    }

    fn axiom_constant(name: &str) -> ParsedConstant {
        ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: name.to_string(),
            kind: ConstantKind::Axiom,
            level_params: Vec::new(),
            type_: None,
            value: None,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        }
    }

    fn constant_with_deps(name: &str, kind: ConstantKind, dep_names: &[&str]) -> ParsedConstant {
        let mut expr: ParsedExpr = ParsedExpr::Sort(ParsedLevel::Zero);
        for dep in dep_names {
            expr = ParsedExpr::App(
                Box::new(ParsedExpr::Const((*dep).to_string(), vec![])),
                Box::new(expr),
            );
        }
        ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: name.to_string(),
            kind,
            level_params: Vec::new(),
            type_: Some(expr),
            value: None,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        }
    }

    fn profile_in_shard(shard: &SealedShard, name: &str) -> crate::types::AxiomProfile {
        let mut buf = Vec::new();
        shard.writer.write(&mut buf).expect("write should succeed");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read should succeed");
        reader
            .constants
            .iter()
            .find(|c| reader.strings.get(c.name_idx as usize).map(String::as_str) == Some(name))
            .map(|c| c.axiom_profile)
            .unwrap_or_else(|| panic!("constant {name} not found in shard {}", shard.name))
    }

    #[test]
    fn test_builder_cross_shard_closure_taints_downstream_shard() {
        // Mirror the builder split: shard A holds the axiom + a tainted def,
        // shard B holds a theorem that depends on the def by name. This is the
        // dependency the within-shard pass cannot resolve.
        let module_a = mock_module(vec![
            axiom_constant("Classical.choice"),
            constant_with_deps("taint", ConstantKind::Definition, &["Classical.choice"]),
        ]);
        let module_b = mock_module(vec![constant_with_deps(
            "downstream",
            ConstantKind::Theorem,
            &["taint"],
        )]);

        // Seal each shard exactly as the builder does (in-shard closure + buffer).
        let mut sealed: Vec<SealedShard> = Vec::new();
        let mut writer_a = ShardWriter::new();
        crate::lean4::olean::alpha::import_module(&module_a, &mut writer_a)
            .expect("import A should succeed");
        seal_shard(
            &mut sealed,
            &mut writer_a,
            "lean4_0000".to_string(),
            2,
            false,
        );

        let mut writer_b = ShardWriter::new();
        crate::lean4::olean::alpha::import_module(&module_b, &mut writer_b)
            .expect("import B should succeed");
        seal_shard(
            &mut sealed,
            &mut writer_b,
            "lean4_0001".to_string(),
            1,
            false,
        );

        // REGRESSION: after sealing (within-shard closure only), `downstream`
        // in shard B is still reported pure.
        assert!(
            profile_in_shard(&sealed[1], "downstream").is_pure(),
            "pre-cross-shard: downstream theorem in shard B reported pure (the gap)"
        );

        // Run the builder's cross-shard finalization.
        let upgraded = finalize_library_axiom_profiles(&mut sealed);

        // `downstream` must now honestly carry CHOICE.
        let after = profile_in_shard(&sealed[1], "downstream");
        assert!(
            after.has(crate::types::AxiomProfile::CHOICE),
            "post-cross-shard: downstream must carry CHOICE through its cross-shard dep"
        );
        assert!(!after.is_pure(), "downstream is no longer pure");
        assert!(upgraded >= 1, "cross-shard pass should upgrade downstream");
    }

    #[test]
    fn test_build_init_module() {
        if !lean4_lib_available() {
            eprintln!("SKIP: Lean 4 toolchain not found at {LEAN4_LIB}");
            return;
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let config = BuildConfig {
            lean_lib_dir: PathBuf::from(LEAN4_LIB),
            output_dir: tmp.path().join("mathverse"),
            modules: vec!["Init".to_string()],
            shard_size_limit: 5000,
            // Skip files >2.5MB to avoid slow parsing of compiler internals
            // (Init/Meta.olean=3.4MB, Init/Prelude.olean=3.2MB).
            // Core types (Bool, Nat) are in Init/Core.olean (1.9MB) — included.
            max_file_size: 2_500_000,
            verbose: true,
        };

        let result = build_lean4_library(&config).expect("build should succeed");

        eprintln!("--- Init module build results ---");
        eprintln!("  total_files:     {}", result.total_files);
        eprintln!("  files_parsed:    {}", result.files_parsed);
        eprintln!("  files_failed:    {}", result.files_failed);
        eprintln!("  total_constants: {}", result.total_constants);
        eprintln!("  total_axioms:    {}", result.total_axioms);
        eprintln!("  total_with_value:{}", result.total_with_value);
        eprintln!("  shards_written:  {}", result.shards_written);
        eprintln!("  elapsed_ms:      {}", result.elapsed_ms);

        // Print first 10 failures for diagnostics.
        if !result.failed_files.is_empty() {
            eprintln!("  first failures:");
            for (path, err) in result.failed_files.iter().take(10) {
                eprintln!("    {}: {}", path.display(), err);
            }
        }

        // Init has ~207 files; some large ones skipped.
        assert!(
            result.files_parsed > 150,
            "expected >150 parsed files, got {}",
            result.files_parsed
        );
        assert!(
            result.total_constants > 0,
            "expected >0 constants, got {}",
            result.total_constants
        );
        assert!(
            result.shards_written > 0,
            "expected >0 shards, got {}",
            result.shards_written
        );

        // Load the built library and verify it works.
        let library = load_built_library(&config.output_dir).expect("load should succeed");

        // Verify the library has constants.
        let n = library.constant_count();
        assert!(n > 1000, "expected >1000 constants in library, got {n}");

        // Print some sample names for diagnostics.
        let mut sample_names = Vec::new();
        for i in 0..std::cmp::min(20, n as u32) {
            if let Some(name) = library.get_name(i) {
                sample_names.push(name.to_string());
            }
        }
        eprintln!(
            "  sample constants: {:?}",
            &sample_names[..std::cmp::min(10, sample_names.len())]
        );

        // Verify name lookup works for at least one constant.
        if let Some(first) = sample_names.first() {
            assert!(
                library.lookup_name(first).is_some(),
                "lookup_name for first constant should work"
            );
        }
    }

    #[test]
    fn test_build_all_modules() {
        if !lean4_lib_available() {
            eprintln!("SKIP: Lean 4 toolchain not found at {LEAN4_LIB}");
            return;
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let config = BuildConfig {
            lean_lib_dir: PathBuf::from(LEAN4_LIB),
            output_dir: tmp.path().join("mathverse"),
            modules: vec![], // all modules
            shard_size_limit: 10_000,
            // Skip files >2.5MB (only Init/Meta, Init/Prelude, and Lemma files)
            max_file_size: 2_500_000,
            verbose: true,
        };

        let result = build_lean4_library(&config).expect("build should succeed");

        eprintln!("--- All modules build results ---");
        eprintln!("  total_files:     {}", result.total_files);
        eprintln!("  files_parsed:    {}", result.files_parsed);
        eprintln!("  files_failed:    {}", result.files_failed);
        eprintln!("  total_constants: {}", result.total_constants);
        eprintln!("  total_axioms:    {}", result.total_axioms);
        eprintln!("  total_with_value:{}", result.total_with_value);
        eprintln!("  shards_written:  {}", result.shards_written);
        eprintln!("  elapsed_ms:      {}", result.elapsed_ms);

        if !result.failed_files.is_empty() {
            eprintln!("  first failures:");
            for (path, err) in result.failed_files.iter().take(10) {
                eprintln!("    {}: {}", path.display(), err);
            }
        }

        // Expect all 1,138 files discovered (Init=207 + Std=145 + Lean=655 + Lake=126).
        assert!(
            result.total_files >= 1100,
            "expected >=1100 total files, got {}",
            result.total_files
        );
        // Many parsed; some large ones skipped.
        assert!(
            result.files_parsed > 500,
            "expected >500 parsed files, got {}",
            result.files_parsed
        );
        assert!(
            result.total_constants > 0,
            "expected >0 constants, got {}",
            result.total_constants
        );
        assert!(
            result.shards_written > 0,
            "expected >0 shards, got {}",
            result.shards_written
        );

        // Load and verify the full library.
        let library = load_built_library(&config.output_dir).expect("load should succeed");

        let n = library.constant_count();
        assert!(
            n > 10_000,
            "expected >10K constants in full library, got {n}"
        );

        eprintln!("  library constants: {n}");

        // Verify name lookup works.
        let mut found_any = false;
        for i in 0..std::cmp::min(50, n as u32) {
            if let Some(name) = library.get_name(i) {
                if library.lookup_name(name).is_some() {
                    found_any = true;
                    break;
                }
            }
        }
        assert!(
            found_any,
            "should be able to look up at least one constant by name"
        );
    }

    #[test]
    fn test_build_combined_library() {
        if !lean4_lib_available() {
            eprintln!("SKIP: Lean 4 toolchain not found at {LEAN4_LIB}");
            return;
        }

        let coq_extract = std::path::PathBuf::from("/tmp/coq_stdlib_extract.txt");
        let coq_path = if coq_extract.exists() {
            Some(coq_extract.as_path())
        } else {
            eprintln!("NOTE: Coq extract not found, building Lean 4 only");
            None
        };

        let tmp = tempfile::tempdir().expect("tempdir");
        let result = super::build_combined_library(
            Path::new(LEAN4_LIB),
            coq_path,
            &tmp.path().join("mathverse"),
            2_500_000,
            true,
        )
        .expect("combined build should succeed");

        eprintln!("--- Combined build results ---");
        eprintln!("  Lean 4 constants: {}", result.lean4.total_constants);
        eprintln!("  Coq constants:    {}", result.coq_constants);
        eprintln!("  elapsed_ms:       {}", result.elapsed_ms);

        assert!(
            result.lean4.total_constants > 100_000,
            "expected >100K Lean 4 constants, got {}",
            result.lean4.total_constants
        );

        if coq_path.is_some() {
            assert!(
                result.coq_constants > 30,
                "expected >30 Coq constants, got {}",
                result.coq_constants
            );
        }
    }
}
