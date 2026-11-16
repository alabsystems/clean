// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean .olean file parser
//!
//! This crate parses Lean 4 compiled `.olean` files and loads them
//! into the clean kernel environment.
//!
//! # .olean File Format (Lean 4 v4.x)
//!
//! The file consists of a fixed header followed by a compacted region:
//!
//! | Offset | Size | Field      | Description                           |
//! |--------|------|------------|---------------------------------------|
//! | 0      | 5    | magic      | "olean" ASCII bytes                   |
//! | 5      | 1    | version    | Format version (currently 1)          |
//! | 6      | 42   | git_hash   | Build git hash, null-padded           |
//! | 48     | 8    | base_addr  | Memory address for mmap (little-endian) |
//! | 56     | n    | data       | Compacted region (serialized objects) |
//!
//! The compacted region is a memory dump of Lean 4 runtime objects with
//! pointer fixups for relocation. It uses a sharing-optimized format.

// Suppress unused-crate warnings: `constant_time_eq` is listed as a direct
// dependency in Cargo.toml solely to pin it to `=0.4.2` (transitive via
// `blake3`). Pinning is required because 0.4.3 bumps MSRV to 1.95 while the
// local toolchain is 1.94.1. `Cargo.lock` is tracked and public/release lanes
// run with `--locked`; this explicit manifest pin keeps deliberate lockfile
// refreshes from selecting 0.4.3 until the toolchain moves. See issue #3535.
use constant_time_eq as _;

#[path = "../lean_toolchain.rs"]
mod lean_toolchain;

pub mod bootstrap_verify;
#[cfg(feature = "cli")]
pub mod cli;
pub mod coq_import;
pub mod dep_graph;
pub mod error;
pub mod export;
pub mod expr;
pub mod fixed_cohort;
pub mod header;
pub mod import;
pub mod import_reverification_metric;
pub mod semr_bool_body;
mod semr_model;
pub use semr_model::SemrModelRefusal;
pub mod semr_native_execution;
pub mod semr_scalar;
// The compiled-IR decoder: `clean olean ir-census` (`cli`) and `.olean`
// import's late-binding judgement read it.
pub(crate) mod lean_ir;
pub mod level;
pub mod metamath;
pub mod module;
pub mod ndjson;
pub mod olean_level;
pub mod payload;
pub mod payload_entry; // KR1 increment 3: a Clean payload through the reference entry (R143)
pub mod recheck_closed;
pub mod region;
pub mod replay_families;
// `clean olean replay`'s engine; its only production caller is the CLI verb.
pub mod replay_census;
#[cfg(any(feature = "cli", test))]
mod replay_module;
pub mod replay_order;
#[cfg(any(test, feature = "test-support"))]
pub mod test_support;
pub mod toolchain_identity;
pub mod verify_batch;
pub mod verify_batch_full;
pub mod verify_cache;
pub mod verify_parallel;
pub mod verify_report;
#[cfg(test)]
mod verify_report_tests;
pub(crate) mod world;

pub use bootstrap_verify::{
    categorize_failures, format_report, verify_bootstrap_lane, verify_bootstrap_lane_in_env,
    verify_init_bootstrap, BootstrapFailure, BootstrapVerifyReport, INIT_BOOTSTRAP_MODULES,
};
pub use error::{OleanError, OleanResult};
pub use expr::{expr_tags, BigNat, ParsedBinderInfo, ParsedExpr, ParsedLiteral};
pub use header::{OleanHeader, HEADER_SIZE, MAGIC, VERSION};
pub use import::{
    active_stdlib_toolchain, add_global_instance_entry, alias_resolvable_toolchain_versions,
    clean_payload_imports_required, convert_parsed_constant_to_const_info,
    convert_parsed_constant_to_declaration, convert_parsed_constant_to_type_stub,
    default_fn_binder_idx, default_search_paths, default_toolchain_versions, discover_olean_parts,
    find_module_olean, has_global_instance_entry, import_world_for_file, lean_accepts_restatement,
    load_module_with_deps, load_module_with_deps_bounded, load_module_with_deps_bounded_shared,
    load_module_with_deps_bounded_shared_with_policy, load_module_with_deps_cached,
    load_module_with_deps_cached_guarded, load_module_with_deps_parallel,
    load_module_with_deps_replaying_module, load_module_with_deps_shared,
    load_module_with_deps_shared_with_policy, load_module_with_deps_with_import_policy,
    load_modules_with_deps, load_modules_with_deps_checked,
    load_modules_with_deps_with_import_policy, load_olean_file, load_olean_file_with_import_policy,
    load_parsed_module, load_parsed_module_at_index,
    load_parsed_module_at_index_with_import_policy, load_parsed_module_with_import_policy,
    load_typed_module_with_deps_bounded, load_typed_module_with_deps_bounded_shared,
    load_typed_module_with_deps_cached, load_typed_module_with_deps_parallel,
    parse_imports_and_const_names_only, parse_imports_only, parse_module, parse_module_file,
    parse_module_incremental, parse_module_incremental_types_only, parse_module_parts,
    parse_module_types_only, parse_typed_imports, read_artifact, require_clean_payload_imports,
    resolve_typed_module_path, scoped_instance_idx, search_paths_in_world, source_world_for_file,
    source_world_for_snapshot, source_world_of, stored_family_members,
    toolchain_versions_from_search_paths, type_binder_name_idx, type_binder_names,
    typed_module_rel_path, ActiveStdlibToolchain, ArtifactDepth, ArtifactRead, CapturedModuleBytes,
    ConstantConvertSession, DefaultFnBinderState, DeferredRecursor, DeferredRecursorStatus,
    ExprSharingStats, ImportError, ImportKinds, ImportWorld, ImportWorldRefusal, LeanWorldScope,
    LoadSummary, ModuleCache, OleanImportPolicy, ScopedInstanceState, SearchPathBuilder,
    SkippedConstant, SourceWorldDecision, SourceWorldRefusal, StoredFamilyMembers,
    TypeBinderNameState, TypedImport, TypedImportFlags, UnpinnedOleanImportPolicy,
};
pub use import::{load_modules_with_deps_checked_with_limits, ModuleCaptureLimits};
pub use import_reverification_metric::{
    compute_import_reverification_metric, ImportReverificationMetric, MetricError,
    METRIC_SCHEMA_VERSION,
};
pub use recheck_closed::reference_base::{reference_base_closed, ReferenceBase};
pub use recheck_closed::{
    promote_origins_after_closed_recheck, recheck_closed, ClosedRecheck, ClosedRecheckOptions,
    ClosedRecheckRefusal, ClosedRecheckReport, ImportedConeGate, ImportedConeVerdict, RecheckLevel,
};

// Domain-prefixed alias for collision-free imports
pub use import::runtime::{
    extract_olean_runtime_parts, RuntimeBody, RuntimeDeclaration, RuntimeDeclarationRow,
    RuntimeFamily, RuntimeOleanInput, RuntimeOleanPart, RuntimePartExtraction, RuntimePartIdentity,
    RuntimeRecursorRule,
};
pub use import::ImportError as OleanImportError;
pub use level::{level_tags, ParsedLevel};
pub use module::{
    ConstantKind, ConstructorValData, DefinitionSafety, InductiveValData, OLeanLevel,
    ParsedAttrKind, ParsedClassEntry, ParsedConstant, ParsedExtension, ParsedExtensionEntry,
    ParsedExtensionEntryData, ParsedImport, ParsedInstanceEntry, ParsedModule, ParsedModulePart,
    ParsedQuotKind, ParsedSimpEntry, ParsedSimpEntryKind, RecursorRuleData, RecursorValData,
    RootAnalysis,
};
pub use payload::{
    decode_clean_payload, encode_clean_payload, CleanPayload, CLEAN_PAYLOAD_MAGIC,
    CLEAN_PAYLOAD_VERSION,
};

/// Parse an .olean file header from bytes
///
/// # REQUIRES
/// - `bytes.len() >= 6` (minimum: magic + version byte)
///
/// # ENSURES
/// - On success, returns `OleanHeader` with valid magic, version, git hash
/// - On error, returns specific `OleanError` variant
/// - Delegates to `OleanHeader::parse()` - see that function for full contract
///
/// # Example
///
/// ```rust,no_run
/// use clean_olean::{parse_header, OleanResult};
///
/// fn main() -> OleanResult<()> {
///     let bytes = std::fs::read("Init.Prelude.olean")?;
///     let header = parse_header(&bytes)?;
///     println!("Git hash: {:?}", header.git_hash);
///     Ok(())
/// }
/// ```
pub fn parse_header(bytes: &[u8]) -> OleanResult<OleanHeader> {
    OleanHeader::parse(bytes)
}

/// Read and parse the header of the `.olean` part at `path`: the first 88
/// bytes, which hold a v2 header whole and a v1 header (56 bytes) with room
/// to spare.
///
/// # Errors
///
/// The file cannot be read, or its header does not parse
/// ([`OleanHeader::parse`]).
pub fn read_olean_header(path: impl AsRef<std::path::Path>) -> OleanResult<OleanHeader> {
    use std::io::Read as _;
    let mut bytes = Vec::with_capacity(header::HEADER_SIZE_V2);
    std::fs::File::open(path)?
        .take(header::HEADER_SIZE_V2 as u64)
        .read_to_end(&mut bytes)?;
    OleanHeader::parse(&bytes)
}

// ---------------------------------------------------------------------------
// Lean worlds (docs/DECISIONS.md R38, R81): every Lean-written `.olean` part
// an environment reads is of one world of `crates/clean-olean/lean_worlds.tsv`.
// A loader that reads parts itself holds a `LeanWorldScope` to the same rule.
// ---------------------------------------------------------------------------

/// Declare that `env` reads the Lean world `world` (a row of
/// `crates/clean-olean/lean_worlds.tsv`, e.g. `v4.13.0`), before any part of
/// it is loaded. A Measured world's parts load only into an environment
/// that declared it; the Oracle, Historical and Frontend-only worlds load
/// without a declaration, and declaring one only fixes the environment to it.
///
/// # Errors
///
/// [`ImportError::UnknownLeanWorld`] for a world no row names or a Canary
/// world; [`ImportError::MixedLeanWorlds`] when `env` already reads another
/// world.
pub fn declare_environment_world(
    env: &mut clean_kernel::env::Environment,
    world: &str,
) -> Result<(), ImportError> {
    import::declare_world(env, world)
}

/// The Lean world `env` reads: bound by the first Lean-written part loaded
/// into it, or by [`declare_environment_world`]. `None` while it holds no
/// Lean part (Clean-written parts are of no world).
#[must_use]
pub fn environment_world(env: &clean_kernel::env::Environment) -> Option<&'static str> {
    import::bound_world(env)
}

/// The Lean world of the `.olean` part at `path`, as an environment that
/// declared nothing reads it: `Some(world)` for a Lean-written part of a
/// world such an environment loads, `None` for a part Clean's exporter wrote.
///
/// # Errors
///
/// The file cannot be read or parsed, or its world is refused
/// ([`ImportError::UnsupportedLeanWorld`]).
pub fn lean_world_of_olean_file(
    path: impl AsRef<std::path::Path>,
) -> Result<Option<&'static str>, ImportError> {
    let path = path.as_ref();
    let bytes = std::fs::read(path).map_err(|source| ImportError::FileUnreadable {
        path: path.to_path_buf(),
        source,
    })?;
    let label = path.display().to_string();
    import::part_world(&label, &bytes)
}

impl ImportError {
    /// A refusal of an `.olean` part's Lean world (R38, R81). No import
    /// policy may stand anything in for the module it refused: there is no
    /// warn-and-continue mode.
    #[must_use]
    pub fn is_world_refusal(&self) -> bool {
        matches!(
            self,
            Self::UnsupportedLeanWorld { .. }
                | Self::MixedLeanWorlds { .. }
                | Self::UnknownLeanWorld { .. }
        )
    }
}

pub use export::OleanExporter;
pub use region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};

/// Resolve the Lean standard library from this checkout's exact
/// `lean-toolchain` pin.
///
/// The lookup is anchored at the crate manifest rather than the process
/// current directory. It returns `None` instead of falling back to an
/// arbitrary installed Lean ABI.
#[must_use]
pub fn pinned_lean_lib_path() -> Option<std::path::PathBuf> {
    if let Some(compiled) = option_env!("CLEAN_OLEAN_PINNED_LEAN_LIB") {
        let path = std::path::PathBuf::from(compiled);
        if path.join("Init/Prelude.olean").is_file() {
            return Some(path);
        }
    }
    lean_toolchain::resolve_pinned_lean(std::path::Path::new(env!("CARGO_MANIFEST_DIR")))
        .ok()
        .map(|resolved| resolved.lib_path)
}

/// Resolve an INSTALLED Lean standard library by its exact, fully-qualified
/// toolchain name (`leanprover/lean4:v4.8.0`), for a toolchain Clean measures
/// against besides the workspace pin — trust-ir's Lean 4.8.0 semantics are
/// one (`crates/clean-olean/tests/native_fold_canon_lean_v4_8_0.rs`).
///
/// Looks only for that toolchain's own elan directory under `$ELAN_HOME` and
/// `~/.elan` (the roots [`pinned_lean_lib_path`] searches). It never runs
/// `elan` — which would install a missing toolchain as a side effect — and it
/// never answers with a different version: `None` means exactly that
/// toolchain is not installed here.
#[must_use]
pub fn installed_lean_lib_path(toolchain: &str) -> Option<std::path::PathBuf> {
    lean_toolchain::installed_lean_lib(toolchain)
}

/// The `lean` executable of the exact toolchain [`pinned_lean_lib_path`]
/// resolves: `<toolchain>/lib/lean` → `<toolchain>/bin/lean`, returned only
/// when that file exists.
///
/// This is the only in-tree Lean locator that honours the workspace pin; the
/// PATH / `~/.elan/bin/lean` lookups elsewhere may answer with any installed
/// version. Measured 2026-09-15 on this checkout: `lib/lean` is
/// `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean`, so this
/// returns `…/leanprover--lean4---v4.30.0-rc2/bin/lean`, whose `--version` is
/// `Lean (version 4.30.0-rc2, …, commit 3dc1a088b6d2…, Release)`.
#[must_use]
pub fn pinned_lean_binary() -> Option<std::path::PathBuf> {
    let lib = pinned_lean_lib_path()?;
    let binary = lib.parent()?.parent()?.join("bin").join("lean");
    binary.is_file().then_some(binary)
}

/// Return the exact repository-pinned Lean standard library or an actionable
/// error. Authority-bearing integration gates should use this API rather than
/// silently accepting a different installed toolchain.
///
/// # Errors
///
/// Returns an error when the workspace pin is invalid or its exact elan
/// toolchain is unavailable.
pub fn require_pinned_lean_lib_path() -> Result<std::path::PathBuf, String> {
    pinned_lean_lib_path().ok_or_else(|| {
        let pin = option_env!("CLEAN_OLEAN_PINNED_LEAN_TOOLCHAIN")
            .map(str::to_string)
            .or_else(|| {
                std::env::var(lean_toolchain::PINNED_LEAN_TOOLCHAIN_ENV)
                    .ok()
                    .filter(|value| !value.is_empty())
            })
            .unwrap_or_else(|| {
                "the toolchain named by the workspace lean-toolchain file".to_string()
            });
        format!("repository-pinned Lean toolchain is unavailable: {pin}")
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn get_lean_lib_path() -> Option<PathBuf> {
        pinned_lean_lib_path()
    }

    #[test]
    fn test_parse_init_prelude_header() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            eprintln!("Skipping test: Init/Prelude.olean not found at {prelude_path:?}");
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = parse_header(&bytes).expect("Failed to parse header");

        // Verify magic
        assert_eq!(header.magic, *b"olean");

        assert!(
            matches!(header.version, VERSION | header::VERSION_V2),
            "unexpected .olean header version: {}",
            header.version
        );

        // Git hash should be 40 hex characters
        let hash_str = header.git_hash_str();
        assert!(
            hash_str.chars().all(|c| c.is_ascii_hexdigit()),
            "Git hash should be hex: {hash_str}"
        );

        // Base address should be non-zero
        assert!(header.base_addr != 0, "Base address should be non-zero");

        println!("Parsed header successfully:");
        println!("  Magic: {:?}", std::str::from_utf8(&header.magic));
        println!("  Version: {}", header.version);
        println!("  Git hash: {hash_str}");
        println!("  Base addr: 0x{:x}", header.base_addr);
        let header_size = match header.version {
            VERSION => HEADER_SIZE,
            header::VERSION_V2 => header::HEADER_SIZE_V2,
            _ => HEADER_SIZE,
        };
        println!(
            "  Data size: {} bytes",
            bytes.len().saturating_sub(header_size)
        );
    }

    #[test]
    fn test_parse_multiple_oleans() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let mut count = 0;
        let mut total_size = 0usize;

        // Test a few different .olean files
        let test_files = ["Init/Prelude.olean", "Init/Core.olean", "Init/Coe.olean"];

        for file in test_files {
            let path = lib_path.join(file);
            if !path.exists() {
                continue;
            }

            let bytes = std::fs::read(&path).expect("Failed to read file");
            let header = parse_header(&bytes).expect("Failed to parse header");

            assert_eq!(header.magic, *b"olean");
            assert!(
                matches!(header.version, VERSION | header::VERSION_V2),
                "unexpected .olean header version: {}",
                header.version
            );

            count += 1;
            total_size += bytes.len();
        }

        println!("Parsed {count} .olean files, total {total_size} bytes");
    }

    #[test]
    fn test_find_names_in_prelude() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            eprintln!("Skipping test: Init/Prelude.olean not found at {prelude_path:?}");
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = parse_header(&bytes).expect("Failed to parse header");

        // Create compacted region from full file
        let region = CompactedRegion::new(&bytes, header.base_addr);

        // Find all names
        let names = region.find_all_names();
        println!("Found {} Name objects in Init/Prelude.olean", names.len());

        // Should find many names
        assert!(
            names.len() > 100,
            "Expected > 100 names, got {}",
            names.len()
        );

        // Should find some well-known names
        let name_set: std::collections::HashSet<_> =
            names.iter().map(|(_, n)| n.as_str()).collect();

        // Print first 30 names for debugging
        println!("First 30 names:");
        for (off, name) in names.iter().take(30) {
            println!("  {off}: {name}");
        }

        // Check for expected names (these should exist in Prelude)
        let expected = ["Nat", "Bool", "List", "String", "Prop"];
        for exp in expected {
            if name_set.contains(exp) {
                println!("Found expected name: {exp}");
            }
        }
    }

    #[test]
    fn test_read_specific_name() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = parse_header(&bytes).expect("Failed to parse header");
        let region = CompactedRegion::new(&bytes, header.base_addr);

        // Find where "Nat" string object is by searching for the pattern
        // The string "Nat" should be in a String object at some offset
        let names = region.find_all_names();
        let nat_names: Vec<_> = names.iter().filter(|(_, n)| n == "Nat").collect();

        if nat_names.is_empty() {
            println!("'Nat' name not found - checking available names...");
        } else {
            println!("Found 'Nat' name at offsets: {nat_names:?}");
        }
    }

    #[test]
    fn test_parse_imports_only() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        // Init.Core should import at least one Init.* module.
        let core_path = lib_path.join("Init/Core.olean");
        if !core_path.exists() {
            eprintln!("Skipping test: Init/Core.olean not found");
            return;
        }

        let bytes = std::fs::read(&core_path).expect("Failed to read file");

        // Test fast parse_imports_only
        let imports_fast = parse_imports_only(&bytes).expect("Failed to parse imports");

        // Also parse full module and compare
        let full_module = parse_module(&bytes).expect("Failed to parse module");

        // Both should have same imports
        assert_eq!(
            imports_fast.len(),
            full_module.imports.len(),
            "Import counts should match"
        );

        // Sanity: should include Init.* imports
        let import_names: Vec<_> = imports_fast
            .iter()
            .map(|i| i.module_name.as_str())
            .collect();
        println!("Init.Core imports: {import_names:?}");

        assert!(
            import_names.iter().any(|m| m.starts_with("Init.")),
            "Init.Core should import at least one Init.* module"
        );

        // Verify imports match between fast and full parse
        for (fast_imp, full_imp) in imports_fast.iter().zip(full_module.imports.iter()) {
            assert_eq!(
                fast_imp.module_name, full_imp.module_name,
                "Import names should match"
            );
        }

        println!(
            "parse_imports_only works correctly - {} imports",
            imports_fast.len()
        );
    }

    #[test]
    fn test_parse_imports_only_performance() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        // Test with Init.Meta which has many imports
        let meta_path = lib_path.join("Init/Meta.olean");
        if !meta_path.exists() {
            eprintln!("Skipping test: Init/Meta.olean not found");
            return;
        }

        let bytes = std::fs::read(&meta_path).expect("Failed to read file");

        // Time fast path
        let start = std::time::Instant::now();
        for _ in 0..10 {
            let _ = parse_imports_only(&bytes).unwrap();
        }
        let fast_time = start.elapsed() / 10;

        // Time full parse
        let start = std::time::Instant::now();
        for _ in 0..10 {
            let _ = parse_module(&bytes).unwrap();
        }
        let full_time = start.elapsed() / 10;

        let speedup = full_time.as_secs_f64() / fast_time.as_secs_f64();

        println!("\n=== parse_imports_only Performance ===");
        println!("Fast path (imports only): {fast_time:?}");
        println!("Full parse:               {full_time:?}");
        println!("Speedup:                  {speedup:.1}x");

        // Fast path should be significantly faster
        assert!(
            speedup > 2.0,
            "parse_imports_only should be at least 2x faster than full parse, got {speedup:.1}x"
        );
    }

    // =========================================================================
    // OLeanLevel Tests
    // =========================================================================

    #[test]
    fn test_olean_level_default() {
        let level: OLeanLevel = Default::default();
        assert_eq!(level, OLeanLevel::Exported);
    }

    #[test]
    fn test_olean_level_display() {
        assert_eq!(format!("{}", OLeanLevel::Exported), "exported");
        assert_eq!(format!("{}", OLeanLevel::Server), "server");
        assert_eq!(format!("{}", OLeanLevel::Private), "private");
    }

    #[test]
    fn test_olean_level_file_suffix() {
        assert_eq!(OLeanLevel::Exported.file_suffix(), "");
        assert_eq!(OLeanLevel::Server.file_suffix(), ".server");
        assert_eq!(OLeanLevel::Private.file_suffix(), ".private");
    }

    #[test]
    fn test_olean_level_all_order() {
        let all = OLeanLevel::all();
        assert_eq!(all.len(), 3);
        assert_eq!(all[0], OLeanLevel::Exported);
        assert_eq!(all[1], OLeanLevel::Server);
        assert_eq!(all[2], OLeanLevel::Private);
    }

    #[test]
    fn test_olean_level_from_path_exported() {
        let path = PathBuf::from("Init/Core.olean");
        let result = OLeanLevel::from_path(&path);
        let (level, base) = result.expect("should parse .olean as Exported level");
        assert_eq!(level, OLeanLevel::Exported);
        assert_eq!(base, path);
    }

    #[test]
    fn test_olean_level_from_path_server() {
        let path = PathBuf::from("Init/Core.olean.server");
        let result = OLeanLevel::from_path(&path);
        let (level, base) = result.expect("should parse .olean.server as Server level");
        assert_eq!(level, OLeanLevel::Server);
        assert_eq!(base, PathBuf::from("Init/Core.olean"));
    }

    #[test]
    fn test_olean_level_from_path_private() {
        let path = PathBuf::from("Init/Core.olean.private");
        let result = OLeanLevel::from_path(&path);
        let (level, base) = result.expect("should parse .olean.private as Private level");
        assert_eq!(level, OLeanLevel::Private);
        assert_eq!(base, PathBuf::from("Init/Core.olean"));
    }

    #[test]
    fn test_olean_level_from_path_invalid() {
        let path = PathBuf::from("Init/Core.lean");
        let result = OLeanLevel::from_path(&path);
        assert!(
            result.is_none(),
            ".lean extension should not parse as OLeanLevel"
        );
    }
}
