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

pub mod bootstrap_verify;
#[cfg(feature = "cli")]
pub mod cli;
pub mod coq_import;
pub mod dep_graph;
pub mod error;
pub mod export;
pub mod expr;
pub mod header;
pub mod import;
pub mod import_reverification_metric;
pub mod level;
pub mod metamath;
pub mod module;
pub mod olean_level;
pub mod payload;
pub mod region;
pub mod verify_batch;
pub mod verify_batch_full;
pub mod verify_cache;
pub mod verify_parallel;
pub mod verify_report;
#[cfg(test)]
mod verify_report_tests;

pub use bootstrap_verify::{
    categorize_failures, format_report, verify_bootstrap_lane, verify_bootstrap_lane_in_env,
    verify_init_bootstrap, BootstrapFailure, BootstrapVerifyReport, INIT_BOOTSTRAP_MODULES,
};
pub use error::{OleanError, OleanResult};
pub use expr::{expr_tags, BigNat, ParsedBinderInfo, ParsedExpr, ParsedLiteral};
pub use header::{OleanHeader, HEADER_SIZE, MAGIC, VERSION};
pub use import::{
    active_stdlib_toolchain, alias_resolvable_toolchain_versions,
    convert_parsed_constant_to_const_info, convert_parsed_constant_to_declaration,
    convert_parsed_constant_to_type_stub, default_search_paths, default_toolchain_versions,
    discover_olean_parts, find_module_olean, load_module_with_deps, load_module_with_deps_bounded,
    load_module_with_deps_bounded_shared, load_module_with_deps_bounded_shared_with_policy,
    load_module_with_deps_cached, load_module_with_deps_parallel, load_module_with_deps_shared,
    load_module_with_deps_shared_with_policy, load_module_with_deps_with_import_policy,
    load_modules_with_deps, load_modules_with_deps_with_import_policy, load_olean_file,
    load_olean_file_with_import_policy, load_parsed_module, load_parsed_module_with_import_policy,
    parse_imports_and_const_names_only, parse_imports_only, parse_module, parse_module_file,
    parse_module_incremental, parse_module_incremental_types_only, parse_module_parts,
    parse_module_types_only, toolchain_versions_from_search_paths, ActiveStdlibToolchain,
    ConstantConvertSession, ExprSharingStats, ImportError, ImportKinds, LoadSummary, ModuleCache,
    OleanImportPolicy, SearchPathBuilder, SkippedConstant, UnpinnedOleanImportPolicy,
};
pub use import_reverification_metric::{
    compute_import_reverification_metric, ImportReverificationMetric, MetricError,
    METRIC_SCHEMA_VERSION,
};

// Domain-prefixed alias for collision-free imports
pub use import::ImportError as OleanImportError;
pub use level::{level_tags, ParsedLevel};
pub use module::{
    ConstantKind, ConstructorValData, DefinitionSafety, InductiveValData, OLeanLevel,
    ParsedAttrKind, ParsedClassEntry, ParsedConstant, ParsedExtension, ParsedExtensionEntry,
    ParsedExtensionEntryData, ParsedImport, ParsedInstanceEntry, ParsedModule, ParsedModulePart,
    ParsedQuotKind, RecursorRuleData, RecursorValData, RootAnalysis,
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

pub use export::OleanExporter;
pub use region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn get_lean_lib_path() -> Option<PathBuf> {
        // Look for lean installation
        let home = std::env::var("HOME").ok()?;
        let elan_path = PathBuf::from(home).join(".elan/toolchains");

        if elan_path.exists() {
            // Find first lean4 toolchain
            for entry in std::fs::read_dir(&elan_path).ok()? {
                let entry = entry.ok()?;
                let name = entry.file_name();
                if name.to_string_lossy().contains("lean4") {
                    return Some(entry.path().join("lib/lean"));
                }
            }
        }
        None
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
