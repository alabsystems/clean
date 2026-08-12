// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parse .olean files into `ParsedModule` structures.
//!
//! Provides functions for parsing complete modules, multi-part modules,
//! and fast import-only parsing for dependency graph construction.

use crate::error::{OleanError, OleanResult};
use crate::header::OleanHeader;
use crate::module::{OLeanLevel, ParsedImport, ParsedModule, ParsedModulePart};
use crate::parse_header;
use crate::region::CompactedRegion;
use std::path::{Path, PathBuf};

/// Parse a complete .olean file into a `ParsedModule`.
///
/// # REQUIRES
/// - `bytes` must be a valid .olean file with correct magic bytes ("olean")
/// - `bytes.len() >= HEADER_SIZE` (56 or 88 bytes depending on version)
///
/// # ENSURES
/// - On success, returns `ParsedModule` with all constants from the file
/// - On failure, returns `OleanError` with specific error type (magic, version, size, parse)
/// - Parsing is deterministic: same bytes always produce the same result
pub fn parse_module(bytes: &[u8]) -> OleanResult<ParsedModule> {
    let header = parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.read_module_data()
}

/// Parse a complete .olean file into a `ParsedModule`, TYPES-ONLY.
///
/// Identical to [`parse_module`] except the `value` (proof-term) `Expr` of every
/// `Theorem`/`Opaque` constant is NOT reconstructed — those constants come back
/// value-less. Every constant's TYPE (and any non-opaque `Definition` value, kept
/// for δ-reduction) is read exactly as in the full path.
///
/// The kernel never δ-unfolds a `Theorem`/`Opaque` during type-checking, so for a
/// TRUSTED-import closure a dependency's proof body is dead weight; skipping its
/// reconstruction is the peak-RSS lever behind `per-constant-verify`'s ability to
/// kernel-verify analysis lemmas (MVT, Taylor) without OOM.
///
/// # ENSURES
/// - Result equals [`parse_module`] except `Theorem`/`Opaque` `value == None`.
/// - Does not reconstruct `Theorem`/`Opaque` proof `Expr`s (much lighter).
pub fn parse_module_types_only(bytes: &[u8]) -> OleanResult<ParsedModule> {
    let header = parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.read_module_data_opts(true)
}

/// Parse a module from disk.
///
/// # REQUIRES
/// - `path` must point to an existing file
/// - File must be a valid .olean format
///
/// # ENSURES
/// - On success, returns `ParsedModule` identical to `parse_module(std::fs::read(path)?)`
/// - On I/O error, returns `OleanError::Io`
/// - On parse error, returns appropriate `OleanError` variant
pub fn parse_module_file(path: impl AsRef<Path>) -> OleanResult<ParsedModule> {
    let bytes = std::fs::read(path)?;
    parse_module(&bytes)
}

/// Decide whether `region_bytes` is a *higher-address incremental* olean that
/// cross-references `base_bytes` (i.e. its objects must be resolved against the
/// base), as opposed to a self-contained region sharing the base's address
/// range.
///
/// A module-system `.olean.server` / `.olean.private` is loaded by Lean at an
/// address strictly *above* the end of the base region, so its base address is
/// `>= base_base_addr + base_len`. A classic, self-contained olean shares (or
/// overlaps) the base's address range and must be parsed standalone.
///
/// Both headers are parsed here, so a malformed `region_bytes` (e.g. a
/// truncated or non-olean file) surfaces its header error to the caller rather
/// than being silently misrouted.
///
/// # ENSURES
/// - Returns `Ok(true)` iff `region.base_addr >= base.base_addr + base.len`.
/// - Propagates `OleanError` if either header fails to parse.
fn is_higher_address_region(base_bytes: &[u8], region_bytes: &[u8]) -> OleanResult<bool> {
    let base_header = OleanHeader::parse(base_bytes)?;
    let region_header = OleanHeader::parse(region_bytes)?;
    let Some(base_end) = base_header.base_addr.checked_add(base_bytes.len() as u64) else {
        // A base whose address range overflows u64 cannot anchor an incremental
        // region; treat the companion as self-contained (standalone parse).
        return Ok(false);
    };
    Ok(region_header.base_addr >= base_end)
}

/// Parse an .olean.private file as an incremental region that shares pointers
/// with its base .olean file (and optionally the .olean.server file).
///
/// Creates a combined buffer spanning all address ranges so that cross-region
/// pointers resolve correctly. Returns a `ParsedModule` with fully materialized
/// `ParsedExpr` trees.
///
/// Address layout: `base < server < private` (contiguous with small gaps).
pub fn parse_module_incremental(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: &[u8],
) -> OleanResult<ParsedModule> {
    parse_module_incremental_opts(base_bytes, server_bytes, private_bytes, false)
}

/// Parse an .olean.private companion TYPES-ONLY.
///
/// Identical to [`parse_module_incremental`] except `Theorem`/`Opaque` proof-term
/// values in the private region are NOT reconstructed. This is how the
/// per-constant loader merges a dependency's private companion (which is almost
/// entirely proof bodies) without paying to rebuild those proof `Expr`s: only
/// `Definition` values (δ-reducible) and every constant's type survive the merge.
pub fn parse_module_incremental_types_only(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: &[u8],
) -> OleanResult<ParsedModule> {
    parse_module_incremental_opts(base_bytes, server_bytes, private_bytes, true)
}

/// Shared implementation of [`parse_module_incremental`] /
/// [`parse_module_incremental_types_only`]. `skip_proof_values` toggles TYPES-ONLY
/// reconstruction of the private region's constants.
fn parse_module_incremental_opts(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: &[u8],
    skip_proof_values: bool,
) -> OleanResult<ParsedModule> {
    let base_header = OleanHeader::parse(base_bytes)?;
    let private_header = OleanHeader::parse(private_bytes)?;

    let base_base_addr = base_header.base_addr;
    let private_base_addr = private_header.base_addr;

    let base_end = base_base_addr
        .checked_add(base_bytes.len() as u64)
        .ok_or_else(|| {
            OleanError::Region(format!(
                "incremental region base address overflows u64: base_addr=0x{:x}, len={}",
                base_base_addr,
                base_bytes.len()
            ))
        })?;
    if private_base_addr < base_end {
        return Err(OleanError::Region(format!(
            "incremental region overlap: base ends at 0x{:x}, private starts at 0x{:x}",
            base_end, private_base_addr
        )));
    }

    let gap = (private_base_addr - base_end) as usize;

    const MAX_GAP: usize = 100 * 1024 * 1024;
    if gap > MAX_GAP {
        return Err(OleanError::Region(format!(
            "incremental region gap too large: {} bytes (max {})",
            gap, MAX_GAP
        )));
    }

    let combined_len = base_bytes.len() + gap + private_bytes.len();
    let mut combined = Vec::with_capacity(combined_len);
    combined.extend_from_slice(base_bytes);
    combined.resize(base_bytes.len() + gap, 0);

    if let Some(srv_bytes) = server_bytes {
        if let Ok(srv_header) = OleanHeader::parse(srv_bytes) {
            let srv_addr = srv_header.base_addr;
            if srv_addr >= base_end && srv_addr + srv_bytes.len() as u64 <= private_base_addr {
                let srv_offset = (srv_addr - base_base_addr) as usize;
                let end = srv_offset + srv_bytes.len();
                if end <= combined.len() {
                    combined[srv_offset..end].copy_from_slice(srv_bytes);
                }
            }
        }
    }

    combined.extend_from_slice(private_bytes);

    let region = CompactedRegion::new(&combined, base_base_addr);

    let private_start = base_bytes.len() + gap;
    let private_header_size = match private_bytes.get(5) {
        Some(&1) => crate::header::HEADER_SIZE,
        Some(&2) => crate::header::HEADER_SIZE_V2,
        _ => return Err(OleanError::Region("unknown .olean.private version".into())),
    };
    let root_ptr_offset = private_start + private_header_size;
    let root_ptr = region.read_u64_at(root_ptr_offset)?;

    region.read_module_data_from_ptr_opts(root_ptr, private_bytes, skip_proof_values)
}

/// Parse all .olean parts (.olean, .olean.server, .olean.private) for a module.
///
/// Given a base .olean path, this function discovers and parses any additional
/// .olean.server and .olean.private parts that exist alongside it.
///
/// # Arguments
///
/// * `base_path` - Path to the base `.olean` file (the exported/public part)
///
/// # Returns
///
/// A vector of `ParsedModulePart` in level order:
/// 1. Exported (base `.olean`)
/// 2. Server (`.olean.server`) - if exists
/// 3. Private (`.olean.private`) - if exists
///
/// # REQUIRES
/// - `base_path` must point to an existing `.olean` file
///
/// # ENSURES
/// - Returns at least one part (the exported base)
/// - Parts are returned in `OLeanLevel::all()` order
/// - Non-existent server/private files are silently skipped (not errors)
/// - Existing but malformed server/private files produce errors (strict parsing)
/// - Private only parsed if server also exists (per Lean 4 semantics)
/// - Each part's `level` field matches its file suffix
///
/// # Example
///
/// ```rust,no_run
/// use clean_olean::{parse_module_parts, OLeanLevel, OleanResult};
///
/// fn main() -> OleanResult<()> {
///     let parts = parse_module_parts("Init.Core.olean")?;
///     for part in &parts {
///         // process part.level, part.module.constants
///     }
///     Ok(())
/// }
/// ```
///
/// Source: Lean 4 `readModuleDataParts` in `Environment.lean:1723-1746`
pub fn parse_module_parts(base_path: impl AsRef<Path>) -> OleanResult<Vec<ParsedModulePart>> {
    let base_path = base_path.as_ref();
    let mut parts = Vec::with_capacity(3);

    // Always parse the base .olean (exported level)
    let base_bytes = std::fs::read(base_path)?;
    let module = parse_module(&base_bytes)?;
    parts.push(ParsedModulePart {
        level: OLeanLevel::Exported,
        module,
    });

    // Parse .olean.server if it exists (errors propagate - strict parsing)
    let server_path = base_path.with_extension("olean.server");
    if server_path.exists() {
        let server_bytes = std::fs::read(&server_path)?;
        // ROUTE BY ADDRESS. Under the module system the `.olean.server` is a
        // higher-address INCREMENTAL region whose objects cross-reference the
        // base, so parsing it standalone resolves its pointers against the wrong
        // buffer. A classic self-contained server olean instead shares the base's
        // address range and parses standalone. Deciding by header address covers
        // both; assuming either one silently corrupts the other.
        let module = if is_higher_address_region(&base_bytes, &server_bytes)? {
            parse_module_incremental(&base_bytes, None, &server_bytes)?
        } else {
            parse_module(&server_bytes)?
        };
        parts.push(ParsedModulePart {
            level: OLeanLevel::Server,
            module,
        });

        // Private is only parsed if server also exists (per Lean 4 semantics).
        // Uses incremental region parsing: private pointers may reference
        // objects in the base or server address spaces (#3107).
        let private_path = base_path.with_extension("olean.private");
        if private_path.exists() {
            let private_bytes = std::fs::read(&private_path)?;
            let module =
                parse_module_incremental(&base_bytes, Some(&server_bytes), &private_bytes)?;
            parts.push(ParsedModulePart {
                level: OLeanLevel::Private,
                module,
            });
        }
    }

    Ok(parts)
}

/// Discover all .olean parts that exist for a given base path.
///
/// Returns paths to existing .olean files for each level.
/// This is useful for checking what parts are available before loading.
///
/// # Arguments
///
/// * `base_path` - Path to the base `.olean` file
///
/// # Returns
///
/// A vector of `(OLeanLevel, PathBuf)` tuples for each existing part.
///
/// # ENSURES
/// - Empty if base path does not exist
/// - Private only included if server also exists (per Lean 4 semantics)
/// - Results are in `OLeanLevel::all()` order
///
/// Source: Lean 4 `findOLeanParts` in `Environment.lean:1989-2002`
pub fn discover_olean_parts(base_path: impl AsRef<Path>) -> Vec<(OLeanLevel, PathBuf)> {
    let base_path = base_path.as_ref();
    let mut parts = Vec::with_capacity(3);

    // Base is required - if it doesn't exist, return empty
    if !base_path.exists() {
        return parts;
    }
    parts.push((OLeanLevel::Exported, base_path.to_path_buf()));

    // Server must exist for private to be included (per Lean 4 semantics)
    let server_path = base_path.with_extension("olean.server");
    if server_path.exists() {
        parts.push((OLeanLevel::Server, server_path));

        // Private is only included if server also exists
        let private_path = base_path.with_extension("olean.private");
        if private_path.exists() {
            parts.push((OLeanLevel::Private, private_path));
        }
    }

    parts
}

/// Parse only the imports from an .olean file, skipping constant parsing.
///
/// This is much faster than `parse_module` when you only need the dependency list
/// (e.g., for building a module dependency graph).
///
/// # REQUIRES
/// - `bytes` must be a valid .olean file (same as `parse_header`)
///
/// # ENSURES
/// - Returns exactly the import list from the module, in file order
/// - Result equivalent to `parse_module(bytes)?.imports`
/// - Faster than full `parse_module` (~2-10x depending on module size)
/// - Does NOT parse constants, types, or expressions
///
/// # Example
///
/// ```rust,no_run
/// use clean_olean::{parse_imports_only, OleanResult};
///
/// fn main() -> OleanResult<()> {
///     let bytes = std::fs::read("Init.Core.olean")?;
///     let imports = parse_imports_only(&bytes)?;
///     for import in imports {
///         // process import.module_name
///     }
///     Ok(())
/// }
/// ```
pub fn parse_imports_only(bytes: &[u8]) -> OleanResult<Vec<ParsedImport>> {
    let header = parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.read_imports_only()
}

/// Parse a module's imports AND its declared constant names, skipping the
/// `constants` array (no `Expr` reconstruction).
///
/// This is the header-only read the PER-CONSTANT streaming closure loader uses
/// to build a `name -> owning .olean` index over a whole import closure. It is
/// dramatically cheaper than `parse_module` because it never materializes a
/// single constant's type/value tree — it only walks the two `Name` arrays.
///
/// # ENSURES
/// - Returns `(imports, names)` where `names` is `constNames ++ extraConstNames`.
/// - Does NOT parse constants, types, or expressions.
pub fn parse_imports_and_const_names_only(
    bytes: &[u8],
) -> OleanResult<(Vec<ParsedImport>, Vec<String>)> {
    let header = parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.read_imports_and_const_names_only()
}

#[cfg(test)]
mod incremental_overflow_tests {
    use super::*;

    /// Build a minimal, header-valid v1 .olean byte buffer with the given
    /// `base_addr`. The header validates magic + version + hex git hash; the
    /// `base_addr` field is read verbatim with no range check.
    fn make_v1_bytes(base_addr: u64) -> Vec<u8> {
        let mut b = vec![0u8; crate::header::HEADER_SIZE];
        b[0..5].copy_from_slice(b"olean");
        b[5] = 1; // version 1
        b[6..46].copy_from_slice(b"0123456789abcdef0123456789abcdef01234567");
        // b[46], b[47] stay null-padded
        b[48..56].copy_from_slice(&base_addr.to_le_bytes());
        b
    }

    /// Regression: a base .olean whose header `base_addr` is near `u64::MAX`
    /// must NOT panic on the `base_addr + base_bytes.len()` computation in
    /// `parse_module_incremental`. Before the fix this aborts with
    /// "attempt to add with overflow" under `overflow-checks = true`
    /// (both dev and release profiles). After the fix it returns a clean
    /// `OleanError::Region`.
    #[test]
    fn test_incremental_base_addr_near_u64_max_does_not_overflow() {
        let base = make_v1_bytes(u64::MAX);
        let private = make_v1_bytes(0x1000); // valid header; value irrelevant
        let result = parse_module_incremental(&base, None, &private);
        // Must be a graceful error, not a panic/abort.
        match result {
            Err(OleanError::Region(_)) => {}
            other => panic!("expected OleanError::Region on overflowing base_addr, got {other:?}"),
        }
    }

    /// A base_addr exactly at the overflow boundary (`u64::MAX - len + 1`)
    /// still overflows `base_addr + len` and must be rejected gracefully.
    #[test]
    fn test_incremental_base_addr_at_overflow_boundary_is_rejected() {
        let len = crate::header::HEADER_SIZE as u64;
        let base = make_v1_bytes(u64::MAX - len + 1);
        let private = make_v1_bytes(0x1000);
        let result = parse_module_incremental(&base, None, &private);
        assert!(
            matches!(result, Err(OleanError::Region(_))),
            "boundary base_addr must be rejected, not overflow"
        );
    }
}
