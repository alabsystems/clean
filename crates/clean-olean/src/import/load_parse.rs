// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Load-only module representation that preserves raw expression pointers (#2428).
//!
//! Unlike `ParsedModule` which materializes `ParsedExpr` trees for every
//! type/value/rhs expression, `LoadModule` stores raw binary pointers so
//! the direct converter (`read_and_convert_expr`) can produce kernel `Expr`
//! in a single pass without intermediate allocations.

use crate::error::{OleanError, OleanResult};
use crate::header::OleanHeader;
use crate::module::{
    ConstantKind, ConstructorValData, DefinitionSafety, InductiveValData, ParsedExtension,
    ParsedImport, ReducibilityHintsData,
};
use crate::payload::{decode_clean_payload, CleanPayload};
use crate::region::{is_ptr, is_scalar, tags, CompactedRegion};

/// A load-ready module that preserves raw expression pointers.
///
/// This is an importer-only optimization surface. The public `ParsedModule`
/// API remains unchanged for round-trip/export/debug consumers.
pub(crate) struct LoadModule {
    /// Owned copy of the .olean file bytes.
    pub(crate) bytes: Vec<u8>,
    /// Base address for CompactedRegion reconstruction.
    pub(crate) base_addr: u64,
    /// Import declarations (already resolved to strings).
    pub(crate) imports: Vec<ParsedImport>,
    /// Constants with raw expression pointers.
    pub(crate) constants: Vec<LoadConstant>,
    /// Persistent environment extension entries (already parsed).
    pub(crate) entries: Vec<ParsedExtension>,
    /// Optional clean payload.
    pub(crate) clean_payload: Option<CleanPayload>,
}

impl LoadModule {
    /// Reconstruct a `CompactedRegion` from the owned bytes.
    pub(crate) fn region(&self) -> CompactedRegion<'_> {
        CompactedRegion::new(&self.bytes, self.base_addr)
    }
}

/// A constant with raw binary pointers instead of materialized `ParsedExpr`.
pub(crate) struct LoadConstant {
    /// Full name of the constant.
    pub(crate) name: String,
    /// Kind of constant.
    pub(crate) kind: ConstantKind,
    /// Universe parameter names.
    pub(crate) level_params: Vec<String>,
    /// Raw pointer to the type expression (or 0 if absent).
    pub(crate) type_ptr: u64,
    /// Raw pointer to the value expression (or 0 if absent).
    pub(crate) value_ptr: u64,
    /// Extra data for inductive types.
    pub(crate) inductive_val: Option<InductiveValData>,
    /// Extra data for constructors.
    pub(crate) constructor_val: Option<ConstructorValData>,
    /// Extra data for recursors (with raw rhs pointers).
    pub(crate) recursor_val: Option<LoadRecursorValData>,
    /// Reducibility hints (for definitions only).
    pub(crate) hints: Option<ReducibilityHintsData>,
    /// `DefinitionVal.safety` (for `ConstantKind::Definition` only).
    ///
    /// Lean `unsafe def`s are recursive with no termination proof; replaying
    /// one as an ordinary safe `Definition` through one-shot `add_decl` fails
    /// on its self-reference (`Unknown constant: <self>`). Preserving the flag
    /// lets consumers route unsafe definitions to a trusted-context lane
    /// (mirrors `ParsedConstant::definition_safety`). `None` for
    /// non-definitions or `DefnVal`s that predate the `safety` slot.
    pub(crate) definition_safety: Option<DefinitionSafety>,
}

/// Recursor data with raw expression pointers for rule RHS.
pub(crate) struct LoadRecursorValData {
    /// Names of all inductives in mutual group.
    pub(crate) all: Vec<String>,
    pub(crate) num_params: u32,
    pub(crate) num_indices: u32,
    pub(crate) num_motives: u32,
    pub(crate) num_minors: u32,
    /// Recursor rules with raw RHS pointers.
    pub(crate) rules: Vec<LoadRecursorRule>,
    pub(crate) k: bool,
}

/// A recursor rule with a raw pointer to the RHS expression.
pub(crate) struct LoadRecursorRule {
    pub(crate) ctor: String,
    pub(crate) num_fields: u32,
    /// Raw pointer to the RHS expression (or 0 if absent).
    pub(crate) rhs_ptr: u64,
}

/// Parse an .olean file into a `LoadModule` without materializing `ParsedExpr`.
///
/// This is the load-only parser: it reads constant metadata and preserves
/// raw expression pointers for type/value/rhs fields. The direct converter
/// (`read_and_convert_expr`) resolves these pointers during registration.
pub(crate) fn parse_load_module(bytes: Vec<u8>) -> OleanResult<LoadModule> {
    let header = crate::parse_header(&bytes)?;
    let base_addr = header.base_addr;
    let region = CompactedRegion::new(&bytes, base_addr);

    let root_ptr = region.root_ptr()?;
    if !is_ptr(root_ptr) {
        return Err(OleanError::Region("Invalid root pointer".into()));
    }

    let root_offset = region.ptr_to_offset(root_ptr)?;
    let root_header = region.read_header_at(root_offset)?;
    let num_fields = root_header.other as usize;
    let field_offset = root_offset + 8;

    let mut imports = Vec::new();
    let mut constants = Vec::new();
    let mut entries = Vec::new();

    // Field 0: imports
    if num_fields >= 1 {
        let imports_ptr = region.read_u64_at(field_offset)?;
        imports = region.read_import_array_raw(imports_ptr)?;
    }

    // Field 1: constNames — skipped (not needed by direct converter)

    // Field 2: constants — read with raw expression pointers
    if num_fields >= 3 {
        let constants_ptr = region.read_u64_at(field_offset + 16)?;
        constants = read_load_constant_array(&region, constants_ptr)?;
    }

    // Field 3: extraConstNames — skipped (not needed by direct converter)

    // Field 4: entries
    if num_fields >= 5 {
        let entries_ptr = region.read_u64_at(field_offset + 32)?;
        entries = region.read_extension_entries_array(entries_ptr)?;
    }

    let clean_payload = decode_clean_payload(&bytes)?;

    Ok(LoadModule {
        bytes,
        base_addr,
        imports,
        constants,
        entries,
        clean_payload,
    })
}

/// Parse an .olean.private file as an incremental region that shares pointers
/// with its base .olean file (and optionally the .olean.server file).
///
/// Lean 4 v4.29+ stores private constants (match splitters, recursive helpers,
/// proof helpers) in `.olean.private` companion files. These are incremental
/// compacted regions whose pointers may reference objects in the base `.olean`
/// and `.olean.server` address spaces.
///
/// Address layout: `base < server < private` (contiguous with small gaps).
/// This function creates a combined buffer spanning all address ranges so that
/// cross-region pointers resolve correctly through a single `CompactedRegion`.
pub(crate) fn parse_load_module_incremental(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: Vec<u8>,
) -> OleanResult<LoadModule> {
    let base_header = OleanHeader::parse(base_bytes)?;
    let private_header = OleanHeader::parse(&private_bytes)?;

    let base_base_addr = base_header.base_addr;
    let private_base_addr = private_header.base_addr;

    // Private region must start at or after the base region ends.
    // `base_base_addr` is an unvalidated header field; a corrupt/hostile .olean
    // can set it near u64::MAX so this addition would overflow. Reject such a
    // base address instead of panicking (overflow-checks=true aborts otherwise).
    let base_end = base_base_addr
        .checked_add(base_bytes.len() as u64)
        .ok_or_else(|| {
            OleanError::Region(format!(
                "incremental base region address overflow: base_addr 0x{:x} + len {} exceeds u64",
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

    // Sanity check: gap shouldn't be enormous (typically ~111KB)
    const MAX_GAP: usize = 100 * 1024 * 1024; // 100MB
    if gap > MAX_GAP {
        return Err(OleanError::Region(format!(
            "incremental region gap too large: {} bytes (max {})",
            gap, MAX_GAP
        )));
    }

    // Build combined buffer: base_bytes + gap_data + private_bytes
    // The gap may contain the server file's data if present.
    let combined_len = base_bytes.len() + gap + private_bytes.len();
    let mut combined = Vec::with_capacity(combined_len);
    combined.extend_from_slice(base_bytes);
    combined.resize(base_bytes.len() + gap, 0);

    // If server bytes are provided, overlay them at the correct position in the gap.
    // Layout: base_end -> [gap1] -> server -> [gap2] -> private
    if let Some(srv_bytes) = server_bytes {
        if let Ok(srv_header) = OleanHeader::parse(srv_bytes) {
            let srv_addr = srv_header.base_addr;
            // `srv_addr` is an unvalidated header field; guard its addition so a
            // near-u64::MAX server base_addr cannot overflow. On overflow the
            // `checked_add` is `None`, so the overlay is skipped (best-effort,
            // same as the `end <= combined.len()` guard below).
            let srv_fits = srv_addr
                .checked_add(srv_bytes.len() as u64)
                .is_some_and(|srv_end| srv_end <= private_base_addr);
            if srv_addr >= base_end && srv_fits {
                let srv_offset = (srv_addr - base_base_addr) as usize;
                let end = srv_offset + srv_bytes.len();
                if end <= combined.len() {
                    combined[srv_offset..end].copy_from_slice(srv_bytes);
                }
            }
        }
    }

    combined.extend_from_slice(&private_bytes);

    let region = CompactedRegion::new(&combined, base_base_addr);

    // Read private file's root pointer from its header location in the combined buffer
    let private_start = base_bytes.len() + gap;
    let private_header_size = match private_bytes.get(5) {
        Some(&1) => crate::header::HEADER_SIZE,
        Some(&2) => crate::header::HEADER_SIZE_V2,
        _ => return Err(OleanError::Region("unknown .olean.private version".into())),
    };
    let root_ptr_offset = private_start + private_header_size;
    let root_ptr = region.read_u64_at(root_ptr_offset)?;

    if !is_ptr(root_ptr) {
        return Err(OleanError::Region(
            "Invalid root pointer in .olean.private".into(),
        ));
    }

    let root_offset = region.ptr_to_offset(root_ptr)?;
    let root_header = region.read_header_at(root_offset)?;
    let num_fields = root_header.other as usize;
    let field_offset = root_offset + 8;

    let mut imports = Vec::new();
    let mut constants = Vec::new();

    if num_fields >= 1 {
        let imports_ptr = region.read_u64_at(field_offset)?;
        imports = region.read_import_array_raw(imports_ptr)?;
    }

    if num_fields >= 3 {
        let constants_ptr = region.read_u64_at(field_offset + 16)?;
        constants = read_load_constant_array(&region, constants_ptr)?;
    }

    // Skip extension entries (field 4) for private files — they use a
    // different format and we only need the constants for type checking.

    let clean_payload = decode_clean_payload(&private_bytes)?;

    Ok(LoadModule {
        bytes: combined,
        base_addr: base_base_addr,
        imports,
        constants,
        entries: Vec::new(),
        clean_payload,
    })
}

/// Read an array of constants, preserving raw expression pointers.
fn read_load_constant_array(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<Vec<LoadConstant>> {
    if !is_ptr(ptr) {
        return Ok(Vec::new());
    }

    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;

    if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
        return Ok(Vec::new());
    }

    let size = region.read_usize_at(offset + 8, "Constant array")?;
    region.validate_array_bounds(offset, size)?;
    let mut constants = Vec::with_capacity(size);

    for i in 0..size {
        let elem_offset = region.array_elem_offset(offset, i, "Constant array")?;
        let const_ptr = region.read_u64_at(elem_offset)?;
        let constant = read_load_constant_info(region, const_ptr)?;
        constants.push(constant);
    }

    Ok(constants)
}

/// Read a single ConstantInfo, storing raw expression pointers.
fn read_load_constant_info(region: &CompactedRegion<'_>, ptr: u64) -> OleanResult<LoadConstant> {
    if !is_ptr(ptr) {
        return Err(OleanError::Region("Invalid constant pointer".into()));
    }

    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;

    let kind = match header.tag {
        1 => ConstantKind::Definition,
        2 => ConstantKind::Theorem,
        3 => ConstantKind::Opaque,
        4 => ConstantKind::Quot,
        5 => ConstantKind::Inductive,
        6 => ConstantKind::Constructor,
        7 => ConstantKind::Recursor,
        _ => ConstantKind::Axiom,
    };

    // XxxVal is the first field
    let val_ptr = region.read_u64_at(offset + 8)?;
    if !is_ptr(val_ptr) {
        return Err(OleanError::Region("Invalid XxxVal pointer".into()));
    }

    let val_offset = region.ptr_to_offset(val_ptr)?;
    let val_header = region.read_header_at(val_offset)?;

    // Read base ConstantVal fields: name, level_params, type_ptr (raw)
    let (name, level_params, type_ptr) = read_constant_val_fields_raw(region, val_offset)?;

    // Read value pointer for definitions, theorems, opaques
    let value_ptr = read_constant_value_ptr(region, &kind, val_offset, &val_header)?;

    // Read reducibility hints
    let hints = region.read_reducibility_hints(&kind, val_offset, &val_header)?;

    // Read DefinitionSafety (safe/unsafe/partial) for definitions.
    let definition_safety = region.read_definition_safety(&kind, val_offset, &val_header)?;

    // Parse extra fields based on kind
    let (inductive_val, constructor_val, recursor_val) = match kind {
        ConstantKind::Inductive => (
            Some(region.read_inductive_val_data(val_offset)?),
            None,
            None,
        ),
        ConstantKind::Constructor => (
            None,
            Some(region.read_constructor_val_data(val_offset)?),
            None,
        ),
        ConstantKind::Recursor => (
            None,
            None,
            Some(read_load_recursor_val_data(region, val_offset)?),
        ),
        _ => (None, None, None),
    };

    Ok(LoadConstant {
        name,
        kind,
        level_params,
        type_ptr,
        value_ptr,
        inductive_val,
        constructor_val,
        recursor_val,
        hints,
        definition_safety,
    })
}

/// Read ConstantVal fields: name, level_params, and raw type pointer.
fn read_constant_val_fields_raw(
    region: &CompactedRegion<'_>,
    val_offset: usize,
) -> OleanResult<(String, Vec<String>, u64)> {
    let const_val_ptr = region.read_u64_at(val_offset + 8)?;

    let (name_ptr, level_params_ptr, type_ptr) = if is_ptr(const_val_ptr) {
        let cv_offset = region.ptr_to_offset(const_val_ptr)?;
        (
            region.read_u64_at(cv_offset + 8)?,
            region.read_u64_at(cv_offset + 16)?,
            region.read_u64_at(cv_offset + 24)?,
        )
    } else {
        (
            const_val_ptr,
            region.read_u64_at(val_offset + 16)?,
            region.read_u64_at(val_offset + 24)?,
        )
    };

    let name = region.resolve_name_ptr(name_ptr)?;
    let level_params = region.read_name_list(level_params_ptr)?;

    // Keep the raw type pointer instead of calling read_expr_at
    Ok((name, level_params, type_ptr))
}

/// Read the raw value pointer for definitions, theorems, and opaques.
fn read_constant_value_ptr(
    region: &CompactedRegion<'_>,
    kind: &ConstantKind,
    val_offset: usize,
    val_header: &crate::region::ObjectHeader,
) -> OleanResult<u64> {
    let needs_value = matches!(
        kind,
        ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
    );
    if needs_value && val_header.other >= 2 {
        let value_ptr = region.read_u64_at(val_offset + 16)?;
        if is_ptr(value_ptr) {
            return Ok(value_ptr);
        }
    }
    Ok(0)
}

/// Read RecursorVal extra data, preserving raw RHS pointers.
fn read_load_recursor_val_data(
    region: &CompactedRegion<'_>,
    val_offset: usize,
) -> OleanResult<LoadRecursorValData> {
    let all_ptr = region.read_u64_at(val_offset + 16)?;
    let all = region.read_name_list(all_ptr)?;

    let num_params = region.read_u32_at_pub(val_offset + 24, "numParams")?;
    let num_indices = region.read_u32_at_pub(val_offset + 32, "numIndices")?;
    let num_motives = region.read_u32_at_pub(val_offset + 40, "numMotives")?;
    let num_minors = region.read_u32_at_pub(val_offset + 48, "numMinors")?;

    let rules_ptr = region.read_u64_at(val_offset + 56)?;
    let rules = read_load_recursor_rules(region, rules_ptr)?;

    let k = region.read_bool_at_pub(val_offset + 64)?;
    // is_unsafe at offset 72 is not needed by the direct converter; skip.

    Ok(LoadRecursorValData {
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
    })
}

/// Read recursor rules, preserving raw RHS pointers.
fn read_load_recursor_rules(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<Vec<LoadRecursorRule>> {
    const MAX_ITERATIONS: usize = 10_000;

    let mut rules = Vec::new();
    let mut current_ptr = ptr;

    for _i in 0..MAX_ITERATIONS {
        if is_scalar(current_ptr) || !is_ptr(current_ptr) {
            return Ok(rules);
        }

        let offset = region.ptr_to_offset(current_ptr)?;
        let header = region.read_header_at(offset)?;

        match (header.tag, header.other) {
            (1, 2) => {
                let head_ptr = region.read_u64_at(offset + 8)?;
                let tail_ptr = region.read_u64_at(offset + 16)?;

                if is_ptr(head_ptr) {
                    let rule = read_load_recursor_rule(region, head_ptr)?;
                    rules.push(rule);
                }
                current_ptr = tail_ptr;
            }
            _ => return Ok(rules),
        }
    }

    if is_scalar(current_ptr) || !is_ptr(current_ptr) {
        return Ok(rules);
    }

    Err(OleanError::IterationLimitExceeded {
        limit: MAX_ITERATIONS,
        context: "recursor rules",
    })
}

/// Read a single recursor rule, preserving the raw RHS pointer.
fn read_load_recursor_rule(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<LoadRecursorRule> {
    let offset = region.ptr_to_offset(ptr)?;

    let ctor_ptr = region.read_u64_at(offset + 8)?;
    let ctor = region.resolve_name_ptr(ctor_ptr)?;

    let num_fields = region.read_u32_at_pub(offset + 16, "nfields")?;

    let rhs_ptr = region.read_u64_at(offset + 24)?;
    let rhs_ptr = if is_ptr(rhs_ptr) { rhs_ptr } else { 0 };

    Ok(LoadRecursorRule {
        ctor,
        num_fields,
        rhs_ptr,
    })
}

#[cfg(test)]
mod overflow_repro_tests {
    use super::*;

    /// Build a minimal-but-parseable v1 .olean header with the given base_addr.
    /// Only the header is required for `parse_load_module_incremental` to reach
    /// the `base_base_addr + base_bytes.len()` arithmetic at line 171.
    fn v1_file(base_addr: u64, total_len: usize) -> Vec<u8> {
        let mut b = vec![0u8; total_len.max(crate::header::HEADER_SIZE)];
        b[0..5].copy_from_slice(b"olean");
        b[5] = 1; // version 1
        b[6..46].copy_from_slice(b"0000000000000000000000000000000000000000");
        b[48..56].copy_from_slice(&base_addr.to_le_bytes());
        b
    }

    #[test]
    fn base_addr_near_u64_max_does_not_panic() {
        // base_addr chosen so base_addr + base_bytes.len() overflows u64.
        // With overflow-checks=true (dev+release) the current code PANICS here.
        let base_addr = u64::MAX - 40; // even => valid pointer base
        let base = v1_file(base_addr, 128); // len 128 > 40 => base_addr + len overflows
                                            // private header: any valid header; base_addr irrelevant to the overflow.
        let private = v1_file(0x1000, crate::header::HEADER_SIZE);

        // Must return an Err (rejected), never panic/abort.
        let res = parse_load_module_incremental(&base, None, private);
        assert!(res.is_err(), "huge base_addr must be rejected, got Ok");
    }

    /// End-to-end reachability: a base file that ALSO parses via `parse_load_module`
    /// (the on-disk `load_module_recursive` gate) and still overflows at line 171.
    #[test]
    fn e2e_parseable_base_reaches_incremental_overflow() {
        // room = u64::MAX - base_addr. We need room < len (=> overflow) and the root
        // object to sit at offset <= room (=> no wrap when forming its absolute ptr).
        let room: u64 = 97; // offsets 0..=97 form valid (non-wrapping) pointers
        let base_addr = u64::MAX - room; // even (MAX is odd, room odd => even)
        let len = 200usize; // > room => base_addr + len overflows u64
        let mut base = v1_file(base_addr, len);

        // Place a root ModuleData object with 0 fields at an EVEN offset <= room,
        // so base_addr + root_off is even (is_ptr), <= u64::MAX (no wrap), and its
        // 8-byte header fits within len.
        let root_off = 88usize; // even, <= room(97), 88+8=96 <= len(200)
                                // Object header: rc=1, cs_sz=0, other=0 (num_fields=0), tag=CTOR(0).
        base[root_off..root_off + 4].copy_from_slice(&1i32.to_le_bytes());
        base[root_off + 6] = 0; // other = 0 fields
        base[root_off + 7] = 0; // ctor tag
                                // Root pointer stored at header_size (56) points at the root object.
        let root_ptr = base_addr + root_off as u64; // even => is_ptr
        base[crate::header::HEADER_SIZE..crate::header::HEADER_SIZE + 8]
            .copy_from_slice(&root_ptr.to_le_bytes());

        // Sanity: the base MUST parse through the normal load gate first
        // (this is the `load_module_recursive` gate before companions load).
        let parsed = parse_load_module(base.clone());
        assert!(
            parsed.is_ok(),
            "base must parse via parse_load_module to reach the companion/incremental path"
        );

        // Now the companion path calls the incremental parser with this same base.
        let private = v1_file(0x1000, crate::header::HEADER_SIZE);
        let res = parse_load_module_incremental(&base, None, private);
        assert!(res.is_err(), "huge base_addr must be rejected, got Ok");
    }
}
