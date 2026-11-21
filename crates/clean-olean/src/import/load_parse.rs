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
use crate::module::typed_extensions::TypedExtension;
use crate::module::{
    ConstantKind, ConstructorValData, DefinitionSafety, InductiveValData, ParsedImport,
    ReducibilityHintsData,
};
use crate::payload::{decode_clean_payload, CleanPayload};
use crate::region::{is_ptr, is_scalar, tags, CompactedRegion, TypedModuleLayout};
use clean_kernel::name::Name;

mod constants;
use constants::{read_load_constant_array, read_runtime_constant_rows};

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
    /// Structural import identities; the older `imports` field is only the
    /// compatibility projection retained for existing diagnostic consumers.
    pub(crate) typed_imports: Vec<super::TypedImport>,
    /// The part's `constNames` (ModuleData field 1), as typed names. Lean writes
    /// `constNames := constants.map (·.name)`; R113's artifact reader takes a
    /// part's declared names from here at its header depth.
    pub(crate) const_names: Vec<Name>,
    /// Strict observation only; compatibility projections retain their old fallback.
    pub(crate) inventory_arrays_valid: bool,
    /// Constants with raw expression pointers (empty at the header depth).
    pub(crate) constants: Vec<LoadConstant>,
    /// Runtime-only per-index results. Logical loading never uses this lane.
    pub(crate) runtime_rows: Option<Vec<Result<LoadConstant, String>>>,
    /// Full persistent-extension snapshot for this part, in source order.
    /// Companion levels are cumulative, not append-only entry deltas. Shared
    /// pointers do not justify dropping rows: newly available constants may
    /// resolve metadata targets that an earlier part could not register.
    pub(crate) entries: Vec<TypedExtension>,
    /// Optional clean payload.
    pub(crate) clean_payload: Option<CleanPayload>,
    /// This part's `ModuleData.isModule`: written by a `module` file under
    /// Lean's module system. `false` for a layout that carries no such flag
    /// (Lean v4.13, Clean's own exporter). A consumer that is not itself a
    /// `module` — every file Clean checks — reads a module-system
    /// artifact's `.olean.private` and nothing else of it (`lean` v4.30.0-rc2
    /// `Environment.lean`: `ImportedModule.mainModule?` at `OLeanLevel.private`).
    pub(crate) is_module: bool,
    /// The base `.olean` this part was read beside, when a loader read it
    /// from disk ([`Self::read_from`]): `.olean` import reads the module's
    /// compiled IR from there to judge a late `@[implemented_by]` binding
    /// (`super::late_binding`). `None` for bytes from anywhere else.
    pub(crate) source_olean: Option<std::path::PathBuf>,
    /// All inputs of a checked import's later compiled-IR judgement, including
    /// frozen absence. None preserves ordinary file-backed loader behavior.
    pub(crate) captured_ir: Option<std::sync::Arc<crate::lean_ir::module_ir::CapturedIrInput>>,
}

impl LoadModule {
    /// This part, read beside the base `.olean` at `path`.
    #[must_use]
    pub(crate) fn read_from(mut self, path: &std::path::Path) -> Self {
        self.source_olean = Some(path.to_path_buf());
        self
    }

    /// Reconstruct a `CompactedRegion` from the owned bytes.
    pub(crate) fn region(&self) -> CompactedRegion<'_> {
        CompactedRegion::new(&self.bytes, self.base_addr)
    }
}

/// A constant with raw binary pointers instead of materialized `ParsedExpr`.
pub(crate) struct LoadConstant {
    /// Full name of the constant.
    pub(crate) name: String,
    /// Exact raw identity; `name` is only its diagnostic display projection.
    pub(crate) kernel_name: Name,
    /// Kind of constant.
    pub(crate) kind: ConstantKind,
    /// Exact declared universe parameter names.
    pub(crate) kernel_level_params: Vec<Name>,
    /// Exact name-bearing family fields; scalar metadata stays in the existing
    /// kind-specific structures and is not inferred from name spelling.
    pub(crate) kernel_all: Vec<Name>,
    pub(crate) kernel_ctors: Vec<Name>,
    pub(crate) kernel_inductive: Option<Name>,
    /// Ordered source mutual-definition/theorem/opaque group. None
    /// means not applicable or absent in the explicitly supported legacy ABI.
    pub(crate) runtime_mutual: Option<Vec<Name>>,
    /// Raw pointer to the type expression (or 0 if absent).
    pub(crate) type_ptr: u64,
    /// Raw pointer to the value expression (or 0 if absent).
    pub(crate) value_ptr: u64,
    /// Extra data for inductive types.
    pub(crate) inductive_val: Option<InductiveValData>,
    /// Exact modern nested-family multiplicity. The older flag-only format
    /// has no count; its existing `is_nested` projection remains unchanged.
    pub(crate) num_nested: Option<u64>,
    /// Extra data for constructors.
    pub(crate) constructor_val: Option<ConstructorValData>,
    /// Extra data for recursors (with raw rhs pointers).
    pub(crate) recursor_val: Option<LoadRecursorValData>,
    /// Reducibility hints (for definitions only).
    pub(crate) hints: Option<ReducibilityHintsData>,
    /// Declaration safety for definitions, axioms, and opaques.
    ///
    /// Lean `unsafe def`s are recursive with no termination proof; replaying
    /// one as an ordinary safe `Definition` through one-shot `add_decl` fails
    /// on its self-reference (`Unknown constant: <self>`). Preserving the flag
    /// lets consumers route non-safe declarations to a trusted-context lane
    /// (mirrors `ParsedConstant::definition_safety`). Axioms and opaques use
    /// this historical field for their `isUnsafe` Bool; `None` is reserved for
    /// kinds that carry no declaration-safety field.
    pub(crate) definition_safety: Option<DefinitionSafety>,
}

/// Recursor data with raw expression pointers for rule RHS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LoadRecursorValData {
    /// Names of all inductives in mutual group.
    pub(crate) all: Vec<Name>,
    pub(crate) num_params: u32,
    pub(crate) num_indices: u32,
    pub(crate) num_motives: u32,
    pub(crate) num_minors: u32,
    /// Recursor rules with raw RHS pointers.
    pub(crate) rules: Vec<LoadRecursorRule>,
    pub(crate) k: bool,
    pub(crate) is_unsafe: bool,
}

/// A recursor rule with a raw pointer to the RHS expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LoadRecursorRule {
    pub(crate) ctor: Name,
    pub(crate) num_fields: u32,
    /// Raw pointer to the RHS expression (or 0 if absent).
    pub(crate) rhs_ptr: u64,
}

/// Parse an .olean file into a `LoadModule` without materializing `ParsedExpr`.
///
/// This is the load-only parser: it reads constant metadata and preserves
/// raw expression pointers for type/value/rhs fields. The direct converter
/// (`read_and_convert_expr`) resolves these pointers during registration.
/// Which ModuleData fields a parse reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ParseMode {
    /// Imports, `constNames`, constants (raw pointers) and entries: a load.
    Load,
    /// Runtime rows only (`lean_ir`).
    Runtime,
    /// Imports and `constNames` only: R113's artifact reader at its header depth.
    Header,
}

pub(crate) fn parse_load_module(bytes: Vec<u8>) -> OleanResult<LoadModule> {
    parse_load_module_mode(bytes, ParseMode::Load)
}

pub(crate) fn parse_runtime_module(bytes: Vec<u8>) -> OleanResult<LoadModule> {
    parse_load_module_mode(bytes, ParseMode::Runtime)
}

/// A part's header (imports, `constNames`, `isModule`, trailer refusal) without
/// its constants or entries.
pub(crate) fn parse_header_module(bytes: Vec<u8>) -> OleanResult<LoadModule> {
    parse_load_module_mode(bytes, ParseMode::Header)
}

/// Read a ModuleData `Array Name` (field 1, `constNames`) as typed names.
pub(crate) fn read_typed_name_array(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<(Vec<Name>, bool)> {
    if !is_ptr(ptr) {
        return Ok((Vec::new(), false));
    }
    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;
    // As the `ParsedModule` reader reads it (`read_name_array_from_names`).
    if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
        return Ok((Vec::new(), false));
    }
    let size = region.read_usize_at(offset + 8, "constNames array")?;
    region.validate_array_bounds(offset, size)?;
    let mut names = Vec::with_capacity(size);
    for i in 0..size {
        let elem_offset = region.array_elem_offset(offset, i, "constNames array")?;
        names.push(region.read_kernel_name_ptr(region.read_u64_at(elem_offset)?)?);
    }
    Ok((names, true))
}

/// A part's `constNames` (field 1). At the header depth they are the part's
/// declared names and must read; in a load the rule reads the constants
/// instead, so a `constNames` this reader cannot decode never refuses a load
/// that read before it was added.
fn read_const_names(
    region: &CompactedRegion<'_>,
    num_fields: usize,
    field_offset: usize,
    mode: ParseMode,
) -> OleanResult<(Vec<Name>, bool)> {
    if num_fields < 2 || mode == ParseMode::Runtime {
        return Ok((Vec::new(), false));
    }
    let names = region
        .read_u64_at(field_offset + 8)
        .and_then(|ptr| read_typed_name_array(region, ptr));
    match mode {
        ParseMode::Header => names,
        _ => Ok(names.unwrap_or_default()),
    }
}

fn parse_load_module_mode(bytes: Vec<u8>, mode: ParseMode) -> OleanResult<LoadModule> {
    let runtime = mode == ParseMode::Runtime;
    let header = crate::parse_header(&bytes)?;
    let base_addr = header.base_addr;
    let region = CompactedRegion::new(&bytes, base_addr);
    // Validate even an empty/anonymous-only module; a missing Name object is
    // not permission to bypass the measured envelope policy.
    region.typed_module_layout()?;

    let root_ptr = region.root_ptr()?;
    if !is_ptr(root_ptr) {
        return Err(OleanError::Region("Invalid root pointer".into()));
    }

    let root_offset = region.ptr_to_offset(root_ptr)?;
    let root_header = region.read_header_at(root_offset)?;
    let num_fields = root_header.other as usize;
    let field_offset = root_offset + 8;

    let mut imports = Vec::new();
    let mut typed_imports = Vec::new();
    let mut constants = Vec::new();
    let mut runtime_rows = None;
    let mut entries = Vec::new();

    // Field 0: imports
    if num_fields >= 1 && !runtime {
        let imports_ptr = region.read_u64_at(field_offset)?;
        imports = region.read_import_array_raw(imports_ptr)?;
        typed_imports = region.read_typed_import_array(imports_ptr)?;
    }

    // Field 1: constNames — the part's declared names (R113's artifact reader)
    let (const_names, names_valid) = read_const_names(&region, num_fields, field_offset, mode)?;
    let mut records_valid = false;

    // Field 2: constants — read with raw expression pointers
    if num_fields >= 3 && mode != ParseMode::Header {
        let constants_ptr = region.read_u64_at(field_offset + 16)?;
        if runtime {
            runtime_rows = Some(read_runtime_constant_rows(&region, constants_ptr)?);
        } else {
            (constants, records_valid) = read_load_constant_array(&region, constants_ptr)?;
        }
    }

    // Field 3: extraConstNames — skipped (not needed by direct converter)

    // Field 4: entries
    if num_fields >= 5 && mode == ParseMode::Load {
        let entries_ptr = region.read_u64_at(field_offset + 32)?;
        entries = region.read_typed_extension_entries(entries_ptr)?;
    }

    let clean_payload = decode_clean_payload(&bytes)?;
    reject_foreign_payload_trailer(&region, root_ptr, &clean_payload)?;
    let is_module = read_is_module(&region, root_ptr)?;

    Ok(LoadModule {
        bytes,
        base_addr,
        imports,
        typed_imports,
        const_names,
        inventory_arrays_valid: names_valid && records_valid,
        constants,
        runtime_rows,
        entries,
        clean_payload,
        is_module,
        source_olean: None,
        captured_ir: None,
    })
}

/// `ModuleData.isModule` of the part rooted at `root`: the one scalar after
/// the five object fields of the measured modern layout (`cs_sz` 56). A
/// layout without the field is not a module-system part. A byte that is not
/// a canonical `Bool` is malformed, never read as either value.
fn read_is_module(region: &CompactedRegion<'_>, root: u64) -> OleanResult<bool> {
    match region.typed_module_layout_at(root)? {
        TypedModuleLayout::LeanV2 => {
            let offset = region.ptr_to_offset(root)?;
            match region.bytes_at(offset + 8 + 5 * 8, 1)?[0] {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err(OleanError::Region(
                    "ModuleData.isModule is not a canonical Bool".into(),
                )),
            }
        }
        TypedModuleLayout::LeanV1 | TypedModuleLayout::CleanLegacy => Ok(false),
    }
}

/// Refuse a `CLEANENV` payload trailer on a part Lean's own compiler wrote
/// (R113, finding B3). Clean's exporter appends that trailer only to its own
/// `CleanLegacy` layout; a trailer on a `LeanV1`/`LeanV2` part was appended
/// after Lean wrote it, and `lean` never reads it, so a re-check that trusted
/// its declarations would admit constants `leanchecker` never sees. The part
/// is refused here, in every loader and for an import as for a target.
pub(crate) fn reject_foreign_payload_trailer(
    region: &CompactedRegion<'_>,
    root: u64,
    payload: &Option<CleanPayload>,
) -> OleanResult<()> {
    if payload.is_some() && region.root_is_lean_layout(root)? {
        return Err(OleanError::PayloadOnLeanPart(
            "a Lean-written `.olean` part carries a `CLEANENV` trailer".into(),
        ));
    }
    Ok(())
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
    parse_load_module_incremental_mode(base_bytes, server_bytes, private_bytes, ParseMode::Load)
}

pub(crate) fn parse_runtime_module_incremental(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    bytes: Vec<u8>,
) -> OleanResult<LoadModule> {
    parse_load_module_incremental_mode(base_bytes, server_bytes, bytes, ParseMode::Runtime)
}

/// A companion part's header (see [`parse_header_module`]).
pub(crate) fn parse_header_module_incremental(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    bytes: Vec<u8>,
) -> OleanResult<LoadModule> {
    parse_load_module_incremental_mode(base_bytes, server_bytes, bytes, ParseMode::Header)
}

/// The production Load pointer-space assembly and all existing part/root
/// validation, shared with strict capture preflight. This decodes no import
/// rows, names, constants or payload. The display parser's more permissive
/// assembler must not substitute for this one.
pub(crate) fn assemble_load_part(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: &[u8],
) -> OleanResult<super::parse::AssembledPart> {
    let base_header = OleanHeader::parse(base_bytes)?;
    let private_header = OleanHeader::parse(private_bytes)?;

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

    let gap = usize::try_from(private_base_addr - base_end).map_err(|_| {
        OleanError::Region("incremental region gap does not fit this process".into())
    })?;

    // Sanity check: gap shouldn't be enormous (typically ~111KB)
    const MAX_GAP: usize = 100 * 1024 * 1024; // 100MB
    if gap > MAX_GAP {
        return Err(OleanError::Region(format!(
            "incremental region gap too large: {} bytes (max {})",
            gap, MAX_GAP
        )));
    }

    // A combined pointer space must not silently reinterpret one part under
    // another part's Name/Nat format. Present malformed companions are errors,
    // not optional holes. Actual names may still refer across validated parts.
    let mut part_roots = Vec::new();
    for part in std::iter::once(base_bytes)
        .chain(server_bytes)
        .chain(std::iter::once(private_bytes))
    {
        let header = OleanHeader::parse(part)?;
        if (
            header.version,
            header.flags,
            &header.lean_version,
            header.git_hash,
        ) != (
            base_header.version,
            base_header.flags,
            &base_header.lean_version,
            base_header.git_hash,
        ) {
            return Err(OleanError::Region(
                "incremental Name/Nat format mismatch".into(),
            ));
        }
        let region = CompactedRegion::new(part, header.base_addr);
        let header_size = if header.version == 1 {
            crate::header::HEADER_SIZE
        } else {
            crate::header::HEADER_SIZE_V2
        };
        let object_start = header
            .base_addr
            .checked_add(header_size as u64 + 8)
            .ok_or_else(|| OleanError::Region("incremental object start overflow".into()))?;
        let end = header
            .base_addr
            .checked_add(part.len() as u64)
            .ok_or_else(|| OleanError::Region("incremental captured extent overflow".into()))?;
        part_roots.push(CapturedPartRoot {
            object_start,
            end,
            root: region.root_ptr()?,
        });
    }

    // Build combined buffer: base_bytes + gap_data + private_bytes
    // The gap may contain the server file's data if present.
    let combined_len = base_bytes
        .len()
        .checked_add(gap)
        .and_then(|length| length.checked_add(private_bytes.len()))
        .ok_or_else(|| OleanError::Region("incremental combined length overflow".into()))?;
    let mut combined = Vec::new();
    combined.try_reserve_exact(combined_len).map_err(|error| {
        OleanError::Region(format!("incremental assembly allocation failed: {error}"))
    })?;
    combined.extend_from_slice(base_bytes);
    combined.resize(base_bytes.len() + gap, 0);

    // If server bytes are provided, overlay them at the correct position in the gap.
    // Layout: base_end -> [gap1] -> server -> [gap2] -> private
    if let Some(srv_bytes) = server_bytes {
        let srv_header = OleanHeader::parse(srv_bytes)?;
        let srv_addr = srv_header.base_addr;
        // `srv_addr` is an unvalidated header field; guard its addition so a
        // near-u64::MAX server base_addr cannot overflow. An invalid
        // supplied region is refused rather than silently omitted.
        let srv_fits = srv_addr
            .checked_add(srv_bytes.len() as u64)
            .is_some_and(|srv_end| srv_end <= private_base_addr);
        if srv_addr >= base_end && srv_fits {
            let srv_offset = (srv_addr - base_base_addr) as usize;
            let end = srv_offset + srv_bytes.len();
            if end <= combined.len() {
                combined[srv_offset..end].copy_from_slice(srv_bytes);
            } else {
                return Err(OleanError::Region(
                    "server region outside combined buffer".into(),
                ));
            }
        } else {
            return Err(OleanError::Region(
                "server region overlaps or overflows companion address space".into(),
            ));
        }
    }

    combined.extend_from_slice(private_bytes);

    let region = CompactedRegion::new(&combined, base_base_addr);
    validate_captured_part_roots(&region, &part_roots)?;

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

    Ok(super::parse::AssembledPart {
        bytes: combined,
        base_addr: base_base_addr,
        root_ptr,
    })
}

fn parse_load_module_incremental_mode(
    base_bytes: &[u8],
    server_bytes: Option<&[u8]>,
    private_bytes: Vec<u8>,
    mode: ParseMode,
) -> OleanResult<LoadModule> {
    let runtime = mode == ParseMode::Runtime;
    let super::parse::AssembledPart {
        bytes: combined,
        base_addr: base_base_addr,
        root_ptr,
    } = assemble_load_part(base_bytes, server_bytes, &private_bytes)?;
    let region = CompactedRegion::new(&combined, base_base_addr);

    let root_offset = region.ptr_to_offset(root_ptr)?;
    let root_header = region.read_header_at(root_offset)?;
    let num_fields = root_header.other as usize;
    let field_offset = root_offset + 8;

    let mut imports = Vec::new();
    let mut typed_imports = Vec::new();
    let mut constants = Vec::new();
    let mut runtime_rows = None;

    if num_fields >= 1 && !runtime {
        let imports_ptr = region.read_u64_at(field_offset)?;
        imports = region.read_import_array_raw(imports_ptr)?;
        typed_imports = region.read_typed_import_array(imports_ptr)?;
    }

    let (const_names, names_valid) = read_const_names(&region, num_fields, field_offset, mode)?;
    let mut records_valid = false;

    if num_fields >= 3 && mode != ParseMode::Header {
        let constants_ptr = region.read_u64_at(field_offset + 16)?;
        if runtime {
            runtime_rows = Some(read_runtime_constant_rows(&region, constants_ptr)?);
        } else {
            (constants, records_valid) = read_load_constant_array(&region, constants_ptr)?;
        }
    }

    // ModuleData field 4 has the same typed extension envelope at each
    // validated level. Decode against the combined captured region so entries
    // may borrow objects from earlier parts. Keep the complete snapshot even
    // when the entire root is borrowed; existing registration handles repeated
    // recognized targets, while per-part accounting retains every raw row.
    // This does not implement importAll, scoped activation, erasure, or the
    // opaque payloads that the typed reader explicitly leaves unmeasured.
    let entries = if num_fields >= 5 && mode == ParseMode::Load {
        region.read_typed_extension_entries(region.read_u64_at(field_offset + 32)?)?
    } else {
        Vec::new()
    };

    let clean_payload = decode_clean_payload(&private_bytes)?;
    reject_foreign_payload_trailer(&region, root_ptr, &clean_payload)?;
    let is_module = read_is_module(&region, root_ptr)?;

    Ok(LoadModule {
        bytes: combined,
        base_addr: base_base_addr,
        imports,
        typed_imports,
        const_names,
        inventory_arrays_valid: names_valid && records_valid,
        constants,
        runtime_rows,
        entries,
        clean_payload,
        is_module,
        source_olean: None,
        captured_ir: None,
    })
}

struct CapturedPartRoot {
    object_start: u64,
    end: u64,
    root: u64,
}

fn validate_captured_part_roots(
    region: &CompactedRegion<'_>,
    parts: &[CapturedPartRoot],
) -> OleanResult<()> {
    let mut first_layout = None;
    for (index, part) in parts.iter().enumerate() {
        // Empty real companions may borrow an earlier root. Zero-filled gaps,
        // headers, missing server bytes and future private objects are not an
        // earlier captured region, even when inside the combined allocation.
        let owner = parts[..=index]
            .iter()
            .find(|owner| part.root >= owner.object_start && part.root < owner.end)
            .ok_or_else(|| {
                OleanError::Region("incremental root outside captured prior/current regions".into())
            })?;
        let layout = region.typed_module_layout_at(part.root)?;
        let bytes = match layout {
            TypedModuleLayout::LeanV2 => 56,
            TypedModuleLayout::LeanV1 | TypedModuleLayout::CleanLegacy => 48,
        };
        if part
            .root
            .checked_add(bytes)
            .is_none_or(|end| end > owner.end)
        {
            return Err(OleanError::Region(
                "incremental root extends beyond captured region".into(),
            ));
        }
        if first_layout.is_some_and(|first| first != layout) {
            return Err(OleanError::Region(
                "incremental Name/Nat format mismatch".into(),
            ));
        }
        first_layout = Some(layout);
    }
    Ok(())
}

#[cfg(test)]
#[path = "load_parse/companion_extension_tests.rs"]
mod companion_extension_tests;

#[cfg(test)]
mod companion_root_tests;

#[cfg(test)]
mod overflow_repro_tests;

#[cfg(test)]
mod trailer_tests;

#[cfg(test)]
mod stub_completion_tests;
