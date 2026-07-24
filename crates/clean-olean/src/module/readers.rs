// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core module data readers for CompactedRegion.
//!
//! Contains the primary read_module_data and read_imports_only methods,
//! plus shared utility readers (array bounds, element offsets) and
//! import/extension parsing.

use super::{ParsedImport, ParsedModule};
use crate::error::{OleanError, OleanResult};
use crate::header::{HEADER_SIZE, HEADER_SIZE_V2, VERSION, VERSION_V2};
use crate::payload::decode_clean_payload;
use crate::region::{is_ptr, is_scalar, tags, CompactedRegion};

impl<'a> CompactedRegion<'a> {
    /// Get the root pointer (first pointer after the header).
    ///
    /// # REQUIRES
    /// - `self.data` contains a valid .olean header (v1 or v2).
    ///
    /// # ENSURES
    /// - Returns the root pointer stored immediately after the header.
    /// - Returns `OleanError::UnsupportedVersion` on unknown header versions.
    pub fn root_ptr(&self) -> OleanResult<u64> {
        let version =
            self.data
                .get(MAGIC.len())
                .copied()
                .ok_or_else(|| OleanError::FileTooSmall {
                    expected: MAGIC.len() + 1,
                    actual: self.data.len(),
                })?;

        let header_size = match version {
            VERSION => HEADER_SIZE,
            VERSION_V2 => HEADER_SIZE_V2,
            _ => {
                return Err(OleanError::UnsupportedVersion {
                    expected: VERSION_V2,
                    actual: version,
                });
            }
        };

        self.read_u64_at(header_size)
    }

    /// Read the ModuleData structure from the root object
    ///
    /// Lean 4 ModuleData layout (from Environment.lean):
    /// - Scalar: isModule (Bool) - stored after pointer fields, always true for .olean
    /// - Field 0: imports (Array Import)
    /// - Field 1: constNames (Array Name)
    /// - Field 2: constants (Array ConstantInfo)
    /// - Field 3: extraConstNames (Array Name)
    /// - Field 4: entries (Array (Name × Array EnvExtensionEntry))
    ///
    /// Note: Module indices (ModuleIdx) are computed at import time based on
    /// position in the import order, not stored in the .olean file.
    ///
    /// # REQUIRES
    /// - Root pointer must reference a valid ModuleData object.
    ///
    /// # ENSURES
    /// - Returns `ParsedModule` with imports, constants, and names populated.
    /// - Returns `OleanError` if the region is malformed or tags mismatch.
    pub fn read_module_data(&self) -> OleanResult<ParsedModule> {
        self.read_module_data_opts(false)
    }

    /// Read the ModuleData structure, optionally in TYPES-ONLY mode.
    ///
    /// When `skip_proof_values` is `true`, the `constants` array is reconstructed
    /// with the `value` proof term of every `Theorem`/`Opaque` constant SKIPPED
    /// (see [`CompactedRegion::read_constant_array_v2_opts`]). Types, names,
    /// imports, extension entries, and `Definition` values are read identically
    /// to the full path. This is the lever the per-constant streaming verifier
    /// uses to load a trusted-import closure without reconstructing hundreds of
    /// analysis-module proof bodies (the peak-RSS cost that OOMs otherwise).
    pub fn read_module_data_opts(&self, skip_proof_values: bool) -> OleanResult<ParsedModule> {
        let root_ptr = self.root_ptr()?;

        if !is_ptr(root_ptr) {
            return Err(OleanError::Region("Invalid root pointer".into()));
        }

        let root_offset = self.ptr_to_offset(root_ptr)?;
        let header = self.read_header_at(root_offset)?;

        let num_fields = header.other as usize;
        let field_offset = root_offset + 8; // Skip header

        let mut imports = Vec::new();
        let mut const_names = Vec::new();
        let mut constants = Vec::new();
        let mut extra_const_names = Vec::new();

        // Field 0: imports (Array Import)
        if num_fields >= 1 {
            let imports_ptr = self.read_u64_at(field_offset)?;
            imports = self.read_import_array(imports_ptr)?;
        }

        // Field 1: constNames (Array Name)
        if num_fields >= 2 {
            let const_names_ptr = self.read_u64_at(field_offset + 8)?;
            const_names = self.read_name_array_from_names(const_names_ptr)?;
        }

        // Field 2: constants (Array ConstantInfo)
        if num_fields >= 3 {
            let constants_ptr = self.read_u64_at(field_offset + 16)?;
            constants = self.read_constant_array_v2_opts(constants_ptr, skip_proof_values)?;
        }

        // Field 3: extraConstNames (Array Name)
        if num_fields >= 4 {
            let extra_ptr = self.read_u64_at(field_offset + 24)?;
            extra_const_names = self.read_name_array_from_names(extra_ptr)?;
        }

        // Field 4: entries (Array (Name × Array (Name × DataValue)))
        let mut entries = Vec::new();
        if num_fields >= 5 {
            let entries_ptr = self.read_u64_at(field_offset + 32)?;
            entries = self.read_extension_entries_array(entries_ptr)?;
        }

        Ok(ParsedModule {
            const_names,
            constants,
            extra_const_names,
            imports,
            entries,
            clean_payload: decode_clean_payload(self.data)?,
        })
    }

    /// Read module data starting from a given root pointer.
    ///
    /// Like `read_module_data` but takes an explicit root pointer instead of
    /// reading it from the region header. Used for incremental regions where
    /// the root pointer is at a different offset (e.g., .olean.private files
    /// embedded in a combined buffer).
    pub fn read_module_data_from_ptr(
        &self,
        root_ptr: u64,
        payload_bytes: &[u8],
    ) -> OleanResult<ParsedModule> {
        self.read_module_data_from_ptr_opts(root_ptr, payload_bytes, false)
    }

    /// Like [`Self::read_module_data_from_ptr`], but optionally TYPES-ONLY: when
    /// `skip_proof_values` is set, `Theorem`/`Opaque` proof-term values in this
    /// (incremental/companion) region are not reconstructed. Used to load an
    /// `.olean.private` proof companion type-only, so a trusted dependency's
    /// proof bodies never become resident.
    pub fn read_module_data_from_ptr_opts(
        &self,
        root_ptr: u64,
        payload_bytes: &[u8],
        skip_proof_values: bool,
    ) -> OleanResult<ParsedModule> {
        if !is_ptr(root_ptr) {
            return Err(OleanError::Region("Invalid root pointer".into()));
        }

        let root_offset = self.ptr_to_offset(root_ptr)?;
        let header = self.read_header_at(root_offset)?;

        let num_fields = header.other as usize;
        let field_offset = root_offset + 8;

        let mut imports = Vec::new();
        let mut const_names = Vec::new();
        let mut constants = Vec::new();
        let mut extra_const_names = Vec::new();

        if num_fields >= 1 {
            let imports_ptr = self.read_u64_at(field_offset)?;
            imports = self.read_import_array(imports_ptr)?;
        }

        if num_fields >= 2 {
            let const_names_ptr = self.read_u64_at(field_offset + 8)?;
            const_names = self.read_name_array_from_names(const_names_ptr)?;
        }

        if num_fields >= 3 {
            let constants_ptr = self.read_u64_at(field_offset + 16)?;
            constants = self.read_constant_array_v2_opts(constants_ptr, skip_proof_values)?;
        }

        if num_fields >= 4 {
            let extra_ptr = self.read_u64_at(field_offset + 24)?;
            extra_const_names = self.read_name_array_from_names(extra_ptr)?;
        }

        // Skip extension entries for incremental regions (different format)

        Ok(ParsedModule {
            const_names,
            constants,
            extra_const_names,
            imports,
            entries: Vec::new(),
            clean_payload: decode_clean_payload(payload_bytes)?,
        })
    }

    /// Read only the imports from a module, skipping all constant parsing.
    ///
    /// This is much faster than `read_module_data` when you only need imports
    ///
    /// # REQUIRES
    /// - Root pointer must reference a valid ModuleData object.
    ///
    /// # ENSURES
    /// - Returns the import list in file order.
    /// - Avoids parsing constants and expressions
    ///   (e.g., for dependency graph discovery).
    pub fn read_imports_only(&self) -> OleanResult<Vec<ParsedImport>> {
        let root_ptr = self.root_ptr()?;

        if !is_ptr(root_ptr) {
            return Err(OleanError::Region("Invalid root pointer".into()));
        }

        let root_offset = self.ptr_to_offset(root_ptr)?;
        let header = self.read_header_at(root_offset)?;

        let num_fields = header.other as usize;
        let field_offset = root_offset + 8; // Skip header

        // Field 0: imports (Array Import)
        if num_fields >= 1 {
            let imports_ptr = self.read_u64_at(field_offset)?;
            self.read_import_array(imports_ptr)
        } else {
            Ok(Vec::new())
        }
    }

    /// Read a module's imports AND declared constant names, skipping the
    /// expensive `constants` array (field 2) entirely.
    ///
    /// This is the header-only read the PER-CONSTANT streaming closure loader
    /// uses to build a `name -> owning .olean` index across a whole import
    /// closure WITHOUT reconstructing a single `Expr`. It reads field 0
    /// (`imports`, for the closure walk), field 1 (`constNames`), and field 3
    /// (`extraConstNames`, codegen-emitted names), and returns them joined —
    /// but never touches field 2 (`constants`), so it costs a name-array walk,
    /// not a full expr reconstruction. Result names are in file order,
    /// `constNames` first then `extraConstNames`.
    ///
    /// # ENSURES
    /// - Returns `(imports, const_names)` equivalent to
    ///   `(parse_module(bytes)?.imports, [const_names ++ extra_const_names])`.
    /// - Does NOT parse constants, types, or expressions (much faster / lighter).
    pub fn read_imports_and_const_names_only(
        &self,
    ) -> OleanResult<(Vec<ParsedImport>, Vec<String>)> {
        let root_ptr = self.root_ptr()?;
        if !is_ptr(root_ptr) {
            return Err(OleanError::Region("Invalid root pointer".into()));
        }
        let root_offset = self.ptr_to_offset(root_ptr)?;
        let header = self.read_header_at(root_offset)?;
        let num_fields = header.other as usize;
        let field_offset = root_offset + 8; // Skip header

        let mut imports = Vec::new();
        let mut names = Vec::new();

        // Field 0: imports (Array Import)
        if num_fields >= 1 {
            let imports_ptr = self.read_u64_at(field_offset)?;
            imports = self.read_import_array(imports_ptr)?;
        }
        // Field 1: constNames (Array Name) — the declared public names.
        if num_fields >= 2 {
            let const_names_ptr = self.read_u64_at(field_offset + 8)?;
            names = self.read_name_array_from_names(const_names_ptr)?;
        }
        // Field 3: extraConstNames (Array Name) — codegen-emitted names. Skips
        // field 2 (constants) between them, which is the expensive array.
        if num_fields >= 4 {
            let extra_ptr = self.read_u64_at(field_offset + 24)?;
            names.extend(self.read_name_array_from_names(extra_ptr)?);
        }

        Ok((imports, names))
    }

    /// Read a u64 length field and convert to usize with overflow checks.
    pub(crate) fn read_usize_at(&self, offset: usize, context: &str) -> OleanResult<usize> {
        let raw = self.read_u64_at(offset)?;
        usize::try_from(raw)
            .map_err(|_| OleanError::Region(format!("{context} size exceeds platform limits")))
    }

    /// Validate array bounds with overflow-safe arithmetic.
    ///
    /// Checks that accessing `size` elements at `offset + 24 + i * 8` is safe.
    /// Returns an error if the calculation would overflow or exceed data bounds.
    pub(crate) fn validate_array_bounds(&self, offset: usize, size: usize) -> OleanResult<()> {
        // Array header is 24 bytes, each element pointer is 8 bytes
        let total_size = size
            .checked_mul(8)
            .and_then(|s| s.checked_add(24))
            .ok_or_else(|| OleanError::Region("Array size overflow".into()))?;

        offset
            .checked_add(total_size)
            .filter(|&end| end <= self.data.len())
            .ok_or_else(|| OleanError::Region("Array extends past data".into()))?;

        Ok(())
    }

    /// Compute the offset of an array element with overflow-safe arithmetic.
    pub(crate) fn array_elem_offset(
        &self,
        offset: usize,
        index: usize,
        context: &str,
    ) -> OleanResult<usize> {
        let elem_offset = index
            .checked_mul(8)
            .and_then(|s| s.checked_add(24))
            .and_then(|s| offset.checked_add(s))
            .ok_or_else(|| OleanError::Region(format!("{context} element offset overflow")))?;

        Ok(elem_offset)
    }

    /// Read an array of Import structures
    pub(crate) fn read_import_array_raw(&self, ptr: u64) -> OleanResult<Vec<ParsedImport>> {
        self.read_import_array(ptr)
    }

    /// Read an array of Import structures
    fn read_import_array(&self, ptr: u64) -> OleanResult<Vec<ParsedImport>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }

        let size = self.read_usize_at(offset + 8, "Import array")?;
        self.validate_array_bounds(offset, size)?;
        let mut imports = Vec::with_capacity(size);

        for i in 0..size {
            // SAFETY: bounds validated above
            let elem_offset = self.array_elem_offset(offset, i, "Import array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if is_ptr(elem_ptr) {
                let import = self.read_import(elem_ptr)?;
                imports.push(import);
            } else {
                // Import array should only contain pointer elements
                return Err(OleanError::Region(format!(
                    "Invalid import element at index {i}: expected pointer, got {elem_ptr:#x}"
                )));
            }
        }

        Ok(imports)
    }

    /// Read a single Import structure
    ///
    /// Import layout: { module: Name, runtimeOnly: Bool }
    /// - tag=0, fields=1 (the Name pointer)
    /// - Bool is stored as scalar data after the pointer fields
    fn read_import(&self, ptr: u64) -> OleanResult<ParsedImport> {
        if !is_ptr(ptr) {
            return Err(OleanError::Region("Invalid import pointer".into()));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        // Read the module name (first field)
        let module_name = if header.other >= 1 {
            let name_ptr = self.read_u64_at(offset + 8)?;
            self.resolve_name_ptr(name_ptr)?
        } else {
            return Err(OleanError::Region("Import has no module name field".into()));
        };

        // Read runtimeOnly (scalar byte after pointer fields)
        // cs_sz includes the 8-byte header, so scalar data starts at offset + 8 + num_fields * 8
        let scalar_offset = offset + 8 + (header.other as usize * 8);
        let runtime_only = if scalar_offset < self.data.len() {
            self.data[scalar_offset] != 0
        } else {
            false
        };

        Ok(ParsedImport {
            module_name,
            runtime_only,
        })
    }

    /// Read an array of Name objects (where elements are actual Name.str objects)
    fn read_name_array_from_names(&self, ptr: u64) -> OleanResult<Vec<String>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }

        let size = self.read_usize_at(offset + 8, "Name array")?;
        self.validate_array_bounds(offset, size)?;
        let mut names = Vec::with_capacity(size);

        for i in 0..size {
            // SAFETY: bounds validated above
            let elem_offset = self.array_elem_offset(offset, i, "Name array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if is_ptr(elem_ptr) {
                let elem_off = self.ptr_to_offset(elem_ptr)?;
                let name = self.read_name_at(elem_off)?;
                names.push(name);
            } else if is_scalar(elem_ptr) {
                // Name.anonymous is represented as scalar 0
                names.push(String::new());
            } else {
                // Name array elements must be pointers (Name.str) or scalars (Name.anonymous)
                return Err(OleanError::Region(format!(
                    "Invalid name element at index {i}: {elem_ptr:#x} is neither pointer nor scalar"
                )));
            }
        }

        Ok(names)
    }
}

use crate::header::MAGIC;
