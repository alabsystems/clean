// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Lean.structureExt` entry parsing for CompactedRegion: the field table and
//! parent list of every structure a module declares.
//!
//! Split out of `extensions.rs` (the generic extension reader) to keep that
//! file under the paragon 1000-line limit.

use super::{
    ParsedExtensionEntry, ParsedStructureEntry, ParsedStructureField, ParsedStructureParent,
};
use crate::error::OleanResult;
use crate::region::{is_ptr, tags, CompactedRegion};

/// The persisted name of Lean 4's structure-metadata extension
/// (`Lean/Structure.lean`, `private builtin_initialize structureExt :
/// PersistentEnvExtension StructureInfo StructureInfo …`, named by
/// `decl_name%`). Because the initializer is `private`, the persisted name
/// carries Lean's private-name prefix — measured on the pinned v4.30.0-rc2
/// `Init/Prelude.olean`: `_private.Lean.Structure.1.Lean.structureExt` — whose
/// numeric component is a per-file counter, so the match is on the suffix
/// (see [`is_structure_extension_name`]). Its exported entries are a plain
/// `Array StructureInfo`, sorted by `StructureInfo.lt` — no
/// `ScopedEnvExtension.Entry` wrapper.
pub(crate) const LEAN_STRUCTURE_EXTENSION: &str = "Lean.structureExt";

/// Whether a persisted extension name is Lean's `structureExt`: the bare
/// name, or the same name under a `_private.…` prefix (a private declaration's
/// `decl_name%`).
#[must_use]
pub(crate) fn is_structure_extension_name(name: &str) -> bool {
    name == LEAN_STRUCTURE_EXTENSION
        || (name.starts_with("_private.") && name.ends_with(".Lean.structureExt"))
}

/// Object (pointer) slots of a Lean 4 v4.x `StructureInfo`: `structName`,
/// `fieldNames : Array Name`, `fieldInfo : Array StructureFieldInfo`,
/// `parentInfo : Array StructureParentInfo` (`Lean/Structure.lean:60-70`).
/// No trailing scalar.
const STRUCTURE_INFO_OBJ_FIELDS: u8 = 4;

/// Object slots of a `StructureFieldInfo`: `fieldName`, `projFn`,
/// `subobject? : Option Name`, `autoParam? : Option Expr`
/// (`Lean/Structure.lean:25-36`). The trailing `binderInfo : BinderInfo` is a
/// `uint8` scalar after the object slots.
const STRUCTURE_FIELD_INFO_OBJ_FIELDS: u8 = 4;

/// Byte offset of the `binderInfo` scalar inside a `StructureFieldInfo`:
/// 8-byte header + 4 object slots.
const STRUCTURE_FIELD_INFO_BINDER_OFFSET: usize =
    8 + (STRUCTURE_FIELD_INFO_OBJ_FIELDS as usize) * 8;

/// Object slots of a `StructureParentInfo`: `structName`, `projFn`
/// (`Lean/Structure.lean:48-55`). The trailing `subobject : Bool` is a
/// `uint8` scalar after the object slots.
const STRUCTURE_PARENT_INFO_OBJ_FIELDS: u8 = 2;

/// Byte offset of the `subobject` scalar inside a `StructureParentInfo`:
/// 8-byte header + 2 object slots.
const STRUCTURE_PARENT_INFO_SUBOBJECT_OFFSET: usize =
    8 + (STRUCTURE_PARENT_INFO_OBJ_FIELDS as usize) * 8;

impl<'a> CompactedRegion<'a> {
    /// Read a `Lean.structureExt` entry array with the real Lean 4 layout:
    /// each element is a `StructureInfo` object (no scoped-entry wrapper).
    ///
    /// Same contract as [`Self::read_class_entry_array`]: an element that does
    /// not match the pinned layout is absent from the result and COUNTED, so
    /// a different toolchain degrades to the pre-decoder behaviour (no field
    /// table, no parents for that structure) loudly rather than wrongly.
    pub(super) fn read_structure_entry_array(
        &self,
        ptr: u64,
    ) -> OleanResult<(Vec<ParsedExtensionEntry>, usize)> {
        if !is_ptr(ptr) {
            return Ok((Vec::new(), 0));
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok((Vec::new(), 0));
        }
        let size = self.read_usize_at(offset + 8, "Structure entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);
        let mut undecoded = 0usize;
        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Structure entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            match self.read_structure_entry(elem_ptr) {
                Ok(Some(entry)) => entries.push(ParsedExtensionEntry::Structure(entry)),
                Ok(None) | Err(_) => undecoded += 1,
            }
        }
        Ok((entries, undecoded))
    }

    /// Decode one Lean 4 `StructureInfo` object (`Lean/Structure.lean:60-70`).
    ///
    /// Object slots in declaration order: `structName : Name` (0),
    /// `fieldNames : Array Name` (1), `fieldInfo : Array StructureFieldInfo`
    /// (2), `parentInfo : Array StructureParentInfo` (3); tag 0, no scalar.
    /// `Ok(None)` when the object does not match, so the caller counts it.
    fn read_structure_entry(&self, ptr: u64) -> OleanResult<Option<ParsedStructureEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if !header.is_constructor() || header.tag != 0 || header.other != STRUCTURE_INFO_OBJ_FIELDS
        {
            return Ok(None);
        }
        let struct_name = self.resolve_name_ptr(self.read_u64_at(offset + 8)?)?;
        let Some(field_names) = self.read_name_array(self.read_u64_at(offset + 16)?)? else {
            return Ok(None);
        };
        let Some(fields) = self.read_structure_field_array(self.read_u64_at(offset + 24)?)? else {
            return Ok(None);
        };
        let Some(parents) = self.read_structure_parent_array(self.read_u64_at(offset + 32)?)?
        else {
            return Ok(None);
        };
        Ok(Some(ParsedStructureEntry {
            struct_name,
            field_names,
            fields,
            parents,
        }))
    }

    /// Decode an `Array StructureFieldInfo`; `Ok(None)` on any element that
    /// does not match the pinned layout (the whole entry is then undecoded —
    /// a partial field table would be worse than none).
    fn read_structure_field_array(
        &self,
        ptr: u64,
    ) -> OleanResult<Option<Vec<ParsedStructureField>>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(None);
        }
        let size = self.read_usize_at(offset + 8, "StructureFieldInfo array")?;
        self.validate_array_bounds(offset, size)?;
        let mut out = Vec::with_capacity(size);
        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "StructureFieldInfo array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if !is_ptr(elem_ptr) {
                return Ok(None);
            }
            let eo = self.ptr_to_offset(elem_ptr)?;
            let eh = self.read_header_at(eo)?;
            if !eh.is_constructor()
                || eh.tag != 0
                || eh.other != STRUCTURE_FIELD_INFO_OBJ_FIELDS
                || (eh.cs_sz as usize) <= STRUCTURE_FIELD_INFO_BINDER_OFFSET
            {
                return Ok(None);
            }
            let field_name = self.resolve_name_ptr(self.read_u64_at(eo + 8)?)?;
            let proj_fn = self.resolve_name_ptr(self.read_u64_at(eo + 16)?)?;
            let Some(subobject) = self.read_option_name(self.read_u64_at(eo + 24)?)? else {
                return Ok(None);
            };
            // Slot 3, `autoParam? : Option Expr`, is deprecated upstream and
            // not consumed here.
            let binder_info = self.bytes_at(eo + STRUCTURE_FIELD_INFO_BINDER_OFFSET, 1)?[0];
            out.push(ParsedStructureField {
                field_name,
                proj_fn,
                subobject,
                binder_info,
            });
        }
        Ok(Some(out))
    }

    /// Decode an `Array StructureParentInfo`; same all-or-nothing contract as
    /// [`Self::read_structure_field_array`].
    fn read_structure_parent_array(
        &self,
        ptr: u64,
    ) -> OleanResult<Option<Vec<ParsedStructureParent>>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(None);
        }
        let size = self.read_usize_at(offset + 8, "StructureParentInfo array")?;
        self.validate_array_bounds(offset, size)?;
        let mut out = Vec::with_capacity(size);
        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "StructureParentInfo array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if !is_ptr(elem_ptr) {
                return Ok(None);
            }
            let eo = self.ptr_to_offset(elem_ptr)?;
            let eh = self.read_header_at(eo)?;
            if !eh.is_constructor()
                || eh.tag != 0
                || eh.other != STRUCTURE_PARENT_INFO_OBJ_FIELDS
                || (eh.cs_sz as usize) <= STRUCTURE_PARENT_INFO_SUBOBJECT_OFFSET
            {
                return Ok(None);
            }
            let struct_name = self.resolve_name_ptr(self.read_u64_at(eo + 8)?)?;
            let proj_fn = self.resolve_name_ptr(self.read_u64_at(eo + 16)?)?;
            let subobject = self.bytes_at(eo + STRUCTURE_PARENT_INFO_SUBOBJECT_OFFSET, 1)?[0] != 0;
            out.push(ParsedStructureParent {
                struct_name,
                subobject,
                proj_fn,
            });
        }
        Ok(Some(out))
    }
}
