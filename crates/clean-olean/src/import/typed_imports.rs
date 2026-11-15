// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural module identities; display-projected ParsedImport is not a
//! dependency graph key. Flag interpretations are explicit per file layout.

use crate::error::{OleanError, OleanResult};
use crate::region::{is_ptr, tags, CompactedRegion, TypedModuleLayout};
use clean_kernel::name::Name;

/// Flags whose meanings must not be conflated across Lean file formats.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedImportFlags {
    /// Lean 4.13 `Import` in upstream `src/Lean/Environment.lean`.
    LeanV1 { runtime_only: bool },
    /// Modern Lean module system; the first bit is not runtime-only.
    LeanV2 {
        import_all: bool,
        is_exported: bool,
        is_meta: bool,
    },
    /// Clean's historical exporter, separately identified from Lean output.
    CleanLegacy { runtime_only: bool },
}

/// Exact module Name and format-specific import flags decoded from file bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedImport {
    pub module_name: Name,
    pub flags: TypedImportFlags,
}

/// Read exact import names without materializing declaration expressions.
/// Unknown envelopes, malformed rows and noncanonical Booleans are errors.
pub fn parse_typed_imports(bytes: &[u8]) -> OleanResult<Vec<TypedImport>> {
    let header = crate::parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.typed_module_layout()?;
    let root = region.ptr_to_offset(region.root_ptr()?)?;
    let pointer = region.read_u64_at(root + 8)?;
    region.read_typed_import_array(pointer)
}

/// Validate the same array envelope as the decoder, without allocating its
/// rows or decoding their names. A checked graph can charge its caller's
/// explicit row budget before row allocation, cache lookup or graph growth.
pub(crate) fn typed_import_count(bytes: &[u8]) -> OleanResult<usize> {
    let header = crate::parse_header(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    region.typed_module_layout()?;
    typed_import_count_from_region(&region, region.root_ptr()?)
}

/// The same envelope count at a validated companion root in the production
/// Load parser's assembled captured pointer space.
pub(crate) fn typed_import_count_from_region(
    region: &CompactedRegion<'_>,
    root_pointer: u64,
) -> OleanResult<usize> {
    let root = region.ptr_to_offset(root_pointer)?;
    let pointer = region.read_u64_at(root + 8)?;
    region
        .typed_import_array_header(pointer)
        .map(|(_, _, size)| size)
}

fn invalid(message: &str) -> OleanError {
    OleanError::Region(message.to_owned())
}

impl CompactedRegion<'_> {
    fn typed_import_array_header(
        &self,
        pointer: u64,
    ) -> OleanResult<(TypedModuleLayout, usize, usize)> {
        let layout = self.typed_module_layout()?;
        if !is_ptr(pointer) {
            return Err(invalid("typed import array must be an Array pointer"));
        }
        let offset = self.ptr_to_offset(pointer)?;
        let header = self.read_header_at(offset)?;
        let array_size = if layout == TypedModuleLayout::CleanLegacy {
            0
        } else {
            1
        };
        if (header.rc, header.cs_sz, header.other, header.tag) != (0, array_size, 0, tags::ARRAY) {
            return Err(invalid("unsupported typed import Array header"));
        }
        let size = self.read_usize_at(offset + 8, "typed import array")?;
        let capacity = self.read_usize_at(offset + 16, "typed import array capacity")?;
        if size > capacity {
            return Err(invalid("typed import Array length exceeds capacity"));
        }
        self.validate_array_bounds(offset, size)?;
        Ok((layout, offset, size))
    }

    pub(crate) fn read_typed_import_array(&self, pointer: u64) -> OleanResult<Vec<TypedImport>> {
        let (layout, offset, size) = self.typed_import_array_header(pointer)?;
        let mut imports = Vec::with_capacity(size);
        for index in 0..size {
            let pointer =
                self.read_u64_at(self.array_elem_offset(offset, index, "typed imports")?)?;
            if !is_ptr(pointer) {
                return Err(invalid("typed Import row must be a constructor pointer"));
            }
            let at = self.ptr_to_offset(pointer)?;
            let header = self.read_header_at(at)?;
            let object_size = if layout == TypedModuleLayout::CleanLegacy {
                0
            } else {
                24
            };
            if (header.rc, header.cs_sz, header.other, header.tag) != (0, object_size, 1, 0) {
                return Err(invalid("unsupported typed Import constructor header"));
            }
            self.bytes_at(at, 24)?;
            let boolean = |index| -> OleanResult<bool> {
                match self.bytes_at(at + 16 + index, 1)?[0] {
                    0 => Ok(false),
                    1 => Ok(true),
                    _ => Err(invalid("typed Import flag is not a canonical Bool")),
                }
            };
            let flags = match layout {
                TypedModuleLayout::LeanV1 => TypedImportFlags::LeanV1 {
                    runtime_only: boolean(0)?,
                },
                TypedModuleLayout::LeanV2 => TypedImportFlags::LeanV2 {
                    import_all: boolean(0)?,
                    is_exported: boolean(1)?,
                    is_meta: boolean(2)?,
                },
                TypedModuleLayout::CleanLegacy => TypedImportFlags::CleanLegacy {
                    runtime_only: boolean(0)?,
                },
            };
            imports.push(TypedImport {
                module_name: self.read_kernel_name_ptr(self.read_u64_at(at + 8)?)?,
                flags,
            });
        }
        Ok(imports)
    }
}
