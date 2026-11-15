// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed identity reads for the direct kernel importer. The legacy String
//! projection remains a diagnostic/round-trip API, not a source of identity.
use super::{is_ptr, tags, CompactedRegion};
use crate::error::{OleanError, OleanResult};
use clean_kernel::level::Level;
use clean_kernel::name::{Name, NameInner};
use std::collections::BTreeSet;

const NAME_COMPONENTS: usize = 256;
const LIST_ITEMS: usize = 100_000;

/// Measured compacted ModuleData variants, not a claim of whole-format support.
/// Keep this shared with direct companion and extension readers: failed modern
/// decoding must never select the Clean-export interpretation of payloads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypedModuleLayout {
    /// Lean v4.13: v1 file header, five fields, no isModule scalar.
    LeanV1,
    /// Measured modern Lean: v2 header, five fields and isModule scalar.
    LeanV2,
    /// Clean's older exporter: v1 header and zero compact object sizes.
    CleanLegacy,
}

fn invalid(message: impl Into<String>) -> OleanError {
    OleanError::Region(message.into())
}

impl CompactedRegion<'_> {
    pub(crate) fn typed_module_layout(&self) -> OleanResult<TypedModuleLayout> {
        self.typed_module_layout_at(self.root_ptr()?)
    }

    /// Decode an explicit root in an already assembled captured pointer space.
    /// The caller must establish matching part headers and captured extents;
    /// this does not authorize references into omitted or future parts.
    pub(crate) fn typed_module_layout_at(&self, pointer: u64) -> OleanResult<TypedModuleLayout> {
        let file = crate::header::OleanHeader::parse(self.data)?;
        if !is_ptr(pointer) || !pointer.is_multiple_of(8) {
            return Err(invalid("invalid compacted ModuleData pointer"));
        }
        let root = self.ptr_to_offset(pointer)?;
        let h = self.read_header_at(root)?;
        if h.rc != 0 || h.tag != 0 || h.other != 5 {
            return Err(invalid("unsupported compacted ModuleData header"));
        }
        let (layout, bytes) = match (file.version, file.flags, h.cs_sz) {
            (1, 0, 48) => (TypedModuleLayout::LeanV1, 48),
            (2, 0 | 1, 56) => (TypedModuleLayout::LeanV2, 56),
            (1, 0, 0) => (TypedModuleLayout::CleanLegacy, 48),
            _ => {
                return Err(invalid(
                    "typed Name decoding requires a recognized ModuleData envelope",
                ))
            }
        };
        self.bytes_at(root, bytes)?;
        Ok(layout)
    }

    /// Whether the ModuleData rooted at `pointer` is a part Lean's own
    /// compiler wrote (`LeanV1`/`LeanV2`), as opposed to Clean's exporter
    /// (`CleanLegacy`). Used to refuse a `CLEANENV` trailer on a Lean part
    /// (R113, finding B3): only Clean's exporter appends that trailer, and only
    /// to its own layout.
    pub(crate) fn root_is_lean_layout(&self, pointer: u64) -> OleanResult<bool> {
        Ok(matches!(
            self.typed_module_layout_at(pointer)?,
            TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2
        ))
    }

    /// Preserve the Name constructors, including empty/dotted/numeric strings.
    /// Only the exact tagged anonymous scalar is accepted without an object.
    pub(crate) fn read_kernel_name_ptr(&self, pointer: u64) -> OleanResult<Name> {
        if pointer == 1 {
            return Ok(Name::anon());
        }
        if let Some(name) = self.typed_names.borrow().get(&pointer) {
            return Ok(name.clone());
        }
        let encoding = self.typed_module_layout()?;
        let mut current = pointer;
        let mut seen = BTreeSet::new();
        enum Part {
            Str(String),
            Num(u64),
        }
        let mut chain = Vec::new();
        let mut name;
        loop {
            if current == 1 {
                name = Name::anon();
                break;
            }
            if !seen.insert(current) {
                return Err(invalid("typed Name cycle or component bound"));
            }
            if !is_ptr(current) {
                return Err(invalid("invalid typed Name scalar or null"));
            }
            if let Some(cached) = self.typed_names.borrow().get(&current) {
                name = cached.clone();
                break;
            }
            let offset = self.ptr_to_offset(current)?;
            let h = self.read_header_at(offset)?;
            if h.rc != 0 {
                return Err(invalid("nonzero compacted typed Name reference count"));
            }
            if matches!(encoding, TypedModuleLayout::CleanLegacy)
                && (h.tag, h.other, h.cs_sz) == (0, 0, 0)
            {
                name = Name::anon();
                self.typed_names.borrow_mut().insert(current, name.clone());
                break;
            }
            // Clean's older exporter uses cs_sz=0 and raw u64 Name.num;
            // modern Lean uses cs_sz=32 and a boxed Nat plus cached hash.
            let size = match encoding {
                TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => 32,
                TypedModuleLayout::CleanLegacy => 0,
            };
            if h.other != 2 || h.cs_sz != size || !matches!(h.tag, 1 | 2) {
                return Err(invalid(format!(
                    "unsupported typed Name layout {}/{}/{}",
                    h.tag, h.other, h.cs_sz
                )));
            }
            self.bytes_at(offset, if size == 0 { 24 } else { usize::from(size) })?;
            let parent = self.read_u64_at(offset + 8)?;
            let value = self.read_u64_at(offset + 16)?;
            let part = if h.tag == 1 {
                if !is_ptr(value) {
                    return Err(invalid("Name.str component is not a String pointer"));
                }
                let s = self.ptr_to_offset(value)?;
                let sh = self.read_header_at(s)?;
                if sh.tag != tags::STRING || sh.rc != 0 || sh.other != 0 {
                    return Err(invalid("invalid compacted Name String header"));
                }
                let size = usize::try_from(self.read_u64_at(s + 8)?)
                    .map_err(|_| invalid("Name String size overflow"))?;
                let capacity = self.read_u64_at(s + 16)?;
                if size == 0 || size > 1_048_576 || size as u64 > capacity {
                    return Err(invalid("Name String size/capacity bound"));
                }
                let start = s
                    .checked_add(32)
                    .ok_or_else(|| invalid("Name String offset overflow"))?;
                let bytes = self.bytes_at(start, size)?;
                let content = bytes
                    .strip_suffix(&[0])
                    .ok_or_else(|| invalid("Name String missing terminator"))?;
                let value = std::str::from_utf8(content)
                    .map_err(|_| invalid("Name String invalid UTF-8"))?;
                if self.read_u64_at(s + 24)? != value.chars().count() as u64 {
                    return Err(invalid("Name String character count mismatch"));
                }
                Part::Str(value.to_owned())
            } else {
                Part::Num(match encoding {
                    TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => {
                        self.read_kernel_nat_u64(value)?
                    }
                    TypedModuleLayout::CleanLegacy => value,
                })
            };
            if chain.len() >= NAME_COMPONENTS {
                return Err(invalid("typed Name component bound"));
            }
            chain.push((current, part));
            current = parent;
        }
        // A cached suffix must not allow a longer name to evade the bound.
        let mut ancestor = &name;
        let mut depth = chain.len();
        while let NameInner::Str(parent, _) | NameInner::Num(parent, _) = ancestor.inner() {
            depth += 1;
            if depth > NAME_COMPONENTS {
                return Err(invalid(
                    "typed Name component bound including cached parent",
                ));
            }
            ancestor = parent;
        }
        for (pointer, part) in chain.into_iter().rev() {
            name = match part {
                Part::Str(value) => name.str(&value),
                Part::Num(value) => name.num(value),
            };
            self.typed_names.borrow_mut().insert(pointer, name.clone());
        }
        Ok(name)
    }

    /// A non-truncating Nat read. Large Name numbers exceed the current kernel
    /// carrier and must refuse, never become a pointer or low-limb alias.
    pub(crate) fn read_kernel_nat_u64(&self, pointer: u64) -> OleanResult<u64> {
        if pointer & 1 == 1 {
            return Ok(pointer >> 1);
        }
        if !is_ptr(pointer) {
            return Err(invalid("null Nat pointer"));
        }
        let file = crate::header::OleanHeader::parse(self.data)?;
        if file.version != 2 || file.flags != 1 {
            return Err(invalid(
                "heap Nat requires the measured v2 GMP region format",
            ));
        }
        let offset = self.ptr_to_offset(pointer)?;
        let h = self.read_header_at(offset)?;
        if h.tag != tags::MPZ || h.rc != 0 || h.other != 0 || h.cs_sz != 32 {
            return Err(invalid("invalid compacted Nat MPZ header"));
        }
        let alloc = self.read_i32_at(offset + 8)?;
        let size = self.read_i32_at(offset + 12)?;
        if size != 1 || alloc != 1 {
            return Err(invalid(
                "Nat does not have a positive single-limb u64 representation",
            ));
        }
        let digits = self.read_u64_at(offset + 16)?;
        let expected = pointer
            .checked_add(24)
            .ok_or_else(|| invalid("MPZ digits address overflow"))?;
        if digits != expected {
            return Err(invalid("compacted MPZ digits are not inline"));
        }
        let value = self.read_u64_at(offset + 24)?;
        if value < (1u64 << 63) {
            return Err(invalid("noncanonical boxed small Nat"));
        }
        Ok(value)
    }

    fn read_typed_list(&self, pointer: u64) -> OleanResult<Vec<u64>> {
        let mut pointer = pointer;
        let mut items = Vec::new();
        let mut seen = BTreeSet::new();
        while pointer != 1 {
            if !is_ptr(pointer) || !seen.insert(pointer) || items.len() >= LIST_ITEMS {
                return Err(invalid("malformed/cyclic/over-bound typed list"));
            }
            let offset = self.ptr_to_offset(pointer)?;
            let h = self.read_header_at(offset)?;
            if (h.tag, h.other, h.rc) != (1, 2, 0) || !matches!(h.cs_sz, 0 | 24) {
                return Err(invalid("malformed typed list constructor"));
            }
            items.push(self.read_u64_at(offset + 8)?);
            pointer = self.read_u64_at(offset + 16)?;
        }
        Ok(items)
    }

    pub(crate) fn read_kernel_name_list(&self, pointer: u64) -> OleanResult<Vec<Name>> {
        self.read_typed_list(pointer)?
            .into_iter()
            .map(|p| self.read_kernel_name_ptr(p))
            .collect()
    }

    pub(crate) fn read_kernel_level_list(&self, pointer: u64) -> OleanResult<Vec<Level>> {
        self.read_typed_list(pointer)?
            .into_iter()
            .map(|p| self.read_kernel_level_ptr(p))
            .collect()
    }

    pub(crate) fn read_kernel_level_ptr(&self, pointer: u64) -> OleanResult<Level> {
        self.read_kernel_level_inner(pointer, &mut BTreeSet::new(), &mut 100_000, 0)
    }

    fn read_kernel_level_inner(
        &self,
        pointer: u64,
        path: &mut BTreeSet<u64>,
        fuel: &mut usize,
        depth: usize,
    ) -> OleanResult<Level> {
        *fuel = fuel
            .checked_sub(1)
            .ok_or_else(|| invalid("typed Level visit bound"))?;
        if depth > 256 || !path.insert(pointer) {
            return Err(invalid("typed Level cycle or depth bound"));
        }
        let result = (|| {
            if pointer == 1 {
                return Ok(Level::zero());
            }
            if !is_ptr(pointer) {
                return Err(invalid("invalid typed Level scalar or null"));
            }
            let offset = self.ptr_to_offset(pointer)?;
            let h = self.read_header_at(offset)?;
            let required = match h.tag {
                0 => 0,
                1 | 4 => 1,
                2 | 3 => 2,
                5 => return Err(invalid("unresolved Level metavariable")),
                _ => return Err(invalid("unknown typed Level tag")),
            };
            if h.other != required || h.rc != 0 {
                return Err(invalid("malformed compacted typed Level header"));
            }
            let bytes = match self.typed_module_layout()? {
                TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => {
                    let expected = 16 + u16::from(required) * 8;
                    if h.cs_sz != expected {
                        return Err(invalid("unknown modern typed Level size"));
                    }
                    usize::from(expected)
                }
                TypedModuleLayout::CleanLegacy => {
                    if h.cs_sz != 0 {
                        return Err(invalid("unknown legacy typed Level size"));
                    }
                    8 + usize::from(required) * 8
                }
            };
            self.bytes_at(offset, bytes)?;
            match h.tag {
                0 => Ok(Level::zero()),
                4 => Ok(Level::param(
                    self.read_kernel_name_ptr(self.read_u64_at(offset + 8)?)?,
                )),
                _ => {
                    let left = self.read_kernel_level_inner(
                        self.read_u64_at(offset + 8)?,
                        path,
                        fuel,
                        depth + 1,
                    )?;
                    if h.tag == 1 {
                        return Ok(Level::succ(left));
                    }
                    let right = self.read_kernel_level_inner(
                        self.read_u64_at(offset + 16)?,
                        path,
                        fuel,
                        depth + 1,
                    )?;
                    // Verbatim, as Lean's kernel reads it (DECISIONS R150).
                    Ok(if h.tag == 2 {
                        Level::Max(left.into(), right.into())
                    } else {
                        Level::IMax(left.into(), right.into())
                    })
                }
            }
        })();
        path.remove(&pointer);
        result
    }
}

#[cfg(test)]
mod tests;
