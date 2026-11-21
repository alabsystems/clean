// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stable Lean v2 object encodings and the ordinary ModuleData root.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::name::NameInner;
use clean_kernel::{BigNat, LeanWorld, Name};

use crate::error::{OleanError, OleanResult};
use crate::header::{OleanHeader, HEADER_SIZE_V2, MAGIC, VERSION_V2};
use crate::region::tags;
use crate::world::{lean_worlds, row_of_source_world, HeaderIdentity, WorldState};
use crate::{TypedImport, TypedImportFlags};

const WORD: usize = 8;
const FIRST_OBJECT: usize = HEADER_SIZE_V2 + WORD;
const MAX_SCALAR: u64 = u64::MAX >> 1;
const MAX_CTOR_SCALARS: usize = 1023;
const GMP_BIGNUMS: u8 = 1;
const LEAN_REGION_ALIGNMENT: u64 = 1 << 16;
const LEAN_REGION_BASE_LIMIT: u64 = 0x7f00_0000_0000;
static NEXT_REGION: AtomicU64 = AtomicU64::new(1);

/// A boxed Lean scalar or a handle to an object in one writer's region group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeanV2Value {
    word: u64,
    region: u64,
}

impl LeanV2Value {
    /// Box an immediate value, such as a nullary constructor tag.
    ///
    /// # Errors
    /// Refuses a value outside the 63-bit immediate range. Use
    /// [`LeanV2RegionWriter::write_nat`] for larger natural numbers.
    pub fn scalar(value: u64) -> OleanResult<Self> {
        if value > MAX_SCALAR {
            return Err(region_error("Lean immediate value exceeds 63 bits"));
        }
        Ok(Self {
            word: (value << 1) | 1,
            region: 0,
        })
    }
}

/// Write the measured 64-bit, little-endian Lean 4.36.0 GMP object layout.
///
/// The target header supplies format compatibility. This low-level writer
/// does not establish declaration validity or compiler provenance.
pub struct LeanV2RegionWriter {
    base_addr: u64,
    region: u64,
    bytes: Vec<u8>,
    strings: HashMap<String, LeanV2Value>,
    names: HashMap<Name, LeanV2Value>,
}

impl LeanV2RegionWriter {
    /// Start an ordinary file for the registered stable Lean 4.36.0 build.
    ///
    /// # Errors
    /// Refuses a mismatching header, an unaligned virtual base, or an
    /// address range that cannot contain the file header.
    pub fn new(target: &OleanHeader, base_addr: u64) -> OleanResult<Self> {
        let stable = row_of_source_world(lean_worlds(), LeanWorld::Lean436)
            .ok_or_else(|| region_error("missing stable Lean export world"))?;
        let version_name = target
            .lean_version_str()
            .filter(|version| version.len() <= 33 && Some(*version) == stable.lean_version);
        let Some(version_name) = version_name else {
            return Err(region_error("wrong Lean version for stable v2 export"));
        };
        if target.magic != *MAGIC
            || target.version != VERSION_V2
            || target.flags != GMP_BIGNUMS
            || stable.state == WorldState::Canary
            || HeaderIdentity::of_header(target) != stable.identity
        {
            return Err(region_error("wrong Lean identity for stable v2 export"));
        }
        if !base_addr.is_multiple_of(WORD as u64)
            || base_addr.checked_add(FIRST_OBJECT as u64).is_none()
        {
            return Err(region_error("invalid virtual base for Lean v2 export"));
        }
        let mut region = NEXT_REGION.load(Ordering::Relaxed);
        loop {
            let next = region
                .checked_add(1)
                .ok_or_else(|| region_error("exhausted Lean v2 writer identities"))?;
            match NEXT_REGION.compare_exchange_weak(
                region,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => region = current,
            }
        }
        let mut bytes = vec![0; FIRST_OBJECT];
        bytes[..5].copy_from_slice(MAGIC);
        bytes[5] = VERSION_V2;
        bytes[6] = target.flags;
        bytes[7..7 + version_name.len()].copy_from_slice(version_name.as_bytes());
        bytes[40..80].copy_from_slice(&target.git_hash[..40]);
        put_word(&mut bytes, 80, base_addr);
        Ok(Self {
            base_addr,
            region,
            bytes,
            strings: HashMap::new(),
            names: HashMap::new(),
        })
    }

    pub(super) fn for_module(target: &OleanHeader, module_name: &Name) -> OleanResult<Self> {
        if module_name.is_anon() {
            return Err(region_error("Lean export requires a named module"));
        }
        let base =
            (module_name.lean4_hash() % LEAN_REGION_BASE_LIMIT) & !(LEAN_REGION_ALIGNMENT - 1);
        Self::new(target, base)
    }

    /// Write an ordinary constructor with boxed fields and trailing scalars.
    ///
    /// # Errors
    /// Refuses a tag, field count, scalar size, or region reference outside
    /// the runtime layout, and any extent or allocation failure.
    pub fn write_constructor(
        &mut self,
        tag: u8,
        fields: &[LeanV2Value],
        scalars: &[u8],
    ) -> OleanResult<LeanV2Value> {
        if tag > tags::MAX_CTOR_TAG || scalars.len() > MAX_CTOR_SCALARS {
            return Err(region_error("unsupported Lean constructor layout"));
        }
        let count = u8::try_from(fields.len())
            .map_err(|_| region_error("too many Lean constructor fields"))?;
        if fields.is_empty() && scalars.is_empty() {
            return LeanV2Value::scalar(u64::from(tag));
        }
        self.check_fields(fields)?;
        let scalar_start = WORD + fields.len() * WORD;
        let size = align_size(scalar_start + scalars.len())?;
        let compact_size = u16::try_from(size)
            .map_err(|_| region_error("Lean constructor exceeds compact object size"))?;
        let (value, object) = self.allocate(tag, count, compact_size, size)?;
        put_fields(object, WORD, fields);
        object[scalar_start..scalar_start + scalars.len()].copy_from_slice(scalars);
        Ok(value)
    }

    /// Write a typed kernel Name, including its cached Lean hash.
    ///
    /// # Errors
    /// Returns an extent or allocation error while writing the Name.
    pub fn write_name(&mut self, name: &Name) -> OleanResult<LeanV2Value> {
        let mut pending = Vec::new();
        let mut current = name;
        let mut parent = loop {
            if let Some(&value) = self.names.get(current) {
                break value;
            }
            match current.inner() {
                NameInner::Anon => break LeanV2Value::scalar(0)?,
                NameInner::Str(prefix, _) | NameInner::Num(prefix, _) => {
                    pending.push(current);
                    current = prefix;
                }
            }
        };
        for component in pending.into_iter().rev() {
            let (tag, field) = match component.inner() {
                NameInner::Str(_, text) => (1, self.write_string(text)?),
                NameInner::Num(_, number) => (2, self.write_nat(&BigNat::Small(*number))?),
                NameInner::Anon => return Err(region_error("invalid Name component")),
            };
            parent = self.write_constructor(
                tag,
                &[parent, field],
                &component.lean4_hash().to_le_bytes(),
            )?;
            self.names.insert(component.clone(), parent);
        }
        Ok(parent)
    }

    /// Write a Nat as an immediate or a GMP object with inline normalized limbs.
    ///
    /// # Errors
    /// Refuses an object too large for the runtime's compact size field, or
    /// an extent or allocation failure.
    pub fn write_nat(&mut self, nat: &BigNat) -> OleanResult<LeanV2Value> {
        let limbs = nat.limbs();
        let len = limbs
            .iter()
            .rposition(|&limb| limb != 0)
            .map_or(0, |i| i + 1);
        let limbs = &limbs[..len];
        match limbs {
            [] => return LeanV2Value::scalar(0),
            [single] if *single <= MAX_SCALAR => return LeanV2Value::scalar(*single),
            _ => {}
        }
        let size = word_extent(24, len)?;
        let compact_size = u16::try_from(size)
            .map_err(|_| region_error("Lean GMP object exceeds compact object size"))?;
        let count = i32::try_from(len).map_err(|_| region_error("too many Lean GMP limbs"))?;
        let (value, object) = self.allocate(tags::MPZ, 0, compact_size, size)?;
        object[8..12].copy_from_slice(&count.to_le_bytes());
        object[12..16].copy_from_slice(&count.to_le_bytes());
        // A successful allocation checked the address of the entire object.
        put_word(object, 16, value.word + 24);
        for (index, &limb) in limbs.iter().enumerate() {
            put_word(object, 24 + WORD * index, limb);
        }
        Ok(value)
    }

    /// Write a Lean String with UTF-8 bytes and its character count.
    ///
    /// # Errors
    /// Returns an extent or allocation error.
    pub fn write_string(&mut self, text: &str) -> OleanResult<LeanV2Value> {
        if let Some(&value) = self.strings.get(text) {
            return Ok(value);
        }
        let count = text
            .len()
            .checked_add(1)
            .ok_or_else(|| region_error("Lean string size overflow"))?;
        let size = 32usize
            .checked_add(count)
            .ok_or_else(|| region_error("Lean string extent overflow"))?;
        let (value, object) = self.allocate(tags::STRING, 0, 1, size)?;
        put_word(object, 8, count as u64);
        put_word(object, 16, count as u64);
        put_word(object, 24, text.chars().count() as u64);
        object[32..32 + text.len()].copy_from_slice(text.as_bytes());
        self.strings.insert(text.to_owned(), value);
        Ok(value)
    }

    /// Write a compacted boxed Array.
    ///
    /// # Errors
    /// Refuses references to another region and extent or allocation failures.
    pub fn write_array(&mut self, elements: &[LeanV2Value]) -> OleanResult<LeanV2Value> {
        self.check_fields(elements)?;
        let size = word_extent(24, elements.len())?;
        let (value, object) = self.allocate(tags::ARRAY, 0, 1, size)?;
        let length = elements.len() as u64;
        put_word(object, 8, length);
        put_word(object, 16, length);
        put_fields(object, 24, elements);
        Ok(value)
    }

    /// Write the ordered array of modern Lean Import records.
    ///
    /// # Errors
    /// Refuses anonymous modules and flags from a different object layout,
    /// as well as extent or allocation errors.
    pub fn write_imports(&mut self, imports: &[TypedImport]) -> OleanResult<LeanV2Value> {
        let mut rows = Vec::new();
        reserve(&mut rows, imports.len())?;
        for import in imports {
            let TypedImportFlags::LeanV2 {
                import_all,
                is_exported,
                is_meta,
            } = &import.flags
            else {
                return Err(region_error("Lean v2 imports require modern import flags"));
            };
            if import.module_name.is_anon() {
                return Err(region_error("Lean imports require a nonanonymous Name"));
            }
            let name = self.write_name(&import.module_name)?;
            rows.push(self.write_constructor(
                0,
                &[name],
                &[
                    u8::from(*import_all),
                    u8::from(*is_exported),
                    u8::from(*is_meta),
                ],
            )?);
        }
        self.write_array(&rows)
    }

    /// Finish ordinary ModuleData from imports and its other four arrays.
    ///
    /// `constants` and `entries` are already serialized native objects from
    /// this writer. Their declaration and extension semantics remain the
    /// producer's responsibility.
    ///
    /// # Errors
    /// Refuses differing constant/name counts, invalid imports or references,
    /// and extent or allocation failures.
    pub fn finish_ordinary_module(
        mut self,
        imports: &[TypedImport],
        const_names: &[Name],
        constants: &[LeanV2Value],
        extra_const_names: &[Name],
        entries: &[LeanV2Value],
    ) -> OleanResult<Vec<u8>> {
        self.write_module_data(
            imports,
            const_names,
            constants,
            extra_const_names,
            entries,
            false,
        )?;
        Ok(self.bytes)
    }

    /// Serialize the current part and keep its saved objects in the writer's
    /// address space for the remaining views of the same module.
    pub(super) fn finish_split_part(
        &mut self,
        imports: &[TypedImport],
        const_names: &[Name],
        constants: &[LeanV2Value],
        entries: &[LeanV2Value],
    ) -> OleanResult<Vec<u8>> {
        self.write_module_data(imports, const_names, constants, &[], entries, true)?;
        self.finish_part_and_advance()
    }

    pub(super) fn finish_ir_signature(&mut self) -> OleanResult<Vec<u8>> {
        self.write_module_data(&[], &[], &[], &[], &[], false)?;
        self.finish_part_and_advance()
    }

    fn finish_part_and_advance(&mut self) -> OleanResult<Vec<u8>> {
        let next = self
            .base_addr
            .checked_add(self.bytes.len() as u64)
            .and_then(|end| end.checked_add(LEAN_REGION_ALIGNMENT - 1))
            .map(|end| end & !(LEAN_REGION_ALIGNMENT - 1))
            .filter(|base| base.checked_add(FIRST_OBJECT as u64).is_some())
            .ok_or_else(|| {
                region_error("Lean v2 companion extent overflows its virtual address")
            })?;
        let mut open = vec![0; FIRST_OBJECT];
        open[..HEADER_SIZE_V2].copy_from_slice(&self.bytes[..HEADER_SIZE_V2]);
        put_word(&mut open, 80, next);
        self.base_addr = next;
        Ok(std::mem::replace(&mut self.bytes, open))
    }

    pub(super) fn finish_module_view(
        mut self,
        imports: &[TypedImport],
        const_names: &[Name],
        constants: &[LeanV2Value],
        entries: &[LeanV2Value],
    ) -> OleanResult<Vec<u8>> {
        self.write_module_data(imports, const_names, constants, &[], entries, true)?;
        Ok(self.bytes)
    }

    fn write_module_data(
        &mut self,
        imports: &[TypedImport],
        const_names: &[Name],
        constants: &[LeanV2Value],
        extra_const_names: &[Name],
        entries: &[LeanV2Value],
        is_module: bool,
    ) -> OleanResult<()> {
        if const_names.len() != constants.len() {
            return Err(region_error("Lean ModuleData names and constants disagree"));
        }
        let imports = self.write_imports(imports)?;
        let const_names = self.write_names(const_names)?;
        let constants = self.write_array(constants)?;
        let extra_const_names = self.write_names(extra_const_names)?;
        let entries = self.write_array(entries)?;
        let root = self.write_constructor(
            0,
            &[imports, const_names, constants, extra_const_names, entries],
            &[u8::from(is_module)],
        )?;
        put_word(&mut self.bytes, HEADER_SIZE_V2, root.word);
        Ok(())
    }

    fn write_names(&mut self, names: &[Name]) -> OleanResult<LeanV2Value> {
        let mut objects = Vec::new();
        reserve(&mut objects, names.len())?;
        for name in names {
            objects.push(self.write_name(name)?);
        }
        self.write_array(&objects)
    }

    fn check_fields(&self, fields: &[LeanV2Value]) -> OleanResult<()> {
        if fields
            .iter()
            .any(|value| value.region != 0 && value.region != self.region)
        {
            return Err(region_error(
                "Lean object belongs to another compacted region",
            ));
        }
        Ok(())
    }

    fn allocate(
        &mut self,
        tag: u8,
        other: u8,
        compact_size: u16,
        size: usize,
    ) -> OleanResult<(LeanV2Value, &mut [u8])> {
        let size = align_size(size)?;
        let start = self.bytes.len();
        let end = start
            .checked_add(size)
            .ok_or_else(|| region_error("Lean object extent overflow"))?;
        self.base_addr
            .checked_add(end as u64)
            .ok_or_else(|| region_error("Lean object address overflow"))?;
        reserve(&mut self.bytes, size)?;
        self.bytes.resize(end, 0);
        let value = LeanV2Value {
            word: self.base_addr + start as u64,
            region: self.region,
        };
        let object = &mut self.bytes[start..end];
        object[4..6].copy_from_slice(&compact_size.to_le_bytes());
        object[6] = other;
        object[7] = tag;
        Ok((value, object))
    }
}

fn put_word(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + WORD].copy_from_slice(&value.to_le_bytes());
}

fn put_fields(bytes: &mut [u8], start: usize, fields: &[LeanV2Value]) {
    for (index, value) in fields.iter().enumerate() {
        put_word(bytes, start + index * WORD, value.word);
    }
}

fn word_extent(prefix: usize, count: usize) -> OleanResult<usize> {
    count
        .checked_mul(WORD)
        .and_then(|bytes| prefix.checked_add(bytes))
        .ok_or_else(|| region_error("Lean object extent overflow"))
}

fn align_size(size: usize) -> OleanResult<usize> {
    size.checked_add(WORD - 1)
        .map(|size| size & !(WORD - 1))
        .ok_or_else(|| region_error("Lean object alignment overflow"))
}

fn reserve<T>(buffer: &mut Vec<T>, additional: usize) -> OleanResult<()> {
    buffer
        .try_reserve(additional)
        .map_err(|error| OleanError::Region(format!("could not allocate Lean v2 object: {error}")))
}

fn region_error(reason: &str) -> OleanError {
    OleanError::Region(reason.to_owned())
}

#[cfg(test)]
#[path = "lean_v2_tests.rs"]
mod tests;
