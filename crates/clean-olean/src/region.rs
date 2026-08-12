// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compacted region parsing
//!
//! Lean 4 stores objects in a "compacted region" - a contiguous memory region
//! with pointer-sharing and relocation support.
//!
//! # File Layout
//!
//! The .olean file has this structure:
//! - Offset 0-55: Header (56 bytes)
//! - Offset 56-63: Root object pointer (8 bytes)
//! - Offset 64+: Compacted region objects
//!
//! The `base_addr` in the header corresponds to file offset 0 when memory-mapped.
//! So a pointer P corresponds to file offset (P - base_addr).
//!
//! # Lean 4 Object Layout
//!
//! Each object has an 8-byte header:
//! ```text
//! struct lean_object {
//!     int      m_rc;       // 4 bytes: reference count (0 for compacted)
//!     unsigned m_cs_sz:16; // 2 bytes: compact size or region size
//!     unsigned m_other:8;  // 1 byte: num fields or element size
//!     unsigned m_tag:8;    // 1 byte: object type tag
//! }
//! ```
//!
//! # Object Tags
//!
//! Tags 0-243: Constructor objects (tag = constructor index)
//! Tag 244: Promise
//! Tag 245: Closure
//! Tag 246: Array
//! Tag 247: Struct Array (array of objects)
//! Tag 248: Scalar Array (array of primitives)
//! Tag 249: String
//! Tag 250: MPZ (big integer)
//! Tag 251: Thunk
//! Tag 252: Task
//! Tag 253: Ref
//! Tag 254: External
//! Tag 255: Reserved
//!
//! # Tagged Pointers
//!
//! Lean uses tagged pointers for small scalars:
//! - If LSB is 1: It's a scalar value (unbox by shifting right 1)
//! - If LSB is 0 and non-null: It's an actual pointer
//! - Common special value: 1 = boxed 0 (e.g., Name.anonymous)
//!
//! # String Object Layout
//!
//! ```text
//! struct lean_string_object {
//!     lean_object m_header;   // 8 bytes
//!     size_t      m_size;     // 8 bytes: byte length including null
//!     size_t      m_capacity; // 8 bytes: buffer capacity
//!     size_t      m_length;   // 8 bytes: UTF-8 character count
//!     char        m_data[];   // Variable: actual string data
//! }
//! ```

use crate::error::{OleanError, OleanResult};
use crate::expr::BigNat;

/// Object tags from Lean 4 runtime
pub mod tags {
    /// Maximum constructor tag (tags 0-243 are constructors)
    pub const MAX_CTOR_TAG: u8 = 243;
    pub const PROMISE: u8 = 244;
    pub const CLOSURE: u8 = 245;
    pub const ARRAY: u8 = 246;
    pub const STRUCT_ARRAY: u8 = 247;
    pub const SCALAR_ARRAY: u8 = 248;
    pub const STRING: u8 = 249;
    pub const MPZ: u8 = 250;
    pub const THUNK: u8 = 251;
    pub const TASK: u8 = 252;
    pub const REF: u8 = 253;
    pub const EXTERNAL: u8 = 254;
    pub const RESERVED: u8 = 255;
}

/// Size of the lean_object header
pub const OBJECT_HEADER_SIZE: usize = 8;

/// Object header from a compacted region
#[derive(Debug, Clone, Copy)]
pub struct ObjectHeader {
    /// Reference count (always 0 in compacted regions)
    pub rc: i32,
    /// Compact size or region size
    pub cs_sz: u16,
    /// Number of fields or element size
    pub other: u8,
    /// Object type tag
    pub tag: u8,
}

impl ObjectHeader {
    /// Parse an object header from bytes
    ///
    /// # REQUIRES
    /// - `bytes.len() >= OBJECT_HEADER_SIZE`.
    ///
    /// # ENSURES
    /// - On success, returns the parsed header fields.
    /// - Returns `OleanError::OutOfBounds` if `bytes` is too short.
    pub fn parse(bytes: &[u8]) -> OleanResult<Self> {
        if bytes.len() < OBJECT_HEADER_SIZE {
            return Err(OleanError::OutOfBounds {
                offset: 0,
                size: bytes.len(),
            });
        }

        let rc = i32::from_le_bytes(bytes[0..4].try_into().expect("slice length verified above"));
        let cs_sz =
            u16::from_le_bytes(bytes[4..6].try_into().expect("slice length verified above"));
        let other = bytes[6];
        let tag = bytes[7];

        Ok(Self {
            rc,
            cs_sz,
            other,
            tag,
        })
    }

    /// Check if this is a constructor object
    ///
    /// # ENSURES
    /// - Returns true iff `tag <= tags::MAX_CTOR_TAG`.
    pub fn is_constructor(&self) -> bool {
        self.tag <= tags::MAX_CTOR_TAG
    }

    /// Check if this is a scalar (non-pointer) object
    ///
    /// # ENSURES
    /// - Returns true iff `tag` is a scalar-array, string, or MPZ tag.
    pub fn is_scalar(&self) -> bool {
        matches!(self.tag, tags::SCALAR_ARRAY | tags::STRING | tags::MPZ)
    }

    /// Get the number of pointer fields for constructor objects
    ///
    /// # ENSURES
    /// - Returns `other` when `is_constructor()` is true, else returns 0.
    pub fn num_fields(&self) -> usize {
        if self.is_constructor() {
            self.other as usize
        } else {
            0
        }
    }
}

/// A reference to an object within a compacted region
#[derive(Debug, Clone, Copy)]
pub struct ObjectRef {
    /// Offset within the region
    pub offset: usize,
    /// The object header
    pub header: ObjectHeader,
}

/// Check if a value is a tagged scalar (LSB = 1)
///
/// # ENSURES
/// - Returns true iff `(ptr & 1) == 1`
/// - Mutually exclusive with `is_ptr` when ptr != 0
#[inline]
pub fn is_scalar(ptr: u64) -> bool {
    (ptr & 1) == 1
}

/// Unbox a tagged scalar value
///
/// # REQUIRES
/// - `is_scalar(ptr) == true` for meaningful result
///
/// # ENSURES
/// - Returns `ptr >> 1` (the untagged value)
/// - For boxed N, `unbox_scalar(N*2 + 1) == N`
#[inline]
pub fn unbox_scalar(ptr: u64) -> u64 {
    ptr >> 1
}

/// Check if a value is an actual pointer (not null, not scalar)
///
/// # ENSURES
/// - Returns true iff `ptr != 0 && (ptr & 1) == 0`
/// - Mutually exclusive with `is_scalar`
/// - False for null pointer (ptr == 0)
#[inline]
pub fn is_ptr(ptr: u64) -> bool {
    ptr != 0 && (ptr & 1) == 0
}

/// Parser for compacted regions (entire .olean file)
///
/// This parser operates on the entire .olean file, not just the region portion.
/// Offsets are file offsets, and pointers are converted using base_addr.
pub struct CompactedRegion<'a> {
    /// The raw bytes of the entire .olean file
    pub(crate) data: &'a [u8],
    /// Base address the region was compiled with (corresponds to file offset 0)
    base_addr: u64,
    /// Memoization cache: file offset of a `Name` object → its fully-resolved
    /// dotted string.
    ///
    /// The region bytes are IMMUTABLE, so a `Name` object at a given offset
    /// always decodes to the same string. `.olean` names are heavily shared —
    /// every `Expr::const` reference to e.g. `Nat.succ` points at the same name
    /// object, and a large module has hundreds of thousands of such references.
    /// Without memoization [`read_name_rc_at_depth`](Self::read_name_rc_at_depth)
    /// re-walks each name's entire parent chain from raw bytes (with repeated
    /// header parsing, UTF-8 validation, and `format!` allocations) on EVERY
    /// reference — the dominant cost of the `Init` pre-load. Caching per offset
    /// collapses that to one parse per distinct name object.
    ///
    /// `Rc<str>` (cheap ref-count clone on hit, single owning allocation) rather
    /// than `String` (a fresh heap copy per hit). `RefCell` gives the interior
    /// mutability the `&self` reader API needs; the region is only ever used
    /// single-threaded during conversion (one region per module, converted
    /// sequentially), so no synchronization is required.
    name_cache: std::cell::RefCell<hashbrown::HashMap<usize, std::rc::Rc<str>>>,
}

impl<'a> CompactedRegion<'a> {
    /// Create a new compacted region parser from the full .olean file
    ///
    /// Note: This takes the entire file bytes, not just the region portion.
    /// The base_addr corresponds to file offset 0.
    ///
    /// # REQUIRES
    /// - `data` is the full .olean file bytes (including header)
    /// - `base_addr` is the address from the parsed header
    ///
    /// # ENSURES
    /// - `len() == data.len()`
    /// - Pointer `P` maps to file offset `P - base_addr`
    pub fn new(data: &'a [u8], base_addr: u64) -> Self {
        Self {
            data,
            base_addr,
            name_cache: std::cell::RefCell::new(hashbrown::HashMap::new()),
        }
    }

    /// Get the size of the data in bytes
    ///
    /// # ENSURES
    /// - Returns `data.len()` as passed to constructor
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if the region is empty
    ///
    /// # ENSURES
    /// - Returns `len() == 0`
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Read an object header at a file offset
    ///
    /// # REQUIRES
    /// - `offset + OBJECT_HEADER_SIZE <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns the parsed header at `offset`.
    /// - Returns `OleanError::OutOfBounds` if the range is invalid.
    pub fn read_header_at(&self, offset: usize) -> OleanResult<ObjectHeader> {
        if offset + OBJECT_HEADER_SIZE > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }

        ObjectHeader::parse(&self.data[offset..])
    }

    /// Read a u64 at a file offset
    ///
    /// # REQUIRES
    /// - `offset + 8 <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns the little-endian u64 at `offset`.
    /// - Returns `OleanError::OutOfBounds` on invalid range.
    pub fn read_u64_at(&self, offset: usize) -> OleanResult<u64> {
        if offset + 8 > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }

        Ok(u64::from_le_bytes(
            self.data[offset..offset + 8]
                .try_into()
                .expect("slice length verified above"),
        ))
    }

    /// Read an i32 at a file offset
    ///
    /// # REQUIRES
    /// - `offset + 4 <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns the little-endian i32 at `offset`.
    /// - Returns `OleanError::OutOfBounds` on invalid range.
    pub fn read_i32_at(&self, offset: usize) -> OleanResult<i32> {
        if offset + 4 > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }

        Ok(i32::from_le_bytes(
            self.data[offset..offset + 4]
                .try_into()
                .expect("slice length verified above"),
        ))
    }

    /// Read a pointer (u64) at a file offset (alias for read_u64_at)
    ///
    /// # REQUIRES
    /// - `offset + 8 <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns the raw pointer value at `offset`.
    pub fn read_ptr_at(&self, offset: usize) -> OleanResult<u64> {
        self.read_u64_at(offset)
    }

    /// Convert a raw pointer to a file offset
    ///
    /// Pointers in the region are stored as absolute addresses based on base_addr.
    /// Since base_addr corresponds to file offset 0, ptr - base_addr = file offset.
    ///
    /// # REQUIRES
    /// - `ptr` is either 0 (null) or a valid pointer in this region.
    ///
    /// # ENSURES
    /// - Returns 0 for null pointers.
    /// - Returns `OleanError::InvalidPointer` if `ptr` is tagged or out of range.
    pub fn ptr_to_offset(&self, ptr: u64) -> OleanResult<usize> {
        if ptr == 0 {
            // Null pointer
            return Ok(0);
        }

        if is_scalar(ptr) {
            return Err(OleanError::InvalidPointer { ptr, offset: 0 });
        }

        if ptr < self.base_addr {
            return Err(OleanError::InvalidPointer { ptr, offset: 0 });
        }

        let offset = (ptr - self.base_addr) as usize;
        if offset >= self.data.len() {
            return Err(OleanError::InvalidPointer { ptr, offset });
        }

        Ok(offset)
    }

    /// Convert a file offset back to a pointer value
    ///
    /// # REQUIRES
    /// - `offset` is within the compacted region.
    ///
    /// # ENSURES
    /// - Returns `base_addr + offset` (no validation).
    pub fn offset_to_ptr(&self, offset: usize) -> u64 {
        self.base_addr + offset as u64
    }

    /// Get the raw bytes at a file offset
    ///
    /// # REQUIRES
    /// - `offset + len <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns a slice of length `len` from `offset`.
    /// - Returns `OleanError::OutOfBounds` on invalid range.
    pub fn bytes_at(&self, offset: usize, len: usize) -> OleanResult<&'a [u8]> {
        if offset + len > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }
        Ok(&self.data[offset..offset + len])
    }

    /// Read a Nat value from a pointer, returning a BigNat for arbitrary-precision values.
    ///
    /// If the pointer is a tagged scalar, returns the unboxed value as BigNat::Small.
    /// If it's a pointer to an MPZ object, reads all limbs and returns a BigNat.
    ///
    /// # REQUIRES
    /// - `ptr` is a tagged scalar or a pointer to a Nat/MPZ object.
    ///
    /// # ENSURES
    /// - Returns a BigNat value on success.
    /// - Returns `OleanError` on unexpected tags or malformed data.
    pub fn read_bignat_value(&self, ptr: u64) -> OleanResult<BigNat> {
        if is_scalar(ptr) {
            return Ok(BigNat::from_u64(unbox_scalar(ptr)));
        }

        if !is_ptr(ptr) {
            return Ok(BigNat::from_u64(0));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        // MPZ tag = 250
        if header.tag == tags::MPZ {
            // MPZ layout (lean_mpz_object):
            //   header(8) + __mpz_struct { _mp_alloc(i32 at +8) + _mp_size(i32 at +12)
            //                              + _mp_d(pointer, 8 bytes at +16) }
            //   + digits[...] (at +24)
            //
            // In compacted .olean regions, _mp_d is patched to point to the inline
            // digit array. The pointer field is still physically present (8 bytes).
            // Reference: Lean 4 runtime/mpz.h lean_mpz_object
            let size_raw = self.read_i32_at(offset + 12)?;
            let size = size_raw.unsigned_abs() as usize;

            if size == 0 {
                return Ok(BigNat::from_u64(0));
            }

            // Read all limbs (little-endian order in memory)
            // Digits start at +24 (after header + alloc + size + _mp_d pointer)
            let mut limbs = Vec::with_capacity(size);
            for i in 0..size {
                let limb = self.read_u64_at(offset + 24 + i * 8)?;
                limbs.push(limb);
            }

            Ok(BigNat::from_limbs(limbs))
        } else {
            Err(OleanError::Region(format!(
                "unexpected object tag {} for Nat at offset {}",
                header.tag, offset
            )))
        }
    }

    /// Read a Nat value from a pointer as u64.
    ///
    /// For BVar indices and other values that should always fit in u64.
    /// Multi-limb values are truncated to low 64 bits.
    pub fn read_nat_value(&self, ptr: u64) -> OleanResult<u64> {
        let bignat = self.read_bignat_value(ptr)?;
        match bignat {
            BigNat::Small(v) => Ok(v),
            BigNat::Big(limbs) => Ok(limbs.first().copied().unwrap_or(0)),
        }
    }

    /// Read a Lean String object at a file offset
    ///
    /// Returns the string content (without null terminator).
    ///
    /// # REQUIRES
    /// - `offset` points to a valid String object.
    ///
    /// # ENSURES
    /// - Returns UTF-8 string data from the region.
    /// - Returns `OleanError::InvalidObjectTag` if tag mismatch.
    pub fn read_lean_string_at(&self, offset: usize) -> OleanResult<&'a str> {
        let header = self.read_header_at(offset)?;
        if header.tag != tags::STRING {
            return Err(OleanError::InvalidObjectTag {
                tag: header.tag,
                offset,
            });
        }

        // String layout: header(8) + size(8) + capacity(8) + length(8) + data
        if offset + 32 > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }

        let m_size = self.read_u64_at(offset + 8)? as usize;
        // m_capacity at offset + 16
        // m_length at offset + 24

        let data_start = offset + 32;
        if data_start + m_size > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset: data_start,
                size: self.data.len(),
            });
        }

        // String data (exclude null terminator)
        let str_len = if m_size > 0 { m_size - 1 } else { 0 };
        let bytes = &self.data[data_start..data_start + str_len];
        std::str::from_utf8(bytes).map_err(|_| OleanError::Region("invalid UTF-8 in string".into()))
    }

    /// Read a Lean Name object at a file offset
    ///
    /// Returns the fully qualified name as a string (e.g., "Nat.add").
    ///
    /// # REQUIRES
    /// - `offset` points to a valid Name object.
    ///
    /// # ENSURES
    /// - Returns the name in dotted string form.
    /// - Returns `OleanError::InvalidObjectTag` if the tag is not a Name ctor.
    pub fn read_name_at(&self, offset: usize) -> OleanResult<String> {
        self.read_name_rc_at_depth(offset, 0)
            .map(|rc| rc.to_string())
    }

    /// Resolve a `Name` object to a shared `Rc<str>`, memoized per file offset.
    ///
    /// This is the cached core of [`read_name_at`](Self::read_name_at): the first
    /// resolution of an offset walks the parent chain and stores the result; every
    /// later reference to the same offset (including as a PARENT of a longer name)
    /// returns a cheap `Rc` clone. See [`name_cache`](Self::name_cache) for why
    /// this is the dominant cost of loading a large `.olean`.
    fn read_name_rc_at_depth(&self, offset: usize, depth: usize) -> OleanResult<std::rc::Rc<str>> {
        if let Some(cached) = self.name_cache.borrow().get(&offset) {
            return Ok(std::rc::Rc::clone(cached));
        }
        if depth > 100 {
            return Err(OleanError::Region("Name depth limit exceeded".into()));
        }

        let resolved = self.read_name_uncached(offset, depth)?;
        let rc: std::rc::Rc<str> = std::rc::Rc::from(resolved.as_str());
        self.name_cache
            .borrow_mut()
            .insert(offset, std::rc::Rc::clone(&rc));
        Ok(rc)
    }

    /// Uncached single-object name decode (recurses through the cached
    /// [`read_name_rc_at_depth`](Self::read_name_rc_at_depth) for parents, so a
    /// shared parent chain is still resolved only once).
    fn read_name_uncached(&self, offset: usize, depth: usize) -> OleanResult<String> {
        let header = self.read_header_at(offset)?;

        match (header.tag, header.other) {
            // Name.anonymous (constructor 0, 0 fields)
            (0, 0) => Ok(String::new()),

            // Name.str (constructor 1, 2 fields: parent, string)
            (1, 2) => {
                let parent_ptr = self.read_u64_at(offset + 8)?;
                let string_ptr = self.read_u64_at(offset + 16)?;

                // Read parent name (cached rc — a shared parent chain such as
                // `Nat`/`List`/`Option` is decoded once and reused).
                let parent: std::rc::Rc<str> = if is_scalar(parent_ptr) {
                    // Scalar 0 = Name.anonymous
                    std::rc::Rc::from("")
                } else if is_ptr(parent_ptr) {
                    let parent_off = self.ptr_to_offset(parent_ptr)?;
                    self.read_name_rc_at_depth(parent_off, depth + 1)?
                } else {
                    std::rc::Rc::from("")
                };

                // Read string component
                let component = if is_ptr(string_ptr) {
                    let str_off = self.ptr_to_offset(string_ptr)?;
                    self.read_lean_string_at(str_off)?
                } else {
                    "<invalid>"
                };

                if parent.is_empty() {
                    Ok(component.to_string())
                } else {
                    Ok(format!("{parent}.{component}"))
                }
            }

            // Name.num (constructor 2, 2 fields: parent, number)
            (2, 2) => {
                let parent_ptr = self.read_u64_at(offset + 8)?;
                let num = self.read_u64_at(offset + 16)?;

                // Read parent name (cached rc).
                let parent: std::rc::Rc<str> = if is_scalar(parent_ptr) {
                    std::rc::Rc::from("")
                } else if is_ptr(parent_ptr) {
                    let parent_off = self.ptr_to_offset(parent_ptr)?;
                    self.read_name_rc_at_depth(parent_off, depth + 1)?
                } else {
                    std::rc::Rc::from("")
                };

                if parent.is_empty() {
                    Ok(num.to_string())
                } else {
                    Ok(format!("{parent}.{num}"))
                }
            }

            _ => Err(OleanError::InvalidObjectTag {
                tag: header.tag,
                offset,
            }),
        }
    }

    /// Find all Name.str objects in the file and return their names
    ///
    /// This is useful for exploring the .olean contents.
    ///
    /// # REQUIRES
    /// - The region data is a valid .olean compacted region.
    ///
    /// # ENSURES
    /// - Returns (offset, name) pairs for discovered Name.str objects.
    /// - Best-effort: malformed entries are skipped.
    pub fn find_all_names(&self) -> Vec<(usize, String)> {
        let mut names = Vec::new();

        // Start at offset 64 (after header + root pointer)
        let mut offset = 64;
        while offset + 24 < self.data.len() {
            if let Ok(header) = self.read_header_at(offset) {
                if header.tag == 1 && header.other == 2 {
                    // This is a Name.str
                    if let Ok(name) = self.read_name_at(offset) {
                        if !name.is_empty() {
                            names.push((offset, name));
                        }
                    }
                }
            }
            offset += 8;
        }

        names
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression: `read_name_at` memoizes each `Name` object by file offset, so
    /// a `Name` shared as the PARENT of several children is decoded exactly once.
    /// This is the fix for the `Init` pre-load hot path, where every `Expr::const`
    /// re-resolved the same deep names from raw bytes. The test asserts both
    /// correctness (identical dotted strings) and that the shared parent lands in
    /// the cache after the first child is read.
    #[test]
    fn test_read_name_at_memoizes_shared_parent() {
        // base_addr = 0 ⇒ pointer value == file offset. Objects are 8-byte
        // aligned so every offset is even and non-zero (a valid `is_ptr`).
        fn push_string(buf: &mut Vec<u8>, s: &str) -> u64 {
            while !buf.len().is_multiple_of(8) {
                buf.push(0);
            }
            let off = buf.len() as u64;
            // header: rc(4)=0, cs_sz(2)=0, other(1)=0, tag(1)=STRING
            buf.extend_from_slice(&0u32.to_le_bytes());
            buf.extend_from_slice(&0u16.to_le_bytes());
            buf.push(0);
            buf.push(tags::STRING);
            let m_size = (s.len() + 1) as u64; // includes null terminator
            buf.extend_from_slice(&m_size.to_le_bytes()); // m_size
            buf.extend_from_slice(&m_size.to_le_bytes()); // m_capacity
            buf.extend_from_slice(&(s.len() as u64).to_le_bytes()); // m_length
            buf.extend_from_slice(s.as_bytes());
            buf.push(0); // null terminator
            off
        }
        fn push_name_str(buf: &mut Vec<u8>, parent_ptr: u64, string_ptr: u64) -> u64 {
            while !buf.len().is_multiple_of(8) {
                buf.push(0);
            }
            let off = buf.len() as u64;
            // header: rc=0, cs_sz=0, other=2 (2 fields), tag=1 (Name.str)
            buf.extend_from_slice(&0u32.to_le_bytes());
            buf.extend_from_slice(&0u16.to_le_bytes());
            buf.push(2);
            buf.push(1);
            buf.extend_from_slice(&parent_ptr.to_le_bytes());
            buf.extend_from_slice(&string_ptr.to_le_bytes());
            off
        }

        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(&[0u8; 8]); // reserve offset 0 as the null slot

        let s_nat = push_string(&mut buf, "Nat");
        let s_succ = push_string(&mut buf, "succ");
        let s_add = push_string(&mut buf, "add");
        const ANON: u64 = 1; // scalar-boxed Name.anonymous
        let n_nat = push_name_str(&mut buf, ANON, s_nat);
        let n_succ = push_name_str(&mut buf, n_nat, s_succ);
        let n_add = push_name_str(&mut buf, n_nat, s_add);

        let region = CompactedRegion::new(&buf, 0);
        assert!(region.name_cache.borrow().is_empty(), "cache starts empty");

        // Reading a child decodes and caches BOTH the child and its parent.
        assert_eq!(region.read_name_at(n_succ as usize).unwrap(), "Nat.succ");
        assert!(
            region.name_cache.borrow().contains_key(&(n_nat as usize)),
            "shared parent `Nat` cached after first child read"
        );
        assert!(region.name_cache.borrow().contains_key(&(n_succ as usize)));

        // A sibling reuses the cached parent yet yields its own distinct name.
        assert_eq!(region.read_name_at(n_add as usize).unwrap(), "Nat.add");
        assert_eq!(region.read_name_at(n_nat as usize).unwrap(), "Nat");

        // Idempotent: a repeat read hits the cache and is byte-identical.
        assert_eq!(region.read_name_at(n_succ as usize).unwrap(), "Nat.succ");
        assert_eq!(region.read_name_at(n_add as usize).unwrap(), "Nat.add");
    }

    #[test]
    fn test_object_header_parse() {
        // Construct a constructor object header
        // rc=0, cs_sz=0x20, other=2 (2 fields), tag=0 (first constructor)
        let bytes = [
            0, 0, 0, 0, // rc = 0
            0x20, 0, // cs_sz = 0x20
            2, // other = 2
            0, // tag = 0
        ];

        let header = ObjectHeader::parse(&bytes).unwrap();
        assert_eq!(header.rc, 0);
        assert_eq!(header.cs_sz, 0x20);
        assert_eq!(header.other, 2);
        assert_eq!(header.tag, 0);
        assert!(header.is_constructor());
        assert_eq!(header.num_fields(), 2);
    }

    #[test]
    fn test_object_header_string() {
        // String object header
        let bytes = [
            0,
            0,
            0,
            0, // rc = 0
            0,
            0,            // cs_sz = 0
            5,            // other = 5 (length?)
            tags::STRING, // tag = STRING
        ];

        let header = ObjectHeader::parse(&bytes).unwrap();
        assert_eq!(header.tag, tags::STRING);
        assert!(!header.is_constructor());
        assert!(header.is_scalar());
    }

    /// Verify ObjectHeader::parse returns OutOfBounds error when slice is too short
    #[test]
    fn test_object_header_parse_short_slice() {
        let bytes = [0u8; OBJECT_HEADER_SIZE - 1];
        let err = ObjectHeader::parse(&bytes).unwrap_err();
        assert!(matches!(
            err,
            OleanError::OutOfBounds {
                offset: 0,
                size
            } if size == bytes.len()
        ));
    }

    /// Verify num_fields() returns 0 for non-constructor objects regardless of `other` field
    #[test]
    fn test_object_header_num_fields_non_constructor() {
        // Non-constructor with other=9 should still return num_fields=0
        let bytes = [
            0,
            0,
            0,
            0, // rc = 0
            0,
            0,            // cs_sz = 0
            9,            // other = 9 (ignored for non-constructors)
            tags::STRING, // tag = STRING (non-constructor tag)
        ];

        let header = ObjectHeader::parse(&bytes).unwrap();
        assert!(!header.is_constructor());
        assert_eq!(header.num_fields(), 0);
    }

    /// Verify is_scalar and is_ptr correctly categorize pointer values by LSB
    #[test]
    fn test_scalar_detection() {
        // Scalar values have LSB = 1
        assert!(is_scalar(1)); // boxed 0 (Name.anonymous)
        assert!(is_scalar(3)); // boxed 1
        assert!(is_scalar(0xFF)); // odd number

        // Pointers have LSB = 0 (and non-zero)
        assert!(is_ptr(0x0010_0000));
        assert!(is_ptr(2));

        // Zero is neither scalar nor valid pointer
        assert!(!is_scalar(0));
        assert!(!is_ptr(0));
    }

    /// Verify is_scalar and is_ptr are mutually exclusive for all pointer values
    #[test]
    fn test_scalar_ptr_exclusivity() {
        // No value can be both scalar AND pointer (mutually exclusive)
        let samples = [0u64, 1, 2, 3, 4, 5, 0x10, 0x11];
        for &ptr in &samples {
            assert!(
                !(is_scalar(ptr) && is_ptr(ptr)),
                "ptr={} should not be both scalar and pointer",
                ptr
            );
        }

        // Verify specific categorizations
        assert!(is_scalar(1)); // odd number = scalar
        assert!(is_ptr(2)); // even non-zero = pointer
    }

    #[test]
    fn test_unbox_scalar() {
        assert_eq!(unbox_scalar(1), 0);
        assert_eq!(unbox_scalar(3), 1);
        assert_eq!(unbox_scalar(5), 2);
        assert_eq!(unbox_scalar(201), 100);
    }

    #[test]
    fn test_compacted_region_string() {
        // Create a mock .olean file structure with a string
        let base_addr = 0x1000u64;

        // We need at least 64 bytes header + object
        let mut data = vec![0u8; 128];

        // String object at offset 64 (first object after header)
        let str_offset = 64;
        // Header
        data[str_offset..str_offset + 4].copy_from_slice(&0i32.to_le_bytes()); // rc
        data[str_offset + 4..str_offset + 6].copy_from_slice(&0u16.to_le_bytes()); // cs_sz
        data[str_offset + 6] = 0; // other
        data[str_offset + 7] = tags::STRING;
        // m_size = 6 (5 chars + null)
        data[str_offset + 8..str_offset + 16].copy_from_slice(&6u64.to_le_bytes());
        // m_capacity = 6
        data[str_offset + 16..str_offset + 24].copy_from_slice(&6u64.to_le_bytes());
        // m_length = 5
        data[str_offset + 24..str_offset + 32].copy_from_slice(&5u64.to_le_bytes());
        // String data "hello\0"
        data[str_offset + 32..str_offset + 38].copy_from_slice(b"hello\0");

        let region = CompactedRegion::new(&data, base_addr);
        let s = region.read_lean_string_at(str_offset).unwrap();
        assert_eq!(s, "hello");
    }

    /// Verify ptr_to_offset validates pointers against region bounds and scalar tagging
    #[test]
    fn test_ptr_to_offset() {
        let base_addr = 0x0010_0000_u64;
        let data = vec![0u8; 100];
        let region = CompactedRegion::new(&data, base_addr);

        // Null pointer
        assert_eq!(region.ptr_to_offset(0).unwrap(), 0);

        // Valid pointer
        assert_eq!(region.ptr_to_offset(base_addr + 50).unwrap(), 50);

        // Base address points at offset 0
        assert_eq!(region.ptr_to_offset(base_addr).unwrap(), 0);

        // Tagged pointer inside the region should still be rejected
        assert!(
            matches!(
                region.ptr_to_offset(base_addr + 1),
                Err(OleanError::InvalidPointer { .. })
            ),
            "tagged pointer should produce InvalidPointer"
        );

        // Pointer before base is invalid
        assert!(
            matches!(
                region.ptr_to_offset(base_addr - 1),
                Err(OleanError::InvalidPointer { .. })
            ),
            "pointer before base should produce InvalidPointer"
        );

        // Pointer beyond region is invalid
        assert!(
            matches!(
                region.ptr_to_offset(base_addr + 200),
                Err(OleanError::InvalidPointer { .. })
            ),
            "pointer beyond region should produce InvalidPointer"
        );

        // Scalar values are not valid pointers
        assert!(
            matches!(
                region.ptr_to_offset(1),
                Err(OleanError::InvalidPointer { .. })
            ),
            "scalar 1 (boxed 0) should produce InvalidPointer"
        );
        assert!(
            matches!(
                region.ptr_to_offset(3),
                Err(OleanError::InvalidPointer { .. })
            ),
            "scalar 3 (boxed 1) should produce InvalidPointer"
        );
    }

    /// Verify ptr_to_offset rejects pointer exactly at end of region (off-by-one boundary)
    #[test]
    fn test_ptr_to_offset_end_boundary() {
        let base_addr = 0x0100_0000_u64;
        let data = vec![0u8; 64];
        let region = CompactedRegion::new(&data, base_addr);
        // Pointer at exactly base_addr + data.len() is invalid (one past end)
        let ptr = base_addr + data.len() as u64;
        let err = region.ptr_to_offset(ptr).unwrap_err();
        assert!(matches!(
            err,
            OleanError::InvalidPointer { ptr: err_ptr, offset }
                if err_ptr == ptr && offset == data.len()
        ));
    }

    /// Verify offset_to_ptr and ptr_to_offset are inverses for valid offsets
    #[test]
    fn test_offset_to_ptr_roundtrip() {
        let base_addr = 0x2000_u64;
        let data = vec![0u8; 32];
        let region = CompactedRegion::new(&data, base_addr);
        // Test roundtrip at start, middle, and end of valid range.
        // Use only even offsets since odd addresses are scalar-tagged in Lean's compacted region.
        // Calculate max_even dynamically in case data size changes.
        let max_even = (data.len() - 1) & !1; // Largest even offset within bounds
        for offset in [0usize, 12usize, max_even] {
            let ptr = region.offset_to_ptr(offset);
            assert_eq!(ptr, base_addr + offset as u64);
            assert_eq!(region.ptr_to_offset(ptr).unwrap(), offset);
        }
    }

    /// Verify odd pointers are rejected as scalars.
    ///
    /// In Lean's runtime, odd addresses (ptr & 1 == 1) represent unboxed scalars,
    /// not heap pointers. The actual value is (ptr >> 1). This test ensures
    /// ptr_to_offset correctly rejects these as InvalidPointer.
    #[test]
    fn test_odd_ptr_rejected_as_scalar() {
        let base_addr = 0x2000_u64;
        let data = vec![0u8; 32];
        let region = CompactedRegion::new(&data, base_addr);
        // Test multiple odd offsets: near start, middle, and near end of range
        for odd_offset in [1usize, 15usize, 31usize] {
            let odd_ptr = base_addr + odd_offset as u64;
            let result = region.ptr_to_offset(odd_ptr);
            assert!(
                result.is_err(),
                "Odd pointer 0x{:x} (offset {}) should be rejected as scalar-tagged",
                odd_ptr,
                odd_offset
            );
        }
    }

    /// Verify read_lean_string_at returns OutOfBounds when m_size exceeds available data
    #[test]
    fn test_read_lean_string_at_length_mismatch() {
        let base_addr = 0x1000u64;
        let mut data = vec![0u8; 96]; // Only 96 bytes total
        let str_offset = 64;

        // Build string header at offset 64
        data[str_offset..str_offset + 4].copy_from_slice(&0i32.to_le_bytes()); // rc
        data[str_offset + 4..str_offset + 6].copy_from_slice(&0u16.to_le_bytes()); // cs_sz
        data[str_offset + 6] = 0; // other
        data[str_offset + 7] = tags::STRING; // tag
                                             // m_size = 20 (string data would need 20 bytes at offset 64+32=96, but only 0 bytes available)
        data[str_offset + 8..str_offset + 16].copy_from_slice(&20u64.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let err = region.read_lean_string_at(str_offset).unwrap_err();
        let data_start = str_offset + 32; // String data starts at header + 32
        assert!(matches!(
            err,
            OleanError::OutOfBounds { offset, size }
                if offset == data_start && size == data.len()
        ));
    }
}
