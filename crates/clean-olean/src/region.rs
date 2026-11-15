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
use crate::header::OleanHeader;

/// Which on-disk `lean::mpz` layout a compacted `LeanMPZ` object uses.
///
/// See [`CompactedRegion::read_mpz_at`] for the two byte layouts and why a
/// decoder that assumes one of them mis-reads the other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MpzLayout {
    /// `__mpz_struct`: `_mp_alloc` i32 @ +8, `_mp_size` i32 @ +12, `_mp_d` @ +16,
    /// 64-bit limbs @ +24.
    Gmp,
    /// GMP-free `lean::mpz`: `m_sign` bool @ +8, `m_size` u64 @ +16,
    /// `m_digits` @ +24, 32-bit digits @ +32.
    LeanNative,
}

pub(crate) use typed::TypedModuleLayout;

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
        // `OBJECT_HEADER_SIZE` is 8: the pattern matches exactly when
        // `bytes.len() >= OBJECT_HEADER_SIZE`.
        const _: () = assert!(OBJECT_HEADER_SIZE == 8);
        let [r0, r1, r2, r3, c0, c1, other, tag, ..] = *bytes else {
            return Err(OleanError::OutOfBounds {
                offset: 0,
                size: bytes.len(),
            });
        };

        Ok(Self {
            rc: i32::from_le_bytes([r0, r1, r2, r3]),
            cs_sz: u16::from_le_bytes([c0, c1]),
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

mod mdata;
mod typed;

#[cfg(test)]
mod parsed_name_tests;

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
    // Typed identities are scoped to these immutable bytes, never to a dotted
    // projection or a cache shared between different compacted regions.
    typed_names: std::cell::RefCell<hashbrown::HashMap<u64, clean_kernel::name::Name>>,
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
            typed_names: std::cell::RefCell::new(hashbrown::HashMap::new()),
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

        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.data[offset..offset + 8]);
        Ok(u64::from_le_bytes(bytes))
    }

    /// Read an i32 at a file offset
    ///
    /// # REQUIRES
    /// - `offset + 4 <= data.len()`.
    ///
    /// # ENSURES
    /// - Returns the little-endian i32 at `offset`.
    /// - Returns `OleanError::OutOfBounds` on invalid range.
    pub(crate) fn read_i32_at(&self, offset: usize) -> OleanResult<i32> {
        if offset + 4 > self.data.len() {
            return Err(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            });
        }

        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.data[offset..offset + 4]);
        Ok(i32::from_le_bytes(bytes))
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
    pub(crate) fn offset_to_ptr(&self, offset: usize) -> u64 {
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
    pub(crate) fn bytes_at(&self, offset: usize, len: usize) -> OleanResult<&'a [u8]> {
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
    pub(crate) fn read_bignat_value(&self, ptr: u64) -> OleanResult<BigNat> {
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
            self.read_mpz_at(ptr, offset, &header)
        } else {
            Err(OleanError::Region(format!(
                "unexpected object tag {} for Nat at offset {}",
                header.tag, offset
            )))
        }
    }

    /// Decode a compacted `LeanMPZ` object into a [`BigNat`].
    ///
    /// # Two on-disk bignum encodings
    ///
    /// Lean ships `lean::mpz` in two shapes and BOTH occur in released
    /// `.olean` files, so a decoder that hard-codes one of them silently
    /// mis-reads the other:
    ///
    /// * **GMP** (`LEAN_USE_GMP`): `lean_mpz_object` is
    ///   `header(8) + __mpz_struct { _mp_alloc: i32 @ +8, _mp_size: i32 @ +12,
    ///   _mp_d: ptr @ +16 }`, with the **64-bit** limbs inline at `+24` and
    ///   `_mp_d` patched to point at them (or left null by Clean's own test
    ///   writers). Object size is `24 + 8 * |_mp_size|`.
    /// * **Lean-native** (GMP-free builds, which includes the released Lean
    ///   4.8.0 toolchain): `lean::mpz` is
    ///   `{ bool m_sign; size_t m_size; mpn_digit *m_digits; }`, so the object
    ///   is `header(8) + sign(1, padded to 8) @ +8 + m_size: u64 @ +16 +
    ///   m_digits: ptr @ +24`, with the **32-bit** digits inline at `+32` and
    ///   `m_digits` left as a stale host pointer. Object size is
    ///   `32 + 4 * m_size`.
    ///
    /// The v2 `.olean` header carries the answer in its flags byte (bit 0 =
    /// "persisted bignums use GMP"); a v1 header does not, so the layout is
    /// then decided STRUCTURALLY and both candidates must be checked.
    ///
    /// # Fail-closed
    ///
    /// A candidate layout is accepted only if every one of its own invariants
    /// holds (`cs_sz` agreement, digit array inside the region, GMP's
    /// `_mp_alloc >= |_mp_size|` and inline/null `_mp_d`, the native sign byte
    /// being a real `bool`). If NEITHER candidate validates, or if BOTH do, the
    /// read is refused with a diagnostic naming both interpretations — never
    /// resolved by guessing.
    fn read_mpz_at(&self, ptr: u64, offset: usize, header: &ObjectHeader) -> OleanResult<BigNat> {
        let gmp = self.mpz_gmp_candidate(ptr, offset, header);
        let native = self.mpz_native_candidate(offset, header);

        match (gmp, native) {
            (Some(limbs), None) | (None, Some(limbs)) => Ok(BigNat::from_limbs(limbs)),
            (Some(_), Some(_)) => Err(OleanError::Region(format!(
                "ambiguous MPZ object at offset {offset}: it validates as BOTH the GMP \
                 (_mp_size @ +12, 64-bit limbs @ +24) and the Lean-native \
                 (m_size @ +16, 32-bit digits @ +32) layout; refusing to guess"
            ))),
            (None, None) => Err(OleanError::Region(format!(
                "unrecognized MPZ object at offset {offset} (cs_sz={}): it matches neither the \
                 GMP layout (_mp_alloc @ +8, _mp_size @ +12, 64-bit limbs @ +24) nor the \
                 Lean-native layout (sign @ +8, m_size @ +16, 32-bit digits @ +32)",
                header.cs_sz
            ))),
        }
    }

    /// The GMP (`__mpz_struct`) reading of an MPZ object, or `None` if this
    /// object does not satisfy that layout's invariants.
    fn mpz_gmp_candidate(
        &self,
        ptr: u64,
        offset: usize,
        header: &ObjectHeader,
    ) -> Option<Vec<u64>> {
        if !self.mpz_layout_permitted(MpzLayout::Gmp) {
            return None;
        }
        let alloc = self.read_i32_at(offset + 8).ok()?;
        let size_raw = self.read_i32_at(offset + 12).ok()?;
        // Lean boxes every value that fits a tagged scalar, so a heap mpz is
        // never zero and never negative.
        if size_raw <= 0 {
            return None;
        }
        let size = size_raw as usize;
        if alloc < size_raw {
            return None;
        }
        if header.cs_sz != 0 && usize::from(header.cs_sz) != 24 + 8 * size {
            return None;
        }
        // `_mp_d` is either patched to the inline digit array or left null by
        // Clean's own writers; anything else is not this layout.
        let mp_d = self.read_u64_at(offset + 16).ok()?;
        if mp_d != 0 && mp_d != ptr.checked_add(24)? {
            return None;
        }
        let mut limbs = Vec::with_capacity(size);
        for i in 0..size {
            limbs.push(self.read_u64_at(offset + 24 + i * 8).ok()?);
        }
        Some(limbs)
    }

    /// The Lean-native (`{bool, size_t, mpn_digit*}`) reading of an MPZ object,
    /// or `None` if this object does not satisfy that layout's invariants.
    ///
    /// `m_digits` at `+24` is deliberately NOT checked: the compactor leaves a
    /// stale host pointer there, which is exactly what made this layout look
    /// like a corrupt GMP object.
    fn mpz_native_candidate(&self, offset: usize, header: &ObjectHeader) -> Option<Vec<u64>> {
        if !self.mpz_layout_permitted(MpzLayout::LeanNative) {
            return None;
        }
        // `m_sign` is a real `bool`; the seven bytes after it are padding and
        // carry uninitialized garbage, so only the first byte may be read.
        let sign = *self.data.get(offset + 8)?;
        if sign > 1 {
            return None;
        }
        let digit_count = usize::try_from(self.read_u64_at(offset + 16).ok()?).ok()?;
        // A heap mpz holds a value Lean could not box as a 63-bit scalar, so it
        // needs at least two 32-bit digits. Requiring that is what keeps this
        // layout from also matching a one-limb GMP object.
        if digit_count < 2 {
            return None;
        }
        if header.cs_sz != 0 && usize::from(header.cs_sz) != 32 + 4 * digit_count {
            return None;
        }
        if sign == 1 {
            // A negative bignum is not a `Nat`. Refuse rather than silently
            // dropping the sign.
            return None;
        }
        let digits_start = offset.checked_add(32)?;
        let digits_end = digits_start.checked_add(4 * digit_count)?;
        if digits_end > self.data.len() {
            return None;
        }
        let mut limbs = vec![0u64; digit_count.div_ceil(2)];
        for i in 0..digit_count {
            let at = digits_start + i * 4;
            let mut bytes = [0u8; 4];
            bytes.copy_from_slice(&self.data[at..at + 4]);
            let digit = u32::from_le_bytes(bytes);
            limbs[i / 2] |= u64::from(digit) << (32 * (i % 2));
        }
        Some(limbs)
    }

    /// Whether `layout` is permitted for this region by the `.olean` header.
    ///
    /// A v2 header states the answer in its flags byte, and that statement is
    /// authority: the other layout is then not even considered. A v1 header (or
    /// a synthetic non-`.olean` buffer, as the unit tests use) carries no such
    /// field, so both layouts stay on the table and the structural checks
    /// decide.
    fn mpz_layout_permitted(&self, layout: MpzLayout) -> bool {
        match OleanHeader::parse(self.data) {
            Ok(header) if header.version == crate::header::VERSION_V2 => {
                header.uses_gmp_bignums() == (layout == MpzLayout::Gmp)
            }
            _ => true,
        }
    }

    /// Read a Nat value from a pointer as u64.
    ///
    /// For BVar indices and other values that should always fit in u64.
    /// Multi-limb values are truncated to low 64 bits.
    pub(crate) fn read_nat_value(&self, ptr: u64) -> OleanResult<u64> {
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
    pub(crate) fn read_lean_string_at(&self, offset: usize) -> OleanResult<&'a str> {
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
    /// Returns the fully qualified name as a string (e.g., "Nat.add"). This
    /// legacy projection is lossy: dotted or numeric String components cannot
    /// be distinguished from hierarchy or Name.num. It is not typed identity.
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
                // Finalized files select an encoding by their measured module
                // envelope, never by retrying a failed modern Nat as raw u64.
                // OleanExporter's existing low-level round-trip helpers also
                // read unfinished buffers with exactly 64 zero reserved bytes.
                // That explicit scratch form is Clean-only, including cs_sz=0.
                let encoding = if self
                    .data
                    .get(..64)
                    .is_some_and(|prefix| prefix.iter().all(|byte| *byte == 0))
                {
                    TypedModuleLayout::CleanLegacy
                } else {
                    self.typed_module_layout()?
                };
                let size = match encoding {
                    TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => 32,
                    TypedModuleLayout::CleanLegacy => 0,
                };
                if header.rc != 0 || header.cs_sz != size {
                    return Err(OleanError::Region(
                        "unsupported projected numeric Name layout".into(),
                    ));
                }
                self.bytes_at(offset, if size == 0 { 24 } else { usize::from(size) })?;
                let parent_ptr = self.read_u64_at(offset + 8)?;
                let field = self.read_u64_at(offset + 16)?;
                let num = match encoding {
                    TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => {
                        self.read_kernel_nat_u64(field)?
                    }
                    TypedModuleLayout::CleanLegacy => field,
                };

                // Read parent name (cached rc).
                let parent: std::rc::Rc<str> = if parent_ptr == 1 {
                    std::rc::Rc::from("")
                } else if is_ptr(parent_ptr) {
                    let parent_off = self.ptr_to_offset(parent_ptr)?;
                    self.read_name_rc_at_depth(parent_off, depth + 1)?
                } else {
                    return Err(OleanError::Region(
                        "invalid projected numeric Name parent".into(),
                    ));
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
    #[cfg(test)]
    pub(crate) fn find_all_names(&self) -> Vec<(usize, String)> {
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
mod tests;

#[cfg(test)]
#[path = "region_mpz_tests.rs"]
mod mpz_tests;
