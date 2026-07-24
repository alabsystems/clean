// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared byte-oriented memory traits for semantics crates.
//!
//! Both `clean-c-sem` and `clean-rust-sem` use provenance-preserving, block-based
//! memory models in the CompCert style:
//!
//! - each live allocation has a stable allocation identifier
//! - pointers are `(alloc_id, offset)` pairs
//! - dereference checks validate provenance, liveness, and bounds
//! - typed loads/stores are layered on top of raw byte operations
//!
//! This module captures that common surface without forcing the two semantics
//! crates to share their richer language-specific invariants.
//!
//! # Mapping From Existing Models
//!
//! `clean-c-sem::memory::Memory`
//! - `AllocId = BlockId`
//! - `Pointer = Pointer { block, offset }`
//! - `alloc(size, align)` maps to `Memory::alloc(size, align)`
//! - `dealloc(ptr)` maps to `Memory::free(ptr)`
//! - `read_bytes(ptr, size)` maps to `Memory::load_bytes(ptr, size)`
//! - `write_bytes(ptr, bytes)` maps to `Memory::store_bytes(ptr, bytes)`
//! - `null_ptr()` maps to `Pointer::null()`
//!
//! `clean-rust-sem::memory::Memory`
//! - `AllocId = AllocId`
//! - `Pointer = Address { alloc_id, offset }`
//! - `alloc(size, align)` maps to `Memory::allocate_aligned(size, align)`
//! - `dealloc(ptr)` maps to `Memory::deallocate(ptr)`
//! - `read_bytes(ptr, size)` maps to `Memory::read_bytes(ptr, size)` with an
//!   owned copy of the returned slice
//! - `write_bytes(ptr, bytes)` maps to `Memory::write_bytes(ptr, bytes)`
//! - `null_ptr()` maps to `Memory::null_ptr()`
//!
//! # Notes
//!
//! The trait intentionally does not standardize every edge-case semantic.
//! For example, `free(NULL)` is a no-op in the C model while null deallocation
//! is an error in the Rust model. Generic code can rely on the shared byte and
//! provenance shape, but language-specific rules still belong to each semantics
//! crate.

use std::hash::Hash;

/// Provenance-carrying pointer in a block/allocation-based memory model.
///
/// The shared contract only needs to know which allocation a pointer came from
/// and what byte offset within that allocation it denotes.
pub trait ProvenanceModel: Copy + Eq {
    /// Stable allocation / block identifier used as provenance.
    type AllocId: Copy + Eq + Hash;

    /// Return the allocation that this pointer originated from.
    fn alloc_id(self) -> Self::AllocId;

    /// Return the pointer's byte offset from the start of its allocation.
    ///
    /// `i128` is used so both signed C offsets and nonnegative Rust offsets fit
    /// in the shared interface.
    fn offset_bytes(self) -> i128;

    /// Construct a pointer from an allocation ID and byte offset.
    ///
    /// Returns `None` when the concrete pointer representation cannot encode
    /// the requested offset.
    fn from_parts(alloc_id: Self::AllocId, offset: i128) -> Option<Self>;

    /// Apply byte-wise pointer arithmetic.
    ///
    /// Returns `None` when the concrete pointer representation would overflow.
    fn with_offset(self, delta: i64) -> Option<Self>;
}

/// Shared CompCert-style memory model interface.
///
/// The trait is intentionally byte-oriented: alignment-sensitive typed loads,
/// borrow tracking, stack-frame discipline, and aliasing rules remain
/// language-specific layers built on top of this abstraction.
pub trait MemoryModel {
    /// Allocation / block identifier type used for provenance.
    type AllocId: Copy + Eq + Hash;

    /// Pointer / address type used by the concrete memory model.
    type Pointer: ProvenanceModel<AllocId = Self::AllocId>;

    /// Concrete error type reported by the memory implementation.
    type Error;

    /// Allocate a new block or allocation with the given size and alignment.
    fn alloc(&mut self, size: usize, align: usize) -> Result<Self::Pointer, Self::Error>;

    /// Deallocate the allocation identified by `ptr`.
    ///
    /// Concrete models may impose additional rules, such as requiring `ptr` to
    /// name the base of the allocation.
    fn dealloc(&mut self, ptr: Self::Pointer) -> Result<(), Self::Error>;

    /// Read `size` bytes starting at `ptr`.
    fn read_bytes(&self, ptr: Self::Pointer, size: usize) -> Result<Vec<u8>, Self::Error>;

    /// Write `bytes` starting at `ptr`.
    fn write_bytes(&mut self, ptr: Self::Pointer, bytes: &[u8]) -> Result<(), Self::Error>;

    /// Return whether `ptr` still denotes a live allocation / block.
    fn is_valid(&self, ptr: Self::Pointer) -> bool;

    /// Return the distinguished null pointer for this memory model.
    fn null_ptr(&self) -> Self::Pointer;

    /// Apply byte-wise pointer arithmetic, returning the offset pointer.
    ///
    /// The default implementation delegates to
    /// [`ProvenanceModel::with_offset`].  Concrete models may override this
    /// to perform additional validity checks (e.g. bounds checking).
    ///
    /// Returns `None` when the resulting pointer cannot be represented.
    fn pointer_offset(&self, ptr: Self::Pointer, delta: i64) -> Option<Self::Pointer> {
        ptr.with_offset(delta)
    }
}

#[cfg(test)]
mod tests {
    use super::{MemoryModel, ProvenanceModel};
    use std::collections::HashMap;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct TestAllocId(u64);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TestPtr {
        alloc_id: TestAllocId,
        offset: i64,
    }

    impl TestPtr {
        const fn null() -> Self {
            Self {
                alloc_id: TestAllocId(0),
                offset: 0,
            }
        }
    }

    impl ProvenanceModel for TestPtr {
        type AllocId = TestAllocId;

        fn alloc_id(self) -> Self::AllocId {
            self.alloc_id
        }

        fn offset_bytes(self) -> i128 {
            i128::from(self.offset)
        }

        fn from_parts(alloc_id: Self::AllocId, offset: i128) -> Option<Self> {
            Some(Self {
                alloc_id,
                offset: i64::try_from(offset).ok()?,
            })
        }

        fn with_offset(self, delta: i64) -> Option<Self> {
            Some(Self {
                alloc_id: self.alloc_id,
                offset: self.offset.checked_add(delta)?,
            })
        }
    }

    #[derive(Debug, Default)]
    struct MockMemory {
        blocks: HashMap<TestAllocId, Vec<u8>>,
        next_alloc: u64,
    }

    impl MockMemory {
        fn new() -> Self {
            Self {
                blocks: HashMap::new(),
                next_alloc: 1,
            }
        }
    }

    impl MemoryModel for MockMemory {
        type AllocId = TestAllocId;
        type Pointer = TestPtr;
        type Error = &'static str;

        fn alloc(&mut self, size: usize, _align: usize) -> Result<Self::Pointer, Self::Error> {
            let alloc_id = TestAllocId(self.next_alloc);
            self.next_alloc += 1;
            self.blocks.insert(alloc_id, vec![0; size]);
            Ok(TestPtr {
                alloc_id,
                offset: 0,
            })
        }

        fn dealloc(&mut self, ptr: Self::Pointer) -> Result<(), Self::Error> {
            self.blocks
                .remove(&ptr.alloc_id)
                .map(|_| ())
                .ok_or("invalid pointer")
        }

        fn read_bytes(&self, ptr: Self::Pointer, size: usize) -> Result<Vec<u8>, Self::Error> {
            let block = self.blocks.get(&ptr.alloc_id).ok_or("invalid pointer")?;
            let start = usize::try_from(ptr.offset).map_err(|_| "negative offset")?;
            let end = start.checked_add(size).ok_or("out of bounds")?;
            block
                .get(start..end)
                .map(|bytes| bytes.to_vec())
                .ok_or("out of bounds")
        }

        fn write_bytes(&mut self, ptr: Self::Pointer, bytes: &[u8]) -> Result<(), Self::Error> {
            let block = self
                .blocks
                .get_mut(&ptr.alloc_id)
                .ok_or("invalid pointer")?;
            let start = usize::try_from(ptr.offset).map_err(|_| "negative offset")?;
            let end = start.checked_add(bytes.len()).ok_or("out of bounds")?;
            let dst = block.get_mut(start..end).ok_or("out of bounds")?;
            dst.copy_from_slice(bytes);
            Ok(())
        }

        fn is_valid(&self, ptr: Self::Pointer) -> bool {
            self.blocks.contains_key(&ptr.alloc_id)
        }

        fn null_ptr(&self) -> Self::Pointer {
            TestPtr::null()
        }
    }

    #[test]
    fn provenance_model_tracks_alloc_id_and_offset() {
        let ptr = TestPtr::from_parts(TestAllocId(7), 12).expect("pointer should fit");
        assert_eq!(ptr.alloc_id(), TestAllocId(7));
        assert_eq!(ptr.offset_bytes(), 12);
        assert_eq!(
            ptr.with_offset(-2).expect("offset should remain in range"),
            TestPtr {
                alloc_id: TestAllocId(7),
                offset: 10,
            }
        );
    }

    #[test]
    fn memory_model_supports_byte_round_trip() {
        let mut memory = MockMemory::new();
        let ptr = memory.alloc(4, 4).expect("allocation should succeed");

        memory
            .write_bytes(ptr, &[1, 2, 3, 4])
            .expect("write should succeed");
        assert_eq!(
            memory.read_bytes(ptr, 4).expect("read should succeed"),
            vec![1, 2, 3, 4]
        );

        memory.dealloc(ptr).expect("deallocation should succeed");
        assert!(!memory.is_valid(ptr));
    }

    #[test]
    fn memory_model_exposes_null_pointer() {
        let memory = MockMemory::new();
        let null = memory.null_ptr();
        assert_eq!(null.alloc_id(), TestAllocId(0));
        assert_eq!(null.offset_bytes(), 0);
    }

    #[test]
    fn pointer_offset_applies_positive_delta() {
        let mut memory = MockMemory::new();
        let ptr = memory.alloc(16, 4).expect("allocation should succeed");
        let offset_ptr = memory
            .pointer_offset(ptr, 8)
            .expect("positive offset should succeed");
        assert_eq!(offset_ptr.alloc_id(), ptr.alloc_id());
        assert_eq!(offset_ptr.offset_bytes(), 8);
    }

    #[test]
    fn pointer_offset_applies_negative_delta() {
        let ptr = TestPtr {
            alloc_id: TestAllocId(1),
            offset: 10,
        };
        let memory = MockMemory::new();
        let offset_ptr = memory
            .pointer_offset(ptr, -3)
            .expect("negative offset should succeed");
        assert_eq!(offset_ptr.offset_bytes(), 7);
    }

    #[test]
    fn pointer_offset_returns_none_on_overflow() {
        let ptr = TestPtr {
            alloc_id: TestAllocId(1),
            offset: i64::MAX,
        };
        let memory = MockMemory::new();
        assert!(
            memory.pointer_offset(ptr, 1).is_none(),
            "offset overflow should return None"
        );
    }

    #[test]
    fn pointer_offset_write_then_read_at_offset() {
        let mut memory = MockMemory::new();
        let base = memory.alloc(8, 4).expect("allocation should succeed");

        memory
            .write_bytes(base, &[0xAA, 0xBB, 0xCC, 0xDD, 0x11, 0x22, 0x33, 0x44])
            .expect("write should succeed");

        let offset_ptr = memory
            .pointer_offset(base, 4)
            .expect("offset should succeed");
        let bytes = memory
            .read_bytes(offset_ptr, 4)
            .expect("read at offset should succeed");
        assert_eq!(bytes, vec![0x11, 0x22, 0x33, 0x44]);
    }
}
