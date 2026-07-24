// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared region-based memory model interface for semantics crates.
//!
//! `clean-c-sem` and `clean-rust-sem` both expose byte-addressable,
//! provenance-preserving memories, but they differ in pointer shape and
//! language-specific aliasing rules. This module captures the common surface
//! as allocation identifiers plus regions within those allocations.

use serde::{Deserialize, Serialize};

/// Stable identifier for an allocation or memory block.
#[derive(
    Debug, Default, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct AllocationId(pub u64);

impl AllocationId {
    /// The distinguished null / invalid allocation ID.
    pub const NULL: Self = Self(0);

    /// Construct an allocation ID from its raw representation.
    pub const fn new(raw: u64) -> Self {
        Self(raw)
    }

    /// Return the raw allocation identifier.
    pub const fn raw(self) -> u64 {
        self.0
    }

    /// Whether this is the distinguished null / invalid allocation.
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }
}

/// Byte range within a single allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MemoryRegion {
    allocation: AllocationId,
    offset: usize,
    len: usize,
}

impl MemoryRegion {
    /// Construct a region within an allocation.
    pub const fn new(allocation: AllocationId, offset: usize, len: usize) -> Self {
        Self {
            allocation,
            offset,
            len,
        }
    }

    /// The allocation this region belongs to.
    pub const fn allocation(self) -> AllocationId {
        self.allocation
    }

    /// Byte offset from the start of the allocation.
    pub const fn offset(self) -> usize {
        self.offset
    }

    /// Length in bytes.
    pub const fn len(self) -> usize {
        self.len
    }

    /// Whether the region is empty.
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }
}

/// Access mode validated by [`MemoryModel::borrow_check`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BorrowAccess {
    /// Shared, read-only access.
    Shared,
    /// Exclusive, mutable access.
    Mutable,
}

/// Shared byte-oriented memory interface used by semantics crates.
///
/// The trait is intentionally region-based so implementations do not need to
/// share a concrete pointer type. C can continue using signed offsets while
/// Rust keeps unsigned addresses and its richer ownership model.
pub trait MemoryModel {
    /// Concrete error type reported by the implementation.
    type Error;

    /// Allocate `size` bytes with the requested alignment.
    fn alloc(&mut self, size: usize, align: usize) -> Result<AllocationId, Self::Error>;

    /// Deallocate an allocation by ID.
    fn dealloc(&mut self, allocation: AllocationId) -> Result<(), Self::Error>;

    /// Read the bytes in `region`.
    fn read(&self, region: MemoryRegion) -> Result<Vec<u8>, Self::Error>;

    /// Write `bytes` into `region`.
    ///
    /// Implementations may reject length mismatches when `bytes.len()` differs
    /// from `region.len()`.
    fn write(&mut self, region: MemoryRegion, bytes: &[u8]) -> Result<(), Self::Error>;

    /// Validate a shared or mutable borrow-style access to `region`.
    fn borrow_check(
        &mut self,
        region: MemoryRegion,
        access: BorrowAccess,
    ) -> Result<(), Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::{AllocationId, BorrowAccess, MemoryModel, MemoryRegion};
    use std::collections::HashMap;

    #[derive(Debug, Default)]
    struct MockMemory {
        allocations: HashMap<AllocationId, Vec<u8>>,
        next_alloc: u64,
        shared_borrows: HashMap<AllocationId, usize>,
        mutable_borrows: HashMap<AllocationId, bool>,
    }

    impl MockMemory {
        fn new() -> Self {
            Self {
                allocations: HashMap::new(),
                next_alloc: 1,
                shared_borrows: HashMap::new(),
                mutable_borrows: HashMap::new(),
            }
        }
    }

    impl MemoryModel for MockMemory {
        type Error = &'static str;

        fn alloc(&mut self, size: usize, _align: usize) -> Result<AllocationId, Self::Error> {
            let alloc = AllocationId(self.next_alloc);
            self.next_alloc += 1;
            self.allocations.insert(alloc, vec![0; size]);
            Ok(alloc)
        }

        fn dealloc(&mut self, allocation: AllocationId) -> Result<(), Self::Error> {
            self.shared_borrows.remove(&allocation);
            self.mutable_borrows.remove(&allocation);
            self.allocations
                .remove(&allocation)
                .map(|_| ())
                .ok_or("invalid allocation")
        }

        fn read(&self, region: MemoryRegion) -> Result<Vec<u8>, Self::Error> {
            let bytes = self
                .allocations
                .get(&region.allocation())
                .ok_or("invalid allocation")?;
            let end = region
                .offset()
                .checked_add(region.len())
                .ok_or("out of bounds")?;
            bytes
                .get(region.offset()..end)
                .map(|slice| slice.to_vec())
                .ok_or("out of bounds")
        }

        fn write(&mut self, region: MemoryRegion, bytes: &[u8]) -> Result<(), Self::Error> {
            if bytes.len() != region.len() {
                return Err("length mismatch");
            }

            let block = self
                .allocations
                .get_mut(&region.allocation())
                .ok_or("invalid allocation")?;
            let end = region
                .offset()
                .checked_add(region.len())
                .ok_or("out of bounds")?;
            let dst = block.get_mut(region.offset()..end).ok_or("out of bounds")?;
            dst.copy_from_slice(bytes);
            Ok(())
        }

        fn borrow_check(
            &mut self,
            region: MemoryRegion,
            access: BorrowAccess,
        ) -> Result<(), Self::Error> {
            let _ = self.read(region)?;
            match access {
                BorrowAccess::Shared => {
                    if self
                        .mutable_borrows
                        .get(&region.allocation())
                        .copied()
                        .unwrap_or(false)
                    {
                        return Err("mutable borrow already active");
                    }
                    *self.shared_borrows.entry(region.allocation()).or_default() += 1;
                }
                BorrowAccess::Mutable => {
                    if self
                        .mutable_borrows
                        .get(&region.allocation())
                        .copied()
                        .unwrap_or(false)
                        || self
                            .shared_borrows
                            .get(&region.allocation())
                            .copied()
                            .unwrap_or(0)
                            > 0
                    {
                        return Err("conflicting borrow already active");
                    }
                    self.mutable_borrows.insert(region.allocation(), true);
                }
            }
            Ok(())
        }
    }

    #[test]
    fn memory_region_tracks_allocation_and_bounds() {
        let region = MemoryRegion::new(AllocationId::new(7), 4, 12);
        assert_eq!(region.allocation(), AllocationId::new(7));
        assert_eq!(region.offset(), 4);
        assert_eq!(region.len(), 12);
        assert!(!region.is_empty());
    }

    #[test]
    fn shared_memory_model_round_trips_bytes() {
        let mut memory = MockMemory::new();
        let alloc = memory.alloc(4, 4).expect("allocation should succeed");
        let region = MemoryRegion::new(alloc, 0, 4);

        memory
            .borrow_check(region, BorrowAccess::Mutable)
            .expect("mutable borrow should be allowed");
        memory
            .write(region, &[1, 2, 3, 4])
            .expect("write should succeed");
        assert_eq!(
            memory.read(region).expect("read should succeed"),
            vec![1, 2, 3, 4]
        );
    }

    #[test]
    fn borrow_check_rejects_conflicting_mutable_access() {
        let mut memory = MockMemory::new();
        let alloc = memory.alloc(8, 8).expect("allocation should succeed");
        let region = MemoryRegion::new(alloc, 0, 8);

        memory
            .borrow_check(region, BorrowAccess::Shared)
            .expect("shared borrow should be allowed");
        assert!(
            memory.borrow_check(region, BorrowAccess::Mutable).is_err(),
            "mutable borrow should conflict with existing shared borrow"
        );
    }
}
