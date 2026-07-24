// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared semantics-level memory abstractions.
//!
//! `clean-c-sem` and `clean-rust-sem` both model memory as provenance-tagged
//! allocations with byte-addressable contents. This module captures only that
//! shared core so the language-specific crates can share helpers without
//! forcing C pointers or Rust addresses into the kernel API.

use serde::{Deserialize, Serialize};

/// Provenance/base-allocation handle shared across semantics crates.
///
/// Offsets are supplied separately to [`MemoryModel::read`] and
/// [`MemoryModel::write`], which keeps this type neutral between the C and Rust
/// memory models.
#[derive(
    Debug, Default, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct Address(pub u64);

impl Address {
    /// The distinguished null / invalid address.
    pub const NULL: Self = Self(0);

    /// Create an address from a raw provenance identifier.
    pub const fn new(raw: u64) -> Self {
        Self(raw)
    }

    /// Return the raw provenance identifier.
    pub const fn raw(self) -> u64 {
        self.0
    }

    /// Check whether this is the distinguished null / invalid address.
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }
}

/// Single byte stored in the shared memory abstraction.
///
/// Richer typed or aligned loads remain the responsibility of concrete memory
/// model implementations.
#[derive(
    Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct MemoryValue(pub u8);

impl MemoryValue {
    /// Zero-initialized memory byte.
    pub const ZERO: Self = Self(0);

    /// Construct a memory byte.
    pub const fn new(byte: u8) -> Self {
        Self(byte)
    }

    /// Return the underlying byte value.
    pub const fn get(self) -> u8 {
        self.0
    }
}

impl From<u8> for MemoryValue {
    fn from(value: u8) -> Self {
        Self(value)
    }
}

impl From<MemoryValue> for u8 {
    fn from(value: MemoryValue) -> Self {
        value.0
    }
}

/// Shared byte-addressable memory model interface.
///
/// This trait intentionally abstracts only the common denominator between the
/// C and Rust semantics memory models:
/// - allocation by size
/// - byte reads and writes relative to a base allocation
/// - deallocation
/// - validity checks
///
/// Alignment, permissions, typed loads/stores, stack-frame tracking, borrow
/// tracking, and provenance-aware pointer arithmetic remain language-specific.
pub trait MemoryModel {
    /// Concrete error type reported by the implementing memory model.
    type Error;

    /// Allocate a new byte-addressable region and return its base address.
    fn allocate(&mut self, size: usize) -> Result<Address, Self::Error>;

    /// Read a byte at `offset` within `addr`.
    fn read(&self, addr: Address, offset: usize) -> Result<MemoryValue, Self::Error>;

    /// Write a byte at `offset` within `addr`.
    fn write(
        &mut self,
        addr: Address,
        offset: usize,
        value: MemoryValue,
    ) -> Result<(), Self::Error>;

    /// Free the allocation identified by `addr`.
    fn free(&mut self, addr: Address) -> Result<(), Self::Error>;

    /// Check whether `addr` still refers to a live allocation.
    fn is_valid(&self, addr: Address) -> bool;
}

#[cfg(test)]
mod tests {
    use super::{Address, MemoryModel, MemoryValue};
    use std::collections::HashMap;

    #[derive(Debug, Default)]
    struct SimpleMemory {
        blocks: HashMap<u64, Vec<u8>>,
        next_id: u64,
    }

    impl SimpleMemory {
        fn new() -> Self {
            Self {
                blocks: HashMap::new(),
                next_id: 1,
            }
        }
    }

    impl MemoryModel for SimpleMemory {
        type Error = &'static str;

        fn allocate(&mut self, size: usize) -> Result<Address, Self::Error> {
            let id = self.next_id;
            self.next_id += 1;
            self.blocks.insert(id, vec![0; size]);
            Ok(Address::new(id))
        }

        fn read(&self, addr: Address, offset: usize) -> Result<MemoryValue, Self::Error> {
            let block = self.blocks.get(&addr.raw()).ok_or("invalid address")?;
            block
                .get(offset)
                .copied()
                .map(MemoryValue::new)
                .ok_or("out of bounds")
        }

        fn write(
            &mut self,
            addr: Address,
            offset: usize,
            value: MemoryValue,
        ) -> Result<(), Self::Error> {
            let block = self.blocks.get_mut(&addr.raw()).ok_or("invalid address")?;
            let byte = block.get_mut(offset).ok_or("out of bounds")?;
            *byte = value.get();
            Ok(())
        }

        fn free(&mut self, addr: Address) -> Result<(), Self::Error> {
            self.blocks
                .remove(&addr.raw())
                .map(|_| ())
                .ok_or("invalid address")
        }

        fn is_valid(&self, addr: Address) -> bool {
            self.blocks.contains_key(&addr.raw())
        }
    }

    #[test]
    fn address_null_sentinel() {
        let addr = Address::NULL;
        assert!(addr.is_null());
        assert_eq!(addr.raw(), 0);
    }

    #[test]
    fn address_non_null() {
        let addr = Address::new(42);
        assert!(!addr.is_null());
        assert_eq!(addr.raw(), 42);
    }

    #[test]
    fn memory_value_round_trip() {
        let val = MemoryValue::new(0xAB);
        assert_eq!(val.get(), 0xAB);

        let from: MemoryValue = 0xCD.into();
        let back: u8 = from.into();
        assert_eq!(back, 0xCD);
    }

    #[test]
    fn simple_memory_allocate_write_read() {
        let mut mem = SimpleMemory::new();
        let addr = mem.allocate(4).expect("allocation should succeed");
        assert!(mem.is_valid(addr));

        mem.write(addr, 0, MemoryValue::new(0x11))
            .expect("write should succeed");
        mem.write(addr, 1, MemoryValue::new(0x22))
            .expect("write should succeed");

        assert_eq!(
            mem.read(addr, 0).expect("read should succeed"),
            MemoryValue::new(0x11)
        );
        assert_eq!(
            mem.read(addr, 1).expect("read should succeed"),
            MemoryValue::new(0x22)
        );
    }

    #[test]
    fn simple_memory_free_invalidates() {
        let mut mem = SimpleMemory::new();
        let addr = mem.allocate(4).expect("allocation should succeed");
        assert!(mem.is_valid(addr));

        mem.free(addr).expect("free should succeed");
        assert!(!mem.is_valid(addr));
    }

    #[test]
    fn simple_memory_read_after_free_fails() {
        let mut mem = SimpleMemory::new();
        let addr = mem.allocate(4).expect("allocation should succeed");
        mem.free(addr).expect("free should succeed");

        assert!(mem.read(addr, 0).is_err());
    }

    #[test]
    fn simple_memory_out_of_bounds_fails() {
        let mut mem = SimpleMemory::new();
        let addr = mem.allocate(2).expect("allocation should succeed");

        assert!(mem.read(addr, 5).is_err());
        assert!(mem.write(addr, 5, MemoryValue::ZERO).is_err());
    }
}
