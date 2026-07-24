// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared memory-model adapter for the Rust semantics memory.

use crate::memory::{Address, AllocId, Memory, MemoryError};
use crate::ownership::{BorrowChecker, BorrowError, OwnershipState, Place};
use crate::types::{Lifetime, Mutability};
use clean_kernel::memory_model::{
    AllocationId, BorrowAccess, MemoryModel as SharedMemoryModel, MemoryRegion,
};
use thiserror::Error;

/// Errors returned by the shared Rust memory-model adapter.
#[derive(Debug, Error)]
pub enum RustMemoryModelError {
    #[error(transparent)]
    Memory(#[from] MemoryError),

    #[error(transparent)]
    Borrow(#[from] BorrowError),

    #[error("write length {actual} does not match region length {expected}")]
    LengthMismatch { expected: usize, actual: usize },
}

/// Region-based adapter over the Rust memory model.
#[derive(Debug, Clone, Default)]
pub struct RustMemoryModel {
    memory: Memory,
    borrow_checker: BorrowChecker,
    ownership: OwnershipState,
}

impl RustMemoryModel {
    /// Create an empty adapter.
    pub fn new() -> Self {
        Self {
            memory: Memory::new(),
            borrow_checker: BorrowChecker::new(),
            ownership: OwnershipState::new(),
        }
    }

    /// Wrap an existing Rust memory instance.
    pub fn from_memory(memory: Memory) -> Self {
        Self {
            memory,
            borrow_checker: BorrowChecker::new(),
            ownership: OwnershipState::new(),
        }
    }

    /// Borrow the wrapped Rust memory.
    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Mutably borrow the wrapped Rust memory.
    pub fn memory_mut(&mut self) -> &mut Memory {
        &mut self.memory
    }

    /// Consume the adapter and return the wrapped Rust memory.
    pub fn into_memory(self) -> Memory {
        self.memory
    }

    fn address_for(region: MemoryRegion) -> Address {
        Address::new(AllocId(region.allocation().raw()), region.offset() as u64)
    }

    fn place_for(allocation: AllocationId) -> Place {
        Place::Static(format!("alloc:{}", allocation.raw()))
    }

    fn lifetime_for(allocation: AllocationId) -> Lifetime {
        Lifetime::Named(format!("alloc:{}", allocation.raw()))
    }

    fn ensure_region_live(&self, region: MemoryRegion) -> Result<(), RustMemoryModelError> {
        self.memory
            .read_bytes(Self::address_for(region), region.len())
            .map(|_| ())
            .map_err(Into::into)
    }

    fn check_write_len(region: MemoryRegion, bytes: &[u8]) -> Result<(), RustMemoryModelError> {
        if bytes.len() == region.len() {
            Ok(())
        } else {
            Err(RustMemoryModelError::LengthMismatch {
                expected: region.len(),
                actual: bytes.len(),
            })
        }
    }
}

impl SharedMemoryModel for RustMemoryModel {
    type Error = RustMemoryModelError;

    fn alloc(&mut self, size: usize, align: usize) -> Result<AllocationId, Self::Error> {
        let addr = self.memory.allocate_aligned(size, align)?;
        let allocation = AllocationId::new(addr.alloc_id.0);
        self.ownership.mark_owned(Self::place_for(allocation));
        Ok(allocation)
    }

    fn dealloc(&mut self, allocation: AllocationId) -> Result<(), Self::Error> {
        let lifetime = Self::lifetime_for(allocation);
        self.ownership.end_borrows(&lifetime);
        self.ownership.mark_moved(Self::place_for(allocation));
        self.memory
            .deallocate(Address::new(AllocId(allocation.raw()), 0))
            .map_err(Into::into)
    }

    fn read(&self, region: MemoryRegion) -> Result<Vec<u8>, Self::Error> {
        self.memory
            .read_bytes(Self::address_for(region), region.len())
            .map(|bytes| bytes.to_vec())
            .map_err(Into::into)
    }

    fn write(&mut self, region: MemoryRegion, bytes: &[u8]) -> Result<(), Self::Error> {
        Self::check_write_len(region, bytes)?;
        self.memory
            .write_bytes(Self::address_for(region), bytes)
            .map_err(Into::into)
    }

    fn borrow_check(
        &mut self,
        region: MemoryRegion,
        access: BorrowAccess,
    ) -> Result<(), Self::Error> {
        self.ensure_region_live(region)?;

        let allocation = region.allocation();
        let place = Self::place_for(allocation);
        let lifetime = Self::lifetime_for(allocation);
        let mutability = match access {
            BorrowAccess::Shared => Mutability::Shared,
            BorrowAccess::Mutable => Mutability::Mutable,
        };

        self.borrow_checker
            .check_borrow(&self.ownership, &place, mutability, &lifetime)?;
        let _ = self.ownership.add_borrow(place, mutability, lifetime)?;
        Ok(())
    }
}
