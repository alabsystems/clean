// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared memory-model adapter for the C semantics memory.

use crate::memory::{BlockId, Memory, Pointer};
use crate::ub::UBKind;
use clean_kernel::memory_model::{
    AllocationId, BorrowAccess, MemoryModel as SharedMemoryModel, MemoryRegion,
};

/// Region-based adapter over the C memory model.
#[derive(Debug, Clone, Default)]
pub struct CMemoryModel {
    memory: Memory,
}

impl CMemoryModel {
    /// Create an empty adapter.
    pub fn new() -> Self {
        Self {
            memory: Memory::new(),
        }
    }

    /// Wrap an existing C memory instance.
    pub fn from_memory(memory: Memory) -> Self {
        Self { memory }
    }

    /// Borrow the wrapped memory.
    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Mutably borrow the wrapped memory.
    pub fn memory_mut(&mut self) -> &mut Memory {
        &mut self.memory
    }

    /// Consume the adapter and return the wrapped memory.
    pub fn into_memory(self) -> Memory {
        self.memory
    }

    fn ptr_for(region: MemoryRegion) -> Result<Pointer, UBKind> {
        let offset = i64::try_from(region.offset()).map_err(|_| UBKind::PointerOverflow)?;
        Ok(Pointer::with_offset(
            BlockId(region.allocation().raw()),
            offset,
        ))
    }

    fn check_write_len(region: MemoryRegion, bytes: &[u8]) -> Result<(), UBKind> {
        if bytes.len() == region.len() {
            Ok(())
        } else {
            Err(UBKind::Other(format!(
                "write length {} does not match region length {}",
                bytes.len(),
                region.len()
            )))
        }
    }
}

impl SharedMemoryModel for CMemoryModel {
    type Error = UBKind;

    fn alloc(&mut self, size: usize, align: usize) -> Result<AllocationId, Self::Error> {
        let ptr = self.memory.alloc(size, align)?;
        Ok(AllocationId::new(ptr.block.0))
    }

    fn dealloc(&mut self, allocation: AllocationId) -> Result<(), Self::Error> {
        self.memory.free(Pointer::new(BlockId(allocation.raw())))
    }

    fn read(&self, region: MemoryRegion) -> Result<Vec<u8>, Self::Error> {
        self.memory.load_bytes(Self::ptr_for(region)?, region.len())
    }

    fn write(&mut self, region: MemoryRegion, bytes: &[u8]) -> Result<(), Self::Error> {
        Self::check_write_len(region, bytes)?;
        self.memory.store_bytes(Self::ptr_for(region)?, bytes)
    }

    fn borrow_check(
        &mut self,
        region: MemoryRegion,
        access: BorrowAccess,
    ) -> Result<(), Self::Error> {
        let ptr = Self::ptr_for(region)?;
        match access {
            BorrowAccess::Shared => self.memory.can_read(ptr, region.len()),
            BorrowAccess::Mutable => self.memory.can_write(ptr, region.len()),
        }
    }
}
