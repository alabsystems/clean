// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Memory Model Formalization
//!
//! This module formalizes the Rust memory model, including:
//!
//! - Memory allocation and deallocation
//! - Pointer validity and provenance
//! - Alignment requirements
//! - Read/write operations
//!
//! The model is inspired by CompCert and Stacked Borrows (Ralf Jung et al.)
//!
//! ## Memory Regions
//!
//! Memory is organized into regions:
//! - Stack frames (per function call)
//! - Heap allocations (Box, Vec, etc.)
//! - Static/global memory
//!
//! Each allocation has:
//! - A unique allocation ID (provenance)
//! - Size and alignment
//! - Read/write permissions

mod allocation;
pub use allocation::Allocation;

use crate::types::RustType;
use clean_kernel::sem_memory_trait::{
    MemoryModel as SharedMemoryModel, ProvenanceModel as SharedProvenanceModel,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// Allocation ID (provenance)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AllocId(pub u64);

/// Memory address (abstract, not real addresses)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Address {
    /// Allocation this pointer came from
    pub alloc_id: AllocId,
    /// Offset within the allocation
    pub offset: u64,
}

impl Address {
    pub fn new(alloc_id: AllocId, offset: u64) -> Self {
        Self { alloc_id, offset }
    }

    /// Add offset to address
    pub fn offset(self, delta: i64) -> Option<Self> {
        let new_offset = if delta >= 0 {
            self.offset.checked_add(delta as u64)?
        } else {
            self.offset.checked_sub(delta.unsigned_abs())?
        };
        Some(Self {
            alloc_id: self.alloc_id,
            offset: new_offset,
        })
    }
}

impl SharedProvenanceModel for Address {
    type AllocId = AllocId;

    fn alloc_id(self) -> Self::AllocId {
        self.alloc_id
    }

    fn offset_bytes(self) -> i128 {
        i128::from(self.offset)
    }

    fn from_parts(alloc_id: Self::AllocId, offset: i128) -> Option<Self> {
        Some(Self {
            alloc_id,
            offset: u64::try_from(offset).ok()?,
        })
    }

    fn with_offset(self, delta: i64) -> Option<Self> {
        self.offset(delta)
    }
}

/// Memory operation errors (Rust memory safety violations)
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum MemoryError {
    /// Failed to allocate memory with requested size and alignment
    #[error("allocation failed: size {size}, alignment {align}")]
    AllocationFailed {
        /// Requested allocation size in bytes
        size: usize,
        /// Requested alignment in bytes
        align: usize,
    },

    /// Pointer refers to non-existent allocation
    #[error("invalid pointer: allocation {0:?} does not exist")]
    InvalidPointer(AllocId),

    /// Attempted to access memory after it was freed
    #[error("use after free: allocation {0:?} has been deallocated")]
    UseAfterFree(AllocId),

    /// Attempted to free already-freed memory
    #[error("double free: allocation {0:?}")]
    DoubleFree(AllocId),

    /// Memory access extends beyond allocation bounds
    #[error("out of bounds access: offset {offset} + size {size} > allocation size {alloc_size}")]
    OutOfBounds {
        /// Byte offset from allocation start
        offset: u64,
        /// Size of attempted access in bytes
        size: usize,
        /// Total size of the allocation
        alloc_size: usize,
    },

    /// Memory access not aligned to type requirements
    #[error("misaligned access: offset {offset} not aligned to {align}")]
    Misaligned {
        /// Byte offset from allocation start
        offset: u64,
        /// Required alignment in bytes
        align: usize,
    },

    /// Attempted to dereference null pointer
    #[error("null pointer dereference")]
    NullPointer,

    /// Contents are conservatively unknown after an opaque side effect
    #[error("tainted memory read: allocation {0:?} was invalidated by an opaque effect")]
    TaintedRead(AllocId),

    /// Pointer arithmetic would wrap around address space
    #[error("integer overflow in pointer arithmetic")]
    PointerOverflow,
}

/// The memory model
#[derive(Debug, Clone)]
pub struct Memory {
    /// All allocations indexed by ID
    allocations: HashMap<AllocId, Allocation>,
    /// Counter for allocation IDs
    next_alloc_id: u64,
    /// Null allocation (never valid to access)
    null_alloc: AllocId,
}

impl Memory {
    /// Create a new memory model
    pub fn new() -> Self {
        let null_alloc = AllocId(0);
        Self {
            allocations: HashMap::new(),
            next_alloc_id: 1, // Start from 1, 0 is null
            null_alloc,
        }
    }

    /// Allocate memory of given size and alignment
    pub fn allocate(&mut self, size: usize) -> Result<Address, MemoryError> {
        self.allocate_aligned(size, 1)
    }

    /// Allocate memory with specific alignment
    pub fn allocate_aligned(&mut self, size: usize, align: usize) -> Result<Address, MemoryError> {
        if align == 0 || !align.is_power_of_two() {
            return Err(MemoryError::AllocationFailed { size, align });
        }

        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;

        let alloc = Allocation::new(id, size, align);
        self.allocations.insert(id, alloc);

        Ok(Address::new(id, 0))
    }

    /// Allocate memory for a typed value
    pub fn allocate_typed(&mut self, ty: &RustType) -> Result<Address, MemoryError> {
        let size = ty
            .size()
            .ok_or(MemoryError::AllocationFailed { size: 0, align: 1 })?;
        let align = self.type_alignment(ty);
        let addr = self.allocate_aligned(size, align)?;

        self.set_allocation_type(addr, ty.clone())?;
        Ok(addr)
    }

    /// Associate semantic type metadata with an allocation.
    pub fn set_allocation_type(&mut self, addr: Address, ty: RustType) -> Result<(), MemoryError> {
        let alloc = self
            .allocations
            .get_mut(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;
        if !alloc.valid {
            return Err(MemoryError::UseAfterFree(addr.alloc_id));
        }
        alloc.set_type(ty);
        Ok(())
    }

    /// Record runtime slice-length metadata for an allocation.
    pub fn record_slice_len(&mut self, addr: Address, len: usize) -> Result<(), MemoryError> {
        let alloc = self
            .allocations
            .get_mut(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;
        if !alloc.valid {
            return Err(MemoryError::UseAfterFree(addr.alloc_id));
        }
        alloc.slice_len = Some(len);
        Ok(())
    }

    /// Recover the semantic type attached to an allocation, if present.
    pub fn allocation_type(&self, addr: Address) -> Option<&RustType> {
        self.allocations
            .get(&addr.alloc_id)
            .filter(|alloc| alloc.valid)
            .and_then(|alloc| alloc.ty.as_ref())
    }

    /// Recover the slice length attached to an allocation, if present.
    pub fn slice_len(&self, addr: Address) -> Option<usize> {
        self.allocations
            .get(&addr.alloc_id)
            .filter(|alloc| alloc.valid)
            .and_then(Allocation::slice_len)
    }

    /// Get alignment for a type
    fn type_alignment(&self, ty: &RustType) -> usize {
        match ty {
            RustType::Unit | RustType::Bool => 1,
            RustType::Char => 4,
            RustType::Uint(u) => u.size(),
            RustType::Int(i) => i.size(),
            RustType::Float(f) => f.size(),
            RustType::Array { element, .. } => self.type_alignment(element),
            RustType::Tuple(elems) => elems
                .iter()
                .map(|e| self.type_alignment(e))
                .max()
                .unwrap_or(1),
            // Default to pointer alignment for references, raw pointers, and other types
            _ => 8,
        }
    }

    /// Deallocate memory
    pub fn deallocate(&mut self, addr: Address) -> Result<(), MemoryError> {
        if self.is_null(addr) {
            return Err(MemoryError::NullPointer);
        }
        let alloc = self
            .allocations
            .get_mut(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;

        if !alloc.valid {
            return Err(MemoryError::DoubleFree(addr.alloc_id));
        }

        alloc.valid = false;
        Ok(())
    }

    /// Check if a pointer is valid
    pub fn is_valid(&self, addr: Address) -> bool {
        self.allocations
            .get(&addr.alloc_id)
            .is_some_and(|a| a.valid)
    }

    /// Check if pointer is null
    pub fn is_null(&self, addr: Address) -> bool {
        addr.alloc_id == self.null_alloc
    }

    /// Get a null pointer
    pub fn null_ptr(&self) -> Address {
        Address::new(self.null_alloc, 0)
    }

    /// Check that a typed access respects both the allocation's declared
    /// alignment and the offset alignment required by the accessed type.
    fn check_aligned(&self, addr: Address, align: usize) -> Result<(), MemoryError> {
        if self.is_null(addr) {
            return Err(MemoryError::NullPointer);
        }
        let alloc = self
            .allocations
            .get(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;

        if !alloc.valid {
            return Err(MemoryError::UseAfterFree(addr.alloc_id));
        }

        if align > 1 && (alloc.align < align || !alloc.is_aligned(addr.offset, align)) {
            return Err(MemoryError::Misaligned {
                offset: addr.offset,
                align,
            });
        }
        Ok(())
    }

    /// Read bytes from memory
    pub fn read_bytes(&self, addr: Address, size: usize) -> Result<&[u8], MemoryError> {
        if self.is_null(addr) {
            return Err(MemoryError::NullPointer);
        }
        let alloc = self
            .allocations
            .get(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;

        if !alloc.valid {
            return Err(MemoryError::UseAfterFree(addr.alloc_id));
        }

        if alloc.tainted {
            return Err(MemoryError::TaintedRead(addr.alloc_id));
        }

        if !alloc.in_bounds(addr.offset, size) {
            return Err(MemoryError::OutOfBounds {
                offset: addr.offset,
                size,
                alloc_size: alloc.size,
            });
        }

        let start = addr.offset as usize;
        Ok(&alloc.data[start..start + size])
    }

    /// Write bytes to memory
    pub fn write_bytes(&mut self, addr: Address, data: &[u8]) -> Result<(), MemoryError> {
        if self.is_null(addr) {
            return Err(MemoryError::NullPointer);
        }
        let alloc = self
            .allocations
            .get_mut(&addr.alloc_id)
            .ok_or(MemoryError::InvalidPointer(addr.alloc_id))?;

        if !alloc.valid {
            return Err(MemoryError::UseAfterFree(addr.alloc_id));
        }

        if !alloc.in_bounds(addr.offset, data.len()) {
            return Err(MemoryError::OutOfBounds {
                offset: addr.offset,
                size: data.len(),
                alloc_size: alloc.size,
            });
        }

        let start = addr.offset as usize;
        alloc.data[start..start + data.len()].copy_from_slice(data);
        if addr.offset == 0 && data.len() == alloc.size {
            alloc.tainted = false;
        }
        Ok(())
    }

    /// Conservatively invalidate all live allocations after an opaque memory effect.
    pub fn havoc_all(&mut self) {
        for allocation in self.allocations.values_mut() {
            if allocation.valid {
                allocation.tainted = true;
            }
        }
    }

    /// Read a u8
    pub fn read_u8(&self, addr: Address) -> Result<u8, MemoryError> {
        let bytes = self.read_bytes(addr, 1)?;
        Ok(bytes[0])
    }

    /// Read a u16
    pub fn read_u16(&self, addr: Address) -> Result<u16, MemoryError> {
        self.check_aligned(addr, 2)?;
        let bytes = self.read_bytes(addr, 2)?;
        Ok(u16::from_le_bytes(bytes.try_into().expect(
            "invariant: read_bytes(2) returns exactly 2 bytes",
        )))
    }

    /// Read a u32
    pub fn read_u32(&self, addr: Address) -> Result<u32, MemoryError> {
        self.check_aligned(addr, 4)?;
        let bytes = self.read_bytes(addr, 4)?;
        Ok(u32::from_le_bytes(bytes.try_into().expect(
            "invariant: read_bytes(4) returns exactly 4 bytes",
        )))
    }

    /// Read a u64
    pub fn read_u64(&self, addr: Address) -> Result<u64, MemoryError> {
        self.check_aligned(addr, 8)?;
        let bytes = self.read_bytes(addr, 8)?;
        Ok(u64::from_le_bytes(bytes.try_into().expect(
            "invariant: read_bytes(8) returns exactly 8 bytes",
        )))
    }

    /// Write a u8
    pub fn write_u8(&mut self, addr: Address, val: u8) -> Result<(), MemoryError> {
        self.write_bytes(addr, &[val])
    }

    /// Write a u16
    pub fn write_u16(&mut self, addr: Address, val: u16) -> Result<(), MemoryError> {
        self.check_aligned(addr, 2)?;
        self.write_bytes(addr, &val.to_le_bytes())
    }

    /// Write a u32
    pub fn write_u32(&mut self, addr: Address, val: u32) -> Result<(), MemoryError> {
        self.check_aligned(addr, 4)?;
        self.write_bytes(addr, &val.to_le_bytes())
    }

    /// Write a u64
    pub fn write_u64(&mut self, addr: Address, val: u64) -> Result<(), MemoryError> {
        self.check_aligned(addr, 8)?;
        self.write_bytes(addr, &val.to_le_bytes())
    }

    /// Get allocation info
    pub fn get_allocation(&self, id: AllocId) -> Option<&Allocation> {
        self.allocations.get(&id)
    }

    /// Get mutable allocation info
    pub fn get_allocation_mut(&mut self, id: AllocId) -> Option<&mut Allocation> {
        self.allocations.get_mut(&id)
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

impl SharedMemoryModel for Memory {
    type AllocId = AllocId;
    type Pointer = Address;
    type Error = MemoryError;

    fn alloc(&mut self, size: usize, align: usize) -> Result<Self::Pointer, Self::Error> {
        Memory::allocate_aligned(self, size, align)
    }

    fn dealloc(&mut self, ptr: Self::Pointer) -> Result<(), Self::Error> {
        Memory::deallocate(self, ptr)
    }

    fn read_bytes(&self, ptr: Self::Pointer, size: usize) -> Result<Vec<u8>, Self::Error> {
        Memory::read_bytes(self, ptr, size).map(|bytes| bytes.to_vec())
    }

    fn write_bytes(&mut self, ptr: Self::Pointer, bytes: &[u8]) -> Result<(), Self::Error> {
        Memory::write_bytes(self, ptr, bytes)
    }

    fn is_valid(&self, ptr: Self::Pointer) -> bool {
        Memory::is_valid(self, ptr)
    }

    fn null_ptr(&self) -> Self::Pointer {
        Memory::null_ptr(self)
    }
}

#[cfg(test)]
mod tests;
