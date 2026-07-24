// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::sem_memory_trait::{MemoryModel, ProvenanceModel};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TestAllocId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TestPtr {
    alloc_id: TestAllocId,
    offset: i64,
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

#[derive(Debug)]
struct MockMemory {
    blocks: HashMap<TestAllocId, Vec<u8>>,
    next_alloc: u64,
}

impl Default for MockMemory {
    fn default() -> Self {
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
        TestPtr {
            alloc_id: TestAllocId(0),
            offset: 0,
        }
    }
}

#[test]
fn shared_memory_trait_round_trip() {
    let mut memory = MockMemory::default();
    let ptr = memory.alloc(4, 4).expect("allocation should succeed");

    assert_eq!(ptr.alloc_id(), TestAllocId(1));
    assert_eq!(ptr.offset_bytes(), 0);
    assert_eq!(
        ptr.with_offset(2).expect("offset should stay in range"),
        TestPtr {
            alloc_id: TestAllocId(1),
            offset: 2,
        }
    );

    memory
        .write_bytes(ptr, &[1, 2, 3, 4])
        .expect("write should succeed");
    assert_eq!(
        memory.read_bytes(ptr, 4).expect("read should succeed"),
        vec![1, 2, 3, 4]
    );

    memory.dealloc(ptr).expect("deallocation should succeed");
    assert!(!memory.is_valid(ptr));
    assert_eq!(memory.null_ptr().alloc_id(), TestAllocId(0));
}
