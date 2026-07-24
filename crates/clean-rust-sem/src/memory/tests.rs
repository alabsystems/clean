// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::stack::Stack;
use crate::types::UintType;

#[test]
fn test_allocation() {
    let mut mem = Memory::new();

    let addr = mem.allocate(16).expect("allocation failed");
    assert!(mem.is_valid(addr));
    assert!(!mem.is_null(addr));
}

#[test]
fn test_read_write() {
    let mut mem = Memory::new();

    let addr = mem.allocate_aligned(8, 8).unwrap();

    mem.write_u32(addr, 42).unwrap();
    assert_eq!(mem.read_u32(addr).unwrap(), 42);

    mem.write_u64(addr, 0xDEAD_BEEF).unwrap();
    assert_eq!(mem.read_u64(addr).unwrap(), 0xDEAD_BEEF);
}

#[test]
fn test_use_after_free() {
    let mut mem = Memory::new();

    let addr = mem.allocate(4).unwrap();
    mem.deallocate(addr).unwrap();

    let result = mem.read_u32(addr);
    assert!(matches!(result, Err(MemoryError::UseAfterFree(_))));
}

#[test]
fn test_double_free() {
    let mut mem = Memory::new();

    let addr = mem.allocate(4).unwrap();
    mem.deallocate(addr).unwrap();

    let result = mem.deallocate(addr);
    assert!(matches!(result, Err(MemoryError::DoubleFree(_))));
}

#[test]
fn test_out_of_bounds() {
    let mut mem = Memory::new();

    let addr = mem.allocate_aligned(4, 8).unwrap();

    // Try to read 8 bytes from 4-byte allocation
    let result = mem.read_u64(addr);
    assert!(matches!(result, Err(MemoryError::OutOfBounds { .. })));
}

#[test]
fn test_pointer_offset() {
    let addr = Address::new(AllocId(1), 10);

    let forward = addr.offset(5).unwrap();
    assert_eq!(forward.offset, 15);

    let backward = addr.offset(-3).unwrap();
    assert_eq!(backward.offset, 7);

    // Overflow protection
    let overflow = addr.offset(-20);
    assert!(
        overflow.is_none(),
        "negative offset past zero should return None"
    );

    // i64::MIN must not panic from negation overflow (#3039)
    assert!(
        addr.offset(i64::MIN).is_none(),
        "i64::MIN offset should return None, not panic"
    );
}

#[test]
fn test_in_bounds_overflow() {
    let alloc = Allocation::new(AllocId(1), 1024, 8);

    // Normal access
    assert!(alloc.in_bounds(0, 1024));
    assert!(!alloc.in_bounds(0, 1025));

    // u64::MAX offset must not wrap (#3039)
    assert!(!alloc.in_bounds(u64::MAX, 1));

    // usize::MAX size must not wrap
    assert!(!alloc.in_bounds(0, usize::MAX));

    // offset + size overflow
    assert!(!alloc.in_bounds(1, usize::MAX));

    #[cfg(target_pointer_width = "32")]
    assert!(!alloc.in_bounds(u64::from(u32::MAX) + 1, 1));
}

#[test]
fn test_typed_allocation() {
    let mut mem = Memory::new();

    let u32_ty = RustType::Uint(UintType::U32);
    let addr = mem.allocate_typed(&u32_ty).unwrap();

    let alloc = mem.get_allocation(addr.alloc_id).unwrap();
    assert_eq!(alloc.size, 4);
    assert_eq!(alloc.ty, Some(u32_ty));
}

#[test]
fn test_typed_array_allocation_tracks_slice_len() {
    let mut mem = Memory::new();
    let array_ty = RustType::Array {
        element: Box::new(RustType::Uint(UintType::U32)),
        len: crate::types::ConstGenericArg::usize(3),
    };

    let addr = mem
        .allocate_typed(&array_ty)
        .expect("typed array allocation");
    let alloc = mem
        .get_allocation(addr.alloc_id)
        .expect("allocation metadata");

    assert_eq!(alloc.ty, Some(array_ty));
    assert_eq!(alloc.slice_len(), Some(3));
    assert_eq!(mem.slice_len(addr), Some(3));
}

#[test]
fn test_stack_frame() {
    let mut mem = Memory::new();
    let mut stack = Stack::new();

    // Push a frame
    let frame = stack.push_frame();
    let addr = mem.allocate(4).unwrap();
    frame.add_local(addr);

    assert_eq!(stack.depth(), 1);
    assert_eq!(stack.current_frame().unwrap().get_local(0), Some(addr));

    // Pop frame
    let popped = stack.pop_frame().unwrap();
    assert_eq!(popped.get_local(0), Some(addr));
    assert_eq!(stack.depth(), 0);
}

#[test]
fn test_misaligned_read() {
    let mut mem = Memory::new();

    // 16 bytes with align 8 so allocation alignment is sufficient;
    // only offset misalignment triggers Misaligned errors.
    let addr = mem.allocate_aligned(16, 8).unwrap();

    // Offset 1 is not aligned for u16 (align 2)
    let misaligned = addr.offset(1).unwrap();
    let result = mem.read_u16(misaligned);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 1,
                align: 2
            })
        ),
        "expected Misaligned for u16 at offset 1, got: {result:?}"
    );

    // Offset 1 is not aligned for u32 (align 4)
    let result = mem.read_u32(misaligned);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 1,
                align: 4
            })
        ),
        "expected Misaligned for u32 at offset 1, got: {result:?}"
    );

    // Offset 2 is aligned for u16 but not u32
    let offset2 = addr.offset(2).unwrap();
    assert!(mem.read_u16(offset2).is_ok());
    let result = mem.read_u32(offset2);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 2,
                align: 4
            })
        ),
        "expected Misaligned for u32 at offset 2, got: {result:?}"
    );

    // Offset 3 is not aligned for u64 (align 8)
    let offset3 = addr.offset(3).unwrap();
    let result = mem.read_u64(offset3);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 3,
                align: 8
            })
        ),
        "expected Misaligned for u64 at offset 3, got: {result:?}"
    );

    // u8 reads never fail alignment (align 1)
    assert!(mem.read_u8(misaligned).is_ok());
}

#[test]
fn test_declared_alignment_required() {
    let mut mem = Memory::new();

    let addr = mem.allocate(8).unwrap();

    let read = mem.read_u32(addr);
    assert!(
        matches!(
            read,
            Err(MemoryError::Misaligned {
                offset: 0,
                align: 4
            })
        ),
        "expected Misaligned for read_u32 on align-1 allocation, got: {read:?}"
    );

    let write = mem.write_u32(addr, 42);
    assert!(
        matches!(
            write,
            Err(MemoryError::Misaligned {
                offset: 0,
                align: 4
            })
        ),
        "expected Misaligned for write_u32 on align-1 allocation, got: {write:?}"
    );
}

#[test]
fn test_misaligned_write() {
    let mut mem = Memory::new();

    let addr = mem.allocate_aligned(16, 8).unwrap();
    let misaligned = addr.offset(1).unwrap();

    let result = mem.write_u32(misaligned, 42);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 1,
                align: 4
            })
        ),
        "expected Misaligned for write_u32 at offset 1, got: {result:?}"
    );

    let result = mem.write_u64(misaligned, 0xFF);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 1,
                align: 8
            })
        ),
        "expected Misaligned for write_u64 at offset 1, got: {result:?}"
    );

    let result = mem.write_u16(misaligned, 7);
    assert!(
        matches!(
            result,
            Err(MemoryError::Misaligned {
                offset: 1,
                align: 2
            })
        ),
        "expected Misaligned for write_u16 at offset 1, got: {result:?}"
    );

    // u8 writes never fail alignment
    assert!(mem.write_u8(misaligned, 0x42).is_ok());
}

#[test]
fn test_aligned_offset_access() {
    let mut mem = Memory::new();

    let addr = mem.allocate_aligned(16, 8).unwrap();

    // Write u32 at offset 0 (aligned to 4)
    mem.write_u32(addr, 0xAAAA).unwrap();
    assert_eq!(mem.read_u32(addr).unwrap(), 0xAAAA);

    // Write u32 at offset 4 (aligned to 4)
    let at4 = addr.offset(4).unwrap();
    mem.write_u32(at4, 0xBBBB).unwrap();
    assert_eq!(mem.read_u32(at4).unwrap(), 0xBBBB);

    // Write u64 at offset 8 (aligned to 8)
    let at8 = addr.offset(8).unwrap();
    mem.write_u64(at8, 0xCCCC_DDDD).unwrap();
    assert_eq!(mem.read_u64(at8).unwrap(), 0xCCCC_DDDD);

    // Write u16 at offset 6 (aligned to 2)
    let at6 = addr.offset(6).unwrap();
    mem.write_u16(at6, 0x1234).unwrap();
    assert_eq!(mem.read_u16(at6).unwrap(), 0x1234);
}

#[test]
fn test_null_pointer() {
    let mut mem = Memory::new();

    let null = mem.null_ptr();
    assert!(mem.is_null(null));

    // Reading from null should fail with NullPointer
    let result = mem.read_u8(null);
    assert!(
        matches!(result, Err(MemoryError::NullPointer)),
        "expected NullPointer on read, got: {result:?}"
    );

    // Writing to null should also fail with NullPointer
    let result = mem.write_bytes(null, &[0x42]);
    assert!(
        matches!(result, Err(MemoryError::NullPointer)),
        "expected NullPointer on write, got: {result:?}"
    );

    // Deallocating null should fail with NullPointer
    let result = mem.deallocate(null);
    assert!(
        matches!(result, Err(MemoryError::NullPointer)),
        "expected NullPointer on deallocate, got: {result:?}"
    );
}
