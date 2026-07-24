// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_c_sem::CMemoryModel;
use clean_kernel::memory_model::{BorrowAccess, MemoryModel, MemoryRegion};
use clean_rust_sem::RustMemoryModel;
use std::fmt::Debug;

fn round_trip_through_shared_trait<M>(mut model: M)
where
    M: MemoryModel,
    M::Error: Debug,
{
    let allocation = model
        .alloc(8, 4)
        .expect("allocation through shared trait should succeed");
    let region = MemoryRegion::new(allocation, 2, 4);

    model
        .borrow_check(region, BorrowAccess::Mutable)
        .expect("mutable borrow should be accepted for a fresh allocation");
    model
        .write(region, &[1, 2, 3, 4])
        .expect("write through shared trait should succeed");
    assert_eq!(
        model.read(region).expect("read should succeed"),
        vec![1, 2, 3, 4]
    );

    model
        .dealloc(allocation)
        .expect("deallocation through shared trait should succeed");
    assert!(
        model.read(region).is_err(),
        "reading a deallocated region should fail"
    );
}

#[test]
fn c_memory_model_satisfies_shared_interface() {
    round_trip_through_shared_trait(CMemoryModel::new());
}

#[test]
fn rust_memory_model_satisfies_shared_interface() {
    round_trip_through_shared_trait(RustMemoryModel::new());
}

#[test]
fn rust_memory_model_rejects_conflicting_borrow() {
    let mut model = RustMemoryModel::new();
    let allocation = model.alloc(16, 8).expect("allocation should succeed");
    let region = MemoryRegion::new(allocation, 0, 8);

    model
        .borrow_check(region, BorrowAccess::Shared)
        .expect("shared borrow should succeed");
    assert!(
        model.borrow_check(region, BorrowAccess::Mutable).is_err(),
        "mutable borrow should conflict with an outstanding shared borrow"
    );
}

#[test]
fn c_memory_model_treats_borrow_check_as_access_validation() {
    let mut model = CMemoryModel::new();
    let allocation = model.alloc(16, 8).expect("allocation should succeed");
    let region = MemoryRegion::new(allocation, 0, 8);

    model
        .borrow_check(region, BorrowAccess::Shared)
        .expect("shared access should succeed");
    model
        .borrow_check(region, BorrowAccess::Mutable)
        .expect("mutable access should also succeed in the C adapter");
}
