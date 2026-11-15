// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conservative requested-storage/copy bounds for the sealed std B-tree.
//! This is logical prepayment, not an allocator/RSS/OOM guarantee.
//!
//! Source: Trust9ee `library/alloc/src/collections/btree/node.rs`, B=6,
//! CAPACITY=11, LeafNode's parent/index/len + key/value arrays, and InternalNode's
//! 12 child edges. `search.rs::find_key_index` searches a node linearly.

use super::ObservedValueError;
use core::alloc::Layout;
use core::mem::MaybeUninit;
use core::ptr::NonNull;

const CAPACITY: usize = 11;
const EDGES: usize = CAPACITY + 1;

pub(crate) struct InsertionCost {
    pub(crate) work: usize,
    pub(crate) copy_bytes: usize,
}

pub(crate) fn population_work(len: usize) -> Result<usize, ObservedValueError> {
    // Even a single leaf can inspect every key. Include an empty-edge visit.
    len.checked_add(1)
        .ok_or(ObservedValueError::CapacityOverflow)
}

fn add(a: usize, b: usize) -> Result<usize, ObservedValueError> {
    a.checked_add(b).ok_or(ObservedValueError::CapacityOverflow)
}

fn multiply(a: usize, b: usize) -> Result<usize, ObservedValueError> {
    a.checked_mul(b).ok_or(ObservedValueError::CapacityOverflow)
}

fn node_storage<K, V>() -> Result<usize, ObservedValueError> {
    // Price an internal node even for a leaf. Include each field's alignment
    // slack and final node alignment, without assuming repr(Rust) field order.
    let fields = [
        Layout::new::<Option<NonNull<()>>>(),
        Layout::new::<MaybeUninit<u16>>(),
        Layout::new::<u16>(),
        Layout::array::<MaybeUninit<K>>(CAPACITY)
            .map_err(|_| ObservedValueError::CapacityOverflow)?,
        Layout::array::<MaybeUninit<V>>(CAPACITY)
            .map_err(|_| ObservedValueError::CapacityOverflow)?,
        Layout::array::<MaybeUninit<NonNull<()>>>(EDGES)
            .map_err(|_| ObservedValueError::CapacityOverflow)?,
    ];
    let mut bytes = 0;
    let mut alignment = 1;
    for field in fields {
        bytes = add(bytes, add(field.size(), field.align() - 1)?)?;
        alignment = alignment.max(field.align());
    }
    add(bytes, alignment - 1)
}

pub(crate) fn insertion_cost<K, V>(len: usize) -> Result<InsertionCost, ObservedValueError> {
    // With n existing keys, height and the number of ancestor splits are at
    // most n+1. Reserve FOUR full internal-node images per level plus a fresh
    // root level: old-node shifts/updates, new split node, parent/root work,
    // and carried temporary key/value/edge storage. This also covers the
    // first empty-tree leaf. Charge each complete node's key/value/edge/header
    // population, including eventual retirement. No logical array extent is
    // used: n is the number of retained map entries.
    let levels = add(len, 2)?;
    let images = multiply(levels, 4)?;
    let node_work = add(add(CAPACITY, EDGES)?, 5)?;
    Ok(InsertionCost {
        work: multiply(images, node_work)?,
        copy_bytes: multiply(images, node_storage::<K, V>()?)?,
    })
}
